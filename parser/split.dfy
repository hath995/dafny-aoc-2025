module Split {
    function join(ss: seq<string>, separator: string ): string {
        if |ss| == 0 then "" else if |ss| == 1 then ss[0] else ss[0] + separator + join(ss[1..], separator)
    }

    function partialSumSeq(ss: seq<string>, separator: string ): string {
        if |ss| == 0 then "" else ss[0] + separator + partialSumSeq(ss[1..], separator)
    }

    function sumLength(xs: seq<string>): nat {
        if |xs| == 0 then 0 else |xs[|xs|-1]|+sumLength(xs[..|xs|-1])
    }

    function prod(x:int,y: int): int {
        x * y
    }

    predicate nextStartingIndex(sindex: nat, separator: string, results: seq<string>) {
        prod((|results|), |separator|) + sumLength(results) == sindex
    }

    predicate finalIndex(s: string, separator: string, results: seq<string>) {
        prod((|results|-1), |separator|) + sumLength(results) == |s|
    }

    lemma sumSeqPartial(ss: seq<string>,  separator: string)
        requires |ss| >0
        ensures join(ss, separator) == partialSumSeq(ss[..|ss|-1], separator)+ss[|ss|-1]
    {
        if |ss| == 1 {

        }else{
            assert |ss| > 1;
            sumSeqPartial(ss[1..], separator);
            assert join(ss[1..], separator) == partialSumSeq(ss[1..][..|ss[1..]|-1], separator)+ss[1..][|ss[1..]|-1];
            assert ss[|ss|-1] == ss[1..][|ss[1..]|-1];
            assert ss[1..][..|ss[1..]|-1] == ss[1..|ss|-1];

        }
    }

    lemma partialSumSeqConcat(ss:seq<string>, xx: seq<string>, separator: string)
        ensures partialSumSeq(ss+xx, separator) == partialSumSeq(ss, separator) + partialSumSeq(xx, separator)
    {
        if |ss| == 0 {
            calc {
                ss+xx;
                []+xx;
                xx;
            }
        }else if |xx| == 0 {
            calc {
                ss+[];
                ss+[];
                ss;
            }
        }else {
            assert |ss| != 0;
            partialSumSeqConcat(ss[1..], xx, separator);
            calc {
                partialSumSeq(ss+xx, separator);
                (ss+xx)[0]+separator+partialSumSeq((ss+xx)[1..],separator);
                {
                    assert (ss+xx)[0] == ss[0];
                    assert (ss+xx)[1..] == ss[1..]+xx;
                }
                ss[0]+separator+partialSumSeq(ss[1..]+xx,separator);
                ss[0]+separator+partialSumSeq(ss[1..], separator)+partialSumSeq(xx,separator);
            }

        }
    }

    function splitOnLetter(s: string, index: int, results: seq<string>): seq<string> 
        requires 0 <= index <= |s|
        requires forall i :: 0 <= i <  index <= |results| ==> s[i..i+1] == results[i]
        requires |results| == index
        ensures forall i :: 0 <= i < |s| <= |splitOnLetter(s, index, results)|  ==> s[i..i+1] == splitOnLetter(s, index, results)[i]
        ensures |splitOnLetter(s, index, results)| == |s|
        decreases |s|-index
    {
        if index < |s| then
            assert index <= index +1;
            var nextResult:= results+[s[index..index+1]];
            splitOnLetter(s, index+1, results+[s[index..index+1]])
        else results
    }

    function splitHelper(s: string, separator: string, index: nat, sindex: nat, results: seq<string>): seq<seq<char>>
        requires index <= |s|
        requires sindex <= |s|
        requires sindex <= index
        requires |separator| > 0
        requires |results| <= index
        requires |results| == 0 ==> sindex == 0
        requires |results| > 0 ==> nextStartingIndex(sindex, separator, results)
        requires partialSumSeq(results, separator) == s[..sindex]
        ensures results <= splitHelper(s, separator, index, sindex, results)
        ensures 1 <= |splitHelper(s, separator, index, sindex, results)| <= |s|+1
        ensures (|splitHelper(s,separator, index, sindex, results)|-1)*|separator| + sumLength(splitHelper(s,separator, index, sindex, results)) == |s|
        ensures join(splitHelper(s, separator, index, sindex, results), separator) == s
        decreases |s| - index
    {
        if index == |s| then
            var next := results+ [s[sindex..index]];
            assert |results| > 0 ==> |results|*|separator| + sumLength(results) == sindex;
            sumSeqPartial(next, separator);
            assert results == next[..|next|-1];
            assert partialSumSeq(next[..|next|-1], separator) == s[..sindex];
            next
        else if index+|separator| > |s| then
            splitHelper(s, separator, |s|, sindex, results)
        else if s[index..index+|separator|] == separator then
            partialSumSeqConcat(results,[s[sindex..index]], separator);
            splitHelper(s, separator, index+|separator|, index+|separator|, results + [s[sindex..index]])
        else splitHelper(s, separator, index+1, sindex, results)
    }

    lemma {:induction } SplitOnLettersSlice(s: string, i: int)
        requires 0 <= i < |s|
        ensures join(splitOnLetter(s, 0, [])[i..], "") == s[i..]
        decreases |s|-i
    {
    }

    lemma SplitOnLettersIdemp(s: string)
        ensures join(splitOnLetter(s, 0, []), "") == s
    {
        if |s| == 0 {
            assert s == "";
            assert splitOnLetter(s, 0,[]) ==[];
            assert join([],"") == "";
            assert join(splitOnLetter(s, 0, []), "") == s;
        }else if |s| == 1 {
            assert splitOnLetter(s, 0,[]) ==[s[0..1]];
        }else{
            assert s == s[0..];
            SplitOnLettersSlice(s, 0);
            assert |splitOnLetter(s,0,[])| == |s|;
            assert 0 <= 1 < |splitOnLetter(s, 0, [])|;
            assert splitOnLetter(s, 0, [])[0] == s[0..1];
        }
    }

    function split(s: string, separator: string): seq<string> 
        ensures join(split(s, separator), separator) == s
    {
        if |separator| == 0 then
            SplitOnLettersIdemp(s);
            splitOnLetter(s, 0, [])
        else
            splitHelper(s, separator, 0, 0, [])
    }

    predicate Contains(haystack: string, needle: string)
        ensures Contains(haystack, needle) <==> exists k :: 0 <= k <= |haystack| && needle <= haystack[k..] 
        ensures Contains(haystack, needle) <==> exists i :: 0 <= i <= |haystack| && (needle <= haystack[i..])
        ensures !Contains(haystack, needle) <==> forall i :: 0 <= i <= |haystack| ==> !(needle <= haystack[i..])
    {
        if needle <= haystack then 
            assert haystack[0..] == haystack;
            true 
        else if |haystack| > 0 then 
            assert forall i :: 1 <= i <= |haystack| ==> haystack[i..] == haystack[1..][(i-1)..];
            Contains(haystack[1..], needle)
        else 
            false
    }

    function splitOnBreak(s: string): seq<string> {
        if Contains(s, "\r\n") then split(s,"\r\n") else split(s,"\n")
    }

    function splitOnDoubleBreak(s: string): seq<string> {
        if Contains(s, "\r\n") then split(s,"\r\n\r\n") else split(s,"\n\n")
    }

    export provides split, Contains, splitOnBreak, splitOnDoubleBreak, join
}