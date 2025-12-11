include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
module Problem3 {
    import opened Split
    import opened ParseInt
    // import opened Std.Collections.Seq
    function Map<T, U>(f: T -> U, xs: seq<T>): seq<U> {
        if xs == [] then [] else [f(xs[0])] + Map(f, xs[1..])
    }

    method parseInput(input: string) returns (xs: seq<seq<nat>>) {
        var lines := splitOnBreak(input);
        xs := [];
        for i := 0 to |lines| 
            invariant |xs| == i
        {
            var bank := Map(Integer, split(lines[i],""));
            expect forall i :: 0 <= i < |bank| ==> bank[i] > 0;
            xs := xs + [bank];
        }
    }

    function ToNat(bank: seq<nat>): nat {
        if bank == [] then 0
        else bank[|bank|-1] + 10*ToNat(bank[..|bank|-1])
    }

    function MaxIndex(xs: seq<nat>): (nat, nat)
        requires |xs| > 0
        ensures 0 <= MaxIndex(xs).1 < |xs|
        ensures MaxIndex(xs).0 == xs[MaxIndex(xs).1]
        ensures forall i :: 0 <= i < |xs| ==> MaxIndex(xs).0 >= xs[i]
        ensures forall i :: 0 <= i < |xs| && xs[i] == MaxIndex(xs).0 ==> MaxIndex(xs).1 <= i
    {
        if |xs| == 1 then
            (xs[0], 0)
        else
            var rest := MaxIndex(xs[1..]);
            if xs[0] >= rest.0 then
                (xs[0], 0)
            else
                assert xs == [xs[0]]+xs[1..];
                (rest.0, rest.1+1)
    }

    function fls(xs: seq<nat>, index: nat, count: nat): seq<nat>
        requires |xs| >= count
        requires index < |xs|-count+1
        requires count > 0
        decreases count
        ensures |fls(xs, index, count)| == count
        ensures forall x :: x in fls(xs, index, count) ==> x in xs
    {
       if count == 1 then
         var mi := MaxIndex(xs[index..]);
         [mi.0]
       else
         var mi := MaxIndex(xs[index..|xs|-count+1]);
         [mi.0]+fls(xs, index+mi.1+1, count-1)
    }
    // fls(xs, index+mi.1+1, count-1) in subsetSeqs(xs[index+mi.1+1..]);
    
    method problem3_1(input: string) returns (x: int) {
        var banks := parseInput(input);
        x := 0;
        for i := 0 to |banks|
        {
            expect |banks[i]| > 2;
            var best := fls(banks[i], 0, 2);
            x := x + ToNat(best);
        }
    }

    method problem3_2(input: string) returns (x: int) {
        var banks := parseInput(input);
        x := 0;
        for i := 0 to |banks|
        {
            expect |banks[i]| > 12;
            var best := fls(banks[i], 0, 12);
            x := x + ToNat(best);
        }
        print "\n";
    }

    function prepend<T(==)>(x: T, xs: seq<T>): seq<T> {
        [x]+ xs
    }

    function subsetSeqs<T(==)>(xs: seq<T>): seq<seq<T>>
    {
        if xs == [] then
            [[]]
        else
            Map((ss: seq<T>) => prepend(xs[0], ss), subsetSeqs(xs[1..]))
            +
            subsetSeqs(xs[1..])
    }

    lemma LemmaSubsetsContained<T>(xs: seq<T>, xxs: seq<T>, i: nat)
        requires |xs| > 0
        requires i < |xs|
        requires xxs in subsetSeqs(xs[i..])
        ensures xxs in subsetSeqs(xs)
    {
        if |xs| == 1 {

            assert xxs in subsetSeqs(xs);
        }else{
            // LemmaSubsetsContained(xs, )
            if i == 0 {
                assert xs[0..] == xs;
                assert xxs in subsetSeqs(xs);
            } else {
                assert xs == [xs[0]]+xs[1..];
                if i == 1 {

                    assert xxs in subsetSeqs(xs);
                }else{
                    LemmaSubsetsContained(xs[1..], xxs, i-1);

                    assert xxs in subsetSeqs(xs);
                }

            }
            assert xxs in subsetSeqs(xs);
        }
    }

    lemma LemmaInMap<T, U>(f: T -> U, xs: seq<T>, x: T)
        requires x in xs
        ensures f(x) in Map(f, xs)
    {
        if xs[0] == x {
            // assert x in xs[1..];
            assert f(xs[0]) == f(x);
            assert Map(f, xs)[0] == f(x);
        } else {
            LemmaInMap(f, xs[1..], x);
        }
    }
    lemma LemmaPrependInSubsetSeqs<T>(head: T, tail: seq<T>, rest: seq<T>)
    requires tail in subsetSeqs(rest)
    ensures (prepend(head, tail)) in subsetSeqs([head] + rest)
{
    var full := [head] + rest;
    // We want to show [head]+tail is in the Map(...) part of subsetSeqs(full)
    var mapper := (ss: seq<T>) => prepend(head, ss);
    
    // Apply the mapping lemma
    LemmaInMap(mapper, subsetSeqs(rest), tail);
    
    assert prepend(head, tail) in Map(mapper, subsetSeqs(rest));
    // By definition, subsetSeqs(full) contains the Map result
    assert prepend(head, tail) in subsetSeqs(full);
}

    lemma lemmaSubsetSeqsContainsEmpty<T>(xs: seq<T>)
        ensures [] in subsetSeqs(xs)
    {
    }

// Main Lemma
lemma LemmaFlsInSubsetsContained(xs: seq<nat>, count: nat, index: nat)
    requires 0 < count < |xs|
    requires index < |xs|-count+1
    ensures fls(xs, index, count) in subsetSeqs(xs[index..])
{
    if count == 1 {
        // 1. Identify the max element
        var mi := MaxIndex(xs[index..]);
        var res := [mi.0];
        var relative_idx := mi.1;
        var element := xs[index + relative_idx];
        
        assert element == mi.0; // Link value
        
        var suffix_of_element := xs[index+relative_idx+1..];
        lemmaSubsetSeqsContainsEmpty(suffix_of_element);
        assert [] in subsetSeqs(suffix_of_element); // Base case

        LemmaPrependInSubsetSeqs(element, [], suffix_of_element);
        assert [element]+[] == [element];
        
        // Link construction to slice
        assert [element] + suffix_of_element == xs[index+relative_idx..];
        
        assert res in subsetSeqs(xs[index+relative_idx..]);

        // Link slice indices
        assert xs[index+relative_idx..] == xs[index..][relative_idx..];

        LemmaSubsetsContained(xs[index..], res, relative_idx);
    } else {
        // 1. Identify the head and tail of the result
        var window := xs[index..|xs|-count+1];
        var mi := MaxIndex(window);
        var res_head := mi.0;
        
        var next_index := index + mi.1 + 1;
        var res_tail := fls(xs, next_index, count-1);
        
        // 2. Apply IH to the tail
        LemmaFlsInSubsetsContained(xs, count-1, next_index);
        assert res_tail in subsetSeqs(xs[next_index..]);

        // 3. Reconstruct the full sequence at the point of the found element
        // The element was found at xs[index + mi.1]
        // Let's call the slice starting at that element "pivot_slice"
        var pivot_index := index + mi.1;
        var pivot_slice := xs[pivot_index..];
        
        assert pivot_slice == [res_head] + xs[next_index..];
        
        // Use Helper 2: [head] + tail is in subsetSeqs([head] + rest)
        LemmaPrependInSubsetSeqs(res_head, res_tail, xs[next_index..]);
        assert [res_head] + res_tail in subsetSeqs(pivot_slice);
        
        // 4. Hoist it up to xs[index..]
        // pivot_slice is a suffix of xs[index..] starting at mi.1
        LemmaSubsetsContained(xs[index..], fls(xs, index, count), mi.1);
    }
}

    predicate lexSort(xs: seq<nat>, ys: seq<nat>)
        requires |xs| > 0
    {
        if |xs| > |ys| then
            true
        else if |xs| < |ys| then
            false
        else
            if xs[0] > ys[0] then
                true
            else if xs[0] < ys[0] then
                false
            else
                if |xs| == 1 && xs[0] == ys[0] then true
                else lexSort(xs[1..], ys[1..])
    }

    lemma equalLex(xs: seq<nat>, ys: seq<nat>)
        requires |xs| > 0
        requires xs == ys
        ensures lexSort(xs, ys)
    {}

    lemma TestLex() {
        assert lexSort([2,1,1], [1,1,1]);
        assert lexSort([2,1,1], [2,1]);
        assert lexSort([2,2,1], [2,2,1]);
        // assert lexSort([2,2,2], [2,2,3]);
    }

    lemma flsInSet(bank: seq<nat>, count: nat)
        requires |bank| > count
        requires 0 < count < |bank|
        ensures fls(bank, 0, count) in set bs | bs in subsetSeqs(bank) && |bs| == count
    {
        LemmaFlsInSubsetsContained(bank, count, 0);
        assert bank[0..] == bank;
    }

    lemma LemmaHeadLocation(xs: seq<nat>, s: seq<nat>) returns (k: nat)
        requires s in subsetSeqs(xs)
        requires |s| > 0
        requires |s| <= |xs|
        ensures k <= |xs| - |s|
        ensures xs[k] == s[0]
        ensures s[1..] in subsetSeqs(xs[k+1..])
    {
        // Must handle empty case to satisfy totality, though preconditions mostly prevent it
        if xs == [] {
            assert false; 
        }

        var mapPart := Map((ss: seq<nat>) => prepend(xs[0], ss), subsetSeqs(xs[1..]));
        
        if s in mapPart {
            k := 0;
            LemmaMapInversion(xs[0], subsetSeqs(xs[1..]), s);
            // Proven: s[0] == xs[0] and s[1..] in subsetSeqs(xs[1..])
        } else {
            // s must be in the tail part
            assert s in subsetSeqs(xs[1..]);

            // FIX: Explicitly prove length bound to satisfy precondition for recursion
            LemmaSubsequenceLengthBound(xs[1..], s);
            assert |s| <= |xs[1..]|;

            var k_tail := LemmaHeadLocation(xs[1..], s);
            k := k_tail + 1;
        }
    }

 lemma LemmaMapInversion<T>(h: T, tails: seq<seq<T>>, s: seq<T>)
        requires s in Map((t: seq<T>) => prepend(h, t), tails)
        requires |s| > 0
        ensures s[0] == h
        ensures s[1..] in tails
    {
        if s == prepend(h, tails[0]) {
        } else {
            LemmaMapInversion(h, tails[1..], s);
        }
    }

    // If a subsequence has the same length as the source, it must be the source itself.
    lemma LemmaSubsequenceLengthEquality<T>(xs: seq<T>, s: seq<T>)
        requires s in subsetSeqs(xs)
        requires |s| == |xs|
        ensures s == xs
    {
        if xs == [] {
        } else {
            if s in subsetSeqs(xs[1..]) {
                LemmaSubsequenceLengthBound(xs[1..], s);
                assert |s| <= |xs|-1; 
                assert false;
            }
            LemmaMapInversion(xs[0], subsetSeqs(xs[1..]), s);
            LemmaSubsequenceLengthEquality(xs[1..], s[1..]);
        }
    }

    lemma LemmaSubsequenceLengthBound<T>(xs: seq<T>, s: seq<T>)
        requires s in subsetSeqs(xs)
        ensures |s| <= |xs|
    {
        if xs == [] {
            assert |s| <= |xs|;
        } else {
            if s in subsetSeqs(xs[1..]) {
                LemmaSubsequenceLengthBound(xs[1..], s);
                assert |s| <= |xs|;
            } else {
                // LemmaMapInversion(xs[0], subsetSeqs(xs[1..]), s);
                // LemmaSubsequenceLengthBound(xs[1..], s[1..]);
                if s == [] {

                    assert |s| <= |xs|;
                }else{
                    assert |s| > 0;
                    calc {
                        subsetSeqs(xs);
                        Map((ss: seq<T>) => prepend(xs[0], ss), subsetSeqs(xs[1..])) + subsetSeqs(xs[1..]);
                    }
                    assert s in Map((ss: seq<T>) => prepend(xs[0], ss), subsetSeqs(xs[1..]));
                    LemmaMapInversion(xs[0], subsetSeqs(xs[1..]), s);
                    assert s[0] == xs[0];
                    LemmaSubsequenceLengthBound(xs[1..], s[1..]);
                    assert |s| <= |xs|;
                }
            }
        }
    }

    lemma LemmaFlsReturnsSuffix(xs: seq<nat>, index: nat, count: nat)
        requires |xs| > count
        requires index < |xs| - count + 1
        requires count > 0
        requires |xs| - index == count // Specific boundary
        decreases count
        ensures fls(xs, index, count) == xs[index..]
    {
        if count == 1 {
            // window is size 1, picks xs[index]
        } else {
            // window is size 1, picks xs[index]
            // recurse on index+1, count-1. |xs| - (index+1) == count - 1.
            LemmaFlsReturnsSuffix(xs, index+1, count-1);
        }
    }



  lemma LemmaFlsSliceEquivalence(xs: seq<nat>, index: nat, count: nat)
        requires |xs| > count
        requires index < |xs|-count+1
        requires count > 0
        requires |xs| - index > count // Strict inequality needed to call fls on the slice
        decreases count
        ensures fls(xs, index, count) == fls(xs[index..], 0, count)
    {
        if count == 1 {
            // Base case: both look at identical sequences
            assert xs[index..] == xs[index..][0..];
            assert fls(xs, index, count) == fls(xs[index..], 0, count);
        } else {
            var window := xs[index..|xs|-count+1];
            var mi := MaxIndex(window);
            var next_idx := index + mi.1 + 1;
            var rel_next_idx := mi.1 + 1;
            
            // Check boundary for the recursive step
            if |xs| - next_idx == count - 1 {
                // Recursion hits boundary -> Use Suffix Lemma
                LemmaFlsReturnsSuffix(xs, next_idx, count-1);
                assert fls(xs, next_idx, count-1) == xs[next_idx..];
                LemmaFlsReturnsSuffix(xs[index..], rel_next_idx, count-1);
                assert fls(xs[index..], rel_next_idx, count-1) == xs[next_idx..];
                assert xs[next_idx..] == xs[index..][rel_next_idx..];
                calc{
                    fls(xs, index, count);
                    [mi.0]+fls(xs, index+mi.1+1, count-1);
                    [mi.0]+fls(xs, next_idx, count-1);
                    [mi.0]+xs[next_idx..];
                }
                assert xs[index..|xs|-count+1] == xs[index..][0..|xs|-index-count+1];
                calc {
                    fls(xs[index..], 0, count);
                    [mi.0]+fls(xs[index..], rel_next_idx, count-1);
                }
                assert fls(xs, index, count) == fls(xs[index..], 0, count);
            } else {
                // Recursion is safe -> Use IH
                LemmaFlsSliceEquivalence(xs, next_idx, count-1);
                LemmaFlsSliceEquivalence(xs[index..], rel_next_idx, count-1);
                assert xs[next_idx..] == xs[index..][rel_next_idx..];
                assert xs[index..|xs|-count+1] == xs[index..][0..|xs|-index-count+1];
                assert fls(xs, index, count) == fls(xs[index..], 0, count);
            }
        }
    }

    lemma TheoremFlsIsLexMax(bank: seq<nat>, count: nat, s: seq<nat>)
        requires |bank| > count
        requires 0 < count < |bank|
        requires s in subsetSeqs(bank)
        requires |s| == count
        ensures lexSort(fls(bank, 0, count), s)
    {
        var f := fls(bank, 0, count);
        
        // 1. Compare Heads
        var window := bank[0..|bank|-count+1];
        var mi := MaxIndex(window);
        var f_idx := mi.1; 
        if count == 1 {
            calc{
                fls(bank, 0, count);
                [mi.0];
            }
        }else{

        }
        assert f[0] == bank[f_idx];

        var s_idx := LemmaHeadLocation(bank, s);
        assert s[0] == bank[s_idx];
        assert s_idx <= |bank| - count; // s_idx in window

        if f[0] > s[0] {
            // f wins immediately
            assert lexSort(fls(bank, 0, count), s);
        } else {
            assert f[0] == s[0];
            // MaxIndex ensures f picks the earliest occurrence
            assert f_idx <= s_idx;

            if count == 1 {
                // Single element sequences are equal
            } else {
                // 2. Compare Tails
                var next_count := count - 1;
                var f_tail := fls(bank, f_idx+1, next_count);
                var s_tail := s[1..];
                
                // s_tail is a subsequence of bank[s_idx+1..]
                // Since f_idx <= s_idx, bank[s_idx+1..] is a suffix of bank[f_idx+1..]
                LemmaSubsetsContained(bank[f_idx+1..], s_tail, s_idx - f_idx);
                
                var remaining_len := |bank| - (f_idx + 1);
                
                if remaining_len == next_count {
                    // Boundary Case: Only one possible subsequence exists
                    LemmaFlsReturnsSuffix(bank, f_idx+1, next_count);
                    assert f_tail == bank[f_idx+1..];
                    
                    LemmaSubsequenceLengthEquality(bank[f_idx+1..], s_tail);
                    assert f_tail == s_tail;
                    assert f[0] >= s[0];
                    assert f == [f[0]]+f_tail;
                    assert s == [s[0]]+s_tail;
                    equalLex(f_tail, s_tail);
                    assert lexSort(f_tail, s_tail);
                    assert lexSort(fls(bank, 0, count), s);
                } else {
                    // Standard Case: Use Induction
                    var next_bank := bank[f_idx+1..];
                    
                    // Induction on the slice
                    TheoremFlsIsLexMax(next_bank, next_count, s_tail);
                    
                    // Prove that fls on the slice is equivalent to fls on the original
                    LemmaFlsSliceEquivalence(bank, f_idx+1, next_count);
                    
                    assert lexSort(f_tail, s_tail);
                    assert lexSort(fls(bank, 0, count), s);
                }
            }
        }
    }

    lemma flsIsLexicographicMax(bank: seq<nat>, count: nat)
        requires |bank| > 0
        requires 0 < count < |bank|
        ensures forall ss :: ss in subsetSeqs(bank) && |ss| == count ==> lexSort(fls(bank, 0, count), ss)
    {
        forall ss | ss in subsetSeqs(bank) && |ss| == count
            ensures lexSort(fls(bank, 0, count), ss)
        {
            TheoremFlsIsLexMax(bank, count, ss);
        }
    }


}
