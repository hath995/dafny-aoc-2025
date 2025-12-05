include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
module Problem5 {
    import opened Split
    import opened ParseInt
    import opened Std.Collections.Seq
    import opened Std.Relations

    method parseInput(input: string) returns (ranges: seq<(nat,nat)>, ids: seq<nat>)
        ensures forall range :: range in ranges ==> range.0 <= range.1
    {
        var pieces := splitOnDoubleBreak(input);
        expect |pieces| == 2;
        var rangeStrings := splitOnBreak(pieces[0]);
        var idStrings := splitOnBreak(pieces[1]);

        ranges := [];
        ids := [];
        for i := 0 to |rangeStrings| 
            invariant |ranges| == i
            invariant forall range :: range in ranges ==> range.0 <= range.1
        {
            var split_range := split(rangeStrings[i], "-");
            expect |split_range| == 2;
            var start := Integer(split_range[0]);
            var end := Integer(split_range[1]);
            expect 0 < start <= end;
            ranges := ranges + [(start, end)];
        }

        for i := 0 to |idStrings|
            invariant |ids| == i
        {
            var id := Integer(idStrings[i]);
            expect 0 < id;
            ids := ids + [id];
        }
    }

    predicate IsFresh(range: (nat, nat), id: nat) {
        range.0 <= id <= range.1
    }

    predicate IsInRanges(ranges: seq<(nat,nat)>, id: nat) {
        exists i :: 0 <= i < |ranges| && IsFresh(ranges[i], id)
    }

    //fresh count function
    method problem5_1(input: string) returns (answer: int) {
        var ranges, ids := parseInput(input);
        answer := 0;
        for i := 0 to |ids| 
        {
            if IsInRanges(ranges, ids[i]) {
                answer := answer + 1;
            }
        }
        print "\n";
    }

    predicate IsOverlapping(left: (nat, nat), right: (nat,nat)) {
        !(left.1 < right.0 || right.1 < left.0)
    }

    lemma test() {
        assert IsOverlapping((3,6),(6,10));
        assert IsOverlapping((6,6),(6,10));
        assert IsOverlapping((6,6),(5,10));
        assert IsOverlapping((6,7),(3,10));
        assert IsOverlapping((542009870509829, 542009870509829), (536745635162015, 542009870509829));
        // assert IsOverlapping((3,5),(6,10));
        // assert IsOverlapping((13,65),(6,10));
        assert mergeRange((6,6),(6,10)) == (6,10);
        assert mergeRange((6,7),(3,10)) == (3,10);
    }

    function min(a: nat ,b:nat): nat {
        if a < b then a else b
    }

    function max(a: nat, b: nat): nat {
        if a <= b then b else a
    }

    function mergeRange(left: (nat, nat), right: (nat,nat)): (nat, nat) {
        (min(left.0, right.0), max(left.1, right.1))
    }

    predicate lteRange(left: (nat, nat), right: (nat, nat)) {
        left.1 <= right.1
    }

    lemma {:axiom} IsTotalOrder()
        ensures TotalOrdering(lteRange)

    predicate HasOverlapping(ranges: seq<(nat,nat)>) {
        exists i :: 0 <= i < |ranges|-1 && IsOverlapping(ranges[i], ranges[i+1])
        // exists i, j :: 0 <= i < j < |ranges| && IsOverlapping(ranges[i], ranges[j])
    }

    function rangeSize(r: (nat,nat)): nat 
        requires r.0<=r.1
    {
        (r.1-r.0)+1
    }

    function rangeSet(r: (nat, nat)): set<nat>
        requires r.0 <= r.1
    {
        set x | r.0 <= x <= r.1
    }

    lemma RangeSizeEqual(r: (nat, nat))
        requires r.0 <= r.1
        decreases r.1 - r.0
        ensures rangeSize(r) == |rangeSet(r)|
    {
        if r.0 == r.1 {
            var s := rangeSet(r);
            assert s == {r.0};
        }else{
            RangeSizeEqual((r.0, r.1-1));
            var s := rangeSet(r);
            assert s == rangeSet((r.0, r.1-1)) + {r.1};
        }
    }

    lemma MergeIsTheSame(r: (nat, nat), l: (nat, nat))
        requires r.0 <= r.1
        requires l.0 <= l.1
        requires IsOverlapping(r, l)
        ensures rangeSet(mergeRange(r,l)) == rangeSet(r)+rangeSet(l)
    {}

    lemma NonOverlappingDisjoint(r: (nat, nat), l: (nat, nat))
        requires r.0 <= r.1
        requires l.0 <= l.1
        requires !IsOverlapping(r, l)
        ensures rangeSet(r)*rangeSet(l) == {}
    {}

    function Union(rs: seq<(nat, nat)>): set<nat>
        requires forall r :: r in rs ==> r.0 <= r.1
        ensures forall x :: x in rs ==> rangeSet(x) <= Union(rs)
        ensures forall y :: y in Union(rs) ==> exists r :: r in rs && y in rangeSet(r)
    {
        if rs == [] then {} else rangeSet(rs[0])+Union(rs[1..])
    }

    lemma UnionConcat(rs: seq<(nat, nat)>, ls:  seq<(nat, nat)>)
        requires forall r :: r in rs ==> r.0 <= r.1
        requires forall r :: r in ls ==> r.0 <= r.1
        ensures Union(rs)+Union(ls) == Union(rs+ls)
    {
        if rs == [] {
            assert Union(rs) == {};
            assert rs+ls == ls;
            assert Union(rs)+Union(ls) == Union(rs+ls);
        }else{
            assert rs == [rs[0]]+rs[1..];
            UnionConcat(rs[1..], ls);
            assert (rs+ls)[1..] == rs[1..]+ls;
            assert Union(rs)+Union(ls) == Union(rs+ls);
        }
    }

    lemma UnionConcatSame(rs: seq<(nat, nat)>, ls:  seq<(nat, nat)>, xs: seq<(nat, nat)>)
        requires forall r :: r in rs ==> r.0 <= r.1
        requires forall r :: r in ls ==> r.0 <= r.1
        requires forall r :: r in xs ==> r.0 <= r.1
        requires ls != xs
        requires Union(ls) == Union(xs)
        ensures Union(rs)+Union(ls) == Union(rs)+Union(xs)
        ensures Union(rs+ls)==Union(rs+xs)
    {
        UnionConcat(rs, ls);
        UnionConcat(rs, xs);
    }

    lemma UnionConcatSame2(rs: seq<(nat, nat)>, ls:  seq<(nat, nat)>, xs: seq<(nat, nat)>)
        requires forall r :: r in rs ==> r.0 <= r.1
        requires forall r :: r in ls ==> r.0 <= r.1
        requires forall r :: r in xs ==> r.0 <= r.1
        requires rs != ls
        requires Union(rs) == Union(ls)
        ensures Union(rs)+Union(xs) == Union(ls)+Union(xs)
        ensures Union(rs+xs)==Union(ls+xs)
    {
        UnionConcat(ls, xs);
        UnionConcat(rs, xs);
    }

    lemma UnionLemma(sortedRanges: seq<(nat, nat)>, i: nat)
        requires 0 <= i < |sortedRanges|-1 && IsOverlapping(sortedRanges[i], sortedRanges[i+1]);
        requires forall r :: r in sortedRanges ==> r.0 <= r.1
        ensures Union(sortedRanges) == Union(sortedRanges[0..i]+[mergeRange(sortedRanges[i], sortedRanges[i+1])] + sortedRanges[i+2..])
    {
        assert sortedRanges[0..i]+sortedRanges[i..i+2]== sortedRanges[0..i+2];
        assert sortedRanges == sortedRanges[0..i+2]+sortedRanges[i+2..];
        assert sortedRanges[0..i+2] == sortedRanges[0..i]+sortedRanges[i..i+2];
        assert Union([mergeRange(sortedRanges[i], sortedRanges[i+1])]) == Union(sortedRanges[i..i+2]) by {
            calc {
                Union([mergeRange(sortedRanges[i], sortedRanges[i+1])]);
                rangeSet(mergeRange(sortedRanges[i], sortedRanges[i+1]));
            }
            assert sortedRanges[i..i+2][0] == sortedRanges[i];
            calc {
                Union(sortedRanges[i..i+2]);
                rangeSet(sortedRanges[i])+ Union(sortedRanges[i+1..i+2]);
                {assert sortedRanges[i+1..i+2][0] == sortedRanges[i+1];}
                rangeSet(sortedRanges[i])+rangeSet(sortedRanges[i+1]);
            }
        }
        UnionConcatSame(sortedRanges[0..i],sortedRanges[i..i+2], [mergeRange(sortedRanges[i], sortedRanges[i+1])]);
        UnionConcatSame2(sortedRanges[0..i+2],sortedRanges[0..i]+ [mergeRange(sortedRanges[i], sortedRanges[i+1])], sortedRanges[i+2..]);
    }

    lemma SortedAreDistjointOverlapping(sortedRanges: seq<(nat, nat)>)
        requires forall r :: r in sortedRanges ==> r.0 <= r.1
        requires !HasOverlapping(sortedRanges)
        requires SortedBy(lteRange, sortedRanges)
        ensures forall i :: 0 < i < |sortedRanges| ==> !IsOverlapping(sortedRanges[0], sortedRanges[i])
    {
        if |sortedRanges| <= 1 {

        }else{
            SortedAreDistjointOverlapping(sortedRanges[1..]);
        }
    }

    lemma SortedAreDistjoint(sortedRanges: seq<(nat, nat)>)
        requires forall r :: r in sortedRanges ==> r.0 <= r.1
        requires !HasOverlapping(sortedRanges)
        requires SortedBy(lteRange, sortedRanges)
        ensures forall i,j :: 0 <= i < j < |sortedRanges| ==> rangeSet(sortedRanges[i]) * rangeSet(sortedRanges[j])  == {} 
    {
        if |sortedRanges| <= 1 {
            assert forall i,j :: 0 <= i < j < |sortedRanges| ==> rangeSet(sortedRanges[i]) * rangeSet(sortedRanges[j])  == {};
        }else{
            SortedAreDistjoint(sortedRanges[1..]);
            assert sortedRanges == [sortedRanges[0]]+sortedRanges[1..];
            assert !IsOverlapping(sortedRanges[0], sortedRanges[1]);
            assert forall i :: 0 <= i <|sortedRanges[1..]| ==> !IsOverlapping(sortedRanges[0], sortedRanges[1..][i]) by {
                forall i | 0 <= i <|sortedRanges[1..]|
                    ensures !IsOverlapping(sortedRanges[0], sortedRanges[1..][i])
                {
                    if i == 0 {
                        assert !IsOverlapping(sortedRanges[0], sortedRanges[1..][i]);
                    }else{
                        // assert sortedRanges[i] == sortedRanges[1..][]
                        SortedAreDistjointOverlapping(sortedRanges[1..]);
                        assert !IsOverlapping(sortedRanges[1..][0], sortedRanges[1..][i]);
                        assert !IsOverlapping(sortedRanges[0], sortedRanges[1..][i]);
                    }
                }
            }
            assert forall i,j :: 0 <= i < j < |sortedRanges| ==> rangeSet(sortedRanges[i]) * rangeSet(sortedRanges[j])  == {};
        }
    }

    lemma UnionSum(sortedRanges: seq<(nat, nat)>)
        requires |sortedRanges| > 0
        requires forall r :: r in sortedRanges ==> r.0 <= r.1
        requires forall i,j :: 0 <= i < j < |sortedRanges| ==> rangeSet(sortedRanges[i]) * rangeSet(sortedRanges[j])  == {} 
        ensures |Union(sortedRanges)| == |rangeSet(sortedRanges[0])| + |Union(sortedRanges[1..])|
    {
        if |sortedRanges| == 1 {

        assert |Union(sortedRanges)| == |rangeSet(sortedRanges[0])| + |Union(sortedRanges[1..])|;
        }else{
            UnionSum(sortedRanges[1..]);
            assert rangeSet(sortedRanges[0]) * Union(sortedRanges[1..]) == {};
            assert |Union(sortedRanges)| == |rangeSet(sortedRanges[0])| + |Union(sortedRanges[1..])|;
        }
    }


    method problem5_2(input: string) returns (answer: int)
        decreases *
    {
        var ranges, ids := parseInput(input);
        answer := 0;
        IsTotalOrder();
        var sortedRanges := MergeSortBy(lteRange, ranges);
        assert forall r :: r in sortedRanges ==> r in multiset(sortedRanges);
        ghost var original := Union(sortedRanges);
        while HasOverlapping(sortedRanges) 
            decreases *
            invariant forall r :: r in sortedRanges ==> r.0 <= r.1
            invariant Union(sortedRanges) == original
        {
            var i :| 0 <= i < |sortedRanges|-1 && IsOverlapping(sortedRanges[i], sortedRanges[i+1]);
            UnionLemma(sortedRanges, i);
            sortedRanges := sortedRanges[0..i]+[mergeRange(sortedRanges[i], sortedRanges[i+1])] + sortedRanges[i+2..];
        }
        for i := 0 to |sortedRanges| 
        {
            answer := answer + rangeSize(sortedRanges[i]);
        }
        print "\n";
    }

    // MergeIsTheSame(sortedRanges[i], sortedRanges[i+1]);
    // UnionConcat(sortedRanges[0..i],sortedRanges[i..i+2]);
    // UnionConcat(sortedRanges[0..i+2],sortedRanges[i+2..]);
    // assert Union(sortedRanges[0..i+2]+ sortedRanges[i+2..]) == Union(sortedRanges);
    // UnionConcat(sortedRanges[0..i],sortedRanges[i..i+2]);
    // UnionConcatSame(sortedRanges[0..i],sortedRanges[i..i+2], [mergeRange(sortedRanges[i], sortedRanges[i+1])]);
    // assert Union(sortedRanges[0..i+2]) == Union(sortedRanges[0..i]+[mergeRange(sortedRanges[i], sortedRanges[i+1])]);
    // assert Union(sortedRanges[0..i]+[mergeRange(sortedRanges[i], sortedRanges[i+1])]+ sortedRanges[i+2..]) == Union(sortedRanges[0..i+2]+ sortedRanges[i+2..]);
    // assert Union(sortedRanges[0..i+2]+ sortedRanges[i+2..]) == original;
}
