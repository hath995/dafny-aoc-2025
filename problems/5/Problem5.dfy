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

    method problem5_2(input: string) returns (answer: int)
        decreases *
    {
        var ranges, ids := parseInput(input);
        answer := 0;
        IsTotalOrder();
        var sortedRanges := MergeSortBy(lteRange, ranges);
        assert forall r :: r in sortedRanges ==> r in multiset(sortedRanges);
        while HasOverlapping(sortedRanges) 
            decreases *
            invariant forall r :: r in sortedRanges ==> r.0 <= r.1
        {
            var i :| 0 <= i < |sortedRanges|-1 && IsOverlapping(sortedRanges[i], sortedRanges[i+1]);
            sortedRanges := sortedRanges[0..i]+[mergeRange(sortedRanges[i], sortedRanges[i+1])] + sortedRanges[i+2..];
        }
        for i := 0 to |sortedRanges| 
        {
            answer := answer + rangeSize(sortedRanges[i]);
        }
        print "\n";
    }
}
