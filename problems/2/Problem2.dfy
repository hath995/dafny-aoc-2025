include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
module Problem2 {
    import opened Split
    import opened ParseInt
    import opened Std.Strings

    method parseInput(input: string) returns (xs: seq<(nat, nat)>)
        ensures forall xx :: xx in xs ==> xx.0 < xx.1
    {
        xs := [];
        var pairs := split(input, ",");
        for i := 0 to |pairs| 
            invariant forall xx :: xx in xs ==> xx.0 < xx.1
            invariant |xs| == i
        {
            var pairpieces := split(pairs[i], "-");
            expect |pairpieces| == 2;
            var start := Integer(pairpieces[0]);
            var end := Integer(pairpieces[1]);
            expect 0 <= start < end;
            xs := xs + [(start, end)];
        }

    }

    function repeat(s: string, k: nat): string {
        if k == 0 then "" else s+repeat(s, k-1)
    }

    predicate Invalid(n: string) {
        // exists k :: 0 < k < |n| && |n| % k == 0  && n == repeat(n[..k], |n|/k)
        // n == repeat(n[..|n|/2], 2)
        n[..|n|/2] == n[|n|/2..]
    }

    predicate InvalidAll(n: string) {
        exists k :: 0 < k < |n| && |n| % k == 0  && n == repeat(n[..k], |n|/k)
        // n == repeat(n[..|n|/2], 2)
    }

    lemma testInvalid() {
        assert Invalid("11");
        assert Invalid("22");
        assert Invalid("1010");
        assert Invalid("1188511885");
    }

    method problem2_1(input: string) returns (x: int) {
        var id_pairs := parseInput(input);
        print "paiurs", id_pairs;
        x := 0;
        for i := 0 to |id_pairs|
        {
            var invalid_ids := set y | id_pairs[i].0 <= y <= id_pairs[i].1 && Invalid(OfNat(y));
            // print "\n", id_pairs[i], " ", id_pairs[i].1-id_pairs[i].0, " ", invalid_ids;
            ghost var all_ids := invalid_ids;
            ghost var removed: set<int> := {};
            while invalid_ids != {} 
                invariant invalid_ids !! removed
                invariant invalid_ids == all_ids - removed
            {
                var id :| id in invalid_ids;
                x := x + id;
                invalid_ids := invalid_ids - {id};
                removed := removed+{id};
            }

        }
        print "\n";
    }

    method problem2_2(input: string) returns (x: int) {
        var id_pairs := parseInput(input);
        print "paiurs", id_pairs;
        x := 0;
        for i := 0 to |id_pairs|
        {
            var invalid_ids := set y | id_pairs[i].0 <= y <= id_pairs[i].1 && InvalidAll(OfNat(y));
            // print "\n", id_pairs[i], " ", id_pairs[i].1-id_pairs[i].0, " ", invalid_ids;
            ghost var all_ids := invalid_ids;
            ghost var removed: set<int> := {};
            while invalid_ids != {} 
                invariant invalid_ids !! removed
                invariant invalid_ids == all_ids - removed
            {
                var id :| id in invalid_ids;
                x := x + id;
                invalid_ids := invalid_ids - {id};
                removed := removed+{id};
            }

        }
        print "\n";
    }
}