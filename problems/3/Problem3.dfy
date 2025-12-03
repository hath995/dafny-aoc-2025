include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
module Problem3 {
    import opened Split
    import opened ParseInt
    import opened Std.Collections.Seq

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
        requires |xs| > count
        requires index < |xs|-count+1
        requires count > 0
        decreases count
        ensures |fls(xs, index, count)| == count
    {
       if count == 1 then
         var mi := MaxIndex(xs[index..]);
         [mi.0]
       else
         var mi := MaxIndex(xs[index..|xs|-count+1]);
         [mi.0]+fls(xs, index+mi.1+1, count-1)
    }
    
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
}
