include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
module Problem9 {
    import opened Split
    import opened ParseInt
    import opened Std.Collections.Seq
    import opened Std.Relations

    method parseInput(input: string) returns (xs: seq<(nat,nat)>)
        ensures |xs| > 0
    {
        var lines := splitOnBreak(input);
        xs := [];
        for i := 0 to |lines| 
            invariant |xs| == i
        {
            var coord_string := split(lines[i],",");
            var coord := Map(Integer, coord_string);
            expect |coord| == 2 && forall k :: 0 <= k < |coord| ==> 0 <= coord[k];
            // expect (coord[0], coord[1]) !in xs;
            xs := xs+[(coord[0], coord[1])];
        }
        expect |xs| > 0;
    }

    function abs(x: int): nat {
        if x < 0 then -x else x
    }

    function max(x: nat, y: nat):nat {
        if x > y then x else y
    }

    function area(a: (nat,nat), b: (nat, nat)): nat 
    {
        (abs(b.0 - a.0)+1)*(abs(b.1 - a.1)+1)
    }

    predicate gte(a: nat,b: nat) {
        a >= b
    }
    
    predicate lteY(a: (nat,nat),b: (nat,nat)) {
        a.1 < b.1 || (a.1 == b.1 && a.0 <= b.0)
    }

    predicate lteX(a: (nat,nat),b: (nat,nat)) {
        a.0 < b.0 || (a.0 == b.0 && a.1 <= b.1)
    }

    function AllPairs(xs: seq<(nat,nat)>, i: nat): seq<nat> 
        ensures |AllPairs(xs, i)| == ((|xs| * (|xs|-1))/2)
    {
        if xs == [] then 
            []
        else seq(|xs|-1, k requires 0 <= k < |xs|-1 => area(xs[0], xs[k+1]))+AllPairs(xs[1..], i+1)
    } by method {
        var arr := new nat[|xs|*(|xs|-1)/2];
        if |xs| == 0 {
            return [];
        }
        var count := 0;
        for i := 0 to |xs|-1 {
            for j := i+1 to |xs| {
                arr[count] := area(xs[i], xs[j]);
                count := count+1;
            }
        }
        return arr[..];
    }

    method problem9_1(input: string) returns (x: int) {
        var coords := parseInput(input);
        expect |coords| > 1;
        // var byX := MergeSortBy(lteX, coords);
        // var byY := MergeSortBy(lteY, coords);
        // var i := 10;
        // var m := 0;
        // while i > 0 && |byX| > 1
        //     invariant |byX| == |byY|
        // {
        //     m := max(m,max(area(byX[0], byX[|byX|-1]), area(byY[0], byY[|byY|-1])));
        //     byX := byX[1..|byX|-1];
        //     byY := byY[1..|byY|-1];
        //     i := i -1;
        // }
        var all := MergeSortBy(gte, AllPairs(coords, 0));
        x := all[0];
        
    }

    method problem9_2(input: string) returns (x: int) {
        return 4;
    }
}
