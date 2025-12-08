include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
include "./QuickUnion.dfy"

module Problem8 {
    import opened Split
    import opened ParseInt
    import opened Std.Collections.Seq
    import opened QuickUnion

    predicate Distinct<T(==)>(xs: seq<T>) {
        // forall i, j :: 0 <= i  < |xs| && 0 <= j < |xs| ==> xs[i] != xs[j]
        forall i, j :: 0 <= i <j  < |xs|  ==> xs[i] != xs[j]
    }

    method parseInput(input: string) returns (xs: seq<(nat,nat,nat)>)
        ensures Distinct(xs)
        ensures |xs| > 0
    {
        var lines := splitOnBreak(input);
        xs := [];
        for i := 0 to |lines| 
            invariant Distinct(xs)
            invariant |xs| == i
        {
            var coord_string := split(lines[i],",");
            var coord := Map(Integer, coord_string);
            expect |coord| == 3 && forall k :: 0 <= k < |coord| ==> 0 <= coord[k];
            expect (coord[0], coord[1], coord[2]) !in xs;
            xs := xs+[(coord[0], coord[1], coord[2])];
        }
        expect |xs| > 0;
    }

    function dist(a: (nat, nat, nat), b: (nat, nat, nat)): nat {
        (a.0-b.0)*(a.0-b.0) + (a.1-b.1)*(a.1-b.1) + (a.2-b.2)*(a.2-b.2)
    }

    function min(a: nat, b: nat): nat {
        if a < b then a else b
    }

    lemma ThereIsAMinimumTuple(s: set<(nat, nat, nat)>)
        requires s != {}
        ensures exists x :: x in s && forall y :: y in s ==> x.2 <= y.2
    {
        assert s != {};
        var x :| x in s;
        if s == {x} {
        } else {
            var s' := s - {x};
            assert s == s' + {x};
            ThereIsAMinimumTuple(s');
        }
    }

    predicate gte(a: nat,b: nat) {
        a >= b
    }

    predicate lte(a: (nat,nat,nat),b: (nat,nat,nat)) {
        a.2 <= b.2
    }

    function AllPairs(xs: seq<(nat,nat,nat)>, i: nat): seq<(nat, nat, nat)> 
        ensures |AllPairs(xs, i)| == ((|xs| * (|xs|-1))/2)
    {
        if xs == [] then 
            []
        else seq(|xs|-1, k requires 0 <= k < |xs|-1 => (i, i+k+1, dist(xs[0], xs[k+1])))+AllPairs(xs[1..], i+1)
    } by method {
        var arr := new (nat,nat,nat)[|xs|*(|xs|-1)/2];
        if |xs| == 0 {
            return [];
        }
        var count := 0;
        for i := 0 to |xs|-1 {
            for j := i+1 to |xs| {
                arr[count] := (i,j,dist(xs[i], xs[j]));
                count := count+1;
            }
        }
        return arr[..];
    }

    method AllPairsArr(xs: seq<(nat,nat, nat)>) returns (arr: array<((nat,nat),int)>) {
        if |xs| == 0 {
            return new ((nat,nat),nat)[0];
        }
        arr := new ((nat,nat),nat)[|xs|*(|xs|-1)/2];
        var count := 0;
        for i := 0 to |xs|-1 {
            for j := i+1 to |xs| {
                arr[count] := ((i,j),dist(xs[i], xs[j]));
                count := count+1;
            }
        }
        return arr;
    }

    method {:verify} problem8_1_1(input: string) returns (x: int) 
        decreases *
    {
        x:=0;
        var coords := parseInput(input);
        var cmap: map<(nat, nat, nat), nat> := map i | 0 <= i < |coords| :: coords[i] := i;
        // var pairs := set i: nat,j: nat | 0 <= i < j < |coords| :: (i,j, dist(coords[i], coords[j]));
        var pairs := MergeSortBy(lte, AllPairs(coords, 0));
        // print "\npairs: ", pairs;
        assert forall p :: p in pairs ==> 0 <= p.0 < p.1 < |coords|;
        // expect pairs != {};
        var qu := new QuickUnion(|coords|);
        assert fresh(qu);
        var count := 1000-1;
        while count > 0 && pairs != [] 
            invariant qu.Valid()
            invariant fresh(qu)
            invariant forall p :: p in pairs ==> 0 <= p.0 < p.1 < |coords|
            invariant qu.n == |coords|
            modifies qu
            decreases *
        {
            var nearest := pairs[0];
            // ThereIsAMinimumTuple(pairs);
            // var nearest :| nearest in pairs && forall p :: p in pairs ==> nearest.2 <= p.2;
            // print "\nnearest: ", coords[nearest.0], " ", coords[nearest.1], " ", nearest.2;
            var areConnected := qu.connected(nearest.0, nearest.1);
            // print "\nareConnected: ", areConnected;
            if !areConnected {
                qu.union(nearest.0, nearest.1);
            }
            count := count - 1;
            pairs:= pairs[1..];

        }
        for i := 0 to |coords| 
            invariant qu.Valid()
            invariant fresh(qu)
            invariant qu.n == |coords|
            modifies qu
        {
            var root := qu.findRoot(i);
        }
        var counts := multiset(qu.parent[..]);
        // print "\ncounts, ", qu.parent[..];
        var res: seq<nat> := [];
        while counts != multiset{} {
            var x :| x in counts;
            res := res + [counts[x]];
            counts := counts[x := 0];
        }
        var sres := MergeSortBy(gte, res);
        print "\n",sres,"\n";
        return FoldLeft((a,b)=>a*b, 1, sres[..min(3, |sres|)]);
    }

    method {:verify} problem8_1(input: string) returns (x: int) 
        decreases *
    {
        x:=0;
        var coords := parseInput(input);
        var cmap: map<(nat, nat, nat), nat> := map i | 0 <= i < |coords| :: coords[i] := i;
        // var pairs := set i: nat,j: nat | 0 <= i < j < |coords| :: (i,j, dist(coords[i], coords[j]));
        var pairs := AllPairsArr(coords);
        var pw := new PriorityQueue<(nat,nat)>(1, (0,0));
        pw.heap := pairs;
        pw.capacity := pairs.Length;
        pw.size := pairs.Length;
        for i := 0 to (pairs.Length/2) - 1 {
            pw.heapifyDown((pairs.Length/2) - 1 - i);
        }
        // print "\npairs: ", pairs;
        // assert forall p :: p in pairs ==> 0 <= p.0 < p.1 < |coords|;
        // expect pairs != {};
        var qu := new QuickUnion(|coords|);
        assert fresh(qu);
        var count := 1000-1;
        while count > 0 
            invariant qu.Valid()
            invariant fresh(qu)
            // invariant forall p :: p in pairs ==> 0 <= p.0 < p.1 < |coords|
            invariant qu.n == |coords|
            modifies qu
            decreases *
        {
            var nearest := pw.extractMin();
            // ThereIsAMinimumTuple(pairs);
            // var nearest :| nearest in pairs && forall p :: p in pairs ==> nearest.2 <= p.2;
            // print "\nnearest: ", coords[nearest.0], " ", coords[nearest.1], " ", nearest.2;
            var areConnected := qu.connected(nearest.0, nearest.1);
            // print "\nareConnected: ", areConnected;
            if !areConnected {
                qu.union(nearest.0, nearest.1);
            }
            count := count - 1;
            // pairs:= pairs[1..];

        }
        for i := 0 to |coords| 
            invariant qu.Valid()
            invariant fresh(qu)
            invariant qu.n == |coords|
            modifies qu
        {
            var root := qu.findRoot(i);
        }
        var counts := multiset(qu.parent[..]);
        // print "\ncounts, ", qu.parent[..];
        var res: seq<nat> := [];
        while counts != multiset{} {
            var x :| x in counts;
            res := res + [counts[x]];
            counts := counts[x := 0];
        }
        var sres := MergeSortBy(gte, res);
        print "\n",sres,"\n";
        return FoldLeft((a,b)=>a*b, 1, sres[..min(3, |sres|)]);
    }

    method problem8_2(input: string) returns (x: int) 
        decreases *
    {
        x:=0;
        var coords := parseInput(input);
        var cmap: map<(nat, nat, nat), nat> := map i | 0 <= i < |coords| :: coords[i] := i;
        // var pairs := set i: nat,j: nat | 0 <= i < j < |coords| :: (i,j, dist(coords[i], coords[j]));
        var pairs := AllPairsArr(coords);
        var pw := new PriorityQueue<(nat,nat)>(1, (0,0));
        pw.heap := pairs;
        pw.capacity := pairs.Length;
        pw.size := pairs.Length;
        for i := 0 to (pairs.Length/2) - 1 {
            pw.heapifyDown((pairs.Length/2) - 1 - i);
        }
        // expect pairs != {};
        var qu := new QuickUnion(|coords|);
        assert fresh(qu);
        var count := 1000-1;
        while count > 0
            invariant qu.Valid()
            invariant fresh(qu)
            // invariant forall p :: p in pairs ==> 0 <= p.0 < p.1 < |coords|
            invariant qu.n == |coords|
            modifies qu
            decreases *
        {
            var nearest := pw.extractMin();
            // ThereIsAMinimumTuple(pairs);
            // var nearest :| nearest in pairs && forall p :: p in pairs ==> nearest.2 <= p.2;
            // print "\nnearest: ", coords[nearest.0], " ", coords[nearest.1], " ", nearest.2;
            var areConnected := qu.connected(nearest.0, nearest.1);
            // print "\nareConnected: ", areConnected;
            if !areConnected {
                qu.union(nearest.0, nearest.1);
                if count == 1 {
                    return coords[nearest.0].0 * coords[nearest.1].0;
                }
                count := count - 1;
            }
            // pairs:= pairs[1..];

        }
    }

    method problem8_2_1(input: string) returns (x: int) 
        decreases *
    {
        x:=0;
        var coords := parseInput(input);
        var cmap: map<(nat, nat, nat), nat> := map i | 0 <= i < |coords| :: coords[i] := i;
        // var pairs := set i: nat,j: nat | 0 <= i < j < |coords| :: (i,j, dist(coords[i], coords[j]));
        var pairs := MergeSortBy(lte, AllPairs(coords, 0));
        assert forall p :: p in pairs ==> 0 <= p.0 < p.1 < |coords|;
        // expect pairs != {};
        var qu := new QuickUnion(|coords|);
        assert fresh(qu);
        var count := 1000-1;
        while count > 0 && pairs != [] 
            invariant qu.Valid()
            invariant fresh(qu)
            invariant forall p :: p in pairs ==> 0 <= p.0 < p.1 < |coords|
            invariant qu.n == |coords|
            modifies qu
            decreases *
        {
            var nearest := pairs[0];
            // ThereIsAMinimumTuple(pairs);
            // var nearest :| nearest in pairs && forall p :: p in pairs ==> nearest.2 <= p.2;
            // print "\nnearest: ", coords[nearest.0], " ", coords[nearest.1], " ", nearest.2;
            var areConnected := qu.connected(nearest.0, nearest.1);
            // print "\nareConnected: ", areConnected;
            if !areConnected {
                qu.union(nearest.0, nearest.1);
                if count == 1 {
                    return coords[nearest.0].0 * coords[nearest.1].0;
                }
                count := count - 1;
            }
            pairs:= pairs[1..];

        }
    }
}
