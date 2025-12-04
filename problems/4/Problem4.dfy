include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
module Problem4 {
    import opened Split
    method parseInput(input: string) returns (grid: seq<string>, n: nat)
        ensures |grid| > 0
        ensures forall i :: 0 <= i < |grid| ==> |grid[i]| == n
    {
        grid := splitOnBreak(input);
        expect |grid| > 0;
        n := |grid[0]|;
        expect forall i :: 0 <= i < |grid| ==> |grid[i]| == n;
    }

    function adjacentIndexes(): set<(int, int)> {
        (set i: int,j: int | -1 <= i <= 1 && -1 <= j <= 1 :: (i,j)) - {(0,0)}
    }

    predicate LteTuple(a: (int, int), b: (int, int)) {
        if a.0 < b.0 then
            true
        else if a.0 > b.0 then
            false
        else if a.1 <= b.1 then
            true
        else
            false
    }

    lemma ThereIsAMinimum(s: set<(int, int)>)
        requires s != {}
        ensures exists x :: x in s && forall y :: y in s ==> LteTuple(x, y)
    {
        assert s != {};
        var x :| x in s;
        if s == {x} {
        } else {
            var s' := s - {x};
            assert s == s' + {x};
            ThereIsAMinimum(s');
        }
    }

    function SetToSequence(s: set<(int,int)>): seq<(int,int)>
        ensures var q := SetToSequence(s); forall i :: 0 <= i < |q| ==> q[i] in s
        ensures |SetToSequence(s)| == |s|
        ensures forall p :: p in s ==> p in SetToSequence(s)
    {
    if s == {} then [] else
        ThereIsAMinimum(s);
        var x :| x in s && forall y :: y in s ==> LteTuple(x, y);
        [x] + SetToSequence(s - {x})
    }


    const Offsets: seq<(int,int)> := SetToSequence(adjacentIndexes())

    function neighbors(grid: seq<string>, x: nat, y: nat, n: nat, offsets: seq<(int, int)>, removed: set<(nat,nat)>): multiset<char> 
        requires forall i :: 0 <= i < |grid| ==> |grid[i]| == n
        requires y < |grid|
        requires x < |grid[y]|
    {
        if offsets == [] then multiset{}
        else 
            var offset := offsets[0];
            if 0 <= y+offset.1 < |grid| && 0 <= x+offset.0 < |grid[y+offset.1]| && (x+offset.0, y+offset.1) !in removed then
                multiset{grid[y+offset.1][x+offset.0]} + neighbors(grid, x, y, n, offsets[1..], removed)
            else
                neighbors(grid, x, y, n, offsets[1..], removed)
    }

    predicate ltFour(grid: seq<string>, x: nat, y: nat, n: nat, removed: set<(nat,nat)>)
        requires forall i :: 0 <= i < |grid| ==> |grid[i]| == n
        requires y < |grid|
        requires x < |grid[y]|
    {
        neighbors(grid, x, y, n, Offsets, removed)['@'] < 4
    }

    method problem4_1(input: string) returns (x: int) {
       var grid, length := parseInput(input);
       x := 0;
       print "indices", Offsets;
       var removed: set<(nat,nat)> := {};
       for i := 0 to |grid| {
           for k := 0 to length {
                if ltFour(grid, k, i, length, removed) && grid[i][k] == '@' {
                    // print "\n(", k, ", ", i, ")";
                    x := x + 1;
                }
           }
       }
    }

    method problem4_helper(grid: seq<string>, length: nat, removed: set<(nat,nat)>) returns (x: int, removed': set<(nat,nat)>)
        requires forall i :: 0 <= i < |grid| ==> |grid[i]| == length
    {
       x := 0;
       var found: set<(nat, nat)> := {};
       for i := 0 to |grid|
            invariant x == |found|
            invariant forall index :: index in found ==> index.1 < i
       {
           for k := 0 to length 
                invariant x == |found|
                invariant forall index :: index in found ==> index.1 <= i
                invariant forall index :: index in found ==> index.0 >= k ==> index.1 < i
           {
                if (k,i) !in removed && grid[i][k] == '@' && ltFour(grid, k, i, length, removed) {
                    assert (k,i) !in found;
                    found := found + {(k,i)};
                    x := x + 1;
                }
           }
       }
       removed' := removed + found;
    }

    method problem4_2(input: string) returns (x: int)
        decreases *
    {
       var grid, length := parseInput(input);
       x := 0;
       var nRemoved, removed := problem4_helper(grid, length, {});
       while nRemoved > 0 
         decreases *
       {
            nRemoved, removed := problem4_helper(grid, length, removed);
            // print "\nRemoved ", nRemoved," ", removed;
       }
       x := |removed|;
    }
}
