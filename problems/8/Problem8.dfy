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
        a.2 < b.2 || (a.2 == b.2 && (a.1 < b.1 || (a.1 == b.1 && a.0 <= b.0)))
    }

    function RowCount(n: nat, i: nat): nat
        requires 0 <= i <= n
        requires n > 0
    {
        // Dafny can usually prove this is >= 0 automatically.
        // If not, it calculates (i * (2*n - i - 1)) / 2, where i <= n implies 2n - i - 1 >= 0.
        calc {
            i * n - (i * (i + 1)) / 2;
            2*(i * n)/2 - (i * (i + 1)) / 2;
        }
        i * n - (i * (i + 1)) / 2 
    }

    lemma LemmaRowStep(n: int, i: int)
        requires 0 <= i < n
        ensures RowCount(n, i+1) == RowCount(n, i) + (n - (i + 1))
    {
        reveal RowCount();
    }

    lemma nv(n: nat)
        ensures (2*n)%2 == 0
    {
        if n == 0 {

        }else{

        }
    }

    lemma NtimesNplusOne(n: int)
        ensures (n * (n + 1)) % 2 == 0
    {
        if n % 2 == 0 {
            var k: int := n/2;
            calc {
                n * (n+1);
                2*k * (n+1);
                2*(k * (n+1));
            }
            assert 2*k == n;
            assert (2*k * (n+1)) % 2 == 0;
            assert (n * (n + 1)) % 2 == 0;
        }else{
            assert (n+1)%2 == 0;
            var k := (n+1)/2;
            var b := n*k;
            calc {
                n*(n+1);
                n*(2*k);
                2*n*k;
                2*b;
            }
            nv(b);
            assert (2*b)%2 == 0;
            assert 2*k == n+1;
            assert (n * (n + 1)) % 2 == 0;
        }
    }
    // 3. Helper to prove the total length matches the end state.
    lemma LemmaTotalSize(n: nat)
        requires n > 0
        ensures RowCount(n, n) == n * (n - 1) / 2
    {
        calc {
            RowCount(n, n);
            n * n - (n * (n + 1)) / 2;
            // Hint: prove evenness much more simply
            { 
                assert n % 2 == 0 || (n + 1) % 2 == 0; 
                NtimesNplusOne(n);
                assert (n * (n + 1)) % 2 == 0; 
            } 
            (2 * n * n) / 2 - (n * (n + 1)) / 2;
            // THE FIX: Explicitly justify the merge of the fractions
            { 
                // We assert the algebraic property explicitly for these specific values
                nv(n*n);
                assert (2 * n * n) % 2 == 0;
                NtimesNplusOne(n);
                assert (n * (n + 1)) % 2 == 0;
                // Lemma logic inline: A/2 - B/2 == (A-B)/2
                assert (2 * n * n) / 2 - (n * (n + 1)) / 2 
                    == (2 * n * n - n * (n + 1)) / 2;
            }
            (2 * n * n - n * (n + 1)) / 2;
            (2 * n * n - (n * n + n)) / 2;
            (n * n - n) / 2;
            n * (n - 1) / 2;
        }
    }

    function AllPairs(xs: seq<(nat,nat,nat)>, offset: nat): seq<(nat, nat, nat)> 
        ensures |AllPairs(xs, offset)| == ((|xs| * (|xs|-1))/2)
    {
        if xs == [] then 
            []
        else seq(|xs|-1, k requires 0 <= k < |xs|-1 => (offset, offset+k+1, dist(xs[0], xs[k+1])))+AllPairs(xs[1..], offset+1)
    } by method {
        var len := |xs| * (|xs|-1) / 2;
        var arr := new (nat,nat,nat)[len];
        
        if |xs| == 0 {
            return [];
        }

        var count := 0; 

        for i := 0 to |xs| 
            invariant 0 <= i <= |xs|
            invariant 0 <= count <= len
            invariant count == i * |xs| - (i * (i + 1)) / 2
            invariant arr[..count] + AllPairs(xs[i..], offset + i) == AllPairs(xs, offset)
        {
            ghost var rowStart := count; 
            
            // Help 1: Pre-state snapshot for slicing logic
            ghost var preArr := arr[..count];

            label Inner:
            for j := i + 1 to |xs| 
                invariant i + 1 <= j <= |xs|
                invariant count == rowStart + (j - (i + 1))
                
                // The "seq" invariant is heavy, but we keep it for correctness.
                // We will add assertions below to help prove it quickly.
                invariant arr[rowStart..count] == 
                        seq(j - (i+1), k requires 0 <= k < j-(i+1) => 
                            (offset+i, offset+i+k+1, dist(xs[i], xs[i+k+1])))
                
                invariant arr[..rowStart] == old@Inner(arr[..rowStart])
            {
                // Help 2: Explicit slicing decomposition
                // This prevents Z3 from having to rediscover how indices map to slices
                assert arr[..count] == arr[..rowStart] + arr[rowStart..count];

                arr[count] := (offset + i, offset + j, dist(xs[i], xs[j]));
                count := count + 1;

                // Help 3: The "Inductive Step" for the sequence
                // We prove that "Old Sequence + New Element == New Sequence"
                // This is the specific "extensionality" help Dafny needs here.
                assert arr[rowStart..count] == 
                    arr[rowStart..count-1] + [arr[count-1]];
            }

            // Help 4: Unroll the recursive function manually
            // At the end of the loop, we are transitioning from 'i' to 'i+1'.
            // We explicitly show Dafny that: 
            // AllPairs(xs[i..]) == CurrentRow + AllPairs(xs[i+1..])
            if i < |xs| {
                assert xs[i..][1..] == xs[i+1..]; // List tail property
                assert AllPairs(xs[i..], offset+i) == 
                    arr[rowStart..count] + AllPairs(xs[i+1..], offset+i+1);
                
                // Help 5: Re-assert the composition for the next outer loop invariant
                assert arr[..count] == arr[..rowStart] + arr[rowStart..count];
            }
        }
        return arr[..];
    }

    lemma kNat(k: nat)
        ensures k * (k - 1) >= 0
    {}

    lemma LemmaInnerRowBound(n: int, i: int, j: int)
        requires 0 <= i < n
        requires i < j <= n 
        ensures RowCount(n, i) + (j - (i + 1)) <= RowCount(n, n)
    {
        reveal RowCount();
        
        var m := i + 1;
        var k := n - m;
        assert k >= 0;

        // Helper: Prove evenness so we can remove division later
        NtimesNplusOne(n);
        NtimesNplusOne(m);
        assert (n * (n + 1)) % 2 == 0;
        assert (m * (m + 1)) % 2 == 0;

        calc {
            2 * (RowCount(n, n) - RowCount(n, m));
            
            // 1. Distribute the 2
            2 * RowCount(n, n) - 2 * RowCount(n, m);
            
            // 2. Expand RowCount(n, n)
            //    Goal: 2 * (n*n - n*(n+1)/2)  ->  n*(n-1)
            {
                calc {
                    2 * RowCount(n, n);
                    2 * (n * n - (n * (n + 1)) / 2);
                    2 * n * n - 2 * ((n * (n + 1)) / 2);
                    // Apply evenness property: 2 * (X / 2) == X
                    2 * n * n - n * (n + 1);
                    2 * n * n - (n * n + n);
                    n * n - n;
                    n * (n - 1);
                }
            }
            n * (n - 1) - 2 * RowCount(n, m);

            // 3. Expand RowCount(n, m)
            //    Goal: 2 * (m*n - m*(m+1)/2)  ->  2mn - (m^2+m)
            {
                calc {
                    2 * RowCount(n, m);
                    2 * (m * n - (m * (m + 1)) / 2);
                    2 * m * n - 2 * ((m * (m + 1)) / 2);
                    // Apply evenness property
                    2 * m * n - m * (m + 1);
                }
            }
            n * (n - 1) - (2 * m * n - m * (m + 1));
            
            // 4. Final Algebraic Simplification
            (n * n - n) - (2 * m * n - m * m - m);
            n * n - 2 * m * n + m * m - n + m;
            // Factor into (n-m) terms
            (n - m) * (n - m) - (n - m);
            k * k - k;
            k * (k - 1);
        }

        // Since k >= 0 (because i < n), k*(k-1) >= 0.
        kNat(k);
        assert RowCount(n, m) <= RowCount(n, n);
        
        // Final logic step connecting index j to the row bounds
        // index == Start(i) + (j - (i+1))
        // Max index in this loop is when j=n, which is Start(i) + (n - (i+1)) == Start(i+1)
    }
    method AllPairsArr(xs: seq<(nat,nat, nat)>) returns (arr: array<((nat,nat),int)>)
    {
        if |xs| == 0 {
            return new ((nat,nat),int)[0](_ => ((0,0),0));
        }

        // Use 'int' for n to match our helper functions
        var n: nat := |xs|;
        assert n > 0;
        
        // Prove correct length calculation
        LemmaTotalSize(n);
        var len := n * (n - 1) / 2;
        
        // Allocate array
        arr := new ((nat,nat),int)[len](_ => ((0,0),0));
        assert arr.Length == len;
        
        var count := 0;
        
        // Outer Loop
        for i := 0 to n
            invariant 0 <= i <= n
            // Map 'count' to our opaque arithmetic function
            invariant count == RowCount(n, i)
            invariant 0 <= count <= len
        {
            // Apply the lemma to transition 'count' for the next iteration
            if i < n {
                LemmaRowStep(n, i);
            }

            ghost var rowStart := count; 
            
            // Inner Loop
            for j := i + 1 to n
                invariant i + 1 <= j <= n
                // Logic here is now purely linear: count = start + offset
                invariant count == rowStart + (j - (i + 1))
                invariant 0 <= count <= len
            {
                LemmaInnerRowBound(n,i,j);
                arr[count] := ((i as nat, j as nat), dist(xs[i], xs[j]));
                count := count + 1;
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
