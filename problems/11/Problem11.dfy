include "../../lib/matrix.dfy"
include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
module Problem11 {
    import opened Matrix
    import opened Split
    import opened ParseInt
    import opened Std.BoundedInts

    @IsolateAssertions
    method parseInput(input: string) returns (nodes: set<string>, nodeIds: map<string, nat>, adjMatrix: array2<nint64>) 
        ensures adjMatrix.Length0 == adjMatrix.Length1 == |nodeIds|
    {
        nodes := {};
        var lines := splitOnBreak(input);
        nodeIds := map[];
        for i := 0 to |lines| 
            invariant nodeIds.Keys == nodes
            invariant forall val :: val in nodeIds.Values ==> val < i
            invariant forall val :: val in nodeIds.Values ==> val <= |lines|
        {
            var pieces:= split(lines[i], ":");
            expect |pieces| == 2;
            expect pieces[0] !in nodes, "found something "+ pieces[0];
            nodes := nodes + {pieces[0]};
            assert i <= |lines|;
            assert forall val :: val in nodeIds.Values ==> val <= |lines|;
            ghost var oldNodeIds:=nodeIds;
            assert pieces[0] !in nodeIds;
            assert i !in oldNodeIds.Values;

            nodeIds := nodeIds[pieces[0] := i];
            assert i in nodeIds.Values;
            assert nodeIds.Values == oldNodeIds.Values + {i};
        } 
        expect "out" !in nodeIds;
        nodeIds := nodeIds["out" := |lines|];
        assert forall val :: val in nodeIds.Values ==> val <= |lines|;
        adjMatrix := new nint64[|nodeIds|, |nodeIds|]((i,j) => 0);
        for i := 0 to |lines| 
        {
            var pieces:= split(lines[i], ": ");
            expect |pieces| == 2;
            var outs := split(pieces[1], " ");
            for j := 0 to |outs| 
            {
                var outId := nodeIds[outs[j]];
                adjMatrix[i, outId] := 1;
            }
        }

    }

    method printMatrixNat(matrix: array2<nint64>)
    {
        for i := 0 to matrix.Length0 {
            for j := 0 to matrix.Length1 {
                    print matrix[i,j], " ";
            }
            print "\n";
        }
    }
    method problem11_1(input: string) returns (x: int) {
        var nodes, ids, adjMatrix := parseInput(input);
        print "\n", nodes, "\n";
        // printMatrixNat(adjMatrix);
        expect |ids| > 0 && "you" in ids && "out" in ids;
        var res := new nint64[|ids|,|ids|]((i,j) => 0);
        var next := matrixAdd(adjMatrix, res, |ids|, |ids|);
        for i := 0 to |ids|-1
            invariant next.Length0 == next.Length1 == |ids|
            invariant res.Length0 == res.Length1 == |ids|
        {
            next := matrixMul64(next, adjMatrix);
            res := matrixAdd(res, next, |ids|, |ids|);
            print "\ni: ", i;
        }
        print "\nanswer is: ";
        // printMatrixNat(res);
        return res[ids["you"], ids["out"]] as int;
    }

    function min(a: int, b:int): int {
        if a < b then a else b
    }

    method problem11_2(input: string) returns (x: int) {
        var nodes, ids, adjMatrix := parseInput(input);
        print "\n", nodes, "\n";
        // printMatrixNat(adjMatrix);
        expect |ids| > 0 && "you" in ids && "out" in ids;
        var res := new nint64[|ids|,|ids|]((i,j) => 0);
        var next := matrixAdd(adjMatrix, res, |ids|, |ids|);
        for i := 0 to min(60, |ids|-1)
            invariant next.Length0 == next.Length1 == |ids|
            invariant res.Length0 == res.Length1 == |ids|
        {
            next := matrixMul64(next, adjMatrix);
            res := matrixAdd(res, next, |ids|, |ids|);
            print "\ni: ", i;
        }
        print "\nanswer is: ";
        // printMatrixNat(res);
        return (res[ids["svr"], ids["fft"]] as int )* (res[ids["fft"], ids["dac"]] as int) * (res[ids["dac"], ids["out"]] as int);
    }
}
