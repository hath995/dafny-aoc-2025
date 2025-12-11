

module Matrix {
    import opened Std.BoundedInts
    newtype {:nativeType "long"} nint64 = x: int | -TWO_TO_THE_63 <= x < TWO_TO_THE_63

    method matrixAdd(left: array2<nint64>, right: array2<nint64>, m: nat, n: nat) returns (result: array2<nint64>)
        requires m > 0 && n > 0
        requires left.Length0 == right.Length0 && left.Length0 == m && left.Length1 == right.Length1 && left.Length1 == n
        ensures result.Length0 == left.Length0 && result.Length1 == left.Length1
        ensures forall i, j :: 0 <= i < m && 0 <= j < n ==> result[i,j] == left[i,j] + right[i,j]
    {
        result := new nint64[m,n];
        for i := 0 to m
        // var i := 0;
        // while i < m
            invariant 0 <= i <= m
            invariant forall x, j :: 0 <= x < i && 0 <= j < n ==> result[x,j] == left[x,j] + right[x,j]
        {
            for j := 0 to n
            // var j := 0;
            // while j < n
                invariant 0 <= j <= n
                invariant forall x, j :: 0 <= x < i && 0 <= j < n ==> result[x,j] == left[x,j] + right[x,j]
                invariant forall x :: 0 <= x < j  <= n ==> result[i,x] == left[i,x] + right[i,x]
            {
                result[i,j] := left[i,j] + right[i,j];
                // j := j + 1;
            }
            // i := i + 1;
        }
    }
    method matrixMul(left: array2<nat>, right: array2<nat>) returns (result: array2<nat>)
        requires left.Length1 == right.Length0
        ensures result.Length0 == left.Length0 && result.Length1 == right.Length1
        ensures fresh(result)
    {
        result := new nat[left.Length0, right.Length1];
        for i := 0 to left.Length0
        {
            // print "i=", i, "\n";
            for j := 0 to right.Length1
            {
                result[i,j] := 0;
                for k := 0 to left.Length1
                {
                    result[i,j] := result[i,j] + left[i,k] * right[k,j];
                }
            }
        }
    }

    method matrixMul64(left: array2<nint64>, right: array2<nint64>) returns (result: array2<nint64>)
        requires left.Length1 == right.Length0
        ensures result.Length0 == left.Length0 && result.Length1 == right.Length1
        ensures fresh(result)
    {
        result := new nint64[left.Length0, right.Length1];
        for i := 0 to left.Length0
        {
            // print "i=", i, "\n";
            for j := 0 to right.Length1
            {
                result[i,j] := 0;
                for k := 0 to left.Length1
                {
                    // expect result[i,j] + left[i,k] * right[k,j] < TWO_TO_THE_63;
                    result[i,j] := result[i,j] + left[i,k] * right[k,j];
                }
            }
        }
    }

    // twostate function ftranspose(matrix: array2<real>): array2<real> 
    //     reads matrix
    //     ensures ftranspose(matrix).Length0 == matrix.Length1 && ftranspose(matrix).Length1 == matrix.Length0
    //     ensures forall i, j :: 0 <= i < matrix.Length1 && 0 <= j < matrix.Length0 ==> ftranspose(matrix)[i,j] == matrix[j,i]
    // {
    //     new real[matrix.Length1, matrix.Length0]((i,j) reads matrix => if 0 <= i < matrix.Length1 && 0 <= j < matrix.Length0 then matrix[j,i] else 0.0)
    // }

    method transpose(matrix: array2<real>) returns (result: array2<real>)
        ensures result.Length0 == matrix.Length1 && result.Length1 == matrix.Length0
        ensures forall i, j :: 0 <= i < matrix.Length1 && 0 <= j < matrix.Length0 ==> result[i,j] == matrix[j,i]
    {
        result := new real[matrix.Length1, matrix.Length0]((i,j) reads matrix => if 0 <= i < matrix.Length1 && 0 <= j < matrix.Length0 then matrix[j,i] else 0.0);
        assert result.Length0 == matrix.Length1;
        assert result.Length1 == matrix.Length0;
    }

    method transpose2(matrix: array2<real>) returns (result: array2<real>)
        ensures result.Length0 == matrix.Length1 && result.Length1 == matrix.Length0
        ensures forall i, j :: 0 <= i < matrix.Length1 && 0 <= j < matrix.Length0 ==> result[i,j] == matrix[j,i]
    {
        result := new real[matrix.Length1, matrix.Length0]((i,j) reads matrix => if 0 <= i < matrix.Length1 && 0 <= j < matrix.Length0 then matrix[j,i] else 0.0);
        assert result.Length0 == matrix.Length1;
        assert result.Length1 == matrix.Length0;
    }
    // for i := 0 to matrix.Length1
    //     invariant 0 <= i <= matrix.Length1
    //     invariant forall x, j :: 0 <= x < i <= matrix.Length1 <= result.Length0 && 0 <= j < matrix.Length0 <= result.Length1 ==> result[i,j] == matrix[j,i]

    // {
    //     for j := 0 to matrix.Length0 
    //         invariant 0 <= j <= matrix.Length0
    //         invariant forall x, j :: 0 <= x < i && 0 <= j < matrix.Length0 ==> result[i,j] == matrix[j,i]
    //         invariant forall x :: 0 <= x < j <= matrix.Length0 ==> result[i,x] == matrix[x, i]

    //     {
    //         result[i,j] := matrix[j,i];
    //     }
    // }


    datatype Matrix<T> = Matrice(vals: seq<seq<T>>, rows: nat, columns: nat)

    predicate isMatrix<T>(mat: Matrix<T>) {
        mat.rows >= 1 && mat.columns >= 1 && |mat.vals| == mat.rows && forall i :: 0 <= i < mat.rows ==> |mat.vals[i]| == mat.columns
    }

    function seqTranspose(mat: Matrix): Matrix
        requires isMatrix(mat)
        ensures isMatrix(seqTranspose(mat))
        ensures seqTranspose(mat).columns == mat.rows
        ensures seqTranspose(mat).rows == mat.columns
    //     ensures seqTranpose(matrix).Length0 == matrix.Length1 && ftranspose(matrix).Length1 == matrix.Length0
        ensures forall i, j :: 0 <= i < mat.columns && 0 <= j < mat.rows ==> seqTranspose(mat).vals[i][j] == mat.vals[j][i]
    {
        Matrice(seq(mat.columns, i requires 0 <= i < mat.columns => seq(mat.rows, j requires 0 <= j < mat.rows => mat.vals[j][i])), mat.columns, mat.rows)
    }

    function matAdd(left: Matrix<real>, right: Matrix<real>): Matrix<real>
        requires isMatrix(left) && isMatrix(right)
        requires left.rows == right.rows
        requires left.columns == right.columns
        ensures isMatrix(matAdd(left,right))
        ensures matAdd(left,right).rows == left.rows && matAdd(left, right).columns == left.columns
        ensures forall i, j :: 0 <= i < left.rows  && 0 <= j < left.columns ==> matAdd(left,right).vals[i][j] == left.vals[i][j] + right.vals[i][j]
    {
        Matrice(seq(left.rows, i requires 0 <= i < left.rows => seq(left.columns, j requires 0 <= j < left.columns => left.vals[i][j] + right.vals[i][j])), left.rows, left.columns)
    }

    function Sum(vals: seq<real>): real
        {
            if |vals| == 0 then 0.0 else vals[0] + Sum(vals[1..])
        } by method {
            var sum := 0.0;
            for i := 0 to |vals| 
                invariant sum == Sum(vals[..i])
            {
                assert sum == Sum(vals[..i]);
                assert vals[..(i+1)] == vals[..i]+[vals[i]];
                sumSeqLemma(vals[..i],[vals[i]]);
                sum := sum + vals[i];
            }
            assert vals[..|vals| ] == vals;
            return sum;
        }

        lemma sumSeqLemma(a: seq<real>, b: seq<real>) 
            ensures Sum(a+b) == Sum(a)+Sum(b)
        {
            if a == [] {
                assert a + b == b;
            }
            else {
                sumSeqLemma(a[1..], b);
                calc {
                Sum(a + b);
                {
                    assert (a + b)[0] == a[0];
                    assert (a + b)[1..] == a[1..] + b;
                }
                a[0] + Sum(a[1..] + b);
                a[0] + Sum(a[1..]) + Sum(b);
                }
            }
        }

    function matMul(left: Matrix<real>, right: Matrix<real>): Matrix<real>
        requires isMatrix(left) && isMatrix(right)
        requires left.columns == right.rows
        ensures isMatrix(matMul(left,right))
        ensures matMul(left,right).rows == left.rows && matMul(left, right).columns == right.columns
        // ensures forall i, j :: 0 <= i < left.rows  && 0 <= j < left.columns ==> matMul(left,right).vals[i][j] == left.vals[i][j] + right.vals[i][j]
    {
        Matrice(seq(left.rows, i requires 0 <= i < left.rows => seq(right.columns, j requires 0 <= j < right.columns => Sum(seq(left.columns, k requires 0 <= k < left.columns => left.vals[i][k]*right.vals[k][j])))), left.rows, right.columns)
    }


    lemma matQ(mat1: Matrix, mat2: Matrix) 
        requires isMatrix(mat1)
        requires isMatrix(mat2)
        requires mat2 == seqTranspose(seqTranspose(mat1))
        requires mat2.columns == mat1.columns
        requires mat2.rows == mat1.rows
        requires |mat1.vals| == |mat2.vals|
        requires forall i :: 0 <= i < |mat1.vals| ==> |mat1.vals[i]| == |mat2.vals[i]| == mat1.columns == mat2.columns
        requires forall i,j :: 0 <= i < mat1.rows <= mat2.columns && 0 <= j < mat1.columns <= mat2.columns ==> mat2.vals[i][j] == seqTranspose(seqTranspose(mat1)).vals[i][j]
        ensures forall i :: 0 <= i < |mat1.vals| ==> mat1.vals[i] == mat2.vals[i]
    {

    }

    lemma matTranspose(mat: Matrix) 
        requires isMatrix(mat)
        ensures seqTranspose(seqTranspose(mat)) == mat
    {
        // calc {
        //     seqTranspose(mat).columns == mat.rows && seqTranspose(mat).rows == mat.columns;
        //     ==>
        //     seqTranspose(seqTranspose(mat)).columns == mat.columns && seqTranspose(seqTranspose(mat)).rows == mat.rows;
        // }
        // assert seqTranspose(seqTranspose(mat)).columns == mat.columns;
        // assert seqTranspose(seqTranspose(mat)).rows == mat.rows;

        // matQ(mat, seqTranspose(seqTranspose(mat)));
        assert forall i :: 0 <= i < |mat.vals| ==> mat.vals[i] == seqTranspose(seqTranspose(mat)).vals[i];
        // assert seqTranspose(seqTranspose(mat)).vals == mat.vals;
    }

    lemma seqEqual<T>(left: seq<seq<T>>, right: seq<seq<T>>, rows: nat, columns: nat)
        requires |left| == |right| == rows
        requires forall i :: 0 <= i < rows ==> |left[i]| == |right[i]| == columns
        //if all in one row i are equal then the rows are equal and if all rows are equal then all 
        requires forall i, j :: 0 <= i < rows && 0 <= j < columns ==> left[i][j] == right[i][j]
        ensures forall i :: 0 <= i < rows ==> left[i] == right[i]
        // ensures left == right
    {

    }

    /*
	FloydWarshall() {
		if(this.rows != this.columns) {
			throw new Error("Matrix incorrectly sized; Must be NxN matrix");
		}
		var D = this.copy(); 
		for(var k=0; k < this.rows; k++) {
			for(var i =0; i < this.rows; i++) {
				for(var j = 0; j < this.rows; j++) {
					if(D.values[i][k]+D.values[k][j] < D.values[i][j]) {
						D.values[i][j] =D.values[i][k]+D.values[k][j]; 
					}
				}
			}
			// $("body").append("D(k)=<br>"+D);
		}
		return D;
	}
    */
    datatype NumberOrInfinity = Number(n: nint64) | Infinity
    function lt(a: NumberOrInfinity, b: NumberOrInfinity): bool
    {
        if !a.Infinity? && !b.Infinity? then a.n < b.n else if !a.Infinity? && b.Infinity? then true else false
    }

    lemma TestLt()
    {
        assert lt(Number(1), Number(2));
        assert !lt(Number(2), Number(1));
        assert lt(Number(1), Infinity);
        assert !lt(Infinity, Number(1));
        assert !lt(Infinity, Infinity);
    }


    function addNumbers(a: NumberOrInfinity, b: NumberOrInfinity): NumberOrInfinity
    {
        if !a.Infinity? && !b.Infinity? then Number(a.n + b.n) else Infinity
    }
    method FloydWarshall(graph: array2<NumberOrInfinity>)
        requires graph.Length0 == graph.Length1
        modifies graph
    {
        var D := graph;
        for k := 0 to D.Length0
        {
            print "FW k=", k," / ", D.Length0, "\n";
            for i := 0 to D.Length0
            {
                for j := 0 to D.Length0
                {
                    if lt(addNumbers(D[i,k], D[k,j]), D[i,j]) {
                        D[i,j] := addNumbers(D[i,k], D[k,j]);
                    }
                }
            }
        }
    }


    method Test() {
        var foo : Matrix := Matrice([[1.0,2.0],[3.0,4.0]],2,2);
        var boo : Matrix := seqTranspose(foo);
    }
}