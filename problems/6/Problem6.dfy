include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
module Problem6 {
    import opened Split
    import opened ParseInt
    import opened Std.Collections.Seq

    datatype Op = Add | Mul
    method parseInput(input: string) returns (data: seq<seq<nat>>, ops: seq<Op>, length: nat)
        ensures |ops| == length
        ensures forall d :: d in data ==> |d| == length
    {
        var lines := splitOnBreak(input);
        expect |lines| > 1;
        var ops_line := split(lines[|lines|-1], " ");
        lines := lines[..|lines|-1];
        data := [];
        ops := [];
        length := 0;
        for i := 0 to |ops_line| {
            if Contains(ops_line[i], "+") {
                ops := ops + [Add];
            } else if Contains(ops_line[i], "*") {
                ops := ops + [Mul];
            }
        }
        length := |ops|;
        print "\nops ", length;
        for i := 0 to |lines| 
            invariant forall d :: d in data ==> |d| == length
            invariant |data| == i
        {
            var row := Map(Integer, Filter(xs => xs != "", split(lines[i], " ")));
            print "\nrow ", i," ", |row|, " ", row;
            expect |row| == length;
            expect forall i: nat :: i < |row| ==> 0 < row[i];
            data := data + [row];
        }
        
    }

    function transpose(vals: seq<seq<nat>>, columns: nat, rows: nat): seq<seq<nat>> 
        requires forall d :: d in vals ==> |d| == columns
        requires |vals| == rows 
    {
        seq(columns, i requires 0 <= i < columns => seq(rows, j requires 0 <= j < rows => vals[j][i]))
    }

    function add(x: nat, y: nat): nat {
        x + y
    }

    function mul(x: nat, y: nat): nat {
        x * y
    }

    method problem6_1(input: string) returns (x: int) {
        var data, ops, length := parseInput(input);
        // print "\n", data;
        print "\n", ops;
        var homework := transpose(data, length, |data|);
        print "\n", homework;
        x := 0;
        expect |homework| == length;
        for i := 0 to |homework| 
        {
            var res := match ops[i] {
                case Add => FoldLeft(add, 0, homework[i])
                case Mul => FoldLeft(mul, 1, homework[i])
            };
            // print "\nwhat: ", what;
            x := x + res;
        }
        print "\n";
    }
    function maxLength<T>(xs: seq<seq<T>>): nat 
        ensures forall d :: d in xs ==> |d| <= maxLength(xs)
    {
        if xs == [] then
            0
        else
            var rl := maxLength(xs[1..]);
            if |xs[0]| > rl then |xs[0]| else rl
    }

    function ToDigits(n: nat): seq<nat> {
        if n < 10 then [n] else ToDigits(n/10)+[n%10]
    }

    method ToCephalopod(nums: seq<nat>) returns (res: seq<nat>)
    {
        print "\n", Map(ToDigits, nums);
        var digits := Map(ToDigits, nums);
        res := [];
        var num_seqs: seq<seq<nat>> := [];
    }

    function opIndexes(s: string, i: nat, idx: seq<nat>): seq<nat> {
        if s == [] then
            idx 
        else match s[0] {
            case '+' => opIndexes(s[1..], i+1, idx+[i])
            case '*' => opIndexes(s[1..], i+1, idx+[i])
            case _ => opIndexes(s[1..],i+1, idx)
        }
    }

    method parseInput2(input: string) returns (data: seq<seq<nat>>, ops: seq<Op>, length: nat)
        ensures |ops| == length
        ensures |data| == length
    {
        var lines := splitOnBreak(input);
        expect |lines| > 1;
        var ops_line := split(lines[|lines|-1], " ");
        var raw_op_lines := lines[|lines|-1];
        lines := lines[..|lines|-1];
        data := [];
        ops := [];
        length := 0;
        for i := 0 to |ops_line| {
            if Contains(ops_line[i], "+") {
                ops := ops + [Add];
            } else if Contains(ops_line[i], "*") {
                ops := ops + [Mul];
            }
        }
        // print "\nraw: ", raw_op_lines;
        var op_indexes := opIndexes(raw_op_lines, 0, []);
        // print "\nidx, ", op_indexes;
        length := |ops|;
        expect |op_indexes| == |ops|;
        for i := 0 to |ops|
        {
            var end:int := |raw_op_lines|;
            if i < |ops| - 1 {
                end := op_indexes[i+1] as int -1;
            }
            expect op_indexes[i] < end;
            var partials: seq<string> := [];
            
            for j := op_indexes[i] to end {
                var partial := "";
                for k := 0 to |lines| {
                    if 0 <= j < |lines[k]| && charInNC(lines[k][j]) {
                        partial := partial+[lines[k][j]];
                    }
                }
                partials := partials + [partial];
            }
            // print "\n",partials;
            var row := Map(Integer, partials);
            expect forall i: nat :: i < |row| ==> 0 < row[i];
            data := data + [row];
        }
        expect |data| == length;
    }

    method problem6_2(input: string) returns (x: int) {
        var data, ops, length := parseInput2(input);
        print "\n", data;
        print "\n", ops;
        x := 0;
        for i := 0 to |data| 
        {
            var res := match ops[i] {
                case Add => FoldLeft(add, 0, data[i])
                case Mul => FoldLeft(mul, 1, data[i])
            };
            // print "\nwhat: ", what;
            x := x + res;
        }
        print "\n";
    }
}
