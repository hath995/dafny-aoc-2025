include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"

module Problem7 {
    import opened Split
    import opened ParseInt
    import opened Std.Collections.Seq
    method parseInput(input:string) returns (start: (nat,nat), splitters: set<(nat, nat)>, lines: seq<string>)
        ensures forall s :: s in splitters ==> s.1 < |lines| && s.0 < |lines[s.1]| && lines[s.1][s.0] == '^'
    {
        lines := splitOnBreak(input);
        start := (0,0);
        splitters := {};
        expect |lines| > 0;
        for y := 0 to |lines| 
            invariant forall s :: s in splitters ==> s.1 < |lines| && s.0 < |lines[s.1]| && lines[s.1][s.0] == '^'
        {
            for x := 0 to |lines[y]|
                invariant forall s :: s in splitters ==> s.1 < |lines| && s.0 < |lines[s.1]| && lines[s.1][s.0] == '^'
            {
                if lines[y][x] == 'S' {
                    start := (x,y);
                } else if lines[y][x] == '^' {
                    splitters := splitters + {(x,y)};
                }
            }
        }
        expect exists y, x :: 0<= y < |lines| && 0 <= x < |lines[y]| && lines[y][x] == 'S' && start == (x,y);
    }
    method problem7_1(input: string) returns (x: int) {
        var start, splitters, lines := parseInput(input);
        x := 0;
        var beams := {start.0};
        for y := 0 to |lines|
        {
            var lines_splitters := set sp | sp in splitters && sp.0 in beams && sp.1 == y :: sp.0;
            x := x + |lines_splitters|;
            beams := beams - lines_splitters + (set sp | sp in lines_splitters && sp > 0 :: sp-1) + (set sp | sp in lines_splitters :: sp+1);
        }
    }

    method problem7_2(input: string) returns (answer: int) {
        var start, splitters, lines := parseInput(input);
        answer := 1;
        var beams := multiset{start.0};
        for y := 0 to |lines|
        {
            var next_beams: multiset<nat> := multiset{};
            var lines_splitters := set sp | sp in splitters && sp.0 in beams && sp.1 == y :: sp.0;
            if lines_splitters != {} {
                // x := x * |lines_splitters|;
                var lefts := set sp | sp in lines_splitters && sp > 0 :: sp-1;
                var rights := set sp | sp in lines_splitters :: sp+1;
                next_beams := beams;
                while lines_splitters != {}
                {
                    var x :| x in lines_splitters;
                    next_beams := next_beams[x := 0];
                    lines_splitters := lines_splitters - {x};
                }
                while lefts != {} {
                    var x :| x in lefts;
                    next_beams := next_beams[x := beams[x+1]+next_beams[x]];
                    lefts := lefts - {x};
                }

                while rights != {} {
                    var x :| x in rights;
                    next_beams := next_beams[x := beams[x-1]+next_beams[x]];
                    rights := rights - {x};
                }
                beams := next_beams;
            }
        }
        answer := |beams|;
    }
}
