include "../../parser/split.dfy"
include "../../parser/parseInt.dfy"
module Problem1 {
    import opened Split
    import opened ParseInt
    datatype Rotation = Left(n: nat) | Right(n: nat)
    method parseInput(input: string) returns (xs: seq<Rotation>) {
        var lines := splitOnBreak(input);
        xs := [];
        for i := 0 to |lines| 
        {
            expect |lines[i]| > 0;
            var dist := Integer(lines[i][1..]);
            expect dist >= 0;
            xs := xs + if lines[i][0] == 'L' then [Left(dist)] else [Right(dist)];
        }
    }

    function rotate(r: Rotation, pos: nat): nat {
        match r {
            case Left(n) => (pos-n)%100
            case Right(n) => (pos+n)%100
        }
    }

    function rotateAndCount(r: Rotation, pos: nat): (nat, nat)
        requires pos < 100
        ensures r.Left? ==> rotateAndCount(r, pos).1 == |set x | pos-r.n <= x < pos && x % 100 == 0|
        ensures r.Right? ==> rotateAndCount(r, pos).1 ==|set x | pos < x <= pos+r.n && x % 100 == 0|  
    {
        LemmaPminusSetSize(pos, r.n);
        LemmaPSetSize(pos, r.n);
        match r {
            // case Left(n) => ((pos-n)%100, |set x | pos-n <= x < pos && x % 100 == 0|)
            // case Right(n) => ((pos+n)%100, |set x | pos < x <= pos+n && x % 100 == 0|)
            case Left(n) => ((pos-n)%100, if pos == 0 then n/100 else (n+100-pos)/100)
            case Right(n) => ((pos+n)%100, (pos+n)/100)
        }
    }

lemma LemmaPminusSetSize(pos: nat, n: nat)
    requires pos < 100
    ensures pos == 0 ==> |set x | pos-n <= x < pos && x % 100 == 0| == n/100
    ensures pos != 0 ==> |set x | pos-n <= x < pos && x % 100 == 0| == (n+100-pos)/100
{
    if n == 0 {
        // Base Case: The set is empty.
        // If pos == 0: n/100 -> 0/100 == 0. Correct.
        // If pos != 0: (n+100-pos)/100 -> (100-pos)/100. 
        //    Since 0 < pos < 100, then 0 < 100-pos < 100. Division yields 0. Correct.
    } else {
        // Inductive Step
        // 1. Define the sets to make the proof readable
        var S_curr := set x | pos - n <= x < pos && x % 100 == 0;
        var S_prev := set x | pos - (n - 1) <= x < pos && x % 100 == 0;
        
        // 2. Identify the new element added to the range at the bottom
        var newVal := pos - n;

        // 3. Apply Induction Hypothesis
        LemmaPminusSetSize(pos, n - 1);

        // 4. Connect S_curr and S_prev
        if newVal % 100 == 0 {
            assert S_curr == S_prev + {newVal};
        } else {
            assert S_curr == S_prev;
        }

        // 5. Prove the arithmetic for both cases
        if pos == 0 {
            // Target Formula: n / 100
            // newVal is (-n).
            // Note: (-n) % 100 == 0 <==> n % 100 == 0
            if newVal % 100 == 0 {
                calc {
                    n / 100;
                    (n - 1) / 100 + 1; // Arithmetic property
                    |S_prev| + 1;
                    |S_curr|;
                }
            } else {
                calc {
                    n / 100;
                    (n - 1) / 100;
                    |S_prev|;
                    |S_curr|;
                }
            }
        } else {
            // Target Formula: (n + 100 - pos) / 100
            // Let's call the numerator 'Num'
            var Num := n + 100 - pos;
            var NumPrev := (n - 1) + 100 - pos;
            
            // Critical Arithmetic Link:
            // newVal is divisible by 100 <==> Num is divisible by 100
            // newVal = pos - n. 
            // Num    = 100 - (pos - n). 
            // If (pos-n) is a multiple of 100, then (100 - (pos-n)) is also a multiple.
            
            if newVal % 100 == 0 {
                calc {
                    Num / 100;
                    (NumPrev + 1) / 100;
                    // Since Num is div by 100, (Num-1)/100 + 1 == Num/100
                    NumPrev / 100 + 1; 
                    |S_prev| + 1;
                    |S_curr|;
                }
            } else {
                calc {
                    Num / 100;
                    (NumPrev + 1) / 100;
                    // Since Num is NOT div by 100, integer division swallows the +1
                    NumPrev / 100;
                    |S_prev|;
                    |S_curr|;
                }
            }
        }
    }
}

    lemma LemmaPSetSize(pos: nat, n: nat)
        requires pos < 100
        ensures |set x | pos < x <= pos+n && x % 100 == 0| == (pos+n)/100
    {
     if n == 0 {
        // Base Case: Range (pos, pos] is empty.
        // LHS: |{}| == 0
        // RHS: (pos + 0) / 100. Since pos < 100, this is 0.
    } else {
        // Inductive Step
        var range_n := set x | pos < x <= pos + n && x % 100 == 0;
        var range_prev := set x | pos < x <= pos + (n - 1) && x % 100 == 0;

        // 1. Apply the Inductive Hypothesis
        LemmaPSetSize(pos, n - 1);
        // We now know: |range_prev| == (pos + n - 1) / 100

        // 2. Analyze the specific new value we just added to the range: (pos + n)
        var newVal := pos + n;

        if newVal % 100 == 0 {
            // Case A: The new value is a multiple of 100.
            // Therefore, range_n includes everything in range_prev PLUS this new value.
            assert range_n == range_prev + {newVal};
            
            // Prove the arithmetic:
            // If X is a multiple of 100, then X/100 == (X-1)/100 + 1
            calc {
                (pos + n) / 100;
                newVal / 100;
                (newVal - 1) / 100 + 1; // Arithmetic property of integer division
                (pos + n - 1) / 100 + 1;
                |range_prev| + 1;
                |range_n|;
            }
        } else {
            // Case B: The new value is NOT a multiple of 100.
            // Therefore, range_n is exactly the same set as range_prev.
            assert range_n == range_prev;
            
            // Prove the arithmetic:
            // If X is NOT a multiple of 100, X/100 == (X-1)/100
            calc {
                (pos + n) / 100;
                (pos + n - 1) / 100;
                |range_prev|;
                |range_n|;
            }
        }
    }
    }

    method problem1_1(input: string) returns (x: int)
    {
        var rots := parseInput(input);
        x := 0;
        var pos: nat := 50;
        for i := 0 to |rots| {
            pos := rotate(rots[i], pos);
            if pos == 0 {
                x := x+1;
            }
        }
    }

    method problem1_2(input: string) returns (x: int)
    {
        var rots := parseInput(input);
        x := 0;
        var pos: nat := 50;
        for i := 0 to |rots|
            invariant pos < 100
        {
            var p := rotateAndCount(rots[i], pos);
            print "\n", p;
            x := x + p.1;
            pos := p.0;
        }
    }
}