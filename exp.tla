-------------------------------- MODULE exp --------------------------------
EXTENDS Naturals,TLC

CONSTANT A,B

Max(S) == CHOOSE x \in S: \A y \in S: x >= y
Div(a,b) == Max({x \in 0..a: x*b < a+1 /\ (x+1)*b > a})

(* --algorithm Exp 
variables res = 1,a = A,b = B;
begin
while b > 0 do
  if b % 2 = 1
    then res := res * a;
  end if;
  a := a * a;
  b := Div(b,2);
end while;
assert res = A^B;
end algorithm *)
\* BEGIN TRANSLATION
VARIABLES res, a, b, pc

vars == << res, a, b, pc >>

Init == (* Global variables *)
        /\ res = 1
        /\ a = A
        /\ b = B
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF b > 0
               THEN /\ IF b % 2 = 1
                          THEN /\ res' = res * a
                          ELSE /\ TRUE
                               /\ res' = res
                    /\ a' = a * a
                    /\ b' = Div(b,2)
                    /\ pc' = "Lbl_1"
               ELSE /\ Assert(res = A^B, 
                              "Failure of assertion at line 19, column 1.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << res, a, b >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Sat Apr 11 16:15:42 JST 2020 by koyamaso
\* Created Sat Apr 11 15:56:03 JST 2020 by koyamaso
