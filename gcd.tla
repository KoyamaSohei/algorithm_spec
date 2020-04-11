-------------------------------- MODULE gcd --------------------------------
EXTENDS Naturals,TLC

CONSTANTS N

p | q == \E d \in 1..q : q = p * d
Divisors(q) == {d \in 1..q : d | q}
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
GCD(p,q) == IF p = 0 \/ q = 0 THEN 0 ELSE Max(Divisors(p) \cap Divisors(q))
Input == {<<x,y>> \in (0..N) \X (0..N) : x+y>0}

(* --algorithm Euclid 
variables xy \in Input,x=xy[1],y=xy[2];
begin
if x < y
then
  x := y || y := x;
end if;
while x # 0 do
  if x < y 
  then
    x := y || y := x;
  end if;
  x := x - y;
end while;
assert y = GCD(xy[1],xy[2]);
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES xy, x, y, pc

vars == << xy, x, y, pc >>

Init == (* Global variables *)
        /\ xy \in Input
        /\ x = xy[1]
        /\ y = xy[2]
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF x < y
               THEN /\ /\ x' = y
                       /\ y' = x
               ELSE /\ TRUE
                    /\ UNCHANGED << x, y >>
         /\ pc' = "Lbl_2"
         /\ xy' = xy

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF x # 0
               THEN /\ IF x < y
                          THEN /\ /\ x' = y
                                  /\ y' = x
                          ELSE /\ TRUE
                               /\ UNCHANGED << x, y >>
                    /\ pc' = "Lbl_3"
               ELSE /\ Assert(y = GCD(xy[1],xy[2]), 
                              "Failure of assertion at line 26, column 1.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << x, y >>
         /\ xy' = xy

Lbl_3 == /\ pc = "Lbl_3"
         /\ x' = x - y
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << xy, y >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun Apr 12 04:46:06 JST 2020 by koyamaso
\* Created Fri Apr 10 20:02:23 JST 2020 by koyamaso
