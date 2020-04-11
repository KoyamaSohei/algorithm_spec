-------------------------------- MODULE gcd --------------------------------
EXTENDS Naturals,TLC

CONSTANTS M, N

p | q == \E d \in 1..q : q = p * d
Divisors(q) == {d \in 1..q : d | q}
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
GCD(p,q) == Max(Divisors(p) \cap Divisors(q))

(* --algorithm Euclid 
variables x \in 1..M, y \in 1..N, x0 = x, y0 = y;
begin
while x # 0 do
  if x < y 
  then
    x := y || y := x;
  end if;
  x := x - y;
end while;
assert y = GCD(x0,y0);
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES x, y, x0, y0, pc

vars == << x, y, x0, y0, pc >>

Init == (* Global variables *)
        /\ x \in 1..M
        /\ y \in 1..N
        /\ x0 = x
        /\ y0 = y
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF x # 0
               THEN /\ IF x < y
                          THEN /\ /\ x' = y
                                  /\ y' = x
                          ELSE /\ TRUE
                               /\ UNCHANGED << x, y >>
                    /\ pc' = "Lbl_2"
               ELSE /\ Assert(y = GCD(x0,y0), 
                              "Failure of assertion at line 21, column 1.")
                    /\ pc' = "Done"
                    /\ UNCHANGED << x, y >>
         /\ UNCHANGED << x0, y0 >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ x' = x - y
         /\ pc' = "Lbl_1"
         /\ UNCHANGED << y, x0, y0 >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1 \/ Lbl_2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun Apr 12 02:42:57 JST 2020 by koyamaso
\* Created Fri Apr 10 20:02:23 JST 2020 by koyamaso
