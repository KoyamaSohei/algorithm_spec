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
a:
if x=0 \/ y=0 
then 
  y := 0;
  goto e
end if;
b:
while x # 0 do
  if x < y 
  then
    x := y || y := x;
  end if;
  c:
  x := x % y;
end while;
e:
assert y = GCD(xy[1],xy[2]);
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES xy, x, y, pc

vars == << xy, x, y, pc >>

Init == (* Global variables *)
        /\ xy \in Input
        /\ x = xy[1]
        /\ y = xy[2]
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF x=0 \/ y=0
           THEN /\ y' = 0
                /\ pc' = "e"
           ELSE /\ pc' = "b"
                /\ y' = y
     /\ UNCHANGED << xy, x >>

b == /\ pc = "b"
     /\ IF x # 0
           THEN /\ IF x < y
                      THEN /\ /\ x' = y
                              /\ y' = x
                      ELSE /\ TRUE
                           /\ UNCHANGED << x, y >>
                /\ pc' = "c"
           ELSE /\ pc' = "e"
                /\ UNCHANGED << x, y >>
     /\ xy' = xy

c == /\ pc = "c"
     /\ x' = x % y
     /\ pc' = "b"
     /\ UNCHANGED << xy, y >>

e == /\ pc = "e"
     /\ Assert(y = GCD(xy[1],xy[2]), 
               "Failure of assertion at line 31, column 1.")
     /\ pc' = "Done"
     /\ UNCHANGED << xy, x, y >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ b \/ c \/ e
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun Apr 12 05:40:53 JST 2020 by koyamaso
\* Created Fri Apr 10 20:02:23 JST 2020 by koyamaso
