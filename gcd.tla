-------------------------------- MODULE gcd --------------------------------
EXTENDS Integers,TLC

CONSTANTS N

Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Abs(p) == IF p < 0 THEN -p ELSE p
Gcd(p,q) == Max({x \in 1..N : p % x = 0 /\ q % x = 0})
Input == {<<x,y>> \in (-N..N) \X (-N..N) : x#0\/y#0 }

(* --algorithm Euclid 
variables xy \in Input,x=xy[1],y=xy[2];
begin
a:
x := Abs(x);
y := Abs(y);
b:
if y = 0
then
  y := x;
  goto f;
end if;
c:
if x = 0
then 
  goto f;
end if;
d:
while x # 0 do
  x := y || y := x;
  e:
  x := x % y;
end while;
f:
assert y = Gcd(xy[1],xy[2]);
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
     /\ x' = Abs(x)
     /\ y' = Abs(y)
     /\ pc' = "b"
     /\ xy' = xy

b == /\ pc = "b"
     /\ IF y = 0
           THEN /\ y' = x
                /\ pc' = "f"
           ELSE /\ pc' = "c"
                /\ y' = y
     /\ UNCHANGED << xy, x >>

c == /\ pc = "c"
     /\ IF x = 0
           THEN /\ pc' = "f"
           ELSE /\ pc' = "d"
     /\ UNCHANGED << xy, x, y >>

d == /\ pc = "d"
     /\ IF x # 0
           THEN /\ /\ x' = y
                   /\ y' = x
                /\ pc' = "e"
           ELSE /\ pc' = "f"
                /\ UNCHANGED << x, y >>
     /\ xy' = xy

e == /\ pc = "e"
     /\ x' = x % y
     /\ pc' = "d"
     /\ UNCHANGED << xy, y >>

f == /\ pc = "f"
     /\ Assert(y = Gcd(xy[1],xy[2]), 
               "Failure of assertion at line 35, column 1.")
     /\ pc' = "Done"
     /\ UNCHANGED << xy, x, y >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ b \/ c \/ d \/ e \/ f
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun Apr 12 07:19:57 JST 2020 by koyamaso
\* Created Fri Apr 10 20:02:23 JST 2020 by koyamaso
