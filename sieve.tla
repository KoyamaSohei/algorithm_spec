------------------------------- MODULE sieve -------------------------------
EXTENDS Naturals,TLC

CONSTANTS N

p | q == \E d \in 1..q : q = p * d
Divisors(q) == {d \in 1..q : d | q}
Prime(p) == Divisors(p) \ {1,p} = {}

AllTRUE[n \in 1..N] == TRUE
ANSWER[n \in 1..N] == IF n = 1 THEN FALSE ELSE Prime(n)

(* --algorithm Eratosthenes
variable isp = AllTRUE,k=2,i=0;
begin
a:
isp[1] := FALSE;
b:
while k * k < N+1 do
  if isp[k] = FALSE
  then 
    goto e;
  else
    i := k+k;
c:
    while i < N+1 do
      isp[i] := FALSE;
      i := i+k;
    end while;
  end if;
e:
k := k+1;
end while;
assert isp = ANSWER;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES isp, k, i, pc

vars == << isp, k, i, pc >>

Init == (* Global variables *)
        /\ isp = AllTRUE
        /\ k = 2
        /\ i = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ isp' = [isp EXCEPT ![1] = FALSE]
     /\ pc' = "b"
     /\ UNCHANGED << k, i >>

b == /\ pc = "b"
     /\ IF k * k < N+1
           THEN /\ IF isp[k] = FALSE
                      THEN /\ pc' = "e"
                           /\ i' = i
                      ELSE /\ i' = k+k
                           /\ pc' = "c"
           ELSE /\ Assert(isp = ANSWER, 
                          "Failure of assertion at line 34, column 1.")
                /\ pc' = "Done"
                /\ i' = i
     /\ UNCHANGED << isp, k >>

e == /\ pc = "e"
     /\ k' = k+1
     /\ pc' = "b"
     /\ UNCHANGED << isp, i >>

c == /\ pc = "c"
     /\ IF i < N+1
           THEN /\ isp' = [isp EXCEPT ![i] = FALSE]
                /\ i' = i+k
                /\ pc' = "c"
           ELSE /\ pc' = "e"
                /\ UNCHANGED << isp, i >>
     /\ k' = k

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ b \/ e \/ c
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Fri Apr 10 23:17:26 JST 2020 by koyamaso
\* Created Fri Apr 10 20:47:11 JST 2020 by koyamaso
