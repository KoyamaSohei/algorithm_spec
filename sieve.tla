------------------------------- MODULE sieve -------------------------------
EXTENDS Naturals,TLC

CONSTANTS N

Prime(p) == p > 1 /\ ~\E d \in 2..(p-1) : p % d = 0

(* --algorithm Eratosthenes
variable isp = [n \in 1..N |-> TRUE],k=2,i=0;
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
assert isp = [n \in 1..N |-> Prime(n)];
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES isp, k, i, pc

vars == << isp, k, i, pc >>

Init == (* Global variables *)
        /\ isp = [n \in 1..N |-> TRUE]
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
           ELSE /\ Assert(isp = [n \in 1..N |-> Prime(n)], 
                          "Failure of assertion at line 29, column 1.")
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
\* Last modified Sat Apr 11 03:40:36 JST 2020 by koyamaso
\* Created Fri Apr 10 20:47:11 JST 2020 by koyamaso
