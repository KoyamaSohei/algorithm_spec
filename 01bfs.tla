------------------------------- MODULE 01bfs -------------------------------
EXTENDS Naturals,Sequences,TLC

RECURSIVE Max(_)
RECURSIVE Min(_)
RECURSIVE Sorted(_)

(*
If All edge cost is 0 or a(>0), 
We can use deque when Dijkstra's algorithm do, instead of priority queue. 
This order is O(E+V),(usually Dijkstra's algorithm is O((E+V)log(E+V)) ).
We'll make sure deque is always sorted.
*)

Max(t) == IF Len(t) = 0 THEN 0      ELSE IF Head(t) > Max(Tail(t)) THEN Head(t) ELSE Max(Tail(t))
Min(t) == IF Len(t) = 0 THEN 100000 ELSE IF Head(t) < Min(Tail(t)) THEN Head(t) ELSE Min(Tail(t))
Sorted(t) == Len(t) <= 1 \/ (Head(t) <= Min(Tail(t)) /\ Sorted(Tail(t)))

(* --algorithm 01bfs 
variables deque = <<>>,cost \in 1..10,times=10,x=0;

macro pushBack(t,x) 
begin
  t := Append(t,x);
end macro;

macro pushFront(t,x) 
begin
  t := <<x>> \o t;
end macro;

macro pop() 
begin 
deque := Tail(deque);
end macro;

macro push(x)
begin 
either
  pushBack(deque,x+cost);
  or
  pushFront(deque,x);
end either;
end macro;

begin
a:
pushBack(deque,0);
b:
while times > 0 do
  times := times-1;
  x := Head(deque);
  pop();
  c:
  push(x);
  d:
  push(x);
  e:
  push(x);
  f:
  assert Sorted(deque)
end while;
end algorithm *)
\* BEGIN TRANSLATION
VARIABLES deque, cost, times, x, pc

vars == << deque, cost, times, x, pc >>

Init == (* Global variables *)
        /\ deque = <<>>
        /\ cost \in 1..10
        /\ times = 10
        /\ x = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ deque' = Append(deque,0)
     /\ pc' = "b"
     /\ UNCHANGED << cost, times, x >>

b == /\ pc = "b"
     /\ IF times > 0
           THEN /\ times' = times-1
                /\ x' = Head(deque)
                /\ deque' = Tail(deque)
                /\ pc' = "c"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << deque, times, x >>
     /\ cost' = cost

c == /\ pc = "c"
     /\ \/ /\ deque' = Append(deque,(x+cost))
        \/ /\ deque' = <<x>> \o deque
     /\ pc' = "d"
     /\ UNCHANGED << cost, times, x >>

d == /\ pc = "d"
     /\ \/ /\ deque' = Append(deque,(x+cost))
        \/ /\ deque' = <<x>> \o deque
     /\ pc' = "e"
     /\ UNCHANGED << cost, times, x >>

e == /\ pc = "e"
     /\ \/ /\ deque' = Append(deque,(x+cost))
        \/ /\ deque' = <<x>> \o deque
     /\ pc' = "f"
     /\ UNCHANGED << cost, times, x >>

f == /\ pc = "f"
     /\ Assert(Sorted(deque), "Failure of assertion at line 61, column 3.")
     /\ pc' = "b"
     /\ UNCHANGED << deque, cost, times, x >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ b \/ c \/ d \/ e \/ f
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sat May 02 17:11:48 JST 2020 by koyamaso
\* Created Sat May 02 13:14:20 JST 2020 by koyamaso
