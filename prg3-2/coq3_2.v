(*
  CSE-433 Logic in Computer Science, POSTECH (gla@postech.ac.kr)
    --- first order logic 

  The handin directory is programming2.postech.ac.kr:/home/class/cs433/<HemosID>/.
 *)

Section FirstOrder. 

Variable Term : Set.

Variables A B : Term -> Prop.

Variable O : Term.
Variable S : Term -> Term.

Variable Nat : Term -> Prop.
Variable Eq : Term -> Term -> Prop.
Variable Lt : Term -> Term -> Prop.

(* 
 * Axioms
 *)

Hypothesis Zero : Nat O.
Hypothesis Succ : forall x : Term, Nat x -> Nat (S x).
Hypothesis Eqi : forall x : Term, Eq x x.
Hypothesis Eqt : forall (x : Term) (y : Term) (z: Term), (Eq x y /\ Eq x z) -> Eq y z.
Hypothesis Lts : forall x : Term, Lt x (S x).
Hypothesis Ltn : forall (x : Term) (y : Term), Eq x y -> ~ Lt x y.

(* 
 * Part 0 - Please redo the exercise given in the handout. 
 *)

Theorem forall_and : 
(forall x : Term, A x /\ B x) -> (forall x : Term, A x)  /\ (forall x : Term, B x).
Admitted.

Theorem exist_neg : (exists x : Term, ~ A x) -> (~ forall x : Term, A x).
Admitted.

Theorem not_weird : forall y : Term, (forall x : Term, A x) -> (exists x : Term, A x).
Admitted.

(* 
 * Part 1
 *)

Theorem Nat_ex : forall x : Term, Nat x -> exists y : Term, Nat y /\ Eq x y.
Admitted.

Theorem Eq_refl : forall (x : Term) (y : Term), Eq x y -> Eq y x.
Admitted.

Theorem Eq_not : ~ exists x : Term, Eq x O /\ Eq x (S O).
Admitted.

(*
 * Part 2
 *)

Theorem Nat_succ2 : forall x : Term, Nat x -> Nat (S (S x)).
Admitted.

Theorem Lt_Neq : forall (x : Term) (y : Term), Lt x y -> ~ Eq x y.
Admitted.

Theorem Not_EqLt : ~ exists x : Term, exists y : Term, Eq x y /\ Lt x y.
Admitted.

End FirstOrder. 



