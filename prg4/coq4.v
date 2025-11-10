(*
  CSE-433 Logic in Computer Science, POSTECH (gla@postech.ac.kr)
    --- Inductive Datatypes, Part 1 

  The handin directory is programming2.postech.ac.kr:/home/class/cs433/handin/<HemosID>/.  
 *)

Section InductiveDatatype.

(* inductive datatype nat *) 
 
Inductive nat : Set :=
| O : nat
| S : nat -> nat.

(* recursive functions plus, mult, double, sum_n *)

Fixpoint plus (m n:nat) {struct m} : nat :=
match m with
| O => n
| S m' => S (plus m' n)
end.

Fixpoint mult (m n:nat) {struct m} : nat :=
match m with
| O => O
| S m' => plus n (mult m' n)
end.

Fixpoint double (m:nat) : nat :=
match m with
| O => O
| S m' => S (S (double m'))
end.

Fixpoint sum_n (n:nat) {struct n} : nat :=
match n with
| O => O
| S n' => plus (S n') (sum_n n')
end.

(* Problem 1 *)

(* You do not need to use induction to prove plus_O_n. *)
Lemma plus_O_n : forall n:nat, n = plus O n.
Proof.
Qed.

(* You need to use induction to prove plus_n_O. *)
Lemma plus_n_O : forall n:nat, n = plus n O.
Proof.
Qed.

Lemma plus_n_S : forall n m:nat, S (plus n m) = plus n (S m).
Proof.
Qed.

Lemma plus_com : forall n m:nat, plus n m = plus m n.
Proof.
Qed.

Lemma plus_assoc : forall (m n l:nat), plus (plus m n) l = plus m (plus n l).
Proof.
Qed.

(* Problem 2 *)

(* Introduce lemmas as necessary. *)

Theorem sum_n_plus : forall n:nat, double (sum_n n) = plus n (mult n n).
Proof.
Qed.

End InductiveDatatype. 


