(*
  CSE-433 Logic in Computer Science, POSTECH (gla@postech.ac.kr)
    --- Proof terms 

  The handin directory is programming2.postech.ac.kr:/home/class/cs433/<HemosID>/.
 *)

Section ProofTerm.

Variables A B C D : Prop.

(*
 * Tactics 
 *)

Definition impl_distr : (A -> B) -> (A -> C) -> A -> B -> C := .

Definition impl_comp : (A -> B) -> (B -> C) -> A -> C := .

Definition impl_perm : (A -> B -> C) -> B -> A -> C := .

Definition impl_conj : A -> B -> A /\ B := .

Definition conj_elim_l : A /\ B -> A := .

Definition disj_intro_l : A -> A \/ B := .

Definition disj_elim : A \/ B -> (A -> C) -> (B -> C) -> C := .

Definition diamond : (A -> B) -> (A -> C) -> (B -> C -> D) -> A -> D := .

Definition weak_peirce : ((((A -> B) -> A) -> A) -> B) -> B := .

Definition disj_impl_dist : (A \/ B -> C) -> (A -> C) /\ (B -> C) := .

Definition disj_impl_dist_inv : (A -> C) /\ (B -> C) -> A \/ B -> C := .

Definition curry : (A /\ B -> C) -> A -> B -> C := .

Definition uncurry : (A -> B -> C) -> A /\ B -> C := .

(*
 * Negation
 *)

Definition contrapositive : (A -> B) -> (~B -> ~A) := .

Definition neg_double : A -> ~~A := .

Definition tneg : ~~~A -> ~A := .

Definition weak_dneg : ~~(~~A -> A) := .

(*
 * Classical logic
 *)

Definition em_peirce : A \/ ~A -> ((A -> B) -> A) -> A := .

Definition peirce_dne : (((A -> False) -> A) -> A) -> ~~A -> A := .

Definition dne_em : (~~(B \/ ~B)-> (B \/ ~B)) -> B \/ ~B := .

End ProofTerm. 

