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

Definition impl_distr : (A -> B) -> (A -> C) -> A -> B -> C :=
  fun (_f: A -> B) (g: A -> C) (a: A) (_b: B) => g a.

Definition impl_comp : (A -> B) -> (B -> C) -> A -> C :=
  fun (f: A -> B) (g: B -> C) (a: A) => g (f a).

Definition impl_perm : (A -> B -> C) -> B -> A -> C :=
  fun (f: A -> B -> C) (b: B) (a: A) => f a b.

Definition impl_conj : A -> B -> A /\ B :=
  fun (a: A) (b: B) => conj a b.

Definition conj_elim_l : A /\ B -> A :=
  fun (x: A /\ B) => and_ind (fun (a: A) (_b: B) => a) x.

Definition disj_intro_l : A -> A \/ B :=
  fun (a: A) => or_introl B a.

Definition disj_elim : A \/ B -> (A -> C) -> (B -> C) -> C :=
  fun (x: A \/ B) (f: A -> C) (g: B -> C) => or_ind f g x.

Definition diamond : (A -> B) -> (A -> C) -> (B -> C -> D) -> A -> D :=
  fun (f: A -> B) (g: A -> C) (h: B -> C -> D) (a: A) => h (f a) (g a).

Definition weak_peirce : ((((A -> B) -> A) -> A) -> B) -> B :=
  fun (f: (((A -> B) -> A) -> A) -> B) =>
    f (fun (g: (A -> B) -> A) =>
      g (fun (a: A) =>
        f (fun (_: (A -> B) -> A) => a))).

Definition disj_impl_dist : (A \/ B -> C) -> (A -> C) /\ (B -> C) :=
  fun (f: A \/ B -> C) =>
    conj
      (fun (a: A) => f (or_introl B a))
      (fun (b: B) => f (or_intror A b)).

Definition disj_impl_dist_inv : (A -> C) /\ (B -> C) -> A \/ B -> C :=
  fun (x: (A -> C) /\ (B -> C)) =>
    fun (y: A \/ B) =>
      or_ind
        (and_ind (fun (a: A -> C) (_b: B -> C) => a) x)
        (and_ind (fun (_a: A -> C) (b: B -> C) => b) x)
        y.

Definition curry : (A /\ B -> C) -> A -> B -> C :=
  fun (f: A /\ B -> C) (a: A) (b: B) => f (conj a b).

Definition uncurry : (A -> B -> C) -> A /\ B -> C :=
  fun (f: A -> B -> C) (x: A /\ B) =>
    f
      (and_ind (fun (a: A) (_b: B) => a) x)
      (and_ind (fun (_a: A) (b: B) => b) x).


(*
 * Negation
 *)

Definition contrapositive : (A -> B) -> (~B -> ~A) :=
  fun (f: A -> B) (nb: ~B) (a: A) => nb (f a).

Definition neg_double : A -> ~~A :=
  fun (a: A) (na: ~A) => na a.

Definition tneg : ~~~A -> ~A :=
  fun (tna: ~~~A) (a: A) => tna (fun (na: ~A) => na a).

Definition weak_dneg : ~~(~~A -> A) :=
  fun (nx: ~(~~A -> A)) =>
    nx (fun (dna: ~~A) => False_ind A (
      dna (fun (a: A) => nx (fun _ => a)))).

(*
 * Classical logic
 *)

Definition em_peirce : A \/ ~A -> ((A -> B) -> A) -> A :=
  fun (x: A \/ ~A) (y: (A -> B) -> A) =>
    or_ind
      (fun (a: A) => a)
      (fun (na: ~A) =>
         y (fun (a: A) => False_ind B (na a)))
      x.

Definition peirce_dne : (((A -> False) -> A) -> A) -> ~~A -> A :=
  fun (x: ((A -> False) -> A) -> A) (dna: ~~A) =>
    x (fun (y: A -> False) =>
      False_ind A (dna (fun (a: A) => y a))).

Definition dne_em : (~~(B \/ ~B) -> (B \/ ~B)) -> B \/ ~B :=
  fun (x: ~~(B \/ ~B) -> (B \/ ~B)) =>
    x (fun (y: ~(B \/ ~B)) =>
      y (or_intror B (fun (b: B) =>
        y (or_introl (~B) b)))).

End ProofTerm.
