(*
  CSE-433 Logic in Computer Science, POSTECH (gla@postech.ac.kr)
    --- Propositional Logic

  The handin directory is programming2.postech.ac.kr:/home/class/cs433/handin/<HemosID>/.
 *)

(*

  Tactics to practice:
    intro[s]
      [H H']
      [H | H']
    apply
    assumption
    exact
    split
    left
    right
    elim
    destruct

  Tacticals to practice:
    T1 ; T2
    [T1 | T2]

  Tactics to remember, but not to be used in your solutions:
    assert
    cut
    auto
 *)

Section Propositional.

Variables A B C D : Prop.

(*
 * Part 0 - introduction
 *)

Lemma id : A -> A.
Proof.
(* Use 'intro' tactic to apply the implication-introduction rule.
   Note that a new hypothesis of A is produced and the goal changes to A.
 *)
intro H.
(* Use 'assumption' tactic to use the hypothesis of A. *)
assumption.
(* You may use 'exact H' to indicate that H is the name of the hypothesis that matches the current goal. *)
Qed.

Lemma id_PP : (A -> A) -> A -> A.
Proof.
(* You may use 'intros' tactic to apply the implication-introduction rules serveral times. *)
intros H H'.
assumption.
Qed.

Lemma imp_dist : (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
(* Use 'intros' tactic to produce three hypotheses H H' H''.
   Note also that if you don't provide the names of hypotheses,
   Coq automatically chooses an appropriate name for each hypothesis. *)
intros H H' H''.
(* Note that the last proposition in H matches the current goal.
   Therefore, by applying the implication elimination rules twice to hypothesis H,
   the whole problem reduces to proving A and B. *)
apply H.
(* Now we have two separate goals A and B.
   For the first goal, we use hypothesis H''. *)
exact H''.
(* For the second goal, we use 'apply' tactic to apply the implication elimination rule to hypothesis H'. *)
apply H'.
exact H''.
Qed.

Lemma conj_com : A /\ B -> B /\ A.
Proof.
(* First introduce a hypothesis H : A /\ B. *)
intro H.
(* Our strategy here is to prove B and A separately.
   So we use 'split' tactic which corresponds to the conjunction-introduction rule. *)
split.
(* Now we apply the conjunction-elimination rule to H.
   Observe that tactic 'elim' changes the goal to A -> B -> B.
   This may seem unusual, but proving A -> B -> B is equivalent to proving B under two
   hypotheses A and B (after applying the implication-introduction rule twice).
   This is the way that Coq handles conjunction. *)
elim H.
intros Ha Hb.
(* Now you can see that both A and B have been introduced as hypotheses. *)
assumption.
(* We can use the ';' tactical to apply a sequence of tactics. *)
elim H; intros Ha Hb; assumption.
Qed.

Lemma conj_com' : A /\ B -> B /\ A.
Proof.
(* Here is another proof of the same judgment.
   Instead of applying 'intro' and then 'elim' tactics, we use a pattern of hypothesis.
   The pattern [Ha Hb] binds Ha to the first hypothesis (which is A in this case)
   Hb to the second hypothesis. *)
intros [Ha Hb].
(* intros [Ha Hb] can be thought of as applying first 'intro H' and then 'destruct H as [Ha Hb]':
        intro H.
        destruct H as [Ha Hb].
 *)
(* The ';' tactical applies the sequence of tactics to each generated subgoal.
    In the following example, 'split' produces two subgoals (A and B), and
    Coq applies to 'assumption' tactic to each subgoal, thereby completing the proof. *)
split; assumption.
Qed.

Lemma disj_com : A \/ B -> B \/ A.
Proof.
(* First introduce a hypothesis H : A \/ B. *)
intro H.
(* We have to apply the disjunction-elimination rule to H.
   The corresponding tactic is 'elim'.
   Since the disjunction-elimination rule consider two possibilities,
   we now have prove the goal B \/ A under two different assumptions. *)
elim H.
(* For the first subgoal, we have to prove the right component of the disjunction,
   that is, apply the disjunction-introduction-right rule.
   The corresponding tactic is 'right'. *)
right.
assumption.
(* Similarly we can use the tactic 'left'. *)
left; assumption.
Qed.

Lemma disj_com' : A \/ B -> B \/ A.
Proof.
(* Here is another proof of the same judgment using a pattern of hypotheses.
   We use [ Ha | Hb ] to bind Ha to the first hypothesis A and Hb to the second hypothesis. *)
intros [ Ha | Hb ].
right; assumption.
left; assumption.
Qed.

Lemma disj_com'' : A \/ B -> B \/ A.
Proof.
(* If you generate two goals such that a tactic T1 solves the first goal and another tactic T2 solves
   the second goal, you can use the tactical [T1 | T2] to solve both subgoals.
   Hence the above judgment can be solved as follows: *)
intros [Ha | Hb]; [ right | left ]; assumption.
Qed.

(* This example illustrates the composition of patterns of hypotheses. *)
Lemma and_assoc : A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
intros [H [H1 H2]].
split; [split; assumption | assumption].
Qed.

(* If we have a hypothesis H of A -> B and another hypothesis p of A,
    we may write (H p) as a hypothesis of B. *)
Lemma and_imp_dist : (A -> B) /\ (C -> D) -> A /\ C -> B /\ D.
Proof.
intros [H H'] [p q].
split; [exact (H p) | exact (H' q)].
Qed.

(* The following example illustrates that the tactic corresponding to the negation-elimination rule
    is 'elim'. *)
Lemma or_and_not : (A \/ B) /\ ~A -> B.
Proof.
intros [[ Ha | Hb] H'].
elim H'.
assumption.
assumption.
Qed.

(*
 * Part 1 - Basic connectives in propositional logic
 *)

Lemma impl_distr : (A -> B) -> (A -> C) -> A -> B -> C.
Proof.
  intros f g a b.
  exact (g a).
Qed.


Lemma impl_comp : (A -> B) -> (B -> C) -> A -> C.
Proof.
  intros f g a.
  exact (g (f a)).
Qed.


Lemma impl_perm : (A -> B -> C) -> B -> A -> C.
Proof.
  intros f b a.
  exact (f a b).
Qed.

Lemma impl_conj : A -> B -> A /\ B.
Proof.
  intros a b.
  split; assumption.
Qed.


Lemma conj_elim_l : A /\ B -> A.
Proof.
  intros [a b].
  assumption.
Qed.

Lemma disj_intro_l : A -> A \/ B.
Proof.
  intro a.
  left; assumption.
Qed.


Lemma disj_elim : A \/ B -> (A -> C) -> (B -> C) -> C.
Proof.
  intros [a|b] f g; [apply f | apply g]; assumption.
Qed.

Lemma diamond : (A -> B) -> (A -> C) -> (B -> C -> D) -> A -> D.
Proof.
  intros f g h a.
  exact (h (f a) (g a)).
Qed.

Lemma weak_peirce : ((((A -> B) -> A) -> A) -> B) -> B.
Proof.
  intros f; apply f.
  intros g; apply g.
  intros a.
  apply f.
  intros _; exact a.
Qed.

Lemma imp_conj_disj : (A -> B /\ C) -> (A -> B) /\ (A -> C).
Proof.
  intros f.
  split; intros a; apply f; assumption.
Qed.

Lemma disj_impl_dist : (A \/ B -> C) -> (A -> C) /\ (B -> C).
Proof.
  intros f.
  split; intros; apply f; [left | right]; assumption.
Qed.

Lemma disj_impl_dist_inv : (A -> C) /\ (B -> C) -> A \/ B -> C.
Proof.
  intros [f g] [a | b]; [apply f | apply g]; assumption.
Qed.

Lemma curry : (A /\ B -> C) -> A -> B -> C.
Proof.
  intros f a b.
  apply f; split; assumption.
Qed.

Lemma uncurry : (A -> B -> C) -> A /\ B -> C.
Proof.
  intros f [a b].
  exact (f a b).
Qed.

(*
 * Part 2 - Negation
 *)

Lemma not_contrad :  ~(A /\ ~A).
Proof.
  intros [a a'].
  apply a'.
  exact a.
Qed.

Lemma not_not_exm : ~~(A \/ ~A).
Proof.
  intros H.
  apply H.
  right.
  intros a.
  apply H.
  left; exact a.
Qed.

Lemma de_morgan_1 : ~(A \/ B) -> ~A /\ ~B.
Proof.
  intros H.
  split; intros x; apply H; [left | right]; assumption.
Qed.

Lemma de_morgan_2 : ~A /\ ~B -> ~(A \/ B).
Proof.
  intros [a' b'] H.
  elim H; assumption.
Qed.

Lemma de_morgan_3 : ~A \/ ~B -> ~(A /\ B).
Proof.
  intros [a' | b'] [a b].
  - exact (a' a).
  - exact (b' b).
Qed.

Lemma contrapositive : (A -> B) -> (~B -> ~A).
Proof.
  intros f b' a.
  apply b'.
  exact (f a).
Qed.

Lemma neg_double : A -> ~~A.
Proof.
  intros a a'.
  apply a'.
  assumption.
Qed.

Lemma tneg : ~~~A -> ~A.
Proof.
  intros x.
  intros a.
  apply x.
  intros y.
  apply y.
  exact a.
Qed.

Lemma weak_dneg : ~~(~~A -> A).
Proof.
  intros x.
  apply x.
  intros a_dneg.
  elim a_dneg.
  intro a.
  apply x.
  intros _.
  exact a.
Qed. (* but I don't know why this works *)

(*
 * Part 3 - Classical logic
 *)

Lemma em_peirce : A \/ ~A -> ((A -> B) -> A) -> A.
Proof.
  intros [a | a'] f.
  - exact a.
  - apply f.
    intros a.
    elim a'.
    exact a.
Qed.

Lemma peirce_dne : (((A -> False) -> A) -> A) -> ~~A -> A.
Proof.
  intros f a_dne.
  apply f.
  intros a'.
  elim a_dne.
  intros a.
  exact (a' a).
Qed. (* but I don't know why this works *)

Lemma dne_em : (~~(B \/ ~B)-> (B \/ ~B)) -> B \/ ~B.
Proof.
  intros x.
  apply x.
  intros y.
  apply y.
  right.
  intros b.
  apply y.
  left.
  exact b.
Qed. (* but I don't know why this works *)




End Propositional.
