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

(* If we have a hypothsis H of A -> B and another hypothesis p of A,
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
Admitted.

Lemma impl_comp : (A -> B) -> (B -> C) -> A -> C.
Admitted.

Lemma impl_perm : (A -> B -> C) -> B -> A -> C. 
Admitted.

Lemma impl_conj : A -> B -> A /\ B. 
Admitted.

Lemma conj_elim_l : A /\ B -> A. 
Admitted.

Lemma disj_intro_l : A -> A \/ B.
Admitted.

Lemma disj_elim : A \/ B -> (A -> C) -> (B -> C) -> C. 
Admitted.

Lemma diamond : (A -> B) -> (A -> C) -> (B -> C -> D) -> A -> D.
Admitted.

Lemma weak_peirce : ((((A -> B) -> A) -> A) -> B) -> B.
Admitted.

Lemma imp_conj_disj : (A -> B /\ C) -> (A -> B) /\ (A -> C).
Admitted.

Lemma disj_impl_dist : (A \/ B -> C) -> (A -> C) /\ (B -> C).
Admitted.
 
Lemma disj_impl_dist_inv : (A -> C) /\ (B -> C) -> A \/ B -> C.
Admitted.

Lemma curry : (A /\ B -> C) -> A -> B -> C.
Admitted.

Lemma uncurry : (A -> B -> C) -> A /\ B -> C.
Admitted.

(* 
 * Part 2 - Negation 
 *)

Lemma not_contrad :  ~(A /\ ~A).
Admitted.

Lemma not_not_exm : ~~(A \/ ~A).
Admitted.

Lemma de_morgan_1 : ~(A \/ B) -> ~A /\ ~B.
Admitted.

Lemma de_morgan_2 : ~A /\ ~B -> ~(A \/ B).
Admitted.

Lemma de_morgan_3 : ~A \/ ~B -> ~(A /\ B).
Admitted.

Lemma contrapositive : (A -> B) -> (~B -> ~A). 
Admitted.

Lemma neg_double : A -> ~~A.
Admitted.

Lemma tneg : ~~~A -> ~A.
Admitted.

Lemma weak_dneg : ~~(~~A -> A).
Admitted.

(* 
 * Part 3 - Classical logic 
 *)

Lemma em_peirce : A \/ ~A -> ((A -> B) -> A) -> A.
Admitted.

Lemma peirce_dne : (((A -> False) -> A) -> A) -> ~~A -> A.
Admitted.

Lemma dne_em : (~~(B \/ ~B)-> (B \/ ~B)) -> B \/ ~B.
Admitted.

End Propositional.


