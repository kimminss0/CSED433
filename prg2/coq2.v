(*
  CSE-433 Logic in Computer Science, POSTECH (gla@postech.ac.kr)
    --- Inductive Set

  The handin directory is programming2.postech.ac.kr:/home/class/cs433/<HemosID>/.
 *)

(*
  Commands to practice:
    Inductive
    Definition
    Fixpoint
 *)

Section InductiveSet.

(*
 * Part 0 - Introduction
 *)

(* We use 'Inductive' command to define inductive sets.
   The following example defines an inductive set 'nat' which has two constructors O and S.
   It corresponds to the inductive definition in our notation:

      nat :: = O | S nat

   Note that the construct 'S' takes another 'nat' as an argument, so it is given a function type 'nat -> nat'.
 *)

Inductive nat : Set :=
| O : nat                 (* O is an element in the set 'nat'. *)
| S : nat -> nat.         (* S t is an element in the set 'nat', given that t is another element in the set 'nat'. *)

(* We use 'Definition' command to define functions.
   The following command defines a function 'dec' whose argument m has type nat and whose return type is nat.
   It decrements the argument by 1 where 'dec O' is defined as 'O'. *)
Definition dec (m:nat) : nat :=
match m with
| O => O
| S m => m end.

(* We may also directly use a nameless function (as in ML-style functional programming), as illustrated below *)
Definition dec' :=
  fun (m:nat) =>
    match m with
    | O => O
    | S m => m end.

(* We use 'Fixpoint' command to define a recursive function.
   The following command defines a recursive function (doubling the argument) on the inductive set 'nat' using
   pattern matching.
 *)
Fixpoint double (m:nat) : nat :=
match m with
| O => O
| S m' => S (S (double m'))
end.

(* A recursive function may have multiple arguments, but the user should specify which argument the function
   recurses on. This is necessary to ensure that every call to a recursive function eventually terminates.
   (Coq does not permit non-terminating functions.)
   In the following example, {struct m} specifies that 'plus' should analyze the first argument 'm'.
   Note that the recursive call to 'plus' is indeed made with a smaller argument m'.
 *)
Fixpoint plus (m n:nat) {struct m} : nat :=
match m with
| O => n
| S m' => S (plus m' n)
end.

(* We use Eval compute in ... to see the result of computing ....
 *)
Eval compute in double (S (S O)).
Eval compute in plus (S O) (S (S O)).

(* A recursive call should be made with strictly smaller arugments which should be simple expressions like
   variables and must not be complex expressions like function applications.
   In the following example, Coq cannot decide if S m' is really smaller than m, and rejects the definition. *)
(*
Fixpoint fib1 (m:nat) : nat :=
match m with
| O => O
| S O => S O
| S (S m') => plus (fib1 (S m')) (fib1 m')
end.
 *)

(* To correct this definition, we can remember S m' as another variable during pattern matching,
   as illustrated below. *)
Fixpoint fib1 (m:nat) : nat :=
match m with
| O => O
| S O => S O
| S ((S m') as m'') => plus (fib1 m'') (fib1 m')
end.

(* Alternatively we can use nested pattern matching. As a rule of thumb, try to use only variables as
   arguments to a recursive function being defined. *)
Fixpoint fib1' (m:nat) : nat :=
match m with
| O => O
| S m' =>
  match m' with
  | O => S O
  | S m'' => plus (fib1' m') (fib1' m'')
  end
end.

Eval compute in fib1 (S (S (S (S (S (S (S O))))))).
Eval compute in fib1' (S (S (S (S (S (S (S O))))))).

(* An inductive definition of a set may use another inductive definition.
   Here is the translation of inductive sets E and T:

    E ::= LP | RP
    T ::= eps | cons E T
 *)
Inductive E : Set :=
| LP : E        (* left parenthesis *)
| RP : E.       (* right parenthesis *)

Inductive T : Set :=
| eps : T                 (* empty string, epsilon *)
| cons : E -> T -> T.     (* concatenation of E and T *)

(* The function 'concat' concatenates two strings of type T. It recurses on the first string s1.
 *)
Fixpoint concat (s1 s2:T) {struct s1} : T :=
match s1 with
| eps => s2
| cons e s2' => cons e (concat s2' s2) end.

Eval compute in concat (cons RP (cons LP (cons RP (cons LP eps)))) (cons RP (cons LP eps)).

(*
 * Part 1
   You may use functions defined above such as 'dec' and 'plus'.
 *)

(* Write a recursive function 'mult' that multiplies two natural numbers. *)

Fixpoint mult (m n:nat) {struct m} : nat :=
match m with
| O => O
| S m' => plus n (mult m' n)
end.

(* Write a recursive function 'sum_n' such that 'sum_n n' adds natural number zero (O) up to n (inclusive). *)

Fixpoint sum_n (n:nat) {struct n}: nat :=
match n with
| O => O
| S n' => plus n (sum_n n')
end.

(* Write a recursive function is_equal taking two natural numbers.
   It returns TT if the two natural numbers are equal, and FF otherwise.
 *)

Inductive bool : Set :=
| TT : bool
| FF : bool.

Fixpoint is_equal (m n:nat) {struct m} : bool :=
match (m, n) with
| (O, O) => TT
| (S m', S n') => is_equal m' n'
| _ => FF
end.

(* Write a tail-recursive function fib2 for Fibonacci function using the following definition:

    fun fib2 m n 0 = m
      | fib2 m n p = fib2 n (m + n) (p - 1)       // p >= 1
 *)

Fixpoint fib2 (m n p:nat) {struct p} : nat :=
match p with
| O => m
| S p' => fib2 n (plus m n) p'
end.

Eval compute in mult (S (S O)) (S (S (S (S (S (S (S O))))))).
Eval compute in sum_n (S (S (S (S (S (S (S O))))))).
Eval compute in fib2 O (S O) (S (S (S (S (S (S (S O))))))).

(* Write a tail-recursive function reverse' for reversing a given string of parentheses. *)

Fixpoint reverse' (s sa:T) {struct s} : T :=
match s with
| eps => sa
| cons e s' => reverse' s' (cons e sa)
end.

Definition reverse (s:T) := reverse' s eps.

Eval compute in          concat (cons RP (cons LP (cons RP (cons LP eps)))) (cons LP (cons LP eps)).
Eval compute in reverse (concat (cons RP (cons LP (cons RP (cons LP eps)))) (cons LP (cons LP eps))).

(*
 * Part 2
 *)

(* Inductive set 'tm' for terms in the simple language. *)
Inductive tm : Set :=
| tm_true : tm
| tm_false : tm
| tm_if : tm -> tm -> tm -> tm
| tm_zero : tm
| tm_succ : tm -> tm
| tm_pred : tm -> tm
| tm_iszero : tm -> tm.

(* Inductive set 'nat_option' for optional natural numbers. *)
Inductive nat_option : Set :=
| some_nat : nat -> nat_option
| no_nat : nat_option.

(* Define a recursive function tm_to_nat such that
   tm_to_nat t returns some_nat t if t is already a natural number, and returns no_nat otherwise.
   Note that it does not matter whether t eventually reduces to a natural number;
   tm_to_nat inspects only its current form.

Examples:

  tm_to_nat tm_true.  ===> no_nat
  tm_to_nat tm_zero.  ===> some_nat O
  tm_to_nat (tm_succ tm_zero).  ===> some_nat (S O).
  tm_to_nat (tm_succ (tm_if tm_true tm_zero (tm_succ tm_zero))).  ===> no_nat
  tm_to_nat (tm_pred tm_zero).  ===> no_nat
  tm_to_nat (tm_pred tm_true).  ===> no_nat
 *)

Fixpoint tm_to_nat (t : tm) {struct t} : nat_option :=
match t with
| tm_zero => some_nat O
| tm_succ t' =>
  match tm_to_nat t' with
  | some_nat n => some_nat (S n)
  | no_nat => no_nat
  end
| _ => no_nat
end.

(* Define a recursive function interp that returns the result of evaluating its argument (reducing it until no
   further reduction rule is applicable) under the small-step semantics described in the separate handout.
   You want to use tm_to_nat when analyzing tm_pred t' or tm_iszero t'.
 *)

Fixpoint interp (t:tm) {struct t} : tm :=
match t with
| tm_true | tm_false | tm_zero => t
| tm_if tcond t1 t2 =>
  match interp tcond with
  | tm_true => interp t1
  | tm_false => interp t2
  | t' => tm_if t' t1 t2
  end
| tm_succ t' => tm_succ (interp t')
| tm_pred t' =>
  match interp t' with
  | tm_zero => tm_zero
  | tm_succ t'' as ts =>
    match tm_to_nat t'' with
    | some_nat _ => t''
    | no_nat => tm_pred ts
    end
  | t'' => tm_pred t''
  end
| tm_iszero t' =>
  match interp t' with
  | tm_zero => tm_true
  | tm_succ t'' as ts =>
    match tm_to_nat t'' with
    | some_nat _ => tm_false
    | no_nat => tm_iszero ts
    end
  | t'' => tm_iszero t''
  end
end.

(* Test suite *)
Eval compute in interp (tm_false).  (* tm_false *)
Eval compute in interp (tm_true).   (* tm_true *)
Eval compute in interp (tm_zero).   (* tm_zero *)

Eval compute in interp (tm_if tm_true tm_zero (tm_succ tm_zero)).   (* tm_zero *)
Eval compute in interp (tm_succ (tm_if tm_true tm_zero (tm_succ tm_zero))).   (* tm_succ tm_zero *)

(* tm_if tm_zero tm_zero (tm_succ tm_zero) *)
Eval compute in interp (tm_if tm_zero tm_zero (tm_succ tm_zero)).

(* tm_if tm_zero tm_zero (tm_succ tm_zero) *)
Eval compute in interp (tm_if (tm_pred (tm_succ tm_zero)) tm_zero (tm_succ tm_zero)).

Eval compute in interp (tm_succ (tm_if tm_true tm_true tm_false)).   (* tm_succ tm_true *)

Eval compute in interp (tm_pred (tm_succ tm_zero)).   (* tm_zero *)
Eval compute in interp (tm_pred (tm_succ tm_true)).   (* tm_pred (tm_succ tm_true) *)
Eval compute in interp (tm_pred (tm_succ (tm_succ tm_zero))).   (* tm_succ tm_zero *)
Eval compute in interp (tm_pred (tm_succ (tm_pred (tm_succ tm_zero)))).   (* tm_zero *)

Eval compute in interp (tm_iszero tm_zero).   (* tm_true *)
Eval compute in interp (tm_iszero (tm_succ tm_zero)).   (* tm_false *)
Eval compute in interp (tm_iszero (tm_pred (tm_succ (tm_succ tm_zero)))).   (* tm_false *)
Eval compute in interp (tm_iszero (tm_pred (tm_succ tm_zero))).   (* tm_true *)

End InductiveSet.
