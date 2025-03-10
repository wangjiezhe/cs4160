(** * Types: Type Systems *)

(** Our next major topic is _type systems_ -- static program
    analyses that classify expressions according to the "shapes" of
    their results.  We'll begin with a typed version of the simplest
    imaginable language, to introduce the basic ideas of types and
    typing rules and the fundamental theorems about type systems:
    _type preservation_ and _progress_.  In chapter [Stlc] we'll move
    on to the _simply typed lambda-calculus_, which lives at the core
    of every modern functional programming language (including
    Coq!). *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Arith.Arith.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
Set Default Goal Selector "!".

Hint Constructors multi : core.

(* ################################################################# *)
(** * Typed Arithmetic Expressions *)

(** To motivate the discussion of type systems, let's begin as
    usual with a tiny toy language.  We want it to have the potential
    for programs to go wrong because of runtime type errors, so we
    need something a tiny bit more complex than the language of
    constants and addition that we used in chapter [Smallstep]: a
    single kind of data (e.g., numbers) is too simple, but just two
    kinds (numbers and booleans) gives us enough material to tell an
    interesting story.

    The language definition is completely routine. *)

(* ================================================================= *)
(** ** Syntax *)

(** Here is the syntax, informally:

    t ::= true
        | false
        | if t then t else t
        | 0
        | succ t
        | pred t
        | iszero t
*)
(** And here it is formally: *)
Module TM.

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | ite : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm.

Declare Custom Entry tm.
Declare Scope tm_scope.
Notation "'true'"  := true (at level 1): tm_scope.
Notation "'true'" := (tru) (in custom tm at level 0): tm_scope.
Notation "'false'"  := false (at level 1): tm_scope.
Notation "'false'" := (fls) (in custom tm at level 0): tm_scope.
Notation "<{ e }>" := e (e custom tm at level 99): tm_scope.
Notation "( x )" := x (in custom tm, x at level 99): tm_scope.
Notation "x" := x (in custom tm at level 0, x constr at level 0): tm_scope.
Notation "'0'" := (zro) (in custom tm at level 0): tm_scope.
Notation "'0'"  := 0 (at level 1): tm_scope.
Notation "'succ' x" := (scc x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'pred' x" := (prd x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'iszero' x" := (iszro x) (in custom tm at level 80, x custom tm at level 70): tm_scope.
Notation "'if' c 'then' t 'else' e" := (ite c t e)
                 (in custom tm at level 90, c custom tm at level 80,
                  t custom tm at level 80, e custom tm at level 80): tm_scope.
Local Open Scope tm_scope.

(** _Values_ are [<{true}>], [<{false}>], and numeric values... *)
Inductive bvalue : tm -> Prop :=
  | bv_True : bvalue <{ true }>
  | bv_false : bvalue <{ false }>.

Inductive nvalue : tm -> Prop :=
  | nv_0 : nvalue <{ 0 }>
  | nv_succ : forall t, nvalue t -> nvalue <{ succ t }>.

Definition value (t : tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue : core.
Hint Unfold value : core.

(* ================================================================= *)
(** ** Operational Semantics *)

(** Here is the single-step relation, first informally...

                   -------------------------------                   (ST_IfTrue)
                   if true then t1 else t2 --> t1

                   -------------------------------                  (ST_IfFalse)
                   if false then t1 else t2 --> t2

                               t1 --> t1'
            ------------------------------------------------             (ST_If)
            if t1 then t2 else t3 --> if t1' then t2 else t3

                             t1 --> t1'
                         --------------------                          (ST_Succ)
                         succ t1 --> succ t1'

                           ------------                               (ST_Pred0)
                           pred 0 --> 0

                         numeric value v
                        -------------------                        (ST_PredSucc)
                        pred (succ v) --> v

                              t1 --> t1'
                         --------------------                          (ST_Pred)
                         pred t1 --> pred t1'

                          -----------------                         (ST_IsZero0)
                          iszero 0 --> true

                         numeric value v
                      -------------------------                  (ST_IszeroSucc)
                      iszero (succ v) --> false

                            t1 --> t1'
                       ------------------------                      (ST_Iszero)
                       iszero t1 --> iszero t1'
*)

(** ... and then formally: *)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      <{ if true then t1 else t2 }> --> t1
  | ST_IfFalse : forall t1 t2,
      <{ if false then t1 else t2 }> --> t2
  | ST_If : forall c c' t2 t3,
      c --> c' ->
      <{ if c then t2 else t3 }> --> <{ if c' then t2 else t3 }>
  | ST_Succ : forall t1 t1',
      t1 --> t1' ->
      <{ succ t1 }> --> <{ succ t1' }>
  | ST_Pred0 :
      <{ pred 0 }> --> <{ 0 }>
  | ST_PredSucc : forall v,
      nvalue v ->
      <{ pred (succ v) }> --> v
  | ST_Pred : forall t1 t1',
      t1 --> t1' ->
      <{ pred t1 }> --> <{ pred t1' }>
  | ST_Iszero0 :
      <{ iszero 0 }> --> <{ true }>
  | ST_IszeroSucc : forall v,
       nvalue v ->
      <{ iszero (succ v) }> --> <{ false }>
  | ST_Iszero : forall t1 t1',
      t1 --> t1' ->
      <{ iszero t1 }> --> <{ iszero t1' }>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

(** Notice that the [step] relation doesn't care about whether the
    expression being stepped makes global sense -- it just checks that
    the operation in the _next_ reduction step is being applied to the
    right kinds of operands.  For example, the term <{ succ true }> cannot
    take a step, but the almost as obviously nonsensical term

       <{ succ (if true then true else true) }>

    can take a step (once, before becoming stuck). *)

(* ================================================================= *)
(** ** Normal Forms and Values *)

(** The first interesting thing to notice about this [step] relation
    is that the strong progress theorem from the [Smallstep]
    chapter fails here.  That is, there are terms that are normal
    forms (they can't take a step) but not values (they are not
    included in our definition of possible "results of reduction").
    Such terms are said to be _stuck_. *)

Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck : core.

(** **** Exercise: 2 stars, standard (some_term_is_stuck) *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists <{succ true}>. split.
  - unfold step_normal_form, normal_form.
    intro H. solve_by_inverts 3.
  - intro H. solve_by_inverts 3.
Qed.
(** [] *)

(** However, although values and normal forms are _not_ the same in
    this language, the set of values is a subset of the set of normal
    forms.  This is important because it shows we did not accidentally
    define things so that some value could still take a step. *)

(** **** Exercise: 3 stars, standard (value_is_nf) *)
Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  unfold step_normal_form, normal_form.
  induction t; intros H []; try solve_by_inverts 2.
  destruct H.
  - invert H.
  - invert H. invert H0. (* intuition eauto. *)
    apply IHt.
    + right. apply H2.
    + exists t1'. apply H1.
Qed.

(** (Hint: You will reach a point in this proof where you need to
    use an induction to reason about a term that is known to be a
    numeric value.  This induction can be performed either over the
    term itself or over the evidence that it is a numeric value.  The
    proof goes through in either case, but you will find that one way
    is quite a bit shorter than the other.  For the sake of the
    exercise, try to complete the proof both ways.)

    [] *)

Lemma value_is_nf' : forall t,
  value t -> step_normal_form t.
Proof.
  unfold step_normal_form, normal_form.
  intros t H.
  destruct H.
  - intros C. destruct C. invert H0; solve_by_inverts 2.
  - induction H; intros []; try solve_by_inverts 2.
    invert H0.
    apply IHnvalue.
    exists t1'. apply H2.
Qed.

(** **** Exercise: 3 stars, standard, optional (step_deterministic)

    Use [value_is_nf] to show that the [step] relation is also
    deterministic. *)

Ltac solve_by_inverts' n :=
  match goal with
  | H : ?T |- _ =>
    match type of T with Prop =>
      solve [
        inversion H;
        match n with S (S (?n')) => subst; try f_equal; eauto; solve_by_inverts' (S n') end ]
    end
  end.

Ltac solve_by_inverts'' n :=
  match goal with
  | H : nvalue ?x, H': ?x --> _ |- _ =>
    pose proof (value_is_nf _ (or_intror H)); exfalso; eauto
  | H : ?T |- _ =>
    match type of T with Prop =>
      solve [
        inversion H;
        match n with S (S (?n')) => subst; try f_equal; eauto; solve_by_inverts'' (S n') end ]
    end
  end.

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; simpl; intros; try solve_by_inverts'' 3.
  (* - invert Hy2... invert H3.
  - invert Hy2... invert H3.
  - invert Hy2...
    + invert Hy1.
    + invert Hy1.
    + f_equal...
  - invert Hy2. f_equal...
  - invert Hy2... invert H0.
  - invert Hy2... invert H1.
    pose proof (value_is_nf _ (or_intror H)). exfalso...
  - invert Hy2.
    + invert Hy1.
    + invert Hy1.
      pose proof (value_is_nf _ (or_intror H0)). exfalso...
    + f_equal...
  - invert Hy2... invert H0.
  - invert Hy2... invert H1.
    pose proof (value_is_nf _ (or_intror H)). exfalso...
  - invert Hy2.
    + invert Hy1.
    + invert Hy1.
      pose proof (value_is_nf _ (or_intror H0)). exfalso...
    + f_equal... *)
Qed.
(** [] *)

(* ================================================================= *)
(** ** Typing *)

(** The next critical observation is that, although this
    language has stuck terms, they are always nonsensical, mixing
    booleans and numbers in a way that we don't even _want_ to have a
    meaning.  We can easily exclude such ill-typed terms by defining a
    _typing relation_ that relates terms to the types (either numeric
    or boolean) of their final results.  *)

Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.

(** In informal notation, the typing relation is often written
    [|-- t \in T] and pronounced "[t] has type [T]."  The [|--] symbol
    is called a "turnstile."  Below, we're going to see richer typing
    relations where one or more additional "context" arguments are
    written to the left of the turnstile.  For the moment, the context
    is always empty.


                           -----------------                   (T_True)
                           |-- true \in Bool

                          ------------------                   (T_False)
                          |-- false \in Bool

           |-- t1 \in Bool    |-- t2 \in T    |-- t3 \in T
           -----------------------------------------------     (T_If)
                   |-- if t1 then t2 else t3 \in T

                             --------------                    (T_0)
                             |-- 0 \in Nat

                            |-- t1 \in Nat
                          -------------------                  (T_Succ)
                          |-- succ t1 \in Nat

                            |-- t1 \in Nat
                          -------------------                  (T_Pred)
                          |-- pred t1 \in Nat

                            |-- t1 \in Nat
                          ----------------------               (T_Iszero)
                          |-- iszero t1 \in Bool
*)

Reserved Notation "'|--' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_True :
       |-- <{ true }> \in Bool
  | T_False :
       |-- <{ false }> \in Bool
  | T_If : forall t1 t2 t3 T,
       |-- t1 \in Bool ->
       |-- t2 \in T ->
       |-- t3 \in T ->
       |-- <{ if t1 then t2 else t3 }> \in T
  | T_0 :
       |-- <{ 0 }> \in Nat
  | T_Succ : forall t1,
       |-- t1 \in Nat ->
       |-- <{ succ t1 }> \in Nat
  | T_Pred : forall t1,
       |-- t1 \in Nat ->
       |-- <{ pred t1 }> \in Nat
  | T_Iszero : forall t1,
       |-- t1 \in Nat ->
       |-- <{ iszero t1 }> \in Bool

where "'|--' t '\in' T" := (has_type t T).

Hint Constructors has_type : core.

Example has_type_1 :
  |-- <{ if false then 0 else (succ 0) }> \in Nat.
Proof.
  apply T_If.
  - apply T_False.
  - apply T_0.
  - apply T_Succ. apply T_0.
Qed.

(** (Since we've included all the constructors of the typing relation
    in the hint database, the [auto] tactic can actually find this
    proof automatically.) *)

(** It's important to realize that the typing relation is a
    _conservative_ (or _static_) approximation: it does not consider
    what happens when the term is reduced -- in particular, it does
    not calculate the type of its normal form. *)

Example has_type_not :
  ~ ( |-- <{ if false then 0 else true}> \in Bool ).
Proof.
  intros Contra. solve_by_inverts 2.  Qed.

(** **** Exercise: 1 star, standard, optional (succ_hastype_nat__hastype_nat) *)
Example succ_hastype_nat__hastype_nat : forall t,
  |-- <{succ t}> \in Nat ->
  |-- t \in Nat.
Proof.
  induction t; intros H; try solve_by_inverts' 2.
Qed.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Canonical forms *)

(** The following two lemmas capture the fundamental property that the
    definitions of boolean and numeric values agree with the typing
    relation. *)

Lemma bool_canonical : forall t,
  |-- t \in Bool -> value t -> bvalue t.
Proof.
  intros t HT [Hb | Hn].
  - assumption.
  - destruct Hn as [ | Hs].
    + inversion HT.
    + inversion HT.
Qed.

Lemma nat_canonical : forall t,
  |-- t \in Nat -> value t -> nvalue t.
Proof.
  intros t HT [Hb | Hn].
  - inversion Hb; subst; inversion HT.
  - assumption.
Qed.

(* ================================================================= *)
(** ** Progress *)

(** The typing relation enjoys two critical properties.  The first is
    that well-typed normal forms are not stuck -- or conversely, if a
    term is well typed, then either it is a value or it can take at
    least one step.  We call this _progress_. *)

(** **** Exercise: 3 stars, standard (finish_progress) *)
Theorem progress : forall t T,
  |-- t \in T ->
  value t \/ exists t', t --> t'.

(** Complete the formal proof of the [progress] property.  (Make sure
    you understand the parts we've given of the informal proof in the
    following exercise before starting -- this will save you a lot of
    time.) *)
Proof.
  intros t T HT.
  induction HT; auto.
  (* The cases that were obviously values, like T_True and
     T_False, are eliminated immediately by auto *)
  - (* T_If *)
    right. destruct IHHT1.
    + (* t1 is a value *)
    apply (bool_canonical t1 HT1) in H.
    destruct H.
      * exists t2. auto.
      * exists t3. auto.
    + (* t1 can take a step *)
      destruct H as [t1' H1].
      exists (<{ if t1' then t2 else t3 }>). auto.
  - (* T_Succ *)
    destruct IHHT.
    + left. apply (nat_canonical _ HT) in H. auto.
    + right. destruct H as [t1'].
      exists <{ succ t1' }>. auto.
  - (* T_Pred *)
    destruct IHHT.
    + right.
      destruct t1; try solve_by_inverts' 3.
      (* destruct t1; try solve_by_inverts 2.
      * exists <{ 0 }>. auto.
      * apply (nat_canonical _ HT) in H. invert H.
        exists <{ t1 }>. auto. *)
    + destruct H as [t1'].
      right. exists <{ pred t1' }>. auto.
  - (* T_Iszero *)
    destruct IHHT.
    + right.
      destruct t1; try solve_by_inverts' 3.
      (* destruct t1; try solve_by_inverts 2.
      * exists <{ true }>. auto.
      * apply (nat_canonical _ HT) in H. invert H.
        exists <{ false }>. auto. *)
    + right. destruct H as [t1'].
      exists <{ iszero t1' }>. auto.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (finish_progress_informal)

    Complete the corresponding informal proof: *)

(** _Theorem_: If [|-- t \in T], then either [t] is a value or else
    [t --> t'] for some [t']. *)

(** _Proof_: By induction on a derivation of [|-- t \in T].

    - If the last rule in the derivation is [T_If], then [t = if t1
      then t2 else t3], with [|-- t1 \in Bool], [|-- t2 \in T] and [|-- t3
      \in T].  By the IH, either [t1] is a value or else [t1] can step
      to some [t1'].

      - If [t1] is a value, then by the canonical forms lemmas
        and the fact that [|-- t1 \in Bool] we have that [t1]
        is a [bvalue] -- i.e., it is either [true] or [false].
        If [t1 = true], then [t] steps to [t2] by [ST_IfTrue],
        while if [t1 = false], then [t] steps to [t3] by
        [ST_IfFalse].  Either way, [t] can step, which is what
        we wanted to show.

      - If [t1] itself can take a step, then, by [ST_If], so can
        [t].

    - (* FILL IN HERE *)
 *)
(* Do not modify the following line: *)
Definition manual_grade_for_finish_progress_informal : option (nat*string) := None.
(** [] *)

(** This theorem is more interesting than the strong progress theorem
    that we saw in the [Smallstep] chapter, where _all_ normal forms
    were values.  Here a term can be stuck, but only if it is ill
    typed. *)

(* ================================================================= *)
(** ** Type Preservation *)

(** The second critical property of typing is that, when a well-typed
    term takes a step, the result is a well-typed term (of the same type). *)

(** **** Exercise: 2 stars, standard (finish_preservation) *)
Theorem preservation : forall t t' T,
  |-- t \in T ->
  t --> t' ->
  |-- t' \in T.

(** Complete the formal proof of the [preservation] property.  (Again,
    make sure you understand the informal proof fragment in the
    following exercise first.) *)

Proof.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT;
         (* every case needs to introduce a couple of things *)
         intros t' HE;
         (* and we can deal with several impossible
            cases all at once *)
         try solve_by_invert.
    - (* T_If *) inversion HE; subst; clear HE.
      + (* ST_IfTrue *) assumption.
      + (* ST_IfFalse *) assumption.
      + (* ST_If *) apply T_If; try assumption.
        apply IHHT1; assumption.
    - (* T_Succ *) invert HE. apply T_Succ. apply IHHT. assumption.
    - (* T_Pred *) invert HE.
      + assumption.
      + invert HT. assumption.
      + apply T_Pred. apply (IHHT _ H0).
    - (* T_Iszero *)invert HE.
      + apply T_True.
      + apply T_False.
      + apply T_Iszero. apply (IHHT _ H0).
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (finish_preservation_informal)

    Complete the following informal proof: *)

(** _Theorem_: If [|-- t \in T] and [t --> t'], then [|-- t' \in T]. *)

(** _Proof_: By induction on a derivation of [|-- t \in T].

    - If the last rule in the derivation is [T_If], then [t = if t1
      then t2 else t3], with [|-- t1 \in Bool], [|-- t2 \in T] and [|-- t3
      \in T].

      Inspecting the rules for the small-step reduction relation and
      remembering that [t] has the form [if ...], we see that the
      only ones that could have been used to prove [t --> t'] are
      [ST_IfTrue], [ST_IfFalse], or [ST_If].

      - If the last rule was [ST_IfTrue], then [t' = t2].  But we
        know that [|-- t2 \in T], so we are done.

      - If the last rule was [ST_IfFalse], then [t' = t3].  But we
        know that [|-- t3 \in T], so we are done.

      - If the last rule was [ST_If], then [t' = if t1' then t2
        else t3], where [t1 --> t1'].  We know [|-- t1 \in Bool] so,
        by the IH, [|-- t1' \in Bool].  The [T_If] rule then gives us
        [|-- if t1' then t2 else t3 \in T], as required.

    - (* FILL IN HERE *)
*)
(* Do not modify the following line: *)
Definition manual_grade_for_finish_preservation_informal : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard (preservation_alternate_proof)

    Now prove the same property again by induction on the
    _evaluation_ derivation instead of on the typing derivation.
    Begin by carefully reading and thinking about the first few
    lines of the above proofs to make sure you understand what
    each one is doing.  The set-up for this proof is similar, but
    not exactly the same. *)

Theorem preservation' : forall t t' T,
  |-- t \in T ->
  t --> t' ->
  |-- t' \in T.
Proof with eauto.
  intros t t' T HT HE.
  generalize dependent T.
  induction HE; intros T HT; try solve_by_inverts' 3.
Qed.
(** [] *)

(** The preservation theorem is often called _subject reduction_,
    because it tells us what happens when the "subject" of the typing
    relation is reduced.  This terminology comes from thinking of
    typing statements as sentences, where the term is the subject and
    the type is the predicate. *)

(* ================================================================= *)
(** ** Type Soundness *)

(** Putting progress and preservation together, we see that a
    well-typed term can never reach a stuck state.  *)

Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  |-- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  intros t t' T HT P. induction P; intros [R S].
  - apply progress in HT. destruct HT; auto.
  - apply IHP.
    + apply preservation with (t := x); auto.
    + unfold stuck. split; auto.
Qed.

(* ================================================================= *)
(** ** Additional Exercises *)

(** **** Exercise: 3 stars, standard, especially useful (subject_expansion)

    Having seen the subject reduction property, one might
    wonder whether the opposite property -- subject _expansion_ --
    also holds.  That is, is it always the case that, if [t --> t']
    and [|-- t' \in T], then [|-- t \in T]?  If so, prove it.  If
    not, give a counter-example.

    counter-example:
    t = <{ if true then true else 1 }>
    t' = true
    T = Bool
*)

Theorem subject_expansion:
  (forall t t' T, t --> t' /\ |-- t' \in T -> |-- t \in T)
  \/
  ~ (forall t t' T, t --> t' /\ |-- t' \in T -> |-- t \in T).
Proof.
  right. intros H.
  assert (<{ if true then true else 0}> --> <{ true }>) as HE.
  { apply ST_IfTrue. }
  assert (|-- <{true}> \in Bool) as HT'.
  { apply T_True. }
  pose proof (H _ _ _ (conj HE HT')) as HT.
  inversion HT. inversion H6.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (variation1)

    Suppose that we add this new rule to the typing relation:

      | T_SuccBool : forall t,
           |-- t \in Bool ->
           |-- <{ succ t }> \in Bool

   Which of the following properties remain true in the presence of
   this rule?  For each one, write either "remains true" or
   else "becomes false." If a property becomes false, give a
   counterexample.
      - Determinism of [step]
            remains true
      - Progress
            becomes false, counterexample:
            <{ if (succ true) then true else false }> is not a value, and
            can take no steps.
      - Preservation
            remains true
*)

Module Variation1.

Inductive has_type : tm -> ty -> Prop :=
  | T_True :
       |-- <{ true }> \in Bool
  | T_False :
       |-- <{ false }> \in Bool
  | T_If : forall t1 t2 t3 T,
       |-- t1 \in Bool ->
       |-- t2 \in T ->
       |-- t3 \in T ->
       |-- <{ if t1 then t2 else t3 }> \in T
  | T_0 :
       |-- <{ 0 }> \in Nat
  | T_Succ : forall t1,
       |-- t1 \in Nat ->
       |-- <{ succ t1 }> \in Nat
  | T_Pred : forall t1,
       |-- t1 \in Nat ->
       |-- <{ pred t1 }> \in Nat
  | T_Iszero : forall t1,
       |-- t1 \in Nat ->
       |-- <{ iszero t1 }> \in Bool
  | T_SuccBool : forall t,
       |-- t \in Bool ->
       |-- <{ succ t }> \in Bool

where "'|--' t '\in' T" := (has_type t T).

Hint Constructors has_type : core.

Theorem step_deterministic_correct:
  deterministic step.
Proof.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; simpl; intros; try solve_by_inverts'' 3.
Qed.

Theorem progress_wrong : ~ (forall t T,
  |-- t \in T ->
  value t \/ exists t', t --> t').
Proof.
  intros H.
  assert (|-- <{ if (succ true) then true else false }> \in Bool) as HT by auto.
  apply H in HT. try solve_by_inverts' 5.
Qed.

Theorem preservation_correct : forall t t' T,
  |-- t \in T ->
  t --> t' ->
  |-- t' \in T.
Proof.
  intros t t' T HT HE.
  generalize dependent T.
  induction HE; intros T HT; try solve_by_inverts' 3.
Qed.

End Variation1.

(* Do not modify the following line: *)
Definition manual_grade_for_variation1 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (variation2)

    Suppose, instead, that we add this new rule to the [step] relation:

      | ST_Funny1 : forall t2 t3,
           (<{ if true then t2 else t3 }>) --> t3

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

   Determinism of [step] becomes false, counterexample:
   <{ if true then true else false }> --> <{ true }> (ST_IfTrue)
   <{ if true then true else false }> --> <{ false }> (ST_Funny1)
*)

Module Variation2.

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      <{ if true then t1 else t2 }> --> t1
  | ST_IfFalse : forall t1 t2,
      <{ if false then t1 else t2 }> --> t2
  | ST_If : forall c c' t2 t3,
      c --> c' ->
      <{ if c then t2 else t3 }> --> <{ if c' then t2 else t3 }>
  | ST_Succ : forall t1 t1',
      t1 --> t1' ->
      <{ succ t1 }> --> <{ succ t1' }>
  | ST_Pred0 :
      <{ pred 0 }> --> <{ 0 }>
  | ST_PredSucc : forall v,
      nvalue v ->
      <{ pred (succ v) }> --> v
  | ST_Pred : forall t1 t1',
      t1 --> t1' ->
      <{ pred t1 }> --> <{ pred t1' }>
  | ST_Iszero0 :
      <{ iszero 0 }> --> <{ true }>
  | ST_IszeroSucc : forall v,
       nvalue v ->
      <{ iszero (succ v) }> --> <{ false }>
  | ST_Iszero : forall t1 t1',
      t1 --> t1' ->
      <{ iszero t1 }> --> <{ iszero t1' }>
  | ST_Funny1 : forall t2 t3,
      (<{ if true then t2 else t3 }>) --> t3

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Theorem step_deterministic_wrong:
  ~ (deterministic step).
Proof.
  unfold deterministic. intros H.
  assert (<{ if true then true else false }> --> <{ true }>) as Hy1 by auto.
  assert (<{ if true then true else false }> --> <{ false }>) as Hy2 by auto.
  pose proof (H _ _ _ Hy1 Hy2) as G.
  inversion G.
Qed.

Lemma bool_canonical : forall t,
  |-- t \in Bool -> value t -> bvalue t.
Proof.
  intros t HT [Hb | Hn]; try solve_by_inverts' 2.
Qed.

Lemma nat_canonical : forall t,
  |-- t \in Nat -> value t -> nvalue t.
Proof.
  intros t HT [Hb | Hn]; try solve_by_inverts' 2.
Qed.

Hint Resolve bool_canonical nat_canonical : core.

Theorem progress_correct : forall t T,
  |-- t \in T ->
  value t \/ exists t', t --> t'.
Proof.
  intros t T HT.
  induction HT; auto.
  - right. try solve_by_inverts' 4.
  - destruct IHHT.
    + left. auto.
    + right. try solve_by_inverts' 2.
  - right. try solve_by_inverts' 4.
  - right. try solve_by_inverts' 4.
Qed.

Theorem preservation_correct : forall t t' T,
  |-- t \in T ->
  t --> t' ->
  |-- t' \in T.
Proof.
  intros t t' T HT HE.
  generalize dependent T.
  induction HE; intros T HT; try solve_by_inverts' 3.
Qed.

End Variation2.

(* Do not modify the following line: *)
Definition manual_grade_for_variation2 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (variation3)

    Suppose instead that we add this rule:

      | ST_Funny2 : forall t1 t2 t2' t3,
           t2 --> t2' ->
           (<{ if t1 then t2 else t3 }>) --> (<{ if t1 then t2' else t3 }>)

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

   Determinism of [step] becomes false, counterexample:
   <{ if true then (if false then true else false) else false }>
       --> <{ if false then true else false }> (ST_IfTrue)
   <{ if true then (if false then true else false) else false }>
       --> <{ if true then false else false }> (ST_Funny2)
*)

Module Variation3.

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      <{ if true then t1 else t2 }> --> t1
  | ST_IfFalse : forall t1 t2,
      <{ if false then t1 else t2 }> --> t2
  | ST_If : forall c c' t2 t3,
      c --> c' ->
      <{ if c then t2 else t3 }> --> <{ if c' then t2 else t3 }>
  | ST_Succ : forall t1 t1',
      t1 --> t1' ->
      <{ succ t1 }> --> <{ succ t1' }>
  | ST_Pred0 :
      <{ pred 0 }> --> <{ 0 }>
  | ST_PredSucc : forall v,
      nvalue v ->
      <{ pred (succ v) }> --> v
  | ST_Pred : forall t1 t1',
      t1 --> t1' ->
      <{ pred t1 }> --> <{ pred t1' }>
  | ST_Iszero0 :
      <{ iszero 0 }> --> <{ true }>
  | ST_IszeroSucc : forall v,
       nvalue v ->
      <{ iszero (succ v) }> --> <{ false }>
  | ST_Iszero : forall t1 t1',
      t1 --> t1' ->
      <{ iszero t1 }> --> <{ iszero t1' }>
  | ST_Funny2 : forall t1 t2 t2' t3,
      t2 --> t2' ->
      (<{ if t1 then t2 else t3 }>) --> (<{ if t1 then t2' else t3 }>)

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Theorem step_deterministic_wrong:
  ~ (deterministic step).
Proof with eauto.
  unfold deterministic. intros H.
  assert (<{ if true then (if false then true else false) else false }>
          --> <{ if false then true else false }>) as Hy1 by auto.
  assert (<{ if true then (if false then true else false) else false }>
          --> <{ if true then false else false }>) as Hy2 by auto.
  pose proof (H _ _ _ Hy1 Hy2) as G.
  inversion G.
Qed.

Lemma bool_canonical : forall t,
  |-- t \in Bool -> value t -> bvalue t.
Proof.
  intros t HT [Hb | Hn]; try solve_by_inverts' 2.
Qed.

Lemma nat_canonical : forall t,
  |-- t \in Nat -> value t -> nvalue t.
Proof.
  intros t HT [Hb | Hn]; try solve_by_inverts' 2.
Qed.

Hint Resolve bool_canonical nat_canonical : core.

Theorem progress_correct : forall t T,
  |-- t \in T ->
  value t \/ exists t', t --> t'.
Proof.
  intros t T HT.
  induction HT; auto.
  - right. try solve_by_inverts' 4.
  - destruct IHHT.
    + left. auto.
    + right. try solve_by_inverts' 2.
  - right. try solve_by_inverts' 4.
  - right. try solve_by_inverts' 4.
Qed.

Theorem preservation_correct : forall t t' T,
  |-- t \in T ->
  t --> t' ->
  |-- t' \in T.
Proof.
  intros t t' T HT HE.
  generalize dependent T.
  induction HE; intros T HT; try solve_by_inverts' 3.
Qed.

End Variation3.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (variation4)

    Suppose instead that we add this rule:

      | ST_Funny3 :
          (<{pred false}>) --> (<{ pred (pred false)}>)

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

   all remains true
*)

Module Variation4.

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      <{ if true then t1 else t2 }> --> t1
  | ST_IfFalse : forall t1 t2,
      <{ if false then t1 else t2 }> --> t2
  | ST_If : forall c c' t2 t3,
      c --> c' ->
      <{ if c then t2 else t3 }> --> <{ if c' then t2 else t3 }>
  | ST_Succ : forall t1 t1',
      t1 --> t1' ->
      <{ succ t1 }> --> <{ succ t1' }>
  | ST_Pred0 :
      <{ pred 0 }> --> <{ 0 }>
  | ST_PredSucc : forall v,
      nvalue v ->
      <{ pred (succ v) }> --> v
  | ST_Pred : forall t1 t1',
      t1 --> t1' ->
      <{ pred t1 }> --> <{ pred t1' }>
  | ST_Iszero0 :
      <{ iszero 0 }> --> <{ true }>
  | ST_IszeroSucc : forall v,
       nvalue v ->
      <{ iszero (succ v) }> --> <{ false }>
  | ST_Iszero : forall t1 t1',
      t1 --> t1' ->
      <{ iszero t1 }> --> <{ iszero t1' }>
  | ST_Funny3 :
      (<{pred false}>) --> (<{ pred (pred false)}>)

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation step_normal_form := (normal_form step).

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  unfold step_normal_form, normal_form.
  induction t; intros H []; try solve_by_inverts 2.
  destruct H; try solve_by_invert.
  invert H. invert H0. intuition eauto.
Qed.

Ltac solve_by_inverts'' n :=
  match goal with
  | H : nvalue ?x, H': ?x --> _ |- _ =>
    pose proof (value_is_nf _ (or_intror H)); exfalso; eauto
  | H : ?T |- _ =>
    match type of T with Prop =>
      solve [
        inversion H;
        match n with S (S (?n')) => subst; try f_equal; eauto; solve_by_inverts'' (S n') end ]
    end
  end.

Theorem step_deterministic_correct:
  deterministic step.
Proof with eauto.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; simpl; intros; try solve_by_inverts'' 3.
Qed.

Lemma bool_canonical : forall t,
  |-- t \in Bool -> value t -> bvalue t.
Proof.
  intros t HT [Hb | Hn]; try solve_by_inverts' 2.
Qed.

Lemma nat_canonical : forall t,
  |-- t \in Nat -> value t -> nvalue t.
Proof.
  intros t HT [Hb | Hn]; try solve_by_inverts' 2.
Qed.

Hint Resolve bool_canonical nat_canonical : core.

Theorem progress_correct : forall t T,
  |-- t \in T ->
  value t \/ exists t', t --> t'.
Proof.
  intros t T HT.
  induction HT; auto.
  - right. try solve_by_inverts' 4.
  - destruct IHHT.
    + left. auto.
    + right. try solve_by_inverts' 2.
  - right. try solve_by_inverts' 4.
  - right. try solve_by_inverts' 4.
Qed.

Theorem preservation_correct : forall t t' T,
  |-- t \in T ->
  t --> t' ->
  |-- t' \in T.
Proof.
  intros t t' T HT HE.
  generalize dependent T.
  induction HE; intros T HT; try solve_by_inverts' 3.
Qed.

End Variation4.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (variation5)

    Suppose instead that we add this rule:

      | T_Funny4 :
            |-- <{ 0 }> \in Bool

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

   progress becomes false, counterexample:
   |-- <{ 0 }> \in Bool
   <{ if 0 then true else false }> is not a value, and can take no steps
*)

Module Variation5.

Inductive has_type : tm -> ty -> Prop :=
  | T_True :
       |-- <{ true }> \in Bool
  | T_False :
       |-- <{ false }> \in Bool
  | T_If : forall t1 t2 t3 T,
       |-- t1 \in Bool ->
       |-- t2 \in T ->
       |-- t3 \in T ->
       |-- <{ if t1 then t2 else t3 }> \in T
  | T_0 :
       |-- <{ 0 }> \in Nat
  | T_Succ : forall t1,
       |-- t1 \in Nat ->
       |-- <{ succ t1 }> \in Nat
  | T_Pred : forall t1,
       |-- t1 \in Nat ->
       |-- <{ pred t1 }> \in Nat
  | T_Iszero : forall t1,
       |-- t1 \in Nat ->
       |-- <{ iszero t1 }> \in Bool
  | T_Funny4 :
       |-- <{ 0 }> \in Bool

where "'|--' t '\in' T" := (has_type t T).

Hint Constructors has_type : core.

Theorem step_deterministic_correct:
  deterministic step.
Proof with eauto.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; simpl; intros; try solve_by_inverts'' 3.
Qed.

Theorem progress_wrong : ~ (forall t T,
  |-- t \in T ->
  value t \/ exists t', t --> t').
Proof.
  intros H.
  assert (|-- <{ if 0 then true else false }> \in Bool) as HT by auto.
  apply H in HT. try solve_by_inverts' 5.
Qed.

Theorem preservation_correct : forall t t' T,
  |-- t \in T ->
  t --> t' ->
  |-- t' \in T.
Proof.
  intros t t' T HT HE.
  generalize dependent T.
  induction HE; intros T HT; try solve_by_inverts' 3.
Qed.

End Variation5.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (variation6)

    Suppose instead that we add this rule:

      | T_Funny5 :
            |-- <{ pred 0 }> \in Bool

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

   progress becomes remains true!!!

   preservation becomes false, counterexample:
   |-- <{ pred 0 }> \in Bool
   <{ pred 0 }> --> <{ 0 }>
   but (|-- { 0 } \in Bool) is not true.
*)

Module Variation6.

Inductive has_type : tm -> ty -> Prop :=
  | T_True :
       |-- <{ true }> \in Bool
  | T_False :
       |-- <{ false }> \in Bool
  | T_If : forall t1 t2 t3 T,
       |-- t1 \in Bool ->
       |-- t2 \in T ->
       |-- t3 \in T ->
       |-- <{ if t1 then t2 else t3 }> \in T
  | T_0 :
       |-- <{ 0 }> \in Nat
  | T_Succ : forall t1,
       |-- t1 \in Nat ->
       |-- <{ succ t1 }> \in Nat
  | T_Pred : forall t1,
       |-- t1 \in Nat ->
       |-- <{ pred t1 }> \in Nat
  | T_Iszero : forall t1,
       |-- t1 \in Nat ->
       |-- <{ iszero t1 }> \in Bool
  | T_Funny5 :
       |-- <{ pred 0 }> \in Bool

where "'|--' t '\in' T" := (has_type t T).

Hint Constructors has_type : core.

Theorem step_deterministic_correct:
  deterministic step.
Proof with eauto.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; simpl; intros; try solve_by_inverts'' 3.
Qed.

Lemma bool_canonical : forall t,
  |-- t \in Bool -> value t -> bvalue t.
Proof.
  intros t HT [Hb | Hn]; try solve_by_inverts' 2.
Qed.

Lemma nat_canonical : forall t,
  |-- t \in Nat -> value t -> nvalue t.
Proof.
  intros t HT [Hb | Hn]; try solve_by_inverts' 2.
Qed.

Hint Resolve bool_canonical nat_canonical : core.

Theorem progress_correct : forall t T,
  |-- t \in T ->
  value t \/ exists t', t --> t'.
Proof.
  intros t T HT.
  induction HT; auto.
  - right. try solve_by_inverts' 4.
  - destruct IHHT.
    + left. auto.
    + right. try solve_by_inverts' 2.
  - right. try solve_by_inverts' 4.
  - right. try solve_by_inverts' 4.
  - right. eauto.
Qed.

Theorem preservation_wrong : ~ (forall t t' T,
  |-- t \in T ->
  t --> t' ->
  |-- t' \in T).
Proof.
  intros H.
  assert (|-- <{ pred 0 }> \in Bool) as HT by auto.
  assert (<{ pred 0 }> --> <{ 0 }>) as HE by auto.
  pose proof (H _ _ _ HT HE).
  inversion H0.
Qed.

End Variation6.

(** [] *)

(** **** Exercise: 3 stars, standard, optional (more_variations)

    Make up some exercises of your own along the same lines as
    the ones above.  Try to find ways of selectively breaking
    properties -- i.e., ways of changing the definitions that
    break just one of the properties and leave the others alone.
*)
(* FILL IN HERE

    [] *)

(** **** Exercise: 1 star, standard (remove_pred0)

    The reduction rule [ST_Pred0] is a bit counter-intuitive: we
    might feel that it makes more sense for the predecessor of [<{0}>] to
    be undefined, rather than being defined to be [<{0}>].  Can we
    achieve this simply by removing the rule from the definition of
    [step]?  Would doing so create any problems elsewhere?

    No.

    progress becomes fails, since
    <{ pred 0 }> is not a value, and can take no steps.

    and

    soundness is lost, since
     <{ pred 0 }> is well-typed, but it get stuck.
*)

Module RemovePred0.

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      <{ if true then t1 else t2 }> --> t1
  | ST_IfFalse : forall t1 t2,
      <{ if false then t1 else t2 }> --> t2
  | ST_If : forall c c' t2 t3,
      c --> c' ->
      <{ if c then t2 else t3 }> --> <{ if c' then t2 else t3 }>
  | ST_Succ : forall t1 t1',
      t1 --> t1' ->
      <{ succ t1 }> --> <{ succ t1' }>
  (* | ST_Pred0 :
      <{ pred 0 }> --> <{ 0 }> *)
  | ST_PredSucc : forall v,
      nvalue v ->
      <{ pred (succ v) }> --> v
  | ST_Pred : forall t1 t1',
      t1 --> t1' ->
      <{ pred t1 }> --> <{ pred t1' }>
  | ST_Iszero0 :
      <{ iszero 0 }> --> <{ true }>
  | ST_IszeroSucc : forall v,
       nvalue v ->
      <{ iszero (succ v) }> --> <{ false }>
  | ST_Iszero : forall t1 t1',
      t1 --> t1' ->
      <{ iszero t1 }> --> <{ iszero t1' }>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Theorem progress_wrong : ~ (forall t T,
  |-- t \in T ->
  value t \/ exists t', t --> t').
Proof.
  intros H.
  assert (|-- <{ pred 0 }> \in Nat) as HT by auto.
  apply H in HT. try solve_by_inverts' 4.
Qed.

Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck : core.

Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Theorem soundness_wrong :
  exists t t' T,
  |-- t \in T /\ t -->* t' /\ stuck t'.
Proof.
  exists <{ pred 0}>, <{pred 0 }>, Nat.
  repeat split; auto.
  - apply multi_refl.
  - unfold step_normal_form.
    intros [t' H]. try solve_by_inverts' 2.
  - intros H. try solve_by_inverts' 2.
Qed.

End RemovePred0.

(* Do not modify the following line: *)
Definition manual_grade_for_remove_pred0 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced (prog_pres_bigstep)

    Suppose our evaluation relation is defined in the big-step style.
    State appropriate analogs of the progress and preservation
    properties. (You do not need to prove them.)

    Can you see any limitations of either of your properties?  Do they
    allow for nonterminating programs?  Why might we prefer the
    small-step semantics for stating preservation and progress?

    Let "t ==> t'" be "t is evaluated to t' in big-step style".

    Theorem preservation : forall t t' T,
      |-- t \in T ->
      t ==> t' ->
      |-- t' \in T.

    Theorem progress : forall t T,
      |-- t \in T ->
      exists t', value t' /\ t ==> t'.

    If we add nonterminating components (such as [while]), [progress] will fail.
*)

Module BigStep.

Reserved Notation " t '==>' n " (at level 50, left associativity).

Inductive eval : tm -> tm -> Prop :=
  | E_Value : forall t,
      value t ->
      <{ t }> ==> <{ t }>
  | E_IfTrue : forall c t1 t2 t',
      c ==> <{ true }> ->
      t1 ==> t' ->
      <{ if c then t1 else t2 }> ==> t'
  | E_IfFalse : forall c t1 t2 t',
      c ==> <{ false }> ->
      t2 ==> t' ->
      <{ if c then t1 else t2 }> ==> t'
  | E_Succ : forall t t',
      t ==> t' ->
      <{ succ t }> ==> <{ succ t' }>
  | E_Pred0 : forall t,
      t ==> <{ 0 }> ->
      <{ pred t }> ==> <{ 0 }>
  | E_PredSucc : forall t t',
      nvalue t' ->
      t ==> <{ succ t' }> ->
      <{ pred t }> ==> <{ t' }>
  | E_Iszero0 : forall t,
      t ==> <{ 0 }> ->
      <{ iszero t }> ==> <{ true }>
  | E_IszeroSucc : forall t t',
      nvalue t' ->
      t ==> <{ succ t' }> ->
      <{ iszero t }> ==> <{ false }>

where "t '==>' n" := (eval t n).

Hint Constructors eval : core.
Hint Resolve bool_canonical nat_canonical : core.

Lemma nv_canonical : forall t,
  nvalue t -> |-- t \in Nat.
Proof.
  intros. induction H; auto.
Qed.

Hint Resolve nv_canonical : core.

Theorem preservation : forall t t' T,
  |-- t \in T ->
  t ==> t' ->
  |-- t' \in T.
Proof.
  intros t t' T HT HE.
  generalize dependent T.
  induction HE; intros T HT; try solve_by_inverts' 2.
Qed.

Theorem progress : forall t T,
  |-- t \in T ->
  exists t', value t' /\ t ==> t'.
Proof with eauto.
  intros t T HT.
  induction HT.
  - exists <{true}>.  split; auto.
  - exists <{false}>. split; auto.
  - destruct IHHT1 as [t1' [H1 E1]].
    destruct IHHT2 as [t2' [H2 E2]].
    destruct IHHT3 as [t3' [H3 E3]].
    pose proof (preservation _ _ _ HT1 E1) as HT1'.
    apply (bool_canonical _ HT1') in H1.
    destruct H1.
    + exists t2'. split; auto.
    + exists t3'. split; auto.
  - exists <{0}>. split; auto.
  - destruct IHHT as [t1' [H1 E]].
    pose proof (preservation _ _ _ HT E) as HT'.
    exists <{succ t1'}>.
    split; auto.
  - destruct IHHT as [t1' [H1 E]].
    pose proof (preservation _ _ _ HT E) as HT'.
    apply (nat_canonical _ HT') in H1.
    destruct H1.
    + exists <{0}>. split; auto.
    + exists <{t}>. split; auto.
  - destruct IHHT as [t1' [H1 E]].
    pose proof (preservation _ _ _ HT E) as HT'.
    apply (nat_canonical _ HT') in H1.
    destruct H1.
    + exists <{true}>. split; auto.
    + exists <{false}>. split; eauto.
Qed.

End BigStep.

(* Do not modify the following line: *)
Definition manual_grade_for_prog_pres_bigstep : option (nat*string) := None.
(** [] *)
End TM.

(* 2023-03-25 11:16 *)
