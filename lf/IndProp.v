(** * IndProp: Inductively Defined Propositions *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Logic.
From Coq Require Import Lia.

(* ################################################################# *)
(** * Inductively Defined Propositions *)

(** In the [Logic] chapter, we looked at several ways of writing
    propositions, including conjunction, disjunction, and existential
    quantification.

    In this chapter, we bring yet another new tool into the mix:
    _inductively defined propositions_.

    To begin, some examples... *)

(* ================================================================= *)
(** ** The Collatz Conjecture *)

(** The _Collatz Conjecture_ is a famous open problem in number
    theory.

    Its statement is surprisingly simple.  First, we define a function
    [f] on numbers, as follows: *)

Fixpoint div2 (n : nat) :=
  match n with
    0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Definition f (n : nat) :=
  if even n then div2 n
  else (3 * n) + 1.

(** Next, we look at what happens when we repeatedly apply [f] to some
    given starting number.  For example, [f 12] is [6], and [f 6] is
    [3], so by repeatedly applying [f] we get the sequence [12, 6, 3,
    10, 5, 16, 8, 4, 2, 1].

    Similarly, if we start with [19], we get the longer sequence [19,
    58, 29, 88, 44, 22, 11, 34, 17, 52, 26, 13, 40, 20, 10, 5, 16, 8,
    4, 2, 1].

    Both of these sequences eventually reach [1].  The question posed
    by Collatz was: Does the sequence starting from _any_ natural
    number eventually reach [1]? *)

(** To formalize this question in Coq, we might try to define a
    recursive _function_ that computes the total number of steps that
    it takes for such a sequence to reach [1]. *)

Fail Fixpoint reaches_1_in (n : nat) :=
  if n =? 1 then 0
  else 1 + reaches_1_in (f n).

(** This definition is rejected by Coq's termination checker, since
    the argument to the recursive call, [f n], is not "obviously
    smaller" than [n].

    Indeed, this isn't just a silly limitation of the termination
    checker.  Functions in Coq are required to be total, and checking
    that this particular function is total would be equivalent to
    settling the Collatz conjecture! *)

(** Fortunately, there is another way to do it: We can express the
    concept "reaches [1] eventually" as an _inductively defined
    property_ of numbers: *)

Inductive reaches_1 : nat -> Prop :=
  | term_done : reaches_1 1
  | term_more (n : nat) : reaches_1 (f n) -> reaches_1 n.

Check reaches_1.
Check (reaches_1 10).

Example reaaches_1_10 : reaches_1 10.
Proof.
  apply term_more. cbn.
  apply term_more. cbn.
  apply term_more. cbn.
  apply term_more. cbn.
  apply term_more. cbn.
  apply term_more. cbn.
  apply term_done.
Qed.

(** The details of such definitions are written will be explained
    below; for the moment, the way to read this one is: "The number
    [1] reaches [1], and any number [n] reaches [1] if [f n] does." *)

(** The Collatz conjecture then states that the sequence beginning
    from _any_ number reaches [1]: *)

Conjecture collatz : forall n, reaches_1 n.

(** If you succeed in proving this conjecture, you've got a bright
    future as a number theorist.  But don't spend too long on it --
    it's been open since 1937! *)

(* ================================================================= *)
(** ** Transitive Closure *)

(** A binary _relation_ on a set [X] is a family of propositions
    parameterized by two elements of [X] -- i.e., a proposition about
    pairs of elements of [X].  *)

(** For example, a familiar binary relation on [nat] is [le], the
    less-than-or-equal-to relation. *)

Module LePlayground.

(** The following definition says that there are two ways to
    show that one number is less than or equal to another: either
    observe that they are the same number, or, if the second has the
    form [S m], give evidence that the first is less than or equal to
    [m]. *)

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)   : le n n
  | le_S (n m : nat) : le n m -> le n (S m).

Check le.
Check (le 2).
Check (le 2 4).

Example le_2_4 : le 2 4.
Proof.
  apply le_S. apply le_S. apply le_n.
Qed.

Example not_le_4_2 : ~ (le 4 2).
Proof.
  intros H.
  inversion H. inversion H2. inversion H5.
Qed.

End LePlayground.

(** The _transitive closure_ of a relation [R] is the smallest
    relation that contains [R] and that is transitive.  *)

Inductive clos_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | t_step (x y : X) :
      R x y ->
      clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y ->
      clos_trans R y z ->
      clos_trans R x z.

(** **** Exercise: 1 star, standard, optional (close_refl_trans)

    How would you modify this definition so that it defines _reflexive
    and_ transitive closure?  How about reflexive, symmetric, and
    transitive closure? *)

(** A _relation_ on a set [X] is a set of ordered pairs [(x,y)] consisting
    of elements [x] and [y] in [X], i.e. a subset of [X * X]. *)

(** The _reflexive closure_ of a relation [R] is the smallest
    relation that contains [R] and that is reflexive.  *)
Inductive clos_refl {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | r_step (x : X) :
      R x x -> clos_refl R x x
  | r_refl (x y : X) :
      clos_refl R x x -> clos_refl R y y.

(** The _symmetric closure_ of a relation [R] is the smallest
    relation that contains [R] and that is symmetric.  *)
Inductive clos_sym {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | s_step (x y : X) :
      R x y -> clos_sym R x y
  | s_sym (x y : X) :
      clos_sym R x y -> clos_sym R y x.

(* [] *)

(* ================================================================= *)
(** ** Permutations *)

(** The familiar mathematical concept of _permutation_ also has an
    elegant formulation as an inductive relation.  For simplicity,
    let's focus on permutations of lists with exactly three
    elements. *)

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

(** This definition says:
      - If [l2] can be obtained from [l1] by swapping the first and
        second elements, then [l2] is a permutation of [l1].
      - If [l2] can be obtained from [l1] by swapping the second and
        third elements, then [l2] is a permutation of [l1].
      - If [l2] is a permutation of [l1] and [l3] is a permutation of
        [l2], then [l3] is a permutation of [l1]. *)

(** **** Exercise: 1 star, standard, optional (perm)

    According to this definition, is [[1;2;3]] a permutation of
    [[3;2;1]]?  Is [[1;2;3]] a permutation of itself? *)

(* Yes. Since
   [Perms3 [1;2;3] [2;1;3] -> Perms3 [2;1;3] [1;2;3] -> Perms [1;2;3] [1;2;3]].

    [] *)

(* ================================================================= *)
(** ** Evenness (yet again) *)

(** We've already seen two ways of stating a proposition that a number
    [n] is even: We can say

      (1) [even n = true], or

      (2) [exists k, n = double k].

    A third possibility, which we'll use as a running example for the
    rest of this chapter, is to say that [n] is even if we can
    _establish_ its evenness from the following rules:

       - The number [0] is even.
       - If [n] is even, then [S (S n)] is even. *)

(** (Defining evenness in this way may seem a bit confusing,
    since we have already seen another perfectly good way of doing
    it -- "[n] is even if it is equal to the result of doubling some
    number". But it makes a convenient running example because it is
    simple and compact.) *)

(** To illustrate how this new definition of evenness works,
    let's imagine using it to show that [4] is even. First, we give
    the rules names for easy reference:
       - Rule [ev_0]: The number [0] is even.
       - Rule [ev_SS]: If [n] is even, then [S (S n)] is even.

    Now, by rule [ev_SS], it suffices to show that [2] is even. This,
    in turn, is again guaranteed by rule [ev_SS], as long as we can
    show that [0] is even. But this last fact follows directly from
    the [ev_0] rule. *)

(** We can translate the informal definition of evenness from above
    into a formal [Inductive] declaration, where each "way that a
    number can be even" corresponds to a separate constructor: *)

Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(** This definition is interestingly different from previous uses of
    [Inductive].  For one thing, we are defining not a [Type] (like
    [nat]) or a function yielding a [Type] (like [list]), but rather a
    function from [nat] to [Prop] -- that is, a property of numbers.
    But what is really new is that, because the [nat] argument of [ev]
    appears to the _right_ of the colon on the first line, it is
    allowed to take _different_ values in the types of different
    constructors: [0] in the type of [ev_0] and [S (S n)] in the type
    of [ev_SS].  Accordingly, the type of each constructor must be
    specified explicitly (after a colon), and each constructor's type
    must have the form [ev n] for some natural number [n].

    In contrast, recall the definition of [list]:

    Inductive list (X:Type) : Type :=
      | nil
      | cons (x : X) (l : list X).

    or equivalently:

    Inductive list (X:Type) : Type :=
      | nil                       : list X
      | cons (x : X) (l : list X) : list X.

   This definition introduces the [X] parameter _globally_, to the
   _left_ of the colon, forcing the result of [nil] and [cons] to be
   the same type (i.e., [list X]).  But if we had tried to bring [nat]
   to the left of the colon in defining [ev], we would have seen an
   error: *)

Fail Inductive wrong_ev (n : nat) : Prop :=
  | wrong_ev_0 : wrong_ev 0
  | wrong_ev_SS (H: wrong_ev n) : wrong_ev (S (S n)).
(* ===> Error: Last occurrence of "[wrong_ev]" must have "[n]" as 1st
        argument in "[wrong_ev 0]". *)

(** In an [Inductive] definition, an argument to the type constructor
    on the left of the colon is called a "parameter", whereas an
    argument on the right is called an "index" or "annotation."

    For example, in [Inductive list (X : Type) := ...], the [X] is a
    parameter, while in [Inductive ev : nat -> Prop := ...], the
    unnamed [nat] argument is an index. *)

(** We can think of this as defining a Coq property [ev : nat ->
    Prop], together with "evidence constructors" [ev_0 : ev 0] and
    [ev_SS : forall n, ev n -> ev (S (S n))]. *)

(** These evidence constructors can be thought of as "primitive
    evidence of evenness", and they can be used just like proven
    theorems.  In particular, we can use Coq's [apply] tactic with the
    constructor names to obtain evidence for [ev] of particular
    numbers... *)

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ... or we can use function application syntax to combine several
    constructors: *)

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** In this way, we can also prove theorems that have hypotheses
    involving [ev]. *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(** **** Exercise: 1 star, standard (ev_double) *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros n. induction n.
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn.
Qed.
(** [] *)

(* ################################################################# *)
(** * Using Evidence in Proofs *)

(** Besides _constructing_ evidence that numbers are even, we can also
    _destruct_ such evidence, reasoning about how it could have been
    built.

    Introducing [ev] with an [Inductive] declaration tells Coq not
    only that the constructors [ev_0] and [ev_SS] are valid ways to
    build evidence that some number is [ev], but also that these two
    constructors are the _only_ ways to build evidence that numbers
    are [ev]. *)

(** In other words, if someone gives us evidence [E] for the assertion
    [ev n], then we know that [E] must be one of two things:

      - [E] is [ev_0] (and [n] is [O]), or
      - [E] is [ev_SS n' E'] (and [n] is [S (S n')], where [E'] is
        evidence for [ev n']). *)

(** This suggests that it should be possible to analyze a
    hypothesis of the form [ev n] much as we do inductively defined
    data structures; in particular, it should be possible to argue by
    _case analysis_ or by _induction_ on such evidence.  Let's look at a
    few examples to see what this means in practice. *)

(* ================================================================= *)
(** ** Inversion on Evidence *)

(** Suppose we are proving some fact involving a number [n], and
    we are given [ev n] as a hypothesis.  We already know how to
    perform case analysis on [n] using [destruct] or [induction],
    generating separate subgoals for the case where [n = O] and the
    case where [n = S n'] for some [n'].  But for some proofs we may
    instead want to analyze the evidence for [ev n] _directly_.

    As a tool for such proofs, we can formalize the intuitive
    characterization that we gave above for evidence of [ev n], using
    [destruct]. *)

Theorem ev_inversion : forall (n : nat),
    ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.  destruct E as [ | n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

(** Facts like this are often called "inversion lemmas" because they
    allow us to "invert" some given information to reason about all
    the different ways it could have been derived.

    Here, there are two ways to prove [ev n], and the inversion lemma
    makes this explicit. *)

(** We can use the inversion lemma that we proved above to help
    structure proofs: *)

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n H. apply ev_inversion in H.  destruct H as [H0|H1].
  - discriminate H0.
  - destruct H1 as [n' [Hnm Hev]]. injection Hnm as Heq.
    rewrite Heq. apply Hev.
Qed.

(** Note how the inversion lemma produces two subgoals, which
    correspond to the two ways of proving [ev].  The first subgoal is
    a contradiction that is discharged with [discriminate].  The
    second subgoal makes use of [injection] and [rewrite].

    Coq provides a handy tactic called [inversion] that factors out
    this common pattern, saving us the trouble of explicitly stating
    and proving an inversion lemma for every [Inductive] definition we
    make.

    Here, the [inversion] tactic can detect (1) that the first case,
    where [n = 0], does not apply and (2) that the [n'] that appears
    in the [ev_SS] case must be the same as [n].  It includes an
    "[as]" annotation similar to [destruct], allowing us to assign
    names rather than have Coq choose them. *)

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.  inversion E as [| n' E' Heq].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

(** The [inversion] tactic can apply the principle of explosion to
    "obviously contradictory" hypotheses involving inductively defined
    properties, something that takes a bit more work using our
    inversion lemma. Compare: *)

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H.  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ ev 1.
Proof.
  intros H. inversion H. Qed.

(** **** Exercise: 1 star, standard (inversion_practice)

    Prove the following result using [inversion].  (For extra
    practice, you can also prove it using the inversion lemma.) *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros.
  inversion H. inversion H1. apply H3.
Qed.

(* [inversion] does all works of [apply ev_inversion], [rewrite],
   [destruct], [discriminate] and [injection]. *)
Theorem SSSSev__even' : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros.
  apply ev_inversion in H. destruct H as [Hn | [x [H1 H2]]].
  - discriminate Hn.
  - injection H1 as H1. rewrite <- H1 in H2.
    apply ev_inversion in H2. destruct H2 as [Hn | [y [H3 H4]]].
    + discriminate Hn.
    + injection H3 as H3. rewrite H3. apply H4.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (ev5_nonsense)

    Prove the following result using [inversion]. *)

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros. inversion H. inversion H1. inversion H3.
Qed.
(** [] *)

(** The [inversion] tactic does quite a bit of work. For
    example, when applied to an equality assumption, it does the work
    of both [discriminate] and [injection]. In addition, it carries
    out the [intros] and [rewrite]s that are typically necessary in
    the case of [injection]. It can also be applied to analyze
    evidence for arbitrary inductively defined propositions, not just
    equality.  As examples, we'll use it to re-prove some theorems
    from chapter [Tactics].  (Here we are being a bit lazy by
    omitting the [as] clause from [inversion], thereby asking Coq to
    choose names for the variables and hypotheses that it introduces.) *)

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

(** Here's how [inversion] works in general.
      - Suppose the name [H] refers to an assumption [P] in the
        current context, where [P] has been defined by an [Inductive]
        declaration.
      - Then, for each of the constructors of [P], [inversion H]
        generates a subgoal in which [H] has been replaced by the
        specific conditions under which this constructor could have
        been used to prove [P].
      - Some of these subgoals will be self-contradictory; [inversion]
        throws these away.
      - The ones that are left represent the cases that must be proved
        to establish the original goal.  For those, [inversion] adds
        to the proof context all equations that must hold of the
        arguments given to [P] -- e.g., [S (S n') = n] in the proof of
        [evSS_ev]). *)

(** The [ev_double] exercise above shows that our new notion of
    evenness is implied by the two earlier ones (since, by
    [even_bool_prop] in chapter [Logic], we already know that
    those are equivalent to each other). To show that all three
    coincide, we just need the following lemma. *)

Lemma ev_Even_firsttry : forall n,
  ev n -> Even n.
Proof.
  (* WORKED IN CLASS *) unfold Even.

(** We could try to proceed by case analysis or induction on [n].  But
    since [ev] is mentioned in a premise, this strategy seems
    unpromising, because (as we've noted before) the induction
    hypothesis will talk about [n-1] (which is _not_ even!).  Thus, it
    seems better to first try [inversion] on the evidence for [ev].
    Indeed, the first case can be solved trivially. And we can
    seemingly make progress on the second case with a helper lemma. *)

  intros n E. inversion E as [EQ' | n' E' EQ'].
  - (* E = ev_0 *) exists 0. reflexivity.
  - (* E = ev_SS n' E'

    Unfortunately, the second case is harder.  We need to show [exists
    n0, S (S n') = double n0], but the only available assumption is
    [E'], which states that [ev n'] holds.  Since this isn't directly
    useful, it seems that we are stuck and that performing case
    analysis on [E] was a waste of time.

    If we look more closely at our second goal, however, we can see
    that something interesting happened: By performing case analysis
    on [E], we were able to reduce the original result to a similar
    one that involves a _different_ piece of evidence for [ev]: namely
    [E'].  More formally, we could finish our proof if we could show
    that

        exists k', n' = double k',

    which is the same as the original statement, but with [n'] instead
    of [n].  Indeed, it is not difficult to convince Coq that this
    intermediate result would suffice. *)
    assert (H: (exists k', n' = double k')
               -> (exists n0, S (S n') = double n0)).
        { intros [k' EQ'']. exists (S k'). simpl.
          rewrite <- EQ''. reflexivity. }
    apply H.

    (** Unfortunately, now we are stuck. To see this clearly, let's
        move [E'] back into the goal from the hypotheses. *)

    generalize dependent E'.

    (** Now it is obvious that we are trying to prove another instance
        of the same theorem we set out to prove -- only here we are
        talking about [n'] instead of [n]. *)
Abort.

(* ================================================================= *)
(** ** Induction on Evidence *)

(** If this story feels familiar, it is no coincidence: We've
    encountered similar problems in the [Induction] chapter, when
    trying to use case analysis to prove results that required
    induction.  And once again the solution is... induction! *)

(** The behavior of [induction] on evidence is the same as its
    behavior on data: It causes Coq to generate one subgoal for each
    constructor that could have used to build that evidence, while
    providing an induction hypothesis for each recursive occurrence of
    the property in question.

    To prove that a property of [n] holds for all even numbers (i.e.,
    those for which [ev n] holds), we can use induction on [ev
    n]. This requires us to prove two things, corresponding to the two
    ways in which [ev n] could have been constructed. If it was
    constructed by [ev_0], then [n=0] and the property must hold of
    [0]. If it was constructed by [ev_SS], then the evidence of [ev n]
    is of the form [ev_SS n' E'], where [n = S (S n')] and [E'] is
    evidence for [ev n']. In this case, the inductive hypothesis says
    that the property we are trying to prove holds for [n']. *)

(** Let's try proving that lemma again: *)

Lemma ev_Even : forall n,
  ev n -> Even n.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    unfold Even. exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : Even n' *)
    unfold Even in IH.
    destruct IH as [k Hk].
    rewrite Hk.
    unfold Even. exists (S k). simpl. reflexivity.
Qed.

(** Here, we can see that Coq produced an [IH] that corresponds
    to [E'], the single recursive occurrence of [ev] in its own
    definition.  Since [E'] mentions [n'], the induction hypothesis
    talks about [n'], as opposed to [n] or some other number. *)

(** The equivalence between the second and third definitions of
    evenness now follows. *)

Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Proof.
  intros n. split.
  - (* -> *) apply ev_Even.
  - (* <- *) unfold Even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(** As we will see in later chapters, induction on evidence is a
    recurring technique across many areas -- in particular for
    formalizing the semantics of programming languages. *)

(** The following exercises provide simple examples of this
    technique, to help you familiarize yourself with it. *)

(** **** Exercise: 2 stars, standard (ev_sum) *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m En Em.
  induction En as [ |n' En' IH].
  - simpl. apply Em.
  - simpl. apply ev_SS. apply IH.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (ev'_ev)

    In general, there may be multiple ways of defining a
    property inductively.  For example, here's a (slightly contrived)
    alternative definition for [ev]: *)

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

(** Prove that this definition is logically equivalent to the old one.
    To streamline the proof, use the technique (from the [Logic]
    chapter) of applying theorems to arguments, and note that the same
    technique works with constructors of inductively defined
    propositions. *)

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n. split.
  - intros H. induction H.
    + apply ev_0.
    + apply (ev_SS 0 ev_0).
    + apply (ev_sum n m IHev'1 IHev'2).
  - intros H. induction H.
    + apply ev'_0.
    + apply (ev'_sum 2 n ev'_2 IHev).
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced, especially useful (ev_ev__ev) *)
Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
  (* Hint: There are two pieces of evidence you could attempt to induct upon
      here. If one doesn't work, try the other. *)
Proof.
  intros n m Enm En.
  induction En.
  - apply Enm.
  - inversion Enm. apply (IHEn H0).
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (ev_plus_plus)

    This exercise can be completed without induction or case analysis.
    But, you will need a clever assertion and some tedious rewriting.
    Hint: Is [(n+m) + (n+p)] even? *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p Enm Enp.
  assert (ev ((n+n) + (m+p)) -> ev (m+p)).
  { intros E. apply (ev_ev__ev (n+n) (m+p) E).
    rewrite <- double_plus. apply ev_double. }
  apply H.
  rewrite <- add_assoc. rewrite (add_shuffle3 n m). rewrite add_assoc.
  apply (ev_sum (n+m) (n+p) Enm Enp).
Qed.
(** [] *)

(* ################################################################# *)
(** * Inductive Relations *)

(** A proposition parameterized by a number (such as [ev])
    can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module Playground.

(** Just like properties, relations can be defined inductively.  One
    useful example is the "less than or equal to" relation on numbers
    that we briefly saw above. *)

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)                : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m" := (le n m).

(** (We've written the definition a bit differently this time,
    giving explicit names to the arguments to the constructors and
    moving them to the left of the colons.) *)

(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] above. We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) ->
    2+2=5].) *)

(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

Definition lt (n m : nat) := le (S n) m.

Notation "m < n" := (lt m n).

End Playground.

(** **** Exercise: 2 stars, standard, optional (total_relation)

    Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

Inductive total_relation : nat -> nat -> Prop :=
  | tr_n (n : nat) : total_relation n n
  | tr_Sl (n m : nat) (H : total_relation n m) : total_relation (S n) m
  | tr_Sr (n m : nat) (H : total_relation n m) : total_relation n (S m)
.

Theorem total_relation_is_total : forall n m, total_relation n m.
  Proof.
    intros n m.
    induction n.
    - induction m.
      + apply (tr_n 0).
      + apply tr_Sr. apply IHm.
    - apply tr_Sl. apply IHn.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (empty_relation)

    Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

Inductive empty_relation : nat -> nat -> Prop :=
  | er_Sl (n m : nat) (H : empty_relation n m) : empty_relation (S n) m
  | er_Sr (n m : nat) (H : empty_relation n m) : empty_relation n (S m)
.

Theorem empty_relation_is_empty : forall n m, ~ empty_relation n m.
  Proof.
    intros n m ER.
    induction n.
    - induction m.
      + inversion ER.
      + inversion ER. apply (IHm H1).
    - induction m.
      + inversion ER. apply (IHn H0).
      + inversion ER.
        * apply (IHn H0).
        * destruct IHm.
          -- apply H1.
          -- intros. destruct IHn. apply (er_Sr n m ER0).
Qed.
(** [] *)

(** From the definition of [le], we can sketch the behaviors of
    [destruct], [inversion], and [induction] on a hypothesis [H]
    providing evidence of the form [le e1 e2].  Doing [destruct H]
    will generate two cases. In the first case, [e1 = e2], and it
    will replace instances of [e2] with [e1] in the goal and context.
    In the second case, [e2 = S n'] for some [n'] for which [le e1 n']
    holds, and it will replace instances of [e2] with [S n'].
    Doing [inversion H] will remove impossible cases and add generated
    equalities to the context for further use. Doing [induction H]
    will, in the second case, add the induction hypothesis that the
    goal holds when [e2] is replaced with [n']. *)

(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

(** **** Exercise: 5 stars, standard, optional (le_and_lt_facts) *)
Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o Hmn Hno.
  induction Hno as [ | x Hnx IH ].
  - apply Hmn.
  - apply le_S. apply IH.
  (* induction o.
  - intros. inversion H0. rewrite <- H1. apply H.
  - intros. inversion H0.
    + rewrite <- H1. apply H.
    + apply le_S. apply (IHo H H2). *)
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  induction n.
  - apply le_n.
  - apply le_S. apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H.
  induction H as [ | x H IH].
  - apply le_n.
  - apply le_S. apply IH.
  (* intros. induction m.
  - inversion H. apply le_n.
  - inversion H.
    + apply le_n.
    + apply le_S. apply (IHm H1). *)
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H. inversion H as [ H' | x H' H''].
  - apply le_n.
  - apply le_trans with (n:=S n).
    + apply le_S. apply le_n.
    + apply H'.
  (* intros. induction m.
  - inversion H.
    + apply le_n.
    + inversion H1.
  - inversion H.
    + apply le_n.
    + apply le_S. apply (IHm H1). *)
Qed.

Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
  induction m.
  - right. cbv. apply O_le_n.
  - inversion IHm.
    + left. apply le_S. apply H.
    + inversion H.
      * left. cbv. apply le_n.
      * right. cbv. apply n_le_m__Sn_le_Sm. apply H0.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  induction b.
  - rewrite add_0_r. apply le_n.
  - rewrite add_comm. simpl. apply le_S. rewrite add_comm. apply IHb.
Qed.

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
  intros. induction H.
  - split.
    + apply le_plus_l.
    + rewrite add_comm. apply le_plus_l.
  - inversion IHle. split.
    + apply le_S. apply H0.
    + apply le_S. apply H1.
  (* induction m.
  - intros H. inversion H.
    (* Search (?x + ?y = 0). *)
    apply and_exercise in H1. split.
    + apply le_plus_l.
    + rewrite add_comm. apply le_plus_l.
  - intros. inversion H.
    + split.
      * apply le_plus_l.
      * rewrite add_comm. apply le_plus_l.
    + apply IHm in H1. inversion H1. split.
      * apply le_S. apply H2.
      * apply le_S. apply H3. *)
Qed.

Lemma add_cancel_l : forall m n p,
  m + n = m + p -> n = p.
Proof.
  intros. induction m.
  - apply H.
  - simpl in H. injection H. apply IHm.
Qed.

Lemma add_le_elim : forall m n p,
  m + n <= m + p -> n <= p.
Proof.
  intros. induction m.
  - apply H.
  - simpl in H. apply Sn_le_Sm__n_le_m in H. apply (IHm H).
Qed.

Theorem add_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
  (** Hint: May be easiest to prove by induction on [n]. *)
Proof.
  induction n.
  - intros. left. apply O_le_n.
  - intros.
    assert (n + m <= S n + m).
    { simpl. apply le_S. apply le_n. }
    apply (le_trans _ _ _ H0) in H as H'.
    apply IHn in H' as H''. destruct H''.
    + inversion H1.
      * right. rewrite H2 in H'. apply add_le_elim in H'. apply H'.
      * left. apply n_le_m__Sn_le_Sm. apply H2.
    + right. apply H1.
Qed.

Theorem plus_le_compat_l : forall n m p,
  n <= m ->
  p + n <= p + m.
Proof.
  intros. induction H.
  - apply le_n.
  - rewrite (add_comm p (S m)). simpl. apply le_S.
    rewrite (add_comm m p). apply IHle.
  (* induction p.
  - intros. assumption.
  - intros. simpl. apply n_le_m__Sn_le_Sm. apply (IHp H). *)
Qed.

Theorem plus_le_compat_r : forall n m p,
  n <= m ->
  n + p <= m + p.
Proof.
  intros. rewrite (add_comm n p). rewrite (add_comm m p).
  apply plus_le_compat_l. apply H.
Qed.

Theorem le_plus_trans : forall n m p,
  n <= m ->
  n <= m + p.
Proof.
  intros. induction H.
  - apply le_plus_l.
  - simpl. apply le_S. apply IHle.
  (* induction p.
  - intros. rewrite add_0_r. assumption.
  - intros. apply IHp in H.
    assert (m + p <= m + S p).
    { apply plus_le_compat_l. apply le_S. apply le_n. }
    apply (le_trans _ _ _ H H0). *)
Qed.

Theorem n_lt_m__n_le_m : forall n m,
  n < m ->
  n <= m.
Proof.
  intros. induction H.
  - apply le_S. apply le_n.
  - apply le_S. apply IHle.
  (* intros. unfold lt in H.
  assert (n <= S n).
  { apply le_S. apply le_n. }
  apply (le_trans _ _ _ H0 H). *)
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  unfold lt. intros. split.
  - rewrite add_comm in H. rewrite plus_n_Sm in H.
    apply plus_le in H. inversion H. apply H1.
  - rewrite plus_n_Sm in H.
    apply plus_le in H. inversion H. apply H1.
Qed.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (more_le_exercises) *)
Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  intros. apply leb_plus_exists in H. inversion H.
  rewrite H0. apply le_plus_l.
Qed.

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
  (** Hint: May be easiest to prove by induction on [m]. *) (* -_- *)
Proof.
  intros. apply plus_exists_leb.
  induction H.
  - exists 0. rewrite add_0_r. reflexivity.
  - inversion IHle. exists (S x).
    rewrite <- plus_n_Sm. f_equal. apply H0.
  (* induction m.
  - inversion H. exists 0. reflexivity.
  - inversion H.
    + exists 0. rewrite add_0_r. reflexivity.
    + apply IHm in H1. inversion H1. exists (S x).
      rewrite add_comm. simpl. f_equal. rewrite add_comm. apply H2. *)
Qed.

(** Hint: The next two can easily be proved without using [induction]. *)

Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  split.
  - apply leb_complete.
  - apply leb_correct.
Qed.

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros n m o.
  rewrite (leb_iff n m). rewrite (leb_iff m o). rewrite (leb_iff n o).
  apply (le_trans _ _ _).
Qed.
(** [] *)

Module R.

(** **** Exercise: 3 stars, standard, especially useful (R_provability)

    We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
  | c1                                     : R 0     0     0
  | c2 m n o (H : R m     n     o        ) : R (S m) n     (S o)
  | c3 m n o (H : R m     n     o        ) : R m     (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m     n     o
  | c5 m n o (H : R m     n     o        ) : R n     m     o
.

(** - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer. *)

(* First is provable, the second is not.
   No.
   No.
   All provable proposition can be generated with [c1], [c2] and [c3]. *)

(* Do not modify the following line: *)
Definition manual_grade_for_R_provability : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (R_fact)

    The relation [R] above actually encodes a familiar function.
    Figure out which function; then state and prove this equivalence
    in Coq. *)

Definition fR : nat -> nat -> nat :=
  fun m n => m + n.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
  unfold fR. split.
  - intros. induction H.
    + reflexivity.
    + simpl. f_equal. apply IHR.
    + rewrite <- plus_n_Sm. simpl. f_equal. apply IHR.
    + simpl in IHR. injection IHR as H'.
      rewrite <- plus_n_Sm in H'. injection H' as H'. apply H'.
    + rewrite add_comm. apply IHR.
  - intros. induction H.
    induction m.
    + induction n.
      * apply c1.
      * apply c3. apply IHn.
    + simpl. apply c2. apply IHm.
Qed.
(** [] *)

End R.

(** **** Exercise: 3 stars, advanced (subsequence)

    A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,

      [1;2;3]

    is a subsequence of each of the lists

      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]

    but it is _not_ a subsequence of any of the lists

      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove [subseq_refl] that subsequence is reflexive, that is,
      any list is a subsequence of itself.

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3],
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Harder) Prove [subseq_trans] that subsequence is
      transitive -- that is, if [l1] is a subsequence of [l2] and [l2]
      is a subsequence of [l3], then [l1] is a subsequence of [l3]. *)

Inductive subseq : list nat -> list nat -> Prop :=
  | ss_nil : subseq [] []
  | ss_cons_r l1 l2 n (H: subseq l1 l2) : subseq l1 (n :: l2)
  | ss_cons_a l1 l2 n (H: subseq l1 l2) : subseq (n :: l1) (n :: l2)
.

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  induction l.
  - apply ss_nil.
  - apply ss_cons_a. apply IHl.
Qed.

Lemma subseq_empty : forall (l : list nat), subseq [] l.
Proof.
  intros. induction l.
  - apply ss_nil.
  - apply ss_cons_r. apply IHl.
Qed.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  intros. induction H as [ | l1 l2 n H IH | l1 l2 n H IH].
  - simpl. apply subseq_empty.
  - simpl. apply ss_cons_r. apply IH.
  - simpl. apply ss_cons_a. apply IH.
Qed.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  (* Hint: be careful about what you are doing induction on and which
     other things need to be generalized... *)
  intros. generalize dependent l1.   (* Important! *)
  induction H0.
  - intros. apply H.
  - intros. apply ss_cons_r. apply (IHsubseq _ H).
  - intros. inversion H.
    + apply ss_cons_r. apply (IHsubseq _ H3).
    + apply ss_cons_a. apply (IHsubseq _ H3).
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (R_provability2)

    Suppose we give Coq the following definition:

    Inductive R : nat -> list nat -> Prop :=
      | c1                    : R 0     []
      | c2 n l (H: R n     l) : R (S n) (n :: l)
      | c3 n l (H: R (S n) l) : R n     l.

    Which of the following propositions are provable?

    - [R 2 [1;0]]
    - [R 1 [1;2;1;0]]
    - [R 6 [3;2;1;0]]  *)

Module R2.

Inductive R : nat -> list nat -> Prop :=
  | c1                    : R 0     []
  | c2 n l (H: R n     l) : R (S n) (n :: l)
  | c3 n l (H: R (S n) l) : R n     l.

Example ex1 : R 2 [1;0].
Proof.
  apply c2. apply c2. apply c1.
Qed.

Example ex2 : R 1 [1;2;1;0].
Proof.
  apply c3. apply c2.
  apply c3. apply c3. apply c2.
  apply c2. apply c2. apply c1.
Qed.

Example ex3 : R 6 [3;2;1;0].
Abort.

Example ex4 : R 3 [2;0].
Proof.
  apply c2.
Abort.

End R2.

(* [R n l] which is provable requires [n <= S (hd l)] and [i <= (S j)]
   where [i] and [j] are arbitrary neighbouring elements in [l].

    [] *)

(* ################################################################# *)
(** * A Digression on Notation *)

(** There are several equivalent ways of writing inductive
    types.  We've mostly seen this style... *)

Module bin1.
Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).
End bin1.

(** ... which omits the result types because they are all bin. *)

(** It is completely equivalent to this... *)
Module bin2.
Inductive bin : Type :=
  | Z : bin
  | B0 (n : bin) : bin
  | B1 (n : bin) : bin.
End bin2.

(** ... where we fill them in, and this... *)

Module bin3.
Inductive bin : Type :=
  | Z : bin
  | B0 : bin -> bin
  | B1 : bin -> bin.
End bin3.

(** ... where we put everything on the right of the colon. *)

(** For inductively defined _propositions_, we need to explicitly give
    the result type for each constructor (because they are not all the
    same), so the first style doesn't make sense, but we can use
    either the second or the third interchangeably. *)

(* ################################################################# *)
(** * Case Study: Regular Expressions *)

(** The [ev] property provides a simple example for
    illustrating inductive definitions and the basic techniques for
    reasoning about them, but it is not terribly exciting -- after
    all, it is equivalent to the two non-inductive definitions of
    evenness that we had already seen, and does not seem to offer any
    concrete benefit over them.

    To give a better sense of the power of inductive definitions, we
    now show how to use them to model a classic concept in computer
    science: _regular expressions_. *)

(** Regular expressions are a simple language for describing sets of
    strings.  Their syntax is defined as follows: *)

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

(** Note that this definition is _polymorphic_: Regular
    expressions in [reg_exp T] describe strings with characters drawn
    from [T] -- that is, lists of elements of [T].

    (Technical aside: We depart slightly from standard practice in
    that we do not require the type [T] to be finite.  This results in
    a somewhat different theory of regular expressions, but the
    difference is not significant for present purposes.) *)

(** We connect regular expressions and strings via the following
    rules, which define when a regular expression _matches_ some
    string:

      - The expression [EmptySet] does not match any string.

      - The expression [EmptyStr] matches the empty string [[]].

      - The expression [Char x] matches the one-character string [[x]].

      - If [re1] matches [s1], and [re2] matches [s2],
        then [App re1 re2] matches [s1 ++ s2].

      - If at least one of [re1] and [re2] matches [s],
        then [Union re1 re2] matches [s].

      - Finally, if we can write some string [s] as the concatenation
        of a sequence of strings [s = s_1 ++ ... ++ s_k], and the
        expression [re] matches each one of the strings [s_i],
        then [Star re] matches [s].

        In particular, the sequence of strings may be empty, so
        [Star re] always matches the empty string [[]] no matter what
        [re] is. *)

(** We can easily translate this informal definition into an
    [Inductive] one as follows.  We use the notation [s =~ re] in
    place of [exp_match s re].  (By "reserving" the notation before
    defining the [Inductive], we can use it in the definition.) *)

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)

  where "s =~ re" := (exp_match s re).

(** Notice that these rules are not _quite_ the same as the
    informal ones that we gave at the beginning of the section.
    First, we don't need to include a rule explicitly stating that no
    string matches [EmptySet]; we just don't happen to include any
    rule that would have the effect of some string matching
    [EmptySet].  (Indeed, the syntax of inductive definitions doesn't
    even _allow_ us to give such a "negative rule.")

    Second, the informal rules for [Union] and [Star] correspond
    to two constructors each: [MUnionL] / [MUnionR], and [MStar0] /
    [MStarApp].  The result is logically equivalent to the original
    rules but more convenient to use in Coq, since the recursive
    occurrences of [exp_match] are given as direct arguments to the
    constructors, making it easier to perform induction on evidence.
    (The [exp_match_ex1] and [exp_match_ex2] exercises below ask you
    to prove that the constructors given in the inductive declaration
    and the ones that would arise from a more literal transcription of
    the informal rules are indeed equivalent.)

    Let's illustrate these rules with a few examples. *)

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1]).
  - apply MChar.
  - apply MChar.
Qed.

(** (Notice how the last example applies [MApp] to the string
    [[1]] directly.  Since the goal mentions [[1; 2]] instead of
    [[1] ++ [2]], Coq wouldn't be able to figure out how to split
    the string on its own.)

    Using [inversion], we can also show that certain strings do _not_
    match a regular expression: *)

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

(** We can define helper functions for writing down regular
    expressions. The [reg_exp_of_list] function constructs a regular
    expression that matches exactly the list that it receives as an
    argument: *)

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

(** We can also prove general facts about [exp_match].  For instance,
    the following lemma shows that every string [s] that matches [re]
    also matches [Star re]. *)

Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply MStarApp.
  - apply H.
  - apply MStar0.
Qed.

(** (Note the use of [app_nil_r] to change the goal of the theorem to
    exactly the same shape expected by [MStarApp].) *)

(** **** Exercise: 3 stars, standard (exp_match_ex1)

    The following lemmas show that the informal matching rules given
    at the beginning of the chapter can be obtained from the formal
    inductive definition. *)

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s H.
  inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros.
  inversion H.
  - apply (MUnionL _ _ _ H0).
  - apply (MUnionR _ _ _ H0).
Qed.

(** The next lemma is stated in terms of the [fold] function from the
    [Poly] chapter: If [ss : list (list T)] represents a sequence of
    strings [s1, ..., sn], then [fold app ss []] is the result of
    concatenating them all together. *)

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros.
  induction ss.
  - simpl. apply MStar0.
  - simpl. apply MStarApp.
    + apply H. simpl. left. reflexivity.
    + apply IHss. intros. apply H. simpl. right. apply H0.
Qed.
(** [] *)

(** Since the definition of [exp_match] has a recursive
    structure, we might expect that proofs involving regular
    expressions will often require induction on evidence. *)

(** For example, suppose we want to prove the following intuitive
    result: If a regular expression [re] matches some string [s], then
    all elements of [s] must occur as character literals somewhere in
    [re].

    To state this as a theorem, we first define a function [re_chars]
    that lists all characters that occur in a regular expression: *)

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

(** The main theorem: *)

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    simpl in Hin. destruct Hin.
  - (* MChar *)
    simpl. simpl in Hin.
    apply Hin.
  - (* MApp *)
    simpl.

(** Something interesting happens in the [MApp] case.  We obtain
    _two_ induction hypotheses: One that applies when [x] occurs in
    [s1] (which matches [re1]), and a second one that applies when [x]
    occurs in [s2] (which matches [re2]). *)

    rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    simpl.

(** Here again we get two induction hypotheses, and they illustrate
    why we need induction on evidence for [exp_match], rather than
    induction on the regular expression [re]: The latter would only
    provide an induction hypothesis for strings that match [re], which
    would not allow us to reason about the case [In x s2]. *)

    rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

(** **** Exercise: 4 stars, standard (re_not_empty)

    Write a recursive function [re_not_empty] that tests whether a
    regular expression matches some string. Prove that your function
    is correct. *)

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr | Char _ => true
  | App r1 r2 => re_not_empty r1 && re_not_empty r2
  | Union r1 r2 => re_not_empty r1 || re_not_empty r2
  | Star r => true
  end.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  split.
  - intros. induction re.
    + inversion H. inversion H0.
    + reflexivity.
    + reflexivity.
    + simpl.
      (* Search (?x && ?y = true). *)
      rewrite andb_true_iff. split.
      * apply IHre1. inversion H. inversion H0. exists s1. apply H4.
      * apply IHre2. inversion H. inversion H0. exists s2. apply H5.
    + simpl. rewrite orb_true_iff. inversion H. inversion H0.
      * left. apply IHre1. exists x. apply H3.
      * right. apply IHre2. exists x. apply H3.
    + reflexivity.
  - intros. induction re.
    + inversion H.
    + exists []. apply MEmpty.
    + exists [t]. apply MChar.
    + inversion H. apply andb_true_iff in H1. inversion H1.
      apply IHre1 in H0. apply IHre2 in H2.
      inversion H0. inversion H2.
      exists (x ++ x0). apply (MApp _ _ _ _ H3 H4).
    + inversion H. apply orb_true_iff in H1. inversion H1.
      * apply IHre1 in H0. inversion H0.
        exists x. apply (MUnionL _ _ _ H2).
      * apply IHre2 in H0. inversion H0.
        exists x. apply (MUnionR _ _ _ H2).
    + exists []. apply MStar0.
Qed.
(** [] *)

(* ================================================================= *)
(** ** The [remember] Tactic *)

(** One potentially confusing feature of the [induction] tactic is
    that it will let you try to perform an induction over a term that
    isn't sufficiently general.  The effect of this is to lose
    information (much as [destruct] without an [eqn:] clause can do),
    and leave you unable to complete the proof.  Here's an example: *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.

(** Now, just doing an [inversion] on [H1] won't get us very far in
    the recursive cases. (Try it!). So we need induction (on
    evidence!). Here is a naive first attempt.

    (We can begin by generalizing [s2], since it's pretty clear that we
    are going to have to walk over both [s1] and [s2] in parallel.) *)

  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** But now, although we get seven cases (as we would expect
    from the definition of [exp_match]), we have lost a very important
    bit of information from [H1]: the fact that [s1] matched something
    of the form [Star re].  This means that we have to give proofs for
    _all_ seven constructors of this definition, even though all but
    two of them ([MStar0] and [MStarApp]) are contradictory.  We can
    still get the proof to go through for a few constructors, such as
    [MEmpty]... *)

  - (* MEmpty *)
    simpl. intros s2 H. apply H.

(** ... but most cases get stuck.  For [MChar], for instance, we
    must show

      s2     =~ Char x' ->
      x'::s2 =~ Char x'

    which is clearly impossible. *)

  - (* MChar. *) intros s2 H. simpl. (* Stuck... *)
Abort.

(** The problem here is that [induction] over a Prop hypothesis
    only works properly with hypotheses that are "completely
    general," i.e., ones in which all the arguments are variables,
    as opposed to more complex expressions like [Star re].

    (In this respect, [induction] on evidence behaves more like
    [destruct]-without-[eqn:] than like [inversion].)

    A possible, but awkward, way to solve this problem is "manually
    generalizing" over the problematic expressions by adding
    explicit equality hypotheses to the lemma: *)

Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp T),
  re' = Star re ->
  s1 =~ re' ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.

(** We can now proceed by performing induction over evidence
    directly, because the argument to the first hypothesis is
    sufficiently general, which means that we can discharge most cases
    by inverting the [re' = Star re] equality in the context.

    This works, but it makes the statement of the lemma a bit ugly.
    Fortunately, there is a better way... *)
Abort.

(** The tactic [remember e as x] causes Coq to (1) replace all
    occurrences of the expression [e] by the variable [x], and (2) add
    an equation [x = e] to the context.  Here's how we can use it to
    show the above result: *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.

(** We now have [Heqre' : re' = Star re]. *)

  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** The [Heqre'] is contradictory in most cases, allowing us to
    conclude immediately. *)

  - (* MEmpty *)  discriminate.
  - (* MChar *)   discriminate.
  - (* MApp *)    discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.

(** The interesting cases are those that correspond to [Star].  Note
    that the induction hypothesis [IH2] on the [MStarApp] case
    mentions an additional premise [Star re'' = Star re], which
    results from the equality generated by [remember]. *)

  - (* MStar0 *)
    injection Heqre' as Heqre''. intros s H. apply H.

  - (* MStarApp *)
    injection Heqre' as Heqre''.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * rewrite Heqre''. reflexivity.
      * apply H1.
Qed.

(** **** Exercise: 4 stars, standard, optional (exp_match_ex2) *)

(** The [MStar''] lemma below (combined with its converse, the
    [MStar'] exercise above), shows that our definition of [exp_match]
    for [Star] is equivalent to the informal one given previously. *)

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re H. remember (Star re) as re' eqn:E.
  (* generalize dependent s. *)
  (* induction re'.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - exists [s]. split.
    + simpl. symmetry. apply app_nil_r.
    + intros. simpl in H0. destruct H0 as [H0 | []]. *)
  induction H
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2 | s1 re1 re2 Hmatch1 IH1
         | re1 s2 re2 Hmatch2 IH2 | re'' | s1 s2 re'' Hmatch1 IH1 Hmatch2 IH2 ].
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - exists []. split.
    + reflexivity.
    + intros. inversion H.
  - injection E as E'. rewrite E' in *.
    destruct IH2 as [ss' [IH21 IH22]].    (* [destruct IH2] before [exists] ! *)
    { reflexivity. }
    exists (s1::ss').    (* not [exists [s1;s2]] ! *)
    simpl. split.
    + rewrite <- IH21. reflexivity.
    + intros s' H. destruct H.
      * rewrite <- H. apply Hmatch1.
      * apply (IH22 _ H).
Qed.
(** [] *)

(** **** Exercise: 5 stars, advanced (weak_pumping)

    One of the first really interesting theorems in the theory of
    regular expressions is the so-called _pumping lemma_, which
    states, informally, that any sufficiently long string [s] matching
    a regular expression [re] can be "pumped" by repeating some middle
    section of [s] an arbitrary number of times to produce a new
    string also matching [re].  (For the sake of simplicity in this
    exercise, we consider a slightly weaker theorem than is usually
    stated in courses on automata theory -- hence the name
    [weak_pumping].)

    To get started, we need to define "sufficiently long."  Since we
    are working in a constructive logic, we actually need to be able
    to calculate, for each regular expression [re], the minimum length
    for strings [s] to guarantee "pumpability." *)

Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end.

(** You may find these lemmas about the pumping constant useful when
    proving the pumping lemma below. *)

Lemma pumping_constant_ge_1 :
  forall T (re : reg_exp T),
    pumping_constant re >= 1.
Proof.
  intros T re. induction re.
  - (* EmptySet *)
    apply le_n.
  - (* EmptyStr *)
    apply le_n.
  - (* Char *)
    apply le_S. apply le_n.
  - (* App *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Union *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Star *)
    simpl. apply IHre.
Qed.

Lemma pumping_constant_0_false :
  forall T (re : reg_exp T),
    pumping_constant re = 0 -> False.
Proof.
  intros T re H.
  assert (Hp1 : pumping_constant re >= 1).
  { apply pumping_constant_ge_1. }
  inversion Hp1 as [Hp1'| p Hp1' Hp1''].
  - rewrite H in Hp1'. discriminate Hp1'.
  - rewrite H in Hp1''. discriminate Hp1''.
Qed.

(** Next, it is useful to define an auxiliary function that repeats a
    string (appends it to itself) some number of times. *)

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

(** This auxiliary lemma might also be useful in your proof of the
    pumping lemma. *)

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma napp_star :
  forall T m s1 s2 (re : reg_exp T),
    s1 =~ re -> s2 =~ Star re ->
    napp m s1 ++ s2 =~ Star re.
Proof.
  intros T m s1 s2 re Hs1 Hs2.
  induction m.
  - simpl. apply Hs2.
  - simpl. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hs1.
    + apply IHm.
Qed.

(** The (weak) pumping lemma itself says that, if [s =~ re] and if the
    length of [s] is at least the pumping constant of [re], then [s]
    can be split into three substrings [s1 ++ s2 ++ s3] in such a way
    that [s2] can be repeated any number of times and the result, when
    combined with [s1] and [s3], will still match [re].  Since [s2] is
    also guaranteed not to be the empty string, this gives us
    a (constructive!) way to generate strings matching [re] that are
    as long as we like. *)

Lemma weak_pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** Complete the proof below. Several of the lemmas about [le] that
    were in an optional exercise earlier in this chapter may also be
    useful. *)
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl.
    (* intros contra. inversion contra. *)
    lia.
  - (* MChar *)
    simpl.
    (* intros contra. inversion contra. inversion H0. *)
    lia.
  - (* MApp *)
    simpl. intros H.
    (* Search (length (_ ++ _)). *)
    rewrite app_length in H.
    (* Search (_ + _ <= _ + _). *)
    apply add_le_cases in H. destruct H.
    + destruct (IH1 H) as [s2' [s3' [s4' [L [N R]]]]].
      exists s2', s3', (s4'++s2). split.
      * rewrite L. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
      * split. apply N. intros m. rewrite app_assoc. rewrite app_assoc.
        apply MApp. rewrite <- app_assoc. apply R. apply Hmatch2.
    + destruct (IH2 H) as [s2' [s3' [s4' [L [N R]]]]].
      exists (s1++s2'), s3', s4'. split.
      * rewrite L. rewrite <- app_assoc. reflexivity.
      * split. apply N. intros m. rewrite <- app_assoc.
        apply MApp. apply Hmatch1. apply R.
  - (* MUnionL *)
    simpl. intros H.
    (* apply le_trans with (m:=(pumping_constant re1)) in H. *)
    assert (H': pumping_constant re1 <= length s1).
      { apply le_trans with (n:=(pumping_constant re1 + pumping_constant re2)).
        (* Search (?x <= ?x + ?y). *)
        apply le_plus_l. apply H. }
    destruct (IH H') as [s2' [s3' [s4' [L [N R]]]]].
    exists s2', s3', s4'. split.
    + apply L.
    + split. apply N. intros m. apply MUnionL. apply R.
  - (* MUnionR *)
    simpl. intros H.
    assert (H': pumping_constant re2 <= length s2).
      { apply le_trans with (n:=(pumping_constant re1 + pumping_constant re2)).
        rewrite add_comm. apply le_plus_l. apply H. }
    destruct (IH H') as [s1' [s3' [s4' [L [N R]]]]].
    exists s1', s3', s4'. split.
    + apply L.
    + split. apply N. intros m. apply MUnionR. apply R.
  - (* MStar0 *)
    simpl. intros contra. inversion contra.
    (* apply pumping_constant_0_false in H0. destruct H0. *)
    destruct (pumping_constant_0_false _ _ H0).
  - (* MStarApp *)
    (* First: We cannot derive [a<=b] or [a<=c] from [a<=b+c],
              so [IH1] and [IH2] here cannot be used in the general case.
       Second: Given [napp_star], we can see that if we initialize with
               [exists [], s1, s2], we can just get the last consequence
               without using [IH1] and [IH2]. The only problem is that we
               cannot promise that [s1] is not empty.
       Third: To solve the problem above, we can just [destruct s1].
              The base case can be proved by [IH2], the step case guarantees
              the non-emptiness. *)
    destruct s1.
    + intros H. apply (IH2 H).
    + intros _. exists [], (x::s1), s2. split.
      * reflexivity.
      * split.
        -- discriminate.
        -- intros m. simpl.
           apply (napp_star _ _ _ _ _ Hmatch1 Hmatch2).
Qed.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (pumping)

    Now here is the usual version of the pumping lemma. In addition to
    requiring that [s2 <> []], it also requires that [length s1 +
    length s2 <= pumping_constant re]. *)

Lemma add_le_mono : forall n m p q, n <= m -> p <= q -> n + p <= m + q.
Proof.
  intros n m p q Hnm Hpq.
  (* Search (?x <= ?y -> ?x + ?z <= ?y + ?z). *)
  apply le_trans with (n:=m+p).
  - apply plus_le_compat_r. apply Hnm.
  - apply plus_le_compat_l. apply Hpq.
Qed.

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    length s1 + length s2 <= pumping_constant re /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** You may want to copy your proof of weak_pumping below. *)
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  - (* MChar *)
    simpl. intros contra. inversion contra. inversion H0.
  - (* MApp *)
    simpl. intros H.
    rewrite app_length in H.
    apply add_le_cases in H. destruct H.
    + destruct (IH1 H) as [s2' [s3' [s4' [L [N [C R]]]]]].
      exists s2', s3', (s4'++s2). split.
      * rewrite L. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
      * split. apply N. split.
        -- apply le_trans with (n:=(pumping_constant re1)).
           ++ apply C.
           ++ apply le_plus_l.
        -- intros m. rewrite app_assoc. rewrite app_assoc.
          apply MApp. rewrite <- app_assoc. apply R. apply Hmatch2.
    + destruct (IH2 H) as [s2' [s3' [s4' [L [N [C R]]]]]].
      (* Difference from weak_pumping:
           We need to get one more consequence about length and prompint
           constant, which cannot be proved directly. So we divide it into
           two pieces: one case is that the comparation is just satisfied,
           another case is not, but we can use [IH] to find a new instantiation
           like above, where the comparation is easy to prove. *)
      assert (C':
        length s1 < pumping_constant re1 \/ length s1 >= pumping_constant re1
      ).
      { apply lt_ge_cases. }
      destruct C' as [C1| C2].
      * exists (s1++s2'), s3', s4'. split.
        ** rewrite L. rewrite <- app_assoc. reflexivity.
        ** split. apply N. split.
           -- rewrite app_length.
              (* Search (?x < ?y -> ?x <= ?y). *)
              apply n_lt_m__n_le_m in C1.
              (* Search (?a <= ?b -> ?c <= ?d -> ?a + ?c <= ?b + ?d). *)
              rewrite <- add_assoc. apply add_le_mono.
              apply C1. apply C.
           -- intros m. rewrite <- app_assoc.
              apply MApp. apply Hmatch1. apply R.
      * destruct (IH1 C2) as [s2'' [s3'' [s4'' [L' [N' [C' R']]]]]].
        exists s2'', s3'', (s4''++s2). split.
        -- rewrite L'. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
        -- split. apply N'. split.
           ++ apply le_trans with (n:=(pumping_constant re1)).
              ** apply C'.
              ** apply le_plus_l.
           ++ intros m. rewrite app_assoc. rewrite app_assoc.
              apply MApp. rewrite <- app_assoc. apply R'. apply Hmatch2.
  - (* MUnionL *)
    simpl. intros H.
    assert (H': pumping_constant re1 <= length s1).
      { apply le_trans with (n:=(pumping_constant re1 + pumping_constant re2)).
        apply le_plus_l. apply H. }
    destruct (IH H') as [s2' [s3' [s4' [L [N [C R]]]]]].
    exists s2', s3', s4'. split.
    + apply L.
    + split. apply N. split.
      * apply le_trans with (n:=(pumping_constant re1)).
        -- apply C.
        -- apply le_plus_l.
      * intros m. apply MUnionL. apply R.
  - (* MUnionR *)
    simpl. intros H.
    assert (H': pumping_constant re2 <= length s2).
      { apply le_trans with (n:=(pumping_constant re1 + pumping_constant re2)).
        rewrite add_comm. apply le_plus_l. apply H. }
    destruct (IH H') as [s1' [s3' [s4' [L [N [C R]]]]]].
    exists s1', s3', s4'. split.
    + apply L.
    + split. apply N. split.
      * apply le_trans with (n:=(pumping_constant re2)).
        -- apply C.
        -- rewrite add_comm. apply le_plus_l.
      * intros m. apply MUnionR. apply R.
  - (* MStar0 *)
    simpl. intros contra. inversion contra.
    destruct (pumping_constant_0_false _ _ H0).
  - (* MStarApp *)
  intros H. destruct s1.
    + apply (IH2 H).
    + (* Difference from weak_pumping: Same with MApp. *)
      assert (C':
        length (x::s1) < pumping_constant re \/ length (x::s1) >= pumping_constant re
      ).
      { apply lt_ge_cases. }
      destruct C' as [C1 | C2].
      * exists [], (x::s1), s2. split.
        -- reflexivity.
        -- split. discriminate. split.
           ++ apply n_lt_m__n_le_m. apply C1.
           ++ intros m. simpl.
              apply (napp_star _ _ _ _ _ Hmatch1 Hmatch2).
      * destruct (IH1 C2) as [s2' [s3' [s4' [L [N [C R]]]]]].
        exists s2', s3', (s4'++s2). split.
        -- rewrite L. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity.
        -- split. apply N. split.
           ++ simpl. apply C.
           ++ intros m. rewrite app_assoc. rewrite app_assoc.
              apply MStarApp.
              ** rewrite <- app_assoc. apply R.
              ** apply Hmatch2.
Qed.

End Pumping.
(** [] *)

(* ################################################################# *)
(** * Case Study: Improving Reflection *)

(** We've seen in the [Logic] chapter that we often need to
    relate boolean computations to statements in [Prop].  But
    performing this conversion as we did there can result in
    tedious proof scripts.  Consider the proof of the following
    theorem: *)

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (n =? m) eqn:H.
    + (* n =? m = true *)
      intros _. rewrite eqb_eq in H. rewrite H.
      left. reflexivity.
    + (* n =? m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** In the first branch after [destruct], we explicitly apply
    the [eqb_eq] lemma to the equation generated by
    destructing [n =? m], to convert the assumption [n =? m
    = true] into the assumption [n = m]; then we had to [rewrite]
    using this assumption to complete the case. *)

(** We can streamline this sort of reasoning by defining an inductive
    proposition that yields a better case-analysis principle for [n =?
    m].  Instead of generating the assumption [(n =? m) = true], which
    usually requires some massaging before we can use it, this
    principle gives us right away the assumption we really need: [n =
    m].

    Following the terminology introduced in [Logic], we call this
    the "reflection principle for equality on numbers," and we say
    that the boolean [n =? m] is _reflected in_ the proposition [n =
    m]. *)

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT (H :   P) : reflect P true
  | ReflectF (H : ~ P) : reflect P false.

(** The [reflect] property takes two arguments: a proposition
    [P] and a boolean [b].  It states that the property [P]
    _reflects_ (intuitively, is equivalent to) the boolean [b]: that
    is, [P] holds if and only if [b = true].

    To see this, notice that, by definition, the only way we can
    produce evidence for [reflect P true] is by showing [P] and then
    using the [ReflectT] constructor.  If we invert this statement,
    this means that we can extract evidence for [P] from a proof of
    [reflect P true].

    Similarly, the only way to show [reflect P false] is by tagging
    evidence for [~ P] with the [ReflectF] constructor. *)

(** To put this observation to work, we first prove that the
    statements [P <-> b = true] and [reflect P b] are indeed
    equivalent.  First, the left-to-right implication: *)

(* Search (_ <-> _ = true).
   ==> restricted_excluded_middle :
         forall (P : Prop) (b : bool), P <-> b = true -> P \/ ~ P *)

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b eqn:Eb.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

(** Now you prove the right-to-left implication: *)

(** **** Exercise: 2 stars, standard, especially useful (reflect_iff) *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H. inversion H.
  - split.
    + intros _. reflexivity.
    + intros _. apply H0.
  - split.
    + intros Hp. apply H0 in Hp. destruct Hp.
    + intros contra. discriminate.
Qed.
(** [] *)

(** We can think of [reflect] as a kind of variant of the usual "if
    and only if" connective; the advantage of [reflect] is that, by
    destructing a hypothesis or lemma of the form [reflect P b], we
    can perform case analysis on [b] while _at the same time_
    generating appropriate hypothesis in the two branches ([P] in the
    first subgoal and [~ P] in the second). *)

(** Let's use [reflect] to produce a smoother proof of
    [filter_not_empty_In].

    We begin by recasting the [eqb_eq] lemma in terms of [reflect]: *)

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

(** The proof of [filter_not_empty_In] now goes as follows.  Notice
    how the calls to [destruct] and [rewrite] in the earlier proof of
    this theorem are combined here into a single call to
    [destruct]. *)

(** (To see this clearly, execute the two proofs of
    [filter_not_empty_In] with Coq and observe the differences in
    proof state at the beginning of the first case of the
    [destruct].) *)

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** **** Exercise: 3 stars, standard, especially useful (eqbP_practice)

    Use [eqbP] as above to prove the following: *)

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l Hcount. induction l as [| m l' IHl'].
  - simpl. intros Hf. destruct Hf.
  - simpl in *.
    destruct (eqbP n m) as [H | H].
    + discriminate.
    + intros Hf. destruct Hf as [Hf1 | Hf2].
      ** symmetry in Hf1. apply H in Hf1. destruct Hf1.
      ** apply (IHl' Hcount) in Hf2. destruct Hf2.
Qed.
(** [] *)

(** This small example shows reflection giving us a small gain in
    convenience; in larger developments, using [reflect] consistently
    can often lead to noticeably shorter and clearer proof scripts.
    We'll see many more examples in later chapters and in _Programming
    Language Foundations_.

    This use of [reflect] was popularized by _SSReflect_, a Coq
    library that has been used to formalize important results in
    mathematics, including the 4-color theorem and the Feit-Thompson
    theorem.  The name SSReflect stands for _small-scale reflection_,
    i.e., the pervasive use of reflection to simplify small proof
    steps by turning them into boolean computations. *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard, especially useful (nostutter_defn)

    Formulating inductive definitions of properties is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help.

    We say that a list "stutters" if it repeats the same element
    consecutively.  (This is different from not containing duplicates:
    the sequence [[1;4;1]] has two occurrences of the element [1] but
    does not stutter.)  The property "[nostutter mylist]" means that
    [mylist] does not stutter.  Formulate an inductive definition for
    [nostutter]. *)

Inductive nostutter {X:Type} : list X -> Prop :=
  | nostutter_nil : nostutter []
  (* | nostutter_one x : nostutter [x]
  | nostutter_cons x y l (H : nostutter (y :: l)) (H' : x = y) :
      nostutter (x :: y :: l) *)
  | nostutter_cons (x : X) (l : list X) (H : nostutter l)
      (H' : match l with [] => True | h :: t => x <> h end) :
      nostutter (x :: l)
.
(** Make sure each of these tests succeeds, but feel free to change
    the suggested proof (in comments) if the given one doesn't work
    for you.  Your definition might be different from ours and still
    be correct, in which case the examples might need a different
    proof.  (You'll notice that the suggested proofs use a number of
    tactics we haven't talked about, to make them more robust to
    different possible ways of defining [nostutter].  You can probably
    just uncomment and use them as-is, but you can also prove each
    example with more basic tactics.)  *)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof. repeat constructor; apply eqb_neq; auto.
Qed.

Example test_nostutter_2:  nostutter (@nil nat).
Proof. repeat constructor; apply eqb_neq; auto.
Qed.

Example test_nostutter_3:  nostutter [5].
Proof. repeat constructor; auto. Qed.

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
Proof. intro.
repeat match goal with
  h: nostutter _ |- _ => inversion h; clear h; subst
end.
contradiction; auto. Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_nostutter : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge)

    Let's prove that our definition of [filter] from the [Poly]
    chapter matches an abstract specification.  Here is the
    specification, written out informally in English:

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example,

    [1;4;6;2;3]

    is an in-order merge of

    [1;6;2]

    and

    [4;3].

    Now, suppose we have a set [X], a function [test: X->bool], and a
    list [l] of type [list X].  Suppose further that [l] is an
    in-order merge of two lists, [l1] and [l2], such that every item
    in [l1] satisfies [test] and no item in [l2] satisfies test.  Then
    [filter test l = l1].

    First define what it means for one list to be a merge of two
    others.  Do this with an inductive relation, not a [Fixpoint].  *)

Inductive merge {X:Type} : list X -> list X -> list X -> Prop :=
  | merge_nil : merge [] [] []
  | merge_cons_1 x l1 l2 l (H : merge l1 l2 l) : merge (x::l1) l2 (x::l)
  | merge_cons_2 x l1 l2 l (H : merge l1 l2 l) : merge l1 (x::l2) (x::l)
.

Example test_merge : merge [1;6;2] [4;3] [1;4;6;2;3].
Proof.
  repeat constructor.
Qed.

Theorem merge_filter : forall (X : Set) (test: X->bool) (l l1 l2 : list X),
  merge l1 l2 l ->
  All (fun n => test n = true) l1 ->
  All (fun n => test n = false) l2 ->
  filter test l = l1.
Proof.
  intros X test l l1 l2 H Hl1 Hl2.
  induction H as [ | x' l1' l2' l' H' IH | x' l1' l2' l' H' IH].
  - reflexivity.
  - simpl. destruct (test x') eqn:Htest.
    + f_equal. simpl in Hl1. destruct Hl1 as [H1 Hl1].
      apply (IH Hl1 Hl2).
    + simpl in Hl1. destruct Hl1 as [H1 Hl1].
      rewrite Htest in H1. discriminate.
  - simpl. destruct (test x') eqn:Htest.
    + simpl in Hl2. destruct Hl2 as [H2 Hl2].
      rewrite Htest in H2. discriminate.
    + simpl in Hl2. destruct Hl2 as [H2 Hl2].
      apply (IH Hl1 Hl2).
Qed.

(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2)

    A different way to characterize the behavior of [filter] goes like
    this: Among all subsequences of [l] with the property that [test]
    evaluates to [true] on all their members, [filter test l] is the
    longest.  Formalize this claim and prove it. *)

Lemma filter_subset : forall (X : Set) (test : X -> bool) (l1 l: list X),
  (exists l2, merge l1 l2 l) ->
  All (fun n => test n = true) l1 ->
  exists l3, merge l1 l3 (filter test l).
Proof.
  intros X test l1 l H Hl1.
  destruct H as [l2 H].
  exists (filter test l2).
  induction H as [ | x' l1' l2' l' H' IH | x' l1' l2' l' H' IH].
  - simpl. apply merge_nil.
  - simpl in *. destruct (test x') eqn:Htest.
    + destruct Hl1 as [_ Hl1]. apply merge_cons_1. apply (IH Hl1).
    + destruct Hl1 as [contra Hl1]. discriminate.
  - simpl in *. destruct (test x') eqn:Htest.
    + apply merge_cons_2. apply (IH Hl1).
    + apply (IH Hl1).
Qed.

Lemma merge_short : forall (X : Set) (test : X -> bool) (l1 l: list X),
  (exists l2, merge l1 l2 l) -> length l1 <= length l.
Proof.
  intros. destruct H as [l2 H].
  induction H as [ | x' l1' l2' l' H' IH | x' l1' l2' l' H' IH].
  - simpl. reflexivity.
  - simpl. apply n_le_m__Sn_le_Sm. apply IH.
  - simpl. apply le_trans with (n:=length l').
    + apply IH.
    + apply le_S. apply le_n.
Qed.

Theorem filter_longest : forall (X : Set) (test : X -> bool) (l1 l: list X),
  (exists l2, merge l1 l2 l) ->
  All (fun n => test n = true) l1 ->
  length l1 <= length (filter test l).
Proof.
  intros. apply (merge_short X test l1 (filter test l)).
  apply (filter_subset X test l1 l H H0).
Qed.

(* [] *)

(** **** Exercise: 4 stars, standard, optional (palindromes)

    A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor like

        c : forall l, l = rev l -> pal l

      may seem obvious, but will not work very well.)

    - Prove ([pal_app_rev]) that

       forall l, pal (l ++ rev l).

    - Prove ([pal_rev] that)

       forall l, pal l -> l = rev l.
*)

Inductive pal {X:Type} : list X -> Prop :=
  | pal_nil : pal []
  | pal_one x : pal [x]
  | pal_cons x l (H : pal l) : pal (x :: l ++ [x])
(* FILL IN HERE *)
.

Theorem pal_app_rev : forall (X:Type) (l : list X),
  pal (l ++ (rev l)).
Proof.
  intros.
  induction l as [ | n' l'].
  - simpl. apply pal_nil.
  - simpl. rewrite app_assoc. apply pal_cons. apply IHl'.
Qed.

Theorem pal_rev : forall (X:Type) (l: list X) , pal l -> l = rev l.
Proof.
  intros.
  induction H.
  - reflexivity.
  - reflexivity.
  - simpl.
    (* Search (rev (_ ++ _) = (rev _) ++ (rev _)). *)
    rewrite rev_app_distr.
    simpl. rewrite <- IHpal. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (palindrome_converse)

    Again, the converse direction is significantly more difficult, due
    to the lack of evidence.  Using your definition of [pal] from the
    previous exercise, prove that

     forall l, l = rev l -> pal l.
*)

Lemma head_eq_last : forall {X: Type} (l: list X),
  l = rev l -> l = [] \/ (exists x, l = [x]) \/ (exists x' l', l = x' :: l' ++ [x'] /\ l' = rev l').
Proof.
  intros.
  destruct l as [ | n' l'] eqn:Hl.
  - left. apply H.
  - right.
    replace (n'::l') with ([n']++l') in H.
    rewrite rev_app_distr in H. simpl in H.
    destruct (rev l') as [ | m l''] eqn:Hrevl'.
    + left. simpl in H. exists n'. apply H.
    + right. simpl in H. injection H as Heq H.
      rewrite Heq in *.
      exists m, l''. split.
      * f_equal. apply H.
      * (* Search (?x = ?y -> ?f ?x = ?f ?y). *)
        apply (f_equal _ _ rev) in Hrevl'.
        rewrite rev_involutive in Hrevl'.
        replace (m::l'') with ([m]++l'') in Hrevl'.
        rewrite rev_app_distr in Hrevl'.
        rewrite Hrevl' in H. simpl in H.
        apply (f_equal _ _ rev) in H.
        rewrite rev_app_distr in H.
        rewrite rev_app_distr in H.
        rewrite rev_involutive in H.
        simpl in H. injection H as H. apply H.
        { reflexivity. }
    + reflexivity.
Qed.

(* Important:
     1. induction on [length l] instead of [l].
     2. use the second induction instead of the first one,
        i.e. induction using [length l <= n] instead of [length l = n]. *)
Theorem palindrome_converse_length: forall {X: Type} (n: nat) (l: list X),
  length l <= n -> l = rev l -> pal l.
Proof.
  induction n.
  - intros. inversion H. destruct l.
    + apply pal_nil.
    + inversion H2.
  - intros.
    destruct (head_eq_last _ H0).
    + rewrite H1. apply pal_nil.
    + destruct H1.
      * inversion H1. rewrite H2. apply pal_one.
      * inversion H1 as [x [l']]. inversion H2.
        apply (f_equal _ _ length) in H3 as H3'.
        simpl in H3'. rewrite app_length in H3'.
        rewrite add_comm in H3'. simpl in H3'.
        rewrite H3' in H. apply Sn_le_Sm__n_le_m in H.
        apply le_trans with (m:=length l') in H.
        apply IHn in H.
        -- rewrite H3. apply pal_cons. apply H.
        -- apply H4.
        -- apply le_S. apply le_n.
Qed.

Theorem palindrome_converse: forall {X: Type} (l: list X),
    l = rev l -> pal l.
Proof.
  intros X l.
  apply (palindrome_converse_length (length l) l).
  apply le_n.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (NoDup)

    Recall the definition of the [In] property from the [Logic]
    chapter, which asserts that a value [x] appears at least once in a
    list [l]: *)

(* Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
   match l with
   | [] => False
   | x' :: l' => x' = x \/ In A x l'
   end *)

(** Your first task is to use [In] to define a proposition [disjoint X
    l1 l2], which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in
    common. *)

Definition disjoint {X: Type} (l1 l2 : list X) :=
  (forall x, In x l1 -> ~ (In x l2)) /\ (forall x, In x l2 -> ~ (In x l1)).

(** Next, use [In] to define an inductive proposition [NoDup X
    l], which should be provable exactly when [l] is a list (with
    elements of type [X]) where every member is different from every
    other.  For example, [NoDup nat [1;2;3;4]] and [NoDup
    bool []] should be provable, while [NoDup nat [1;2;1]] and
    [NoDup bool [true;true]] should not be.  *)

Inductive NoDup {X: Type} : list X ->Prop :=
  | nodup_nil : NoDup []
  | nodup_cons x l (Hx: ~ (In x l)) (H: NoDup l) : NoDup (x :: l)
.

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [NoDup] and [++] (list append).  *)

Theorem disjoint_app_nodup : forall (X: Type) (l1 l2 : list X),
  disjoint l1 l2 -> NoDup l1 -> NoDup l2 -> NoDup (l1 ++ l2).
Proof.
  intros X l1 l2 H H1 H2.
  destruct H as [H H'].
  induction H1.
  - apply H2.
  - simpl. apply nodup_cons.
    + rewrite In_app_iff. intro. destruct H0.
      * contradiction.
      * apply H in H0.
        -- contradiction.
        -- simpl. left. reflexivity.
    + apply IHNoDup.
      * intros. apply H. simpl. right. apply H0.
      * intros. apply H' in H0. simpl in H0.
        apply de_morgan_not_or in H0. destruct H0. apply H3.
Qed.

Theorem nodup_app_disjoint : forall (X: Type) (l1 l2 : list X),
  NoDup (l1 ++ l2) -> disjoint l1 l2.
Proof.
  intros.
  induction l1.
  - simpl in H. split.
    + intros. inversion H0.
    + intros. intro. inversion H1.
  - inversion H. rewrite In_app_iff in Hx.
    apply de_morgan_not_or in Hx. destruct Hx.
    split.
    + intros. simpl in H5. destruct H5.
      * rewrite <- H5. apply H4.
      * apply IHl1. apply H1. apply H5.
    + intros. intro. simpl in H6. destruct H6.
      * rewrite <- H6 in H5. contradiction.
      * apply IHl1 in H1. destruct H1. apply H1 in H6. contradiction.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_NoDup_disjoint_etc : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (pigeonhole_principle)

    The _pigeonhole principle_ states a basic fact about counting: if
    we distribute more than [n] items into [n] pigeonholes, some
    pigeonhole must contain at least two items.  As often happens, this
    apparently trivial fact about numbers requires non-trivial
    machinery to prove, but we now have enough... *)

(** First prove an easy and useful lemma. *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros. induction l as [ | n' l'].
  - inversion H.
  - simpl in H. destruct H as [H | H].
    + exists [], l'. simpl. rewrite H. reflexivity.
    + apply IHl' in H. destruct H as [l1 [l2 H]].
      exists (n'::l1), l2. rewrite H. simpl. reflexivity.
Qed.

(** Now define a property [repeats] such that [repeats X l] asserts
    that [l] contains at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  | repeats_new x l (H: In x l) : repeats (x :: l)
  | repeats_old y l (H: repeats l) : repeats (y :: l)
.

(* Do not modify the following line: *)
Definition manual_grade_for_check_repeats : option (nat*string) := None.

(** Now, here's a way to formalize the pigeonhole principle.  Suppose
    list [l2] represents a list of pigeonhole labels, and list [l1]
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label -- i.e., list [l1] must contain repeats.

    This proof is much easier if you use the [excluded_middle]
    hypothesis to show that [In] is decidable, i.e., [forall x l, (In x
    l) \/ ~ (In x l)].  However, it is also possible to make the proof
    go through _without_ assuming that [In] is decidable; if you
    manage to do this, you will not need the [excluded_middle]
    hypothesis. *)
Theorem pigeonhole_principle: excluded_middle ->
  forall (X:Type) (l1  l2:list X),
  (forall x, In x l1 -> In x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof.
  intros EM X l1. induction l1 as [ |x l1' IHl1'].
  - intros l2 Hin Hcp.
    inversion Hcp.
  - intros l2 Hin Hcp. simpl in *.
    (* get a new list from [l2] with an [x] throwed away.
       use [in_split]. *)
    assert (H: In x l2).
      { apply Hin. left. reflexivity. }
    apply in_split in H as H'.
    destruct H' as [l2' [l2'' H']].
    apply (f_equal _ _ length) in H' as H''.
    rewrite app_length in H''. simpl in H''.
    replace (S (length l2'')) with (length l2'' + 1) in H''.
    rewrite add_assoc in H''. rewrite <- app_length in H''.
    rewrite add_comm in H''. simpl in H''.
    rewrite H'' in Hcp. apply Sn_le_Sm__n_le_m in Hcp.
    (* use excluded middle to decide which constructor should be used. *)
    assert (Hem: In x l1' \/ ~ (In x l1')).
    { apply EM. }
    destruct Hem as [Ht | Hf].
    + apply repeats_new. apply Ht.
    + apply repeats_old.
      apply IHl1' with (l2:=l2'++l2'').
      * intros y H1. apply In_app_iff.
        (* Search (?y -> ?x \/ ?y). *)
        apply or_intro_l with (B:=x=y) in H1 as H1'.
        apply or_commut in H1'.
        apply Hin in H1'.
        rewrite H' in H1'.
        apply In_app_iff in H1'. simpl in H1'.
        destruct H1' as [H1' | [H1' | H1']].
        -- left. apply H1'.
        -- rewrite H1' in Hf. apply Hf in H1. destruct H1.
        -- right. apply H1'.
      * apply Hcp.
    + rewrite add_comm. reflexivity.
Qed.

(* Proof without [excluded_middle] hypothesis. *)
(* 1. [In x l] for [x] which has arbitrary type is not decidable
      without excluded middle. Nevertheless, [In x l] for [x : nat]
      _is_ decidable, which can be proved with
      [restricted_excluded_middle_eq].
   2. Thus, we can turn [l1] in to a [nat] list [l1'].
      Since all elements in [l1] occur in [l2], we can turn the
      element in [l1] into the index of its first occurrence in [l2].
   3. We cannot just find the index of an element in a list,
      since we cannot compare two elements in an arbitrary type.
      But if we know an index, we can take out the element in the
      list with the right index.
   4. We cannot _construct_ such a list, but we can prove its existence.
   5. We need to find the equivalent version of [In] which use index
      instead of compare elements directly, so we can avoid the
      problem in 3. Both directions are needed, for we have to deal
      with [In] in both evidence and consequence.
   6. We also need to turn [in_split] into an indexed version.
      Same reason with we did in 5. *)

(* Similar with [in_dec] in standar module [List]. *)
Lemma nat_in_or_not: forall (x : nat) (l : list nat),
  In x l \/ ~ (In x l).
Proof.
  intros x l.
  induction l.
  - right. intros contra. destruct contra.
  - simpl in *.
    (* Search (?x \/ ~ ?x). *)
    assert (Hem: x0 = x \/ x0 <> x).
    { apply restricted_excluded_middle_eq. }
    destruct Hem as [Hem | Hem].
    + left. left. apply Hem.
    + destruct IHl as [H | H].
      * left. right. apply H.
      * right. intro Hc. destruct Hc as [Hc | Hc].
        -- apply Hem in Hc. destruct Hc.
        -- apply H in Hc. destruct Hc.
Qed.

(* Same with [nth] in standard module [List]. *)
Fixpoint index {X:Type} (l:list X) (n:nat) (default:X) :=
  match l with
  | [] => default
  | h :: t =>
      match n with
      | O => h
      | S i => index t i default
      end
  end.

(* Same with [In_nth] in standard module [List]. *)
Lemma in_to_index : forall {X:Type} x (l:list X) default,
  In x l -> exists i, i < length l /\ index l i default = x.
Proof.
  intros X x l default H. induction l as [ | x' l'].
  + inversion H.
  + simpl in H. destruct H as [H | H].
    * exists 0. simpl. split.
      -- apply n_le_m__Sn_le_Sm. apply O_le_n.
      -- rewrite H. reflexivity.
    * apply IHl' in H. destruct H as [j [H1 H2]].
      exists (S j). simpl. split.
      -- apply (n_le_m__Sn_le_Sm _ _ H1).
      -- apply H2.
Qed.

(* Same with nth_In in standard module [List]. *)
Lemma index_to_in : forall {X:Type} (l:list X) (n:nat) default,
  n < length l -> In (index l n default) l.
Proof.
  intros X l. induction l as [ | x' l'].
  - intros n d H. inversion H.
  - intros n d H. destruct n.
    + simpl. left. reflexivity.
    + simpl. right. apply IHl'. simpl in H.
      apply (Sn_le_Sm__n_le_m _ _ H).
Qed.

Lemma in_to_nat_list :
  forall (X:Type) (l1  l2:list X) (default:X),
  (forall x, In x l1 -> In x l2) ->
  exists (l:list nat), length l = length l1 /\
    (forall (i:nat),
      i < length l ->
      (index l1 i default = index l2 (index l i 0) default) /\
      index l i 0 < length l2).
Proof.
  induction l1 as [ | x' l1'].
  - intros l2 default H. exists []. split.
    + reflexivity.
    + intros i contra. inversion contra.
  - intros l2 default H. simpl in H.
    (* just use [assert] to destruct H ! *)
    assert (H1: In x' l2).
      { apply H. left. reflexivity. }
    assert (H2: forall x, In x l1' -> In x l2).
      { intros x H2'. apply H. right. apply H2'. }
    (* convert [In] to the indexed equivalent. *)
    apply in_to_index with (default:=default) in H1 as H1'.
    destruct H1' as [j [H1' H1'']].
    apply IHl1' with (default:=default) in H2 as H2'.
    destruct H2' as [l [H2' H2'']].
    exists (j :: l). split.
    + simpl. f_equal. apply H2'.
    + intros i H3. destruct i.
      * simpl. rewrite H1''. split. reflexivity. apply H1'.
      * simpl. apply H2''. simpl in H3.
        apply (Sn_le_Sm__n_le_m _ _ H3).
Qed.

Fixpoint remove_index {X:Type} (l:list X) (i:nat) :=
  match l with
  | [] => []
  | h :: t =>
      match i with
      | O => t
      | S n => h :: remove_index t n
      end
  end.

(* [remove_index l n] just remove [n]th element, others are
   still there. *)
Lemma remove_index_in : forall {X:Type} (l:list X) (j k:nat) (default:X),
  k < length l -> j < length l -> k <> j ->
  In (index l k default) (remove_index l j)
.
Proof.
  intros X. induction l as [ | x' l'].
  - intros j k d Hk Hj Hkj. inversion Hk.
  - intros j k d Hk Hj Hkj.
    destruct k, j.
    + destruct Hkj. reflexivity.
    + simpl. left. reflexivity.
    + simpl. apply index_to_in. simpl in Hk.
      apply (Sn_le_Sm__n_le_m _ _ Hk).
    + simpl in *. right. apply IHl'.
      apply (Sn_le_Sm__n_le_m _ _ Hk).
      apply (Sn_le_Sm__n_le_m _ _ Hj).
      intro. destruct Hkj. f_equal. apply H.
Qed.

Lemma remove_index_length : forall {X:Type} (l:list X) (i:nat),
  i < length l -> length l = S (length (remove_index l i))
.
Proof.
  intros X. induction l.
  - intros i H. inversion H.
  - intros i H. destruct i.
    + simpl. reflexivity.
    + simpl. f_equal. apply IHl. simpl in H.
      apply (Sn_le_Sm__n_le_m _ _ H).
Qed.

Theorem pigeonhole_principle_no_em:
  forall (X:Type) (l1  l2:list X),
  (forall x, In x l1 -> In x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof.
  intros X l1. induction l1 as [ |x' l1' IHl1].
  - intros l2 Hin Hcp.
    inversion Hcp.
  - intros l2 Hin Hcp. simpl in *.
    (* destruct [Hin] manually. *)
    assert (H1: In x' l2).
      { apply Hin. left. reflexivity. }
    assert (H2: forall x, In x l1' -> In x l2).
      { intros x H. apply Hin. simpl. right. apply H. }
    (* destruct [In] in [H1] and [H2] into indexed version. *)
    apply in_to_index with (default:=x') in H1 as H1'.
    destruct H1' as [j [H1_1 H1_2]].
    apply in_to_nat_list with (default:=x') in H2 as H2'.
    destruct H2' as [lnat [H2_1 H2_2]].
    (* use restricted excluded middle. *)
    assert (Hem: In j lnat \/ ~ (In j lnat)).
      { apply nat_in_or_not. }
    destruct Hem as [Ht | Hf].
    + (* [In j lnat], i.e. [In x' l1']. *)
      apply repeats_new.
      apply in_to_index with (default:=0) in Ht as Ht'.
      destruct Ht' as [k [Ht_1 Ht_2]].
      apply H2_2 in Ht_1 as Ht_1'.
      rewrite Ht_2 in Ht_1'.
      rewrite H1_2 in Ht_1'.
      destruct Ht_1' as [Ht_1' Ht_1''].
      rewrite <- Ht_1'.
      apply index_to_in. rewrite <- H2_1. apply Ht_1.
    + (* [~ (In j lnat)], i.e. [~ (In x' l1')]. *)
      apply repeats_old.
      remember (remove_index l2 j) as l2'.
      apply IHl1 with (l2:=l2').
      intros x H3.
      apply in_to_index with (default:=x') in H3 as H3'.
      destruct H3' as [k [H3_1 H3_2]].
      rewrite <- H2_1 in H3_1.
      apply H2_2 in H3_1 as H3_1'.
      rewrite H3_2 in H3_1'.
      destruct H3_1' as [H3_1' H3_1''].
      rewrite H3_1'. rewrite Heql2'.
      apply remove_index_in.
      * apply H3_1''.
      * apply H1_1.
      * intro H. rewrite <- H in Hf. destruct Hf.
        apply index_to_in. apply H3_1.
      * rewrite remove_index_length with (i:=j) in Hcp.
        rewrite Heql2'. apply (Sn_le_Sm__n_le_m _ _ Hcp).
        apply H1_1.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Extended Exercise: A Verified Regular-Expression Matcher *)

(** We have now defined a match relation over regular expressions and
    polymorphic lists. We can use such a definition to manually prove that
    a given regex matches a given string, but it does not give us a
    program that we can run to determine a match automatically.

    It would be reasonable to hope that we can translate the definitions
    of the inductive rules for constructing evidence of the match relation
    into cases of a recursive function that reflects the relation by recursing
    on a given regex. However, it does not seem straightforward to define
    such a function in which the given regex is a recursion variable
    recognized by Coq. As a result, Coq will not accept that the function
    always terminates.

    Heavily-optimized regex matchers match a regex by translating a given
    regex into a state machine and determining if the state machine
    accepts a given string. However, regex matching can also be
    implemented using an algorithm that operates purely on strings and
    regexes without defining and maintaining additional datatypes, such as
    state machines. We'll implement such an algorithm, and verify that
    its value reflects the match relation. *)

(** We will implement a regex matcher that matches strings represented
    as lists of ASCII characters: *)
Require Import Coq.Strings.Ascii.

Definition string := list ascii.

(** The Coq standard library contains a distinct inductive definition
    of strings of ASCII characters. However, we will use the above
    definition of strings as lists as ASCII characters in order to apply
    the existing definition of the match relation.

    We could also define a regex matcher over polymorphic lists, not lists
    of ASCII characters specifically. The matching algorithm that we will
    implement needs to be able to test equality of elements in a given
    list, and thus needs to be given an equality-testing
    function. Generalizing the definitions, theorems, and proofs that we
    define for such a setting is a bit tedious, but workable. *)

(** The proof of correctness of the regex matcher will combine
    properties of the regex-matching function with properties of the
    [match] relation that do not depend on the matching function. We'll go
    ahead and prove the latter class of properties now. Most of them have
    straightforward proofs, which have been given to you, although there
    are a few key lemmas that are left for you to prove. *)

(** Each provable [Prop] is equivalent to [True]. *)
Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

(** Each [Prop] whose negation is provable is equivalent to [False]. *)
Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. destruct H0.
Qed.

(** [EmptySet] matches no string. *)
Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [EmptyStr] only matches the empty string. *)
Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

(** [EmptyStr] matches no non-empty string. *)
Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [Char a] matches no string that starts with a non-[a] character. *)
Lemma char_nomatch_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.

(** If [Char a] matches a non-empty string, then the string's tail is empty. *)
Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

(** [App re0 re1] matches string [s] iff [s = s0 ++ s1], where [s0]
    matches [re0] and [s1] matches [re1]. *)
Lemma app_exists : forall (s : string) re0 re1,
  s =~ App re0 re1 <->
  exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

(** **** Exercise: 3 stars, standard, optional (app_ne)

    [App re0 re1] matches [a::s] iff [re0] matches the empty string
    and [a::s] matches [re1] or [s=s0++s1], where [a::s0] matches [re0]
    and [s1] matches [re1].

    Even though this is a property of purely the match relation, it is a
    critical observation behind the design of our regex matcher. So (1)
    take time to understand it, (2) prove it, and (3) look for how you'll
    use it later. *)
Lemma app_ne : forall (a : ascii) s re0 re1,
  a :: s =~ (App re0 re1) <->
  ([ ] =~ re0 /\ a :: s =~ re1) \/
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros. split.
  - intros. inversion H. destruct s1.
    + simpl in *. left. split. apply H3. apply H4.
    + simpl in *. inversion H1. right.
      exists s1, s2. split. reflexivity. split.
      rewrite <- H6. apply H3. apply H4.
  - intros. destruct H.
    + destruct H. apply (MApp _ _ _ _ H H0).
    + destruct H as [s0 [s1 [H1 [H2 H3]]]].
      rewrite H1.
      apply (MApp _ _ _ _ H2 H3).
Qed.
(** [] *)

(** [s] matches [Union re0 re1] iff [s] matches [re0] or [s] matches [re1]. *)
Lemma union_disj : forall (s : string) re0 re1,
  s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H1.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.

(** **** Exercise: 3 stars, standard, optional (star_ne)

    [a::s] matches [Star re] iff [s = s0 ++ s1], where [a::s0] matches
    [re] and [s1] matches [Star re]. Like [app_ne], this observation is
    critical, so understand it, prove it, and keep it in mind.

    Hint: you'll need to perform induction. There are quite a few
    reasonable candidates for [Prop]'s to prove by induction. The only one
    that will work is splitting the [iff] into two implications and
    proving one by induction on the evidence for [a :: s =~ Star re]. The
    other implication can be proved without induction.

    In order to prove the right property by induction, you'll need to
    rephrase [a :: s =~ Star re] to be a [Prop] over general variables,
    using the [remember] tactic.  *)

Lemma star_ne : forall (a : ascii) s re,
  a :: s =~ Star re <->
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  intros. split.
  - intros H.
    remember (a :: s) as s'.
    remember (Star re) as re'.
    (* since we have remembered [a :: s] as [s'], [H] won't be readded
       intro consequence when we generalize [s] and [a]. *)
    generalize dependent s.
    generalize dependent a.
    induction H
    as [ | x'
         | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
         | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
         | re' | s1 s2 re' Hmatch1 IH1 Hmatch2 IH2].
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + intros. destruct s1 as [ | x' s1'].
      * apply IH2. apply Heqre'. apply Heqs'.
      * inversion Heqs'.
        exists s1', s2. split. reflexivity. split.
        -- inversion Heqre'. rewrite <- H2.
           rewrite <- H0. apply Hmatch1.
        -- apply Hmatch2.
  - intros [s0 [s1 [H [H1 H2]]]].
    rewrite H.
    apply (MStarApp _ _ _ H1 H2).
Qed.
(** [] *)

(** The definition of our regex matcher will include two fixpoint
    functions. The first function, given regex [re], will evaluate to a
    value that reflects whether [re] matches the empty string. The
    function will satisfy the following property: *)
Definition refl_matches_eps m :=
  forall re : reg_exp ascii, reflect ([ ] =~ re) (m re).

(** **** Exercise: 2 stars, standard, optional (match_eps)

    Complete the definition of [match_eps] so that it tests if a given
    regex matches the empty string: *)
Fixpoint match_eps (re: reg_exp ascii) : bool :=
  (* [eps] stands for _EmPty String_. *)
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => false
  | App r1 r2 => match_eps r1 && match_eps r2
  | Union r1 r2 => match_eps r1 || match_eps r2
  | Star r => true
  end.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (match_eps_refl)

    Now, prove that [match_eps] indeed tests if a given regex matches
    the empty string.  (Hint: You'll want to use the reflection lemmas
    [ReflectT] and [ReflectF].) *)

Lemma app_eq_nil : forall {X:Type} (l1 l2:list X),
  l1 ++ l2 = [] -> l1 = [] /\ l2 = [].
Proof.
  intros.
  destruct l1, l2.
  - split. reflexivity. reflexivity.
  - discriminate.
  - discriminate.
  - discriminate.
Qed.

Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  unfold refl_matches_eps. intros.
  apply iff_reflect. split.
  - intros. induction re.
    + inversion H.
    + reflexivity.
    + inversion H.
    + simpl. rewrite andb_true_iff.
      inversion H. apply app_eq_nil in H1. destruct H1.
      split.
      * apply IHre1. rewrite <- H1. apply H3.
      * apply IHre2. rewrite <- H5. apply H4.
    + simpl. rewrite orb_true_iff. inversion H.
      * left. apply (IHre1 H2).
      * right. apply (IHre2 H1).
    + reflexivity.
  - intros. induction re.
    + discriminate.
    + apply MEmpty.
    + discriminate.
    + inversion H. rewrite andb_true_iff in H1. destruct H1.
      apply IHre1 in H0. apply IHre2 in H1.
      apply (MApp _ _ _ _ H0 H1).
    + inversion H. rewrite orb_true_iff in H1. destruct H1.
      * apply IHre1 in H0. apply (MUnionL _ _ _ H0).
      * apply IHre2 in H0. apply (MUnionR _ _ _ H0).
    + apply MStar0.
Qed.
(** [] *)

(** We'll define other functions that use [match_eps]. However, the
    only property of [match_eps] that you'll need to use in all proofs
    over these functions is [match_eps_refl]. *)

(** The key operation that will be performed by our regex matcher will
    be to iteratively construct a sequence of regex derivatives. For each
    character [a] and regex [re], the derivative of [re] on [a] is a regex
    that matches all suffixes of strings matched by [re] that start with
    [a]. I.e., [re'] is a derivative of [re] on [a] if they satisfy the
    following relation: *)

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

(** A function [d] derives strings if, given character [a] and regex
    [re], it evaluates to the derivative of [re] on [a]. I.e., [d]
    satisfies the following property: *)
Definition derives d := forall a re, is_der re a (d a re).

(** **** Exercise: 3 stars, standard, optional (derive)

    Define [derive] so that it derives strings. One natural
    implementation uses [match_eps] in some cases to determine if key
    regex's match the empty string. *)
Fixpoint derive (a : ascii) (re : reg_exp ascii) : reg_exp ascii :=
  (* Brzozowski derivative *)
  match re with
  | EmptySet => EmptySet
  | EmptyStr => EmptySet
  | Char t =>
      if (a =? t)%char
      then EmptyStr
      else EmptySet
  | App r1 r2 =>
      if match_eps r1
      then Union (App (derive a r1) r2) (derive a r2)   (* important ! *)
      else App (derive a r1) r2
  | Union r1 r2 =>
      Union (derive a r1) (derive a r2)
  | Star r =>
      App (derive a r) (Star r)
  end.
(** [] *)

(** The [derive] function should pass the following tests. Each test
    establishes an equality between an expression that will be
    evaluated by our regex matcher and the final value that must be
    returned by the regex matcher. Each test is annotated with the
    match fact that it reflects. *)
Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

(** "c" =~ EmptySet: *)
Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof. reflexivity. Qed.

(** "c" =~ Char c: *)
Example test_der1 : match_eps (derive c (Char c)) = true.
Proof. reflexivity. Qed.

(** "c" =~ Char d: *)
Example test_der2 : match_eps (derive c (Char d)) = false.
Proof. reflexivity. Qed.

(** "c" =~ App (Char c) EmptyStr: *)
Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof. reflexivity. Qed.

(** "c" =~ App EmptyStr (Char c): *)
Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof. reflexivity. Qed.

(** "c" =~ Star c: *)
Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof. reflexivity. Qed.

(** "cd" =~ App (Char c) (Char d): *)
Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof. reflexivity. Qed.

(** "cd" =~ App (Char d) (Char c): *)
Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof. reflexivity. Qed.

(** **** Exercise: 4 stars, standard, optional (derive_corr)

    Prove that [derive] in fact always derives strings.

    Hint: one proof performs induction on [re], although you'll need
    to carefully choose the property that you prove by induction by
    generalizing the appropriate terms.

    Hint: if your definition of [derive] applies [match_eps] to a
    particular regex [re], then a natural proof will apply
    [match_eps_refl] to [re] and destruct the result to generate cases
    with assumptions that the [re] does or does not match the empty
    string.

    Hint: You can save quite a bit of work by using lemmas proved
    above. In particular, to prove many cases of the induction, you
    can rewrite a [Prop] over a complicated regex (e.g., [s =~ Union
    re0 re1]) to a Boolean combination of [Prop]'s over simple
    regex's (e.g., [s =~ re0 \/ s =~ re1]) using lemmas given above
    that are logical equivalences. You can then reason about these
    [Prop]'s naturally using [intro] and [destruct]. *)
Lemma derive_corr : derives derive.
Proof.
  unfold derives. unfold is_der.
  intros. split.
  - intros. remember (a::s) as s'.
    generalize dependent s.
    (* generalize dependent a. *)   (* optional *)
    induction H.
    + intros. inversion Heqs'.
    + intros. inversion Heqs'.
      simpl. destruct (eqb_spec a a).
      * apply MEmpty.
      * destruct n. reflexivity.
    + intros. cbn.
      destruct (match_eps_refl re1).
      * apply union_disj.
        destruct s1 as [ | a' s1'].
        -- right. apply (IHexp_match2 _ Heqs').
        -- left. simpl in Heqs'. inversion Heqs'.
           apply MApp.
           apply IHexp_match1. rewrite H3. reflexivity.
           apply H0.
      * destruct s1 as [ | a' s1'].
        -- contradiction.
        -- inversion Heqs'.
           apply MApp.
           apply IHexp_match1. rewrite H3. reflexivity.
           apply H0.
    + intros. cbn. apply union_disj.
      left. apply (IHexp_match _ Heqs').
    + intros. cbn. apply union_disj.
      right. apply (IHexp_match _ Heqs').
    + intros. inversion Heqs'.
    + intros. destruct s1 as [ | a' s1'].
      * apply (IHexp_match2 _ Heqs').
      * inversion Heqs'.
        cbn. apply MApp.
        apply IHexp_match1. rewrite H2. reflexivity.
        apply H0.
  - generalize dependent s.
    induction re.
    + intros. inversion H.
    + intros. inversion H.
    + intros. cbn in H.
      destruct (eqb_spec a t).
      * inversion H.
        rewrite e. apply MChar.
      * inversion H.
    + intros. cbn in H.
      destruct (match_eps_refl re1).
      * apply union_disj in H.
        destruct H as [H | H].
        -- apply app_exists in H.
           destruct H as [s1 [s2 [H [H1 H2]]]].
           apply IHre1 in H1.
           rewrite H.
           apply (MApp _ _ _ _ H1 H2).
        -- apply IHre2 in H.
           apply (MApp _ _ _ _ H0 H).
      * apply app_exists in H.
        destruct H as [s1 [s2 [H [H1 H2]]]].
        apply IHre1 in H1.
        rewrite H.
        apply (MApp _ _ _ _ H1 H2).
    + intros. cbn in H.
      apply union_disj in H.
      destruct H as [H | H].
      * apply (MUnionL _ _ _ (IHre1 _ H)).
      * apply (MUnionR _ _ _ (IHre2 _ H)).
    + intros. cbn in H.
      apply app_exists in H.
      destruct H as [s1 [s2 [H [H1 H2]]]].
      rewrite H.
      apply (MStarApp _ _ _ (IHre _ H1) H2).
Qed.
(** [] *)

(** We'll define the regex matcher using [derive]. However, the only
    property of [derive] that you'll need to use in all proofs of
    properties of the matcher is [derive_corr]. *)

(** A function [m] _matches regexes_ if, given string [s] and regex [re],
    it evaluates to a value that reflects whether [s] is matched by
    [re]. I.e., [m] holds the following property: *)
Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

(** **** Exercise: 2 stars, standard, optional (regex_match)

    Complete the definition of [regex_match] so that it matches
    regexes. *)
Fixpoint regex_match (s : string) (re : reg_exp ascii) : bool :=
  match s with
  | [] => match_eps re
  | h :: t => regex_match t (derive h re)
  end.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (regex_match_correct)

    Finally, prove that [regex_match] in fact matches regexes.

    Hint: if your definition of [regex_match] applies [match_eps] to
    regex [re], then a natural proof applies [match_eps_refl] to [re]
    and destructs the result to generate cases in which you may assume
    that [re] does or does not match the empty string.

    Hint: if your definition of [regex_match] applies [derive] to
    character [x] and regex [re], then a natural proof applies
    [derive_corr] to [x] and [re] to prove that [x :: s =~ re] given
    [s =~ derive x re], and vice versa. *)
Theorem regex_match_correct : matches_regex regex_match.
Proof.
  unfold matches_regex.
  intros. apply iff_reflect.
  generalize dependent re.
  induction s.
  - intros. apply reflect_iff. apply match_eps_refl.
  - intros. cbn.
    destruct (derive_corr x re) with (s:=s) as [H1 H2].
    split.
    + intros. apply IHs. apply H1. apply H.
    + intros. apply H2. apply IHs. apply H.
Qed.
(** [] *)

(* 2023-03-25 11:11 *)
