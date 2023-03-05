# Software Foundations in Coq

Textbook: [Software Foundations Logo VOLUME 1: LOGICAL FOUNDATIONS](https://softwarefoundations.cis.upenn.edu/lf-current/toc.html)

Chinese Version: [软件基础 第一卷 逻辑基础](https://coq-zh.github.io/SF-zh/lf-current/toc.html)

Videos: [Software Foundations in Coq](https://www.youtube.com/playlist?list=PLre5AT9JnKShFK9l9HYzkZugkJSsXioFs)

Source Code: [clarksmr/sf-lectures](https://github.com/clarksmr/sf-lectures)

## Coq installation

```
opam switch create cs4160 ocaml-base-compiler.4.14.1
opam install utop coq coq-lsp
```

## Coq Syntax

- **Vernacular**:
  - Check, Compute, Search, Locate, Fail, Print, Eval, ...
  - Inductive, Definition, Fixpoint, Arguments, ...
  - Notation, Reserved, Declare, Coercion, ...
  - Theorem, Lemma, Example, Proof, Qed, Axiom, Conjecture, ...
  - Ltac, ...
  - Hint, ...
  <!-- - False, True, I, ... -->
  - Module, End, Export, ...
- **Gallina**:
  - match, if, let, ...
  - fun
  - forall, exists, ...
  - eq ( = ), neq ( <> ),
    and ( /\ ), or ( \/ ), not ( ~ ),
    implies ( -> ), iff ( <-> ), ...
- **Ltac**:
  - intros, destruct, unfold, generalize dependent, clear, ...
  - induction, induction using, ...
  - simpl, cbn, cbv, reflexivity, ...
  - rewrite, apply, discriminate, rename into, exact, ...
  - symmetry, transitivity, injection, f_equal, inversion, ...
  - assumption, contradiction, subst, constructor, ...
  - assert, replace, remember, ...
  - split, left, right, exfalso, ...
  - try, ;, repeat, idtac, ...
  - specialize, pose proof, ...
  - lia, ring, field, congruence, intuition, ...
  - auto, info_auto, auto using, ...
  - eapply, eauto, info_eauto, eexists, econstructor, eassumption, ...
  - match goal, ...
