# Software Foundations in Coq

TEXTBOOK: [Software Foundations Logo VOLUME 1: LOGICAL FOUNDATIONS](https://softwarefoundations.cis.upenn.edu/lf-current/toc.html)

CHINESE Version: [软件基础 第一卷 逻辑基础](https://coq-zh.github.io/SF-zh/lf-current/toc.html)

Source Code: [clarksmr/sf-lectures](https://github.com/clarksmr/sf-lectures)

## Coq installation

```
opam switch create cs4160 ocaml-base-compiler.4.14.1
opam install utop
opam pin add coq 8.15.2
```

## Coq Syntax

- **Vernacular**: Check, Compute, Theroem, Lemma, Proof, Qed, ...
- **Gallina**: match, if, forall, ...
- **Ltac**: intros, simpl, reflexivity, destruct, induction, assert, replace, ...
