---
title: Agda-like Equational Reasoning in Coq using Tactic Notations
---

# Agda-like Equational Reasoning in Coq using Tactic Notations

I am used to the idea that there are two major styles of mechanised proofs:
Agda-style proofs that effectively spell out the proof terms and
Coq-style proofs that are constructed using tactics.

I like Coq's approach since it allows me to poke my goals with tactics
interactively and to *think less hard* about the exact way some lemma
should be applied. However, proof scripts very quickly become impossible
to understand without stepping through them interactively. In Agda,
proofs are often written in equational reasoning style using mixfix
proof combinators, like that:

``` {.sourceCode .agda}
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎
```

This lemma proves commutativity of addition of natural numbers by
structural induction, justifying the equational reasoning steps with the
≡⟨ necessary lemmas ⟩.

I find Agda's style much friendlier to the naked eye. Why can't I have
it in Coq? Well, actually, I can! Here is a Coq proof of the same
theorem that closely mimics the Agda one:

``` {.coq}
Theorem plus_comm :
  forall (m n : nat), m + n = n + m.
Proof.
  intros m n.
  induction n.
  - `Begin
     (m + 0).
    ≡⟨ now rewrite <- plus_n_O ⟩
     (m).
    ≡⟨ reflexivity ⟩
     (0 + m)
    `End.
  - `Begin
     (m + S n).
    ≡⟨ now rewrite plus_n_Sm ⟩
     (S (m + n)).
    ≡⟨ now rewrite IHn ⟩
     (S (n + m)).
    ≡⟨ reflexivity ⟩
     (S n + m)
    `End.
Qed.
```

Neat, isn't it? We invoke the `induction` tactic generating two
subgoals, with which we deal in the same style that we used in Agda! To
achieve this, we need two ingredients: one somewhat arcane (but
standard) tactic and Tactic Notations to make it look prettier.

Tactic Notations + `stepl` = Equational Reasoning!
--------------------------------------------------

Coq proofs consist of tactics which when invoked generate the actual
proof terms that are type-checked by Coq. This is great, but since the
proof terms are hidden, it is not always straightforward to understand a
proof script without stepping through it interactively. What I wanted to
have instead is a neat way to spell out intermediate proof terms
literally and use tactics to justify the rewriting steps connecting
these intermediate terms. To do that, we can use a rather obscure tactic
[`stepl term by tactic`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.stepl)
which does exactly what we want: transforms the left hand-side of the
current equality goal into the `term` we supply with a `tactic` we give.
To make it look more like Agda, we throw in some pretty Unicode
characters and put the justifying tactic first by using a Tactic
Notation:

``` {.coq}
Tactic Notation
  "≡⟨ " tactic(proof) "⟩" constr(rhs) :=
  (stepl rhs by proof).
```

Note how the arguments are passed to the notation: the `proof` is
specified to be an Ltac term (`tactic`), and `rhs` --- a kernel term
(`constr`).

This approach is of course not the perfect emulation of Agda-style
equational reasoning since it does not support holes and inherits Coq's
stepwise proof editing style, i.e. it is not as easy to switch between
forward and backward reasoning as in Agda. Though it is still possible
to sketch proofs and skip steps, since one could use the `admit` tactic
as justification for any rewriting step. More importantly, we gain
something which Agda does not have: between rewriting step we can use
the usual Coq interactive proof style of transforming the goal with
tactics to experiment and find the next rewriting step; after that we
could petrify the interactive proof exploration into a sequence of clear
equational reasoning steps.

A quick Google search gives a number of hits on how to use equational
reasoning in Coq, but most of the projects seem to be developing some
heavy machinery and are not straightforward to use. Among the first hits
however is [this
gist](https://gist.github.com/gallais/f046bcc2c348c5fed5e9), which is
very lightweight and has given me the initial inspiration. It is much
more limited though since the trick it proposes does not allow skipping
proof steps with `admit`.

I have used this style to prove that [Free Rigid
Selective](https://github.com/snowleopard/selective) is a lawful
instance of `Applicative`, you may take a look at the proof scripts
[here](https://github.com/tuura/selective-theory-coq/blob/26fed67487ba9b2f085b9a3ea19168b8684bb0f1/src/Control/Selective/Rigid/Proofs/Applicative.v#L123).

Since this post has been inspired by a Github Gist, I've put the
accompanying Coq code in one too; here is [how to do lightweight
equational reasoning in
Coq](https://gist.github.com/geo2a/31381aeb345c789761504da1b5d42168).
