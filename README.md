# provability-verified

A Rocq formalization of provability in arithmetic: a tower of theories
T_0 ⊆ T_1 ⊆ … over Robinson arithmetic with the induction schema, a
Gödel coding of the syntax, a Σ₁ provability predicate for each level
defined through β-coded computation tables, and the derivability
conditions derived inside T_0.

## Main result

For every level k and every Σ₁ formula σ with free variables
x₁, …, xₘ,

```
T_0 ⊢ σ(x₁,…,xₘ) → Pr_k(⌜σ(ẋ₁,…,ẋₘ)⌝)
```

where ẋ is the numeral of the value of x and the substituted code is
computed inside arithmetic by an explicit numeral-substitution formula.
That formula means what it says: at every valuation it is true in ℕ
exactly when T_k proves σ with the numerals of the values substituted.
The third derivability condition

```
T_0 ⊢ Pr_k(⌜A⌝) → Pr_k(⌜Pr_k(⌜A⌝)⌝)
```

is the instance σ := Pr_k(⌜A⌝).  In Rocq, all four statements are
collected in `provable_sigma1_completeness` (`ArithSigma1.v`):

```coq
Theorem provable_sigma1_completeness : forall k,
  (forall A, FOsigma1 A -> FOProvesTn 0 (FOImplF A (FOSubProv k A))) /\
  (forall e A, FOsat e (FOSubProv k A) <->
     FOProvesTn k (FOsubsts A (fvs A) (map (fun x => FOnumeral (e x)) (fvs A)))) /\
  (forall A, FOsigma1 A -> (forall x, FOfree_in x A = false) ->
     FOProvesTn 0 (FOImplF A (FOProvSentence k A))) /\
  (forall A, FOProvesTn 0
     (FOImplF (FOProvSentence k A) (FOProvSentence k (FOProvSentence k A)))).
```

The second derivability condition is `FOHBL2_internal`
(`ArithDerivability.v`), derived inside T_0 by merging two checked
derivations and their computation tables.  The paper
`paper/provable-sigma1.tex` describes the statements and the proof.

## Build

Requires Rocq 9.0 with its standard library.

```
make
rocqchk -silent -Q . Provability Provability.Provability
```

`Provability.v` re-exports all eleven parts.  The kernel check lists the
axioms `classic` and `constructive_indefinite_description`;
`provable_sigma1_completeness` depends on `classic` alone.

## Files

- `Calculus.v` — the modal language and the polymodal calculus GLP*,
  which the arithmetic layer uses for its modal embedding and its Cantor
  pairing.
- `ArithSyntax.v` — first-order terms and formulas, Robinson Q, the
  Gödel coding of the syntax, the reflection tower `FOProvesTn`, and the
  Δ₀/Σ₁ classification.
- `ArithSemantics.v` — N-satisfaction `FOsat`, the β-coded proof checker
  and its arithmetization, the Hilbert–Bernays–Löb conditions against
  `FOsat`, Löb's rule, Gödel II at every level, and the embedding
  `FOembed`.
- `ArithInternal.v` — object-level arithmetic: instantiation of
  derivable open equations, an object-level ring, derivations under
  hypotheses, the Chinese remainder construction, extension and
  concatenation of β-coded sequences, and Cantor pairing.
- `ArithTransfer.v` — substitution and capture conditions through the
  checker's formula builders, and the transfer of checker clauses to
  larger tables and shifted positions.
- `ArithMerge.v` — merging two checked derivations and their tables.
- `ArithDerivability.v` — the checker body and matrix as object-level
  facts, and `FOHBL2_internal`.
- `ArithRows.v` — rows of the checker's computation tables derived
  inside T_0, one-line derivations of axiom instances, and the checker's
  step clauses introduced from component facts.
- `ArithPatterns.v` — code patterns of terms and formulas with slots for
  numeral codes, and the substitution, occurrence and capture rows of a
  pattern's code.
- `ArithInstances.v` — provable instances of a pattern, with modus
  ponens, instantiation, existential elimination and case splitting;
  numeral codes; term evaluation, sums, products and disequality inside
  the provability predicate.
- `ArithSigma1.v` — the Δ₀ and Σ₁ inductions, the sentence form, the
  third derivability condition `FOHBL3_internal`, the numeral-substitution
  formula `FOSUBNUMS` with its derivation, totality and standard-model
  meaning, and `provable_sigma1_completeness`.

## Origin

The development is the arithmetic layer of
[tiling-verified](https://github.com/CharlesCNorton/tiling-verified),
which formalizes the polymodal provability calculus GLP* and its
application to Yudkowsky–Herreshoff tiling agents.

## License

MIT.
