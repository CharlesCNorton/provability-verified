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

is the instance σ := Pr_k(⌜A⌝).  All four statements are collected in
`provable_sigma1_completeness` (`theories/Sigma1.v`):

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
(`theories/Derivability.v`), derived inside T_0 by merging two checked
derivations and their computation tables.  The paper in `paper/`
([PDF](paper/provable-sigma1.pdf)) presents the statements and the
proof.

## Building

With Rocq 9.0 and its standard library:

```
make          # build
make check    # build, then re-validate with rocqchk
```

The kernel check lists the axioms `classic` and
`constructive_indefinite_description`; `provable_sigma1_completeness`
depends on `classic` alone.

## Layout

`theories/` holds twelve parts, each depending only on those before it,
and the entry point `Provability.v`, which re-exports them under the
logical name `Provability`.

| File | Content |
|------|---------|
| `Modal.v` | the modal language and the polymodal calculus GLP*, used for the modal embedding and the Cantor pairing |
| `Syntax.v` | first-order terms and formulas, Robinson Q, the Gödel coding, the tower `FOProvesTn`, the Δ₀ and Σ₁ classes |
| `Semantics.v` | N-satisfaction `FOsat`, the β-coded proof checker and its arithmetization, the Hilbert–Bernays–Löb conditions against `FOsat`, Löb's rule, Gödel II at every level, the embedding `FOembed` |
| `Internal.v` | object-level arithmetic: instantiation of open equations, an object-level ring, derivations under hypotheses, the Chinese remainder construction, β-coded sequences, Cantor pairing |
| `Transfer.v` | substitution and capture conditions through the checker's formula builders, and the transfer of checker clauses to larger tables |
| `Merge.v` | merging two checked derivations and their tables |
| `Derivability.v` | the checker body and matrix as object-level facts, and `FOHBL2_internal` |
| `Rows.v` | table rows derived inside T_0, one-line derivations of axiom instances, the checker's step clauses |
| `Patterns.v` | code patterns with slots for numeral codes, and the substitution, occurrence and capture rows of a code |
| `Instances.v` | provable instances of a pattern with modus ponens, instantiation, existential elimination and case splitting; numeral codes; evaluation, sums, products and disequality inside the provability predicate |
| `Sigma1.v` | the Δ₀ and Σ₁ inductions, the sentence form, `FOHBL3_internal`, the numeral-substitution formula `FOSUBNUMS` with its derivation, totality and meaning, `provable_sigma1_completeness` |
| `Diagonal.v` | closed rows of the substitution tables inverted inside T_0: closed pairing, the step clause of a row with a known tag, lookups as rows, the substitution step at a closed binary code |

## Origin

This is the arithmetic layer of
[tiling-verified](https://github.com/CharlesCNorton/tiling-verified),
which formalizes the polymodal provability calculus GLP* and its
application to Yudkowsky–Herreshoff tiling agents.

## License

MIT; see `LICENSE`.
