(******************************************************************************)
(*                                                                            *)
(*                            Provability Verified                            *)
(*                                                                            *)
(*     Entry point, re-exporting the eleven parts.                            *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

(** The development is eleven parts, each depending only on those before
    it:

      Modal         the modal language and the polymodal calculus GLP*,
                    used by the arithmetic layer for its modal embedding
                    and its Cantor pairing
      Syntax        first-order syntax, Robinson Q, Goedel coding, the
                    FOProvesTn reflection tower, the Delta_0 and Sigma_1
                    classes
      Semantics     FOsat, the arithmetized proof checker, the HBL
                    conditions against FOsat, Loeb, Goedel II, FOembed
      Internal      object-level arithmetic: instantiation of open
                    equations, the object-level ring, derivations under
                    hypotheses, the Chinese remainder theorem, beta
                    sequence extension and concatenation, Cantor pairing
      Transfer      substitution and capture conditions through the
                    checker's formula builders, and the transfer of every
                    checker clause to larger tables and shifted positions
      Merge         merging two checked derivations: shifted tracks,
                    merged tables, and the new final entry
      Derivability  the checker body and matrix inside the tower, and the
                    second derivability condition FOHBL2_internal
      Rows          rows of the checker's tables derived inside T_0,
                    one-line derivations, the checker's step clauses
      Patterns      code patterns of terms and formulas, and the
                    substitution, occurrence and capture rows of a code
      Instances     provable instances of a pattern, numeral codes, term
                    evaluation, sums, products and disequality inside the
                    provability predicate
      Sigma1        the Delta_0 and Sigma_1 inductions, provable
                    Sigma_1-completeness with the formalized numeral
                    substitution, its standard-model meaning, and the
                    third derivability condition FOHBL3_internal

    Requiring [Provability.Provability] loads and imports all eleven. *)

From Provability Require Export Modal.
From Provability Require Export Syntax.
From Provability Require Export Semantics.
From Provability Require Export Internal.
From Provability Require Export Transfer.
From Provability Require Export Merge.
From Provability Require Export Derivability.
From Provability Require Export Rows.
From Provability Require Export Patterns.
From Provability Require Export Instances.
From Provability Require Export Sigma1.
