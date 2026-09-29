(******************************************************************************)
(*                                                                            *)
(*          Provability Verified: Arithmetic and Its Proof Predicates         *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

(** Entry point.  The development is eleven parts, each depending only on
    those before it:

      Calculus           the modal language and the polymodal calculus
                         GLP*, used by the arithmetic layer for its modal
                         embedding and its Cantor pairing
      ArithSyntax        first-order syntax, Robinson Q, Goedel coding, the
                         FOProvesTn reflection tower, Delta_0/Sigma_1 classes
      ArithSemantics     FOsat, the arithmetized proof checker, the HBL
                         conditions, Loeb, Goedel II, FOembed
      ArithInternal      object-level arithmetic: instantiation of open
                         equations, the object-level ring, derivations under
                         hypotheses, the Chinese remainder theorem, beta
                         sequence extension and concatenation, Cantor pairing
      ArithTransfer      substitution and capture conditions through the
                         checker's formula builders, and the transfer of
                         every checker clause to larger tables and shifted
                         positions
      ArithMerge         merging two checked derivations: shifted tracks,
                         merged tables, and the new final entry
      ArithDerivability  the checker body and matrix inside the tower, and
                         the second derivability condition FOHBL2_internal
      ArithRows          rows of the checker's tables derived inside T_0,
                         one-line derivations, the checker's step clauses
      ArithPatterns      code patterns of terms and formulas, and the
                         substitution, occurrence and capture rows of a code
      ArithInstances     provable instances of a pattern, numeral codes,
                         term evaluation, sums, products and disequality
                         inside the provability predicate
      ArithSigma1        the Delta_0 and Sigma_1 inductions, provable
                         Sigma_1-completeness with the formalized numeral
                         substitution, its standard-model meaning, and the
                         third derivability condition FOHBL3_internal

    Requiring [Provability.Provability] loads and imports all eleven. *)

From Provability Require Export Calculus.
From Provability Require Export ArithSyntax.
From Provability Require Export ArithSemantics.
From Provability Require Export ArithInternal.
From Provability Require Export ArithTransfer.
From Provability Require Export ArithMerge.
From Provability Require Export ArithDerivability.
From Provability Require Export ArithRows.
From Provability Require Export ArithPatterns.
From Provability Require Export ArithInstances.
From Provability Require Export ArithSigma1.
