(*
 * Memory Alias Analysis — Proofs (internal)
 *
 * Cheated proofs for safety properties. The externally-facing API
 * is in memAliasPropsScript.sml (ACCEPT_TAC wrappers).
 *)

Theory memAliasProofs
Ancestors
  memAliasDefs memLocProps
Libs
  finite_mapTheory

(* ===== ma_add_location (internal stepping stones) ===== *)

Theorem ma_add_location_loc_in_domain[local]:
  ∀sets loc. loc ∈ FDOM (ma_add_location sets loc)
Proof
  rw[ma_add_location_def, LET_THM, FDOM_FUPDATE]
QED

Theorem ma_add_location_preserves_domain[local]:
  ∀sets loc k. k ∈ FDOM sets ⇒ k ∈ FDOM (ma_add_location sets loc)
Proof cheat
QED

Theorem ma_add_location_aliases_overlap[local]:
  ∀sets loc aliases.
    FLOOKUP (ma_add_location sets loc) loc = SOME aliases ⇒
    ∀a. MEM a aliases ⇒
      a ∈ FDOM sets ∧ may_overlap loc a ∨
      MEM a (case FLOOKUP sets loc of NONE => [] | SOME l => l)
Proof cheat
QED

Theorem ma_add_location_overlap_recorded[local]:
  ∀sets loc k.
    k ∈ FDOM sets ∧ may_overlap loc k ⇒
    ∃aliases. FLOOKUP (ma_add_location sets loc) k = SOME aliases ∧
              MEM loc aliases
Proof cheat
QED

Theorem ma_add_location_preserves_wf[local]:
  ∀sets loc.
    wf_alias_sets sets ⇒
    wf_alias_sets (ma_add_location sets loc)
Proof cheat
QED

(* ===== domain monotonicity (internal stepping stones) ===== *)

Theorem ma_analyze_block_domain_mono[local]:
  ∀bp addr sets insts k.
    k ∈ FDOM sets ⇒
    k ∈ FDOM (ma_analyze_block bp addr sets insts)
Proof cheat
QED

Theorem ma_analyze_blocks_domain_mono[local]:
  ∀bp addr sets bbs k.
    k ∈ FDOM sets ⇒
    k ∈ FDOM (ma_analyze_blocks bp addr sets bbs)
Proof cheat
QED

(* ===== wf_alias_sets: analysis output is well-formed ===== *)

(* The analysis produces well-formed alias sets.
 * Proof sketch: FEMPTY is trivially wf, ma_add_location preserves wf,
 * ma_analyze_inst/block/blocks preserve wf by induction. *)
Theorem ma_analyze_wf:
  ∀bp_result fn addr_sp.
    wf_alias_sets (ma_analyze bp_result fn addr_sp)
Proof cheat
QED

(* ===== ma_may_alias ===== *)

(* ma_may_alias is equivalent to may_overlap for well-formed alias sets.
 * This is THE key theorem — the alias query is a precomputation of
 * pairwise may_overlap, not an approximation.
 *
 * Proof sketch, by cases on ma_may_alias_def:
 *   volatile: ma_may_alias = may_overlap by definition.
 *   (SOME als1, SOME _): MEM loc2 als1 ⟺ may_overlap loc1 loc2
 *     Forward: wf correctness.  Backward: wf completeness (loc2 ∈ FDOM).
 *   fallback: ma_may_alias = may_overlap by definition. *)
Theorem ma_may_alias_iff:
  ∀sets loc1 loc2.
    wf_alias_sets sets ⇒
    (ma_may_alias sets loc1 loc2 ⇔ may_overlap loc1 loc2)
Proof cheat
QED

(* Locations backed by different base allocations never alias.
 * Convenience corollary: ma_may_alias_iff + different_alloca_no_overlap. *)
Theorem ma_different_alloca_no_alias:
  ∀sets loc1 loc2 a1 a2.
    wf_alias_sets sets ∧
    loc1.ml_alloca = SOME a1 ∧ loc2.ml_alloca = SOME a2 ∧ a1 ≠ a2 ⇒
    ¬ma_may_alias sets loc1 loc2
Proof cheat
QED

(* The empty memory location never aliases with anything.
 * Convenience corollary: ma_may_alias_iff + empty_no_overlap_l. *)
Theorem ma_empty_no_alias:
  ∀sets loc.
    wf_alias_sets sets ⇒
    ¬ma_may_alias sets ml_empty loc
Proof cheat
QED

(* Empty function produces empty alias sets *)
Theorem ma_analyze_empty[local]:
  ∀bp addr_sp fn.
    fn.fn_blocks = [] ⇒
    ma_analyze bp fn addr_sp = FEMPTY
Proof
  rw[ma_analyze_def, ma_analyze_blocks_def]
QED

(* ===== ma_may_alias characterization (local, subsumed by iff) ===== *)

Theorem ma_may_alias_volatile[local]:
  ∀sets loc1 loc2.
    loc1.ml_volatile ∨ loc2.ml_volatile ⇒
    (ma_may_alias sets loc1 loc2 ⇔ may_overlap loc1 loc2)
Proof
  rw[ma_may_alias_def]
QED

Theorem ma_may_alias_unknown[local]:
  ∀sets loc1 loc2.
    ¬loc1.ml_volatile ∧ ¬loc2.ml_volatile ∧
    (FLOOKUP sets loc1 = NONE ∨ FLOOKUP sets loc2 = NONE) ⇒
    (ma_may_alias sets loc1 loc2 ⇔ may_overlap loc1 loc2)
Proof
  rw[ma_may_alias_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* ===== ma_mark_volatile ===== *)

(* The returned location is volatile *)
Theorem ma_mark_volatile_is_volatile:
  ∀sets loc vloc sets'.
    ma_mark_volatile sets loc = (vloc, sets') ⇒
    vloc.ml_volatile
Proof
  rw[ma_mark_volatile_def, memLocDefsTheory.mk_volatile_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* mark_volatile preserves well-formedness of alias sets *)
Theorem ma_mark_volatile_preserves_wf:
  ∀sets loc vloc sets'.
    wf_alias_sets sets ∧
    ma_mark_volatile sets loc = (vloc, sets') ⇒
    wf_alias_sets sets'
Proof cheat
QED

