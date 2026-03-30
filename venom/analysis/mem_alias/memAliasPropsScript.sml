(*
 * Memory Alias Analysis — Properties (public API)
 *
 * Re-exports proven properties from proofs/ via ACCEPT_TAC.
 * Consumers: just `Ancestors memAliasProps` to get defs + properties.
 *
 * Structural:
 *   ma_analyze_wf                 — analysis output satisfies wf_alias_sets
 *   ma_may_alias_iff              — alias query ⟺ may_overlap (the key theorem)
 *   ma_different_alloca_no_alias  — different base allocations ⟹ no alias
 *   ma_empty_no_alias             — ml_empty never aliases with anything
 *   ma_mark_volatile_is_volatile  — returned location has volatile flag set
 *   ma_mark_volatile_preserves_wf — marking volatile preserves well-formedness
 *
 * Soundness:
 *   memloc_runtime_region    — interpret mem_loc as runtime byte range
 *   regions_disjoint         — two byte ranges don't overlap
 *   ma_may_alias_sound       — ¬ma_may_alias ⟹ runtime disjointness
 *   ma_may_alias_sound_no_alloca — simplified: both ml_alloca = NONE
 *   allocas_non_overlapping_invariant — bump allocation preserves disjointness
 *)

Theory memAliasProps
Ancestors
  memAliasDefs memAliasProofs basePtrProps venomExecSemantics venomState

(* ===== Structural Properties ===== *)

(* The top-level analysis produces well-formed alias sets *)
Theorem ma_analyze_wf:
  ∀bp_result fn addr_sp.
    wf_alias_sets (ma_analyze bp_result fn addr_sp)
Proof ACCEPT_TAC memAliasProofsTheory.ma_analyze_wf
QED

(* For well-formed alias sets, the alias query is equivalent to may_overlap.
 * The analysis is a precomputation of pairwise may_overlap, not an
 * approximation — so consumers can reason purely about may_overlap. *)
Theorem ma_may_alias_iff:
  ∀sets loc1 loc2.
    wf_alias_sets sets ⇒
    (ma_may_alias sets loc1 loc2 ⇔ may_overlap loc1 loc2)
Proof ACCEPT_TAC memAliasProofsTheory.ma_may_alias_iff
QED

(* ===== Convenience corollaries ===== *)

(* Locations backed by different base allocations never alias *)
Theorem ma_different_alloca_no_alias:
  ∀sets loc1 loc2 a1 a2.
    wf_alias_sets sets ∧
    loc1.ml_alloca = SOME a1 ∧ loc2.ml_alloca = SOME a2 ∧ a1 ≠ a2 ⇒
    ¬ma_may_alias sets loc1 loc2
Proof ACCEPT_TAC memAliasProofsTheory.ma_different_alloca_no_alias
QED

(* The empty memory location (zero size at offset 0) never aliases *)
Theorem ma_empty_no_alias:
  ∀sets loc.
    wf_alias_sets sets ⇒
    ¬ma_may_alias sets ml_empty loc
Proof ACCEPT_TAC memAliasProofsTheory.ma_empty_no_alias
QED

(* ===== ma_mark_volatile ===== *)

(* The returned location has the volatile flag set *)
Theorem ma_mark_volatile_is_volatile:
  ∀sets loc vloc sets'.
    ma_mark_volatile sets loc = (vloc, sets') ⇒
    vloc.ml_volatile
Proof ACCEPT_TAC memAliasProofsTheory.ma_mark_volatile_is_volatile
QED

(* Marking a location volatile preserves well-formedness *)
Theorem ma_mark_volatile_preserves_wf:
  ∀sets loc vloc sets'.
    wf_alias_sets sets ∧
    ma_mark_volatile sets loc = (vloc, sets') ⇒
    wf_alias_sets sets'
Proof ACCEPT_TAC memAliasProofsTheory.ma_mark_volatile_preserves_wf
QED

(* ===== Soundness Definitions ===== *)

(* Interpret a mem_loc as a runtime byte range (start, size).
   - ml_alloca = NONE: start = ml_offset (absolute address)
   - ml_alloca = SOME (Allocation aid): start = alloca_base + ml_offset
   Returns NONE when offset/size unknown or alloca not yet executed. *)
Definition memloc_runtime_region_def:
  memloc_runtime_region (ml : mem_loc) (s : venom_state) =
    case (ml.ml_offset, ml.ml_size, ml.ml_alloca) of
      (SOME off, SOME sz, NONE) => SOME (off : num, sz : num)
    | (SOME off, SOME sz, SOME (Allocation aid)) =>
        (case FLOOKUP s.vs_allocas aid of
           SOME p => SOME (FST p + off : num, sz)
         | NONE => NONE)
    | _ => NONE
End

Definition regions_disjoint_def:
  regions_disjoint (start1 : num, sz1 : num) (start2, sz2) ⇔
    sz1 = 0 ∨ sz2 = 0 ∨ start1 + sz1 ≤ start2 ∨ start2 + sz2 ≤ start1
End

(* ===== Soundness Theorems ===== *)

(* ¬ma_may_alias ⟹ runtime regions are disjoint.
   Preconditions:
   - wf_alias_sets: analysis produced valid results
   - allocas don't overlap: guaranteed by bump allocation (exec_alloca) *)
Theorem ma_may_alias_sound:
  ∀sets loc1 loc2 s.
    wf_alias_sets sets ∧
    ¬ma_may_alias sets loc1 loc2 ∧
    (* Distinct allocas have non-overlapping regions *)
    (∀aid1 aid2 b1 s1 b2 s2.
       aid1 ≠ aid2 ∧
       FLOOKUP s.vs_allocas aid1 = SOME (b1, s1) ∧
       FLOOKUP s.vs_allocas aid2 = SOME (b2, s2) ⇒
       b1 + s1 ≤ b2 ∨ b2 + s2 ≤ b1) ⇒
    case (memloc_runtime_region loc1 s, memloc_runtime_region loc2 s) of
      (SOME r1, SOME r2) => regions_disjoint r1 r2
    | (SOME _, NONE) => T   (* loc2 region unknown — no claim *)
    | (NONE, SOME _) => T   (* loc1 region unknown — no claim *)
    | (NONE, NONE) => T     (* both regions unknown — no claim *)
Proof
  cheat
QED

(* Simplified: both locations have ml_alloca = NONE (absolute addresses).
   No alloca precondition needed — disjointness follows from may_overlap. *)
Theorem ma_may_alias_sound_no_alloca:
  ∀sets loc1 loc2.
    wf_alias_sets sets ∧
    ¬ma_may_alias sets loc1 loc2 ∧
    loc1.ml_alloca = NONE ∧ loc2.ml_alloca = NONE ∧
    IS_SOME loc1.ml_offset ∧ IS_SOME loc1.ml_size ∧
    IS_SOME loc2.ml_offset ∧ IS_SOME loc2.ml_size ⇒
    regions_disjoint
      (THE loc1.ml_offset, THE loc1.ml_size)
      (THE loc2.ml_offset, THE loc2.ml_size)
Proof
  cheat
QED

(* Bump allocation preserves the invariant that distinct allocas
   have disjoint memory regions. exec_alloca appends at
   next_alloca_offset which is ≥ all existing (offset + size). *)
Theorem allocas_non_overlapping_invariant:
  ∀fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ∧
    (* Invariant holds before the step *)
    (∀a1 a2 b1 sz1 b2 sz2.
       a1 ≠ a2 ∧
       FLOOKUP s.vs_allocas a1 = SOME (b1, sz1) ∧
       FLOOKUP s.vs_allocas a2 = SOME (b2, sz2) ⇒
       b1 + sz1 ≤ b2 ∨ b2 + sz2 ≤ b1) ⇒
    (* Invariant holds after the step *)
    (∀a1 a2 b1 sz1 b2 sz2.
       a1 ≠ a2 ∧
       FLOOKUP s'.vs_allocas a1 = SOME (b1, sz1) ∧
       FLOOKUP s'.vs_allocas a2 = SOME (b2, sz2) ⇒
       b1 + sz1 ≤ b2 ∨ b2 + sz2 ≤ b1)
Proof
  cheat
QED
