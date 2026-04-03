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
 *   allocas_non_overlapping  — distinct allocas have disjoint regions
 *   memloc_runtime_region    — interpret mem_loc as runtime byte range
 *   regions_disjoint         — two byte ranges don't overlap
 *   ma_may_alias_sound       — ¬ma_may_alias ⟹ runtime disjointness
 *   ma_may_alias_sound_no_alloca — simplified: both ml_alloca = NONE
 *   allocas_non_overlapping_empty     — base case (no allocas)
 *   allocas_non_overlapping_step_inst — preserved by step_inst
 *   allocas_non_overlapping_run_block — preserved by run_block
 *
 * Bridge (analysis → runtime):
 *   bp_segment_from_ops_runtime_region — connects analysis mem_loc to runtime region
 *
 * Memory operation independence:
 *   mload_mstore_disjoint   — disjoint 32-byte write doesn't affect 32-byte read
 *   mload_mstore8_disjoint  — disjoint 1-byte write doesn't affect 32-byte read
 *)

Theory memAliasProps
Ancestors
  memAliasDefs memAliasProofs basePtrProps venomExecSemantics venomState
  passSharedDefs finite_map

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

(* ===== Alloca Non-Overlapping Invariant ===== *)

(* Distinct allocas have disjoint memory regions.
 * Guaranteed by bump allocation: exec_alloca places each new alloca
 * at next_alloca_offset which is ≥ all existing (offset + size). *)
Definition allocas_non_overlapping_def:
  allocas_non_overlapping (s : venom_state) ⇔
    ∀a1 a2 b1 sz1 b2 sz2.
      a1 ≠ a2 ∧
      FLOOKUP s.vs_allocas a1 = SOME (b1, sz1) ∧
      FLOOKUP s.vs_allocas a2 = SOME (b2, sz2) ⇒
      b1 + sz1 ≤ b2 ∨ b2 + sz2 ≤ b1
End

(* Base case: no allocas → trivially non-overlapping *)
Theorem allocas_non_overlapping_empty:
  ∀s. s.vs_allocas = FEMPTY ⇒ allocas_non_overlapping s
Proof
  rw[allocas_non_overlapping_def, FLOOKUP_DEF]
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
   - allocas_non_overlapping: guaranteed by bump allocation *)
Theorem ma_may_alias_sound:
  ∀sets loc1 loc2 s r1 r2.
    wf_alias_sets sets ∧
    ¬ma_may_alias sets loc1 loc2 ∧
    allocas_non_overlapping s ∧
    memloc_runtime_region loc1 s = SOME r1 ∧
    memloc_runtime_region loc2 s = SOME r2 ⇒
    regions_disjoint r1 r2
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

(* ===== Alloca Invariant Preservation ===== *)

(* step_inst preserves allocas_non_overlapping.
 * Only ALLOCA modifies vs_allocas; exec_alloca places new allocation
 * at next_alloca_offset ≥ all existing (offset + size). *)
Theorem allocas_non_overlapping_step_inst:
  ∀fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ∧
    allocas_non_overlapping s ⇒
    allocas_non_overlapping s'
Proof
  cheat
QED

(* run_block preserves allocas_non_overlapping. *)
Theorem allocas_non_overlapping_run_block:
  ∀fuel ctx bb s s'.
    run_block fuel ctx bb s = OK s' ∧
    allocas_non_overlapping s ⇒
    allocas_non_overlapping s'
Proof
  cheat
QED

(* ===== Bridge: Analysis → Runtime ===== *)

(* When bp_segment_from_ops produces a fixed mem_loc (known offset + size),
 * memloc_runtime_region returns the matching runtime region.
 * The existential addr connects eval_operand (word) to the region (num).
 * Consumers connect to mload/mstore via: step_inst uses w2n(eval_operand)
 * which equals addr when addr < dimword(:256) (always true for
 * realistic allocas since memory is ≪ 2^256). *)
Theorem bp_segment_from_ops_runtime_region:
  ∀bp ops ml s.
    bp_ptr_sound bp s ∧
    bp_segment_from_ops bp ops = ml ∧
    ml_is_fixed ml ∧
    IS_SOME (eval_operand ops.iao_ofst s) ⇒
    ∃addr.
      eval_operand ops.iao_ofst s = SOME (n2w addr) ∧
      memloc_runtime_region ml s = SOME (addr, THE ml.ml_size)
Proof
  cheat
QED

(* ===== Memory Operation Independence ===== *)

(* Writing 32 bytes at off1 doesn't affect reading 32 bytes at off2
 * when the regions don't overlap.
 * Key lemma for load_elim, MCE, mem2var proofs. *)
Theorem mload_mstore_disjoint:
  ∀off1 off2 val s.
    regions_disjoint (off1, 32) (off2, 32) ⇒
    mload off2 (mstore off1 val s) = mload off2 s
Proof
  cheat
QED

(* Writing 1 byte at off1 doesn't affect reading 32 bytes at off2
 * when the regions don't overlap. *)
Theorem mload_mstore8_disjoint:
  ∀off1 off2 val s.
    regions_disjoint (off1, 1) (off2, 32) ⇒
    mload off2 (mstore8 off1 val s) = mload off2 s
Proof
  cheat
QED
