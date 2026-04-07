(*
 * Base Pointer Analysis — Properties
 *
 * Public API for base pointer analysis consumers.
 * Re-exports proven properties from basePtrProofs via ACCEPT_TAC.
 * Soundness definitions (ptr_matches_var, bp_ptr_sound, bp_ptrs_bounded)
 * are in basePtrDefs.
 *
 * Frame/lookup:
 *   bp_get_ptrs_update_same, bp_get_ptrs_update_diff, bp_get_ptrs_fempty,
 *   bp_handle_inst_other_var, bp_handle_inst_no_output_unchanged
 *
 * Soundness:
 *   bp_ptr_sound_init         — FEMPTY is trivially sound
 *   bp_handle_inst_sound      — transfer function preserves bp_ptr_sound
 *   bp_process_block_sound    — block-level soundness preservation
 *   bp_ptr_from_op_sound      — singleton pointer ⇒ exact runtime address
 *   bp_segment_from_ops_sound — alloca-backed mem_loc ⇒ runtime address
 *   bp_segment_from_ops_lit_offset — literal offset mem_loc (trivial)
 *)

Theory basePtrProps
Ancestors
  basePtrDefs basePtrProofs venomExecSemantics venomWf passSharedDefs
  memLocDefs finite_map
Libs
  pred_setLib

(* ===== bp_get_ptrs lookup lemmas ===== *)

Theorem bp_get_ptrs_update_same:
  ∀result k v. bp_get_ptrs (result |+ (k, v)) k = v
Proof
  rw[bp_get_ptrs_def, FLOOKUP_UPDATE]
QED

Theorem bp_get_ptrs_update_diff:
  ∀result k1 k2 v. k1 ≠ k2 ⇒
    bp_get_ptrs (result |+ (k1, v)) k2 = bp_get_ptrs result k2
Proof
  rw[bp_get_ptrs_def, FLOOKUP_UPDATE]
QED

Theorem bp_get_ptrs_fempty:
  ∀v. bp_get_ptrs FEMPTY v = []
Proof
  rw[bp_get_ptrs_def, FLOOKUP_DEF]
QED

(* ===== bp_handle_inst frame ===== *)

Theorem bp_handle_inst_other_var:
  ∀result inst c r v.
    bp_handle_inst result inst = (c, r) ∧
    inst_output inst ≠ SOME v ⇒
    bp_get_ptrs r v = bp_get_ptrs result v
Proof
  ACCEPT_TAC basePtrProofsTheory.bp_handle_inst_other_var_proof
QED

Theorem bp_handle_inst_no_output_unchanged:
  ∀result inst c r.
    bp_handle_inst result inst = (c, r) ∧
    inst_output inst = NONE ⇒
    r = result
Proof
  ACCEPT_TAC basePtrProofsTheory.bp_handle_inst_no_output_unchanged_proof
QED

(* ===== Soundness Theorems ===== *)

Theorem bp_ptr_sound_init:
  ∀s. bp_ptr_sound FEMPTY s
Proof ACCEPT_TAC basePtrProofsTheory.bp_ptr_sound_init_proof
QED

Theorem bp_handle_inst_sound:
  ∀bp inst c bp' fuel ctx s s'.
    bp_ptr_sound bp s ∧
    bp_handle_inst bp inst = (c, bp') ∧
    step_inst fuel ctx inst s = OK s' ∧
    inst_wf inst ∧
    (∀out. inst_output inst = SOME out ⇒ bp_get_ptrs bp out = []) ∧
    (inst_output inst = NONE ⇒ inst.inst_outputs = []) ∧
    (∀v aid off. MEM (Ptr (Allocation aid) off) (bp_get_ptrs bp v) ⇒
       FLOOKUP s'.vs_allocas aid = FLOOKUP s.vs_allocas aid) ∧
    (∀v. inst.inst_opcode = PHI ∧
         MEM v (MAP SND (phi_pairs inst.inst_operands)) ∧
         IS_SOME (lookup_var v s) ⇒
         bp_get_ptrs bp v ≠ []) ⇒
    bp_ptr_sound bp' s'
Proof ACCEPT_TAC basePtrProofsTheory.bp_handle_inst_sound_proof
QED

Theorem bp_process_block_sound:
  ∀bp bb c bp' fuel ctx s s'.
    bp_ptr_sound bp s ∧
    bp_process_block bp bb.bb_instructions = (c, bp') ∧
    run_block fuel ctx bb s = OK s' ∧
    s.vs_inst_idx = 0 ∧
    bb_well_formed bb ∧
    (∀inst. MEM inst bb.bb_instructions ⇒ inst_wf inst) ∧
    ALL_DISTINCT (FLAT (MAP (λi. i.inst_outputs) bb.bb_instructions)) ∧
    (∀inst out. MEM inst bb.bb_instructions ∧
               inst_output inst = SOME out ⇒
               bp_get_ptrs bp out = []) ∧
    (* Inst ids globally unique across context — ensures ALLOCAs in this
       block and in INVOKE callees don't collide with tracked alloca ids *)
    ctx_inst_ids_distinct ctx ∧
    (* ALLOCA freshness: inst_ids don't collide with initial bp pointers *)
    (∀inst v aid off. MEM inst bb.bb_instructions ∧
       inst.inst_opcode = ALLOCA ∧
       MEM (Ptr (Allocation aid) off) (bp_get_ptrs bp v) ⇒
       aid ≠ inst.inst_id) ∧
    (* ALLOCA inst_ids within the block are pairwise distinct *)
    ALL_DISTINCT (MAP (λi. i.inst_id)
      (FILTER (λi. i.inst_opcode = ALLOCA) bb.bb_instructions)) ∧
    (* PHI sources that are defined must have tracked ptrs *)
    (∀inst v. MEM inst bb.bb_instructions ∧
       inst.inst_opcode = PHI ∧
       MEM v (MAP SND (phi_pairs inst.inst_operands)) ∧
       IS_SOME (lookup_var v s) ⇒
       bp_get_ptrs bp v ≠ []) ⇒
    bp_ptr_sound bp' s'
Proof ACCEPT_TAC basePtrProofsTheory.bp_process_block_sound_proof
QED

Theorem bp_ptr_from_op_sound:
  ∀bp v aid off s.
    bp_ptr_sound bp s ∧
    bp_ptr_from_op bp (Var v) = SOME (Ptr (Allocation aid) (SOME off)) ∧
    IS_SOME (eval_operand (Var v) s) ⇒
    ∃base sz.
      FLOOKUP s.vs_allocas aid = SOME (base, sz) ∧
      eval_operand (Var v) s = SOME (n2w (base + off))
Proof ACCEPT_TAC basePtrProofsTheory.bp_ptr_from_op_sound_proof
QED

Theorem bp_segment_from_ops_sound:
  ∀bp ops ml aid off s.
    bp_ptr_sound bp s ∧
    bp_segment_from_ops bp ops = ml ∧
    ml_is_fixed ml ∧
    ml.ml_alloca = SOME (Allocation aid) ∧
    ml.ml_offset = SOME off ∧
    IS_SOME (eval_operand ops.iao_ofst s) ⇒
    ∃base sz.
      FLOOKUP s.vs_allocas aid = SOME (base, sz) ∧
      eval_operand ops.iao_ofst s = SOME (n2w (base + off))
Proof ACCEPT_TAC basePtrProofsTheory.bp_segment_from_ops_sound_proof
QED

Theorem bp_segment_from_ops_lit_offset:
  ∀bp (n : bytes32) sz_op.
    (bp_segment_from_ops bp
      <| iao_ofst := Lit n; iao_size := sz_op;
         iao_max_size := sz_op |>).ml_offset = SOME (w2n n) ∧
    (bp_segment_from_ops bp
      <| iao_ofst := Lit n; iao_size := sz_op;
         iao_max_size := sz_op |>).ml_alloca = NONE
Proof
  simp[bp_segment_from_ops_def, LET_THM]
QED
