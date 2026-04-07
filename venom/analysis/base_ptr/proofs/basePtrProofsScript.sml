(*
 * Base Pointer Analysis — Proofs
 *
 * TOP-LEVEL:
 *   bp_handle_inst_other_var_proof       — transfer function frame property
 *   bp_handle_inst_no_output_unchanged_proof — no-output identity
 *   bp_ptr_sound_init_proof               — FEMPTY is trivially sound
 *   bp_handle_inst_sound_proof            — transfer preserves bp_ptr_sound
 *   bp_process_block_sound_proof          — block-level soundness
 *   bp_ptr_from_op_sound_proof            — singleton pointer ⇒ exact address
 *   bp_segment_from_ops_sound_proof       — alloca-backed mem_loc soundness
 *)

Theory basePtrProofs
Ancestors
  basePtrDefs venomExecSemantics venomWf memLocDefs
Libs
  finite_mapTheory

(* Transfer function only modifies the output variable's pointer set. *)
Theorem bp_handle_inst_other_var_proof:
  ∀result inst c r v.
    bp_handle_inst result inst = (c, r) ∧
    inst_output inst ≠ SOME v ⇒
    bp_get_ptrs r v = bp_get_ptrs result v
Proof
  rw[bp_handle_inst_def] >>
  Cases_on `inst_output inst` >> gvs[LET_THM] >>
  rename1 `SOME out` >>
  Cases_on `inst.inst_opcode` >> gvs[LET_THM, bp_get_ptrs_def, FLOOKUP_UPDATE] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[bp_get_ptrs_def, FLOOKUP_UPDATE]
QED

(* No-output instructions don't modify the pointer map at all. *)
Theorem bp_handle_inst_no_output_unchanged_proof:
  ∀result inst c r.
    bp_handle_inst result inst = (c, r) ∧
    inst_output inst = NONE ⇒
    r = result
Proof
  rw[bp_handle_inst_def] >>
  Cases_on `inst_output inst` >> gvs[]
QED

(* Initialization: analysis starts from FEMPTY, which is trivially sound. *)
Theorem bp_ptr_sound_init_proof:
  ∀s. bp_ptr_sound FEMPTY s
Proof
  rw[bp_ptr_sound_def, bp_get_ptrs_def, FLOOKUP_DEF]
QED

(* Transfer function preserves bp_ptr_sound through a successful step. *)
Theorem bp_handle_inst_sound_proof:
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
Proof
  cheat
QED

(* Block-level: processing a block preserves soundness through exec_block. *)
Theorem bp_process_block_sound_proof:
  ∀bp bb c bp' fuel ctx s s'.
    bp_ptr_sound bp s ∧
    bp_process_block bp bb.bb_instructions = (c, bp') ∧
    exec_block fuel ctx bb s = OK s' ∧
    s.vs_inst_idx = 0 ∧
    bb_well_formed bb ∧
    (∀inst. MEM inst bb.bb_instructions ⇒ inst_wf inst) ∧
    ALL_DISTINCT (FLAT (MAP (λi. i.inst_outputs) bb.bb_instructions)) ∧
    (∀inst out. MEM inst bb.bb_instructions ∧
               inst_output inst = SOME out ⇒
               bp_get_ptrs bp out = []) ∧
    ctx_inst_ids_distinct ctx ∧
    (∀inst v aid off. MEM inst bb.bb_instructions ∧
       inst.inst_opcode = ALLOCA ∧
       MEM (Ptr (Allocation aid) off) (bp_get_ptrs bp v) ⇒
       aid ≠ inst.inst_id) ∧
    ALL_DISTINCT (MAP (λi. i.inst_id)
      (FILTER (λi. i.inst_opcode = ALLOCA) bb.bb_instructions)) ∧
    (∀inst v. MEM inst bb.bb_instructions ∧
       inst.inst_opcode = PHI ∧
       MEM v (MAP SND (phi_pairs inst.inst_operands)) ∧
       IS_SOME (lookup_var v s) ⇒
       bp_get_ptrs bp v ≠ []) ⇒
    bp_ptr_sound bp' s'
Proof
  cheat
QED

(* Singleton pointer ⇒ exact runtime address. *)
Theorem bp_ptr_from_op_sound_proof:
  ∀bp v aid off s.
    bp_ptr_sound bp s ∧
    bp_ptr_from_op bp (Var v) = SOME (Ptr (Allocation aid) (SOME off)) ∧
    IS_SOME (eval_operand (Var v) s) ⇒
    ∃base sz.
      FLOOKUP s.vs_allocas aid = SOME (base, sz) ∧
      eval_operand (Var v) s = SOME (n2w (base + off))
Proof
  cheat
QED

(* Alloca-backed mem_loc correctly describes runtime address. *)
Theorem bp_segment_from_ops_sound_proof:
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
Proof
  cheat
QED
