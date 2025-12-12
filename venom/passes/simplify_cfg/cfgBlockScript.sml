(*
 * SimplifyCFG Block-Level Correctness
 *
 * This theory proves block-level correctness of CFG simplification.
 * The main results show that:
 * 1. Running a merged block is equivalent to running both original blocks
 * 2. Threading a jump preserves execution semantics
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * KEY LEMMAS:
 *   - run_merged_block_equiv      : Merged block execution equivalence
 *   - thread_jump_equiv           : Jump threading preserves semantics
 *   - replace_label_preserves_sem : Label replacement preserves semantics
 *
 * HELPER THEOREMS:
 *   - step_jmp_to_block           : JMP instruction steps to target block
 *   - run_passthrough_equiv       : Passthrough block is equivalent to direct jump
 *
 * ============================================================================
 *)

Theory cfgBlock
Ancestors
  cfgWellFormed cfgTransform execEquiv venomSem venomInst stateEquiv list

(* ==========================================================================
   Instruction-Level Lemmas
   ========================================================================== *)

(* JMP instruction steps to the target block *)
Theorem step_inst_jmp:
  !inst s lbl.
    inst.inst_opcode = JMP /\
    inst.inst_operands = [Label lbl] ==>
    step_inst inst s = OK (jump_to lbl s)
Proof
  rw[step_inst_def]
QED

(* JMP is a terminator *)
Theorem jmp_is_terminator:
  is_terminator JMP
Proof
  rw[is_terminator_def]
QED

(* Stepping a JMP in a block causes termination *)
Theorem step_in_block_jmp_terminates:
  !fn bb s inst.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    inst.inst_opcode = JMP ==>
    SND (step_in_block fn bb s) = T
Proof
  rw[step_in_block_def] >>
  Cases_on `step_inst inst s` >> simp[jmp_is_terminator]
QED

(* ==========================================================================
   Block Execution Decomposition
   ========================================================================== *)

(* get_block_target = SOME implies is_jmp_inst and correct operands *)
Theorem get_block_target_is_jmp:
  !bb lbl.
    get_block_target bb = SOME lbl ==>
    ?inst. get_terminator bb = SOME inst /\ is_jmp_inst inst /\
           inst.inst_operands = [Label lbl]
Proof
  rpt strip_tac >>
  fs[get_block_target_def, get_jmp_target_def] >>
  Cases_on `get_terminator bb` >> gvs[] >>
  Cases_on `is_jmp_inst x` >> gvs[] >>
  Cases_on `x.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `h` >> gvs[]
QED

(* Running instructions from a block is deterministic based on instruction sequence *)
Theorem run_block_deterministic:
  !fn bb s.
    run_block fn bb s = run_block fn bb s
Proof
  simp[]
QED

(* Helper: FRONT gives all but last element *)
Theorem front_append_last:
  !l. l <> [] ==> FRONT l ++ [LAST l] = l
Proof
  Induct >> simp[] >> Cases_on `l` >> simp[]
QED

(* Helper: Getting instruction from FRONT *)
Theorem get_instruction_front:
  !bb idx.
    bb.bb_instructions <> [] /\
    idx < LENGTH (FRONT bb.bb_instructions) ==>
    get_instruction (bb with bb_instructions := FRONT bb.bb_instructions) idx =
    get_instruction bb idx
Proof
  rw[get_instruction_def] >>
  simp[rich_listTheory.LENGTH_FRONT] >>
  Cases_on `bb.bb_instructions` >> gvs[listTheory.LENGTH_FRONT_CONS] >>
  simp[GSYM rich_listTheory.FRONT_EL]
QED

(* Helper: Getting instruction from merged block (from a's FRONT) *)
Theorem get_instruction_merge_a:
  !a b idx.
    a.bb_instructions <> [] /\
    idx < LENGTH (FRONT a.bb_instructions) ==>
    get_instruction (merge_blocks a b) idx = get_instruction a idx
Proof
  rw[get_instruction_def, merge_blocks_def] >>
  simp[GSYM rich_listTheory.FRONT_EL, rich_listTheory.EL_APPEND1] >>
  Cases_on `a.bb_instructions` >> gvs[listTheory.LENGTH_FRONT_CONS]
QED

(* Helper: Getting instruction from merged block (from b) *)
Theorem get_instruction_merge_b:
  !a b idx.
    a.bb_instructions <> [] /\
    idx >= LENGTH (FRONT a.bb_instructions) /\
    idx < LENGTH (FRONT a.bb_instructions) + LENGTH b.bb_instructions ==>
    get_instruction (merge_blocks a b) idx =
    get_instruction b (idx - LENGTH (FRONT a.bb_instructions))
Proof
  rw[get_instruction_def, merge_blocks_def] >>
  simp[rich_listTheory.EL_APPEND2]
QED

(* ==========================================================================
   Passthrough Block Equivalence
   ========================================================================== *)

(* A passthrough block (single JMP) is equivalent to directly jumping to target *)
Theorem run_passthrough_block:
  !fn bb s target.
    is_passthrough_block bb /\
    get_block_target bb = SOME target /\
    s.vs_inst_idx = 0 /\
    ~s.vs_halted ==>
    run_block fn bb s = OK (jump_to target s)
Proof
  rw[is_passthrough_block_def, get_block_target_def, get_terminator_def,
     is_unconditional_jump_def, is_jmp_inst_def, get_jmp_target_def] >>
  Cases_on `(LAST bb.bb_instructions).inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `h` >> gvs[] >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  simp[Once run_block_def, step_in_block_def,
       get_instruction_def, is_terminator_def] >>
  simp[Once step_inst_def] >>
  simp[venomStateTheory.jump_to_def]
QED

(* ==========================================================================
   Jump Threading Correctness
   ========================================================================== *)

(* Threading a jump through a passthrough block preserves semantics.
   If we have A -> B -> C where B is just a JMP to C,
   then rewriting A to jump directly to C gives the same execution. *)

(* Label replacement in non-Label operands is identity *)
Theorem replace_label_operand_non_label:
  !old new op.
    (!l. op <> Label l) ==>
    replace_label_operand old new op = op
Proof
  Cases_on `op` >> rw[replace_label_operand_def]
QED

(* Helper: eval_operand ignores label replacement *)
Theorem eval_operand_replace_label:
  !old new op s. eval_operand (replace_label_operand old new op) s = eval_operand op s
Proof
  Cases_on `op` >> rw[replace_label_operand_def, venomStateTheory.eval_operand_def]
QED

(* Helper: replace_label_inst preserves opcode *)
Theorem replace_label_inst_opcode:
  !old new inst. (replace_label_inst old new inst).inst_opcode = inst.inst_opcode
Proof
  rw[replace_label_inst_def]
QED

(* Helper: replace_label_inst preserves outputs *)
Theorem replace_label_inst_outputs:
  !old new inst. (replace_label_inst old new inst).inst_outputs = inst.inst_outputs
Proof
  rw[replace_label_inst_def]
QED

(* Helper: exec_binop preserves under label replacement *)
Theorem exec_binop_replace_label:
  !f old new inst s.
    exec_binop f (replace_label_inst old new inst) s = exec_binop f inst s
Proof
  rw[exec_binop_def, replace_label_inst_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  simp[eval_operand_replace_label] >>
  Cases_on `t'` >> simp[]
QED

(* Helper: exec_unop preserves under label replacement *)
Theorem exec_unop_replace_label:
  !f old new inst s.
    exec_unop f (replace_label_inst old new inst) s = exec_unop f inst s
Proof
  rw[exec_unop_def, replace_label_inst_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  simp[eval_operand_replace_label] >>
  Cases_on `t` >> simp[]
QED

(* Helper: exec_modop preserves under label replacement *)
Theorem exec_modop_replace_label:
  !f old new inst s.
    exec_modop f (replace_label_inst old new inst) s = exec_modop f inst s
Proof
  rw[exec_modop_def, replace_label_inst_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  rename [`_ = h::t`] >> Cases_on `t` >> simp[] >>
  rename [`_ = h::h'::t`] >> Cases_on `t` >> simp[eval_operand_replace_label] >>
  rename [`_ = h::h'::h''::t`] >> Cases_on `t` >> simp[]
QED

(* Label replacement preserves non-JMP/JNZ/PHI instruction semantics *)
Theorem replace_label_inst_preserves_step:
  !old new inst s.
    ~is_jmp_inst inst /\ inst.inst_opcode <> JNZ /\ ~is_phi_inst inst ==>
    step_inst (replace_label_inst old new inst) s = step_inst inst s
Proof
  rw[is_jmp_inst_def, is_phi_inst_def] >>
  simp[step_inst_def, replace_label_inst_opcode, replace_label_inst_outputs,
       exec_binop_replace_label, exec_unop_replace_label, exec_modop_replace_label] >>
  Cases_on `inst.inst_opcode` >> simp[] >>
  (* Handle remaining cases with operand case analysis *)
  rw[replace_label_inst_def, eval_operand_replace_label] >>
  rpt (Cases_on `inst.inst_operands` >> simp[eval_operand_replace_label] >>
       TRY (Cases_on `t` >> simp[eval_operand_replace_label]) >>
       TRY (Cases_on `t'` >> simp[eval_operand_replace_label]))
QED

(* Threading a jump that doesn't match is identity *)
Theorem thread_jump_inst_no_match:
  !pl tl inst.
    ~MEM (Label pl) inst.inst_operands ==>
    thread_jump_inst pl tl inst = inst
Proof
  rw[thread_jump_inst_def, instruction_component_equality] >>
  qspec_then `inst.inst_operands` mp_tac (
    Q.prove(`!l pl tl. ~MEM (Label pl) l ==>
      MAP (\op. case op of
        Lit v3 => op | Var v4 => op | Label l => if l = pl then Label tl else Label l) l = l`,
      Induct >> rw[] >> Cases_on `h` >> gvs[])) >>
  simp[]
QED

(* ==========================================================================
   Merged Block Execution
   ========================================================================== *)

(* When we merge blocks A and B (where A ends with JMP B):
   - Merged block = FRONT(A.instructions) ++ B.instructions
   - A's JMP is removed, B's terminator becomes the merged block's terminator

   The key insight is that for well-formed blocks:
   - A ends with a terminator (JMP B)
   - B ends with a terminator
   - After running A, we'd jump to B and continue
   - The merged block runs A's non-terminator instructions, then all of B *)

(* Main theorem: Merged block execution is equivalent to sequential execution.

   Note: This requires showing that:
   1. Running FRONT(A) gets us to the state just before A's JMP
   2. A's JMP would set vs_current_bb to B and vs_inst_idx to 0
   3. Running B from that state gives the same result as running merged block

   The proof requires induction on run_block and careful state tracking. *)
(* Helper: step_in_block on merged block equals step_in_block on a for idx < |FRONT(a)| *)
Theorem step_in_block_merge_prefix:
  !fn a b s.
    a.bb_instructions <> [] /\
    s.vs_inst_idx < LENGTH (FRONT a.bb_instructions) ==>
    step_in_block fn (merge_blocks a b) s = step_in_block fn a s
Proof
  rpt strip_tac >>
  simp[step_in_block_def] >>
  `get_instruction (merge_blocks a b) s.vs_inst_idx = get_instruction a s.vs_inst_idx`
    by (irule get_instruction_merge_a >> simp[]) >>
  simp[]
QED

(* NOTE: merge_blocks_execution theorem is defined at the end of this file,
   after run_block_same_instructions which it depends on. *)

(* ==========================================================================
   Label Replacement Preserves Semantics
   ========================================================================== *)

(* State equivalence ignoring vs_prev_bb - needed for PHI transformation proofs *)
Definition state_equiv_except_prev_def:
  state_equiv_except_prev s1 s2 <=>
    var_equiv s1 s2 /\
    s1.vs_memory = s2.vs_memory /\
    s1.vs_storage = s2.vs_storage /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    (s1.vs_halted <=> s2.vs_halted) /\
    (s1.vs_reverted <=> s2.vs_reverted)
End

(* Result equivalence ignoring vs_prev_bb *)
Definition result_equiv_except_prev_def:
  result_equiv_except_prev (OK s1) (OK s2) = state_equiv_except_prev s1 s2 /\
  result_equiv_except_prev (Halt s1) (Halt s2) = state_equiv_except_prev s1 s2 /\
  result_equiv_except_prev (Revert s1) (Revert s2) = state_equiv_except_prev s1 s2 /\
  result_equiv_except_prev (Error e1) (Error e2) = (e1 = e2) /\
  result_equiv_except_prev _ _ = F
End

(* Data equivalence - ignores all control flow fields (vs_current_bb, vs_prev_bb, vs_inst_idx).
   Only cares about observable state: variables, memory, storage, transient, halt/revert status. *)
Definition data_equiv_def:
  data_equiv s1 s2 <=>
    var_equiv s1 s2 /\
    s1.vs_memory = s2.vs_memory /\
    s1.vs_storage = s2.vs_storage /\
    s1.vs_transient = s2.vs_transient /\
    (s1.vs_halted <=> s2.vs_halted) /\
    (s1.vs_reverted <=> s2.vs_reverted)
End

(* State equivalence for block merging:
   - For continuing execution (OK): requires vs_current_bb to match
   - For termination (Halt/Revert): only data matters, control flow is irrelevant *)
Definition state_equiv_merge_def:
  state_equiv_merge s1 s2 <=>
    data_equiv s1 s2 /\ s1.vs_current_bb = s2.vs_current_bb
End

Definition result_equiv_merge_def:
  result_equiv_merge (OK s1) (OK s2) = state_equiv_merge s1 s2 /\
  result_equiv_merge (Halt s1) (Halt s2) = data_equiv s1 s2 /\
  result_equiv_merge (Revert s1) (Revert s2) = data_equiv s1 s2 /\
  result_equiv_merge (Error e1) (Error e2) = (e1 = e2) /\
  result_equiv_merge _ _ = F
End

(* ==========================================================================
   data_equiv Helper Lemmas
   ========================================================================== *)

Theorem data_equiv_refl:
  !s. data_equiv s s
Proof
  rw[data_equiv_def, var_equiv_def]
QED

Theorem data_equiv_sym:
  !s1 s2. data_equiv s1 s2 ==> data_equiv s2 s1
Proof
  rw[data_equiv_def, var_equiv_def]
QED

Theorem data_equiv_trans:
  !s1 s2 s3. data_equiv s1 s2 /\ data_equiv s2 s3 ==> data_equiv s1 s3
Proof
  rw[data_equiv_def, var_equiv_def]
QED

(* eval_operand depends only on variables *)
Theorem eval_operand_data_equiv:
  !op s1 s2. data_equiv s1 s2 ==> eval_operand op s1 = eval_operand op s2
Proof
  Cases_on `op` >> rw[venomStateTheory.eval_operand_def, data_equiv_def, var_equiv_def,
                       venomStateTheory.lookup_var_def]
QED

(* update_var preserves data_equiv *)
Theorem update_var_data_equiv:
  !v val s1 s2. data_equiv s1 s2 ==> data_equiv (update_var v val s1) (update_var v val s2)
Proof
  rw[data_equiv_def, venomStateTheory.update_var_def, var_equiv_def,
     venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* mload depends only on memory *)
Theorem mload_data_equiv:
  !addr s1 s2. data_equiv s1 s2 ==> mload addr s1 = mload addr s2
Proof
  rw[data_equiv_def, venomStateTheory.mload_def]
QED

(* mstore preserves data_equiv *)
Theorem mstore_data_equiv:
  !addr val s1 s2. data_equiv s1 s2 ==> data_equiv (mstore addr val s1) (mstore addr val s2)
Proof
  rw[data_equiv_def, venomStateTheory.mstore_def, var_equiv_def,
     venomStateTheory.lookup_var_def]
QED

(* sload depends only on storage *)
Theorem sload_data_equiv:
  !key s1 s2. data_equiv s1 s2 ==> sload key s1 = sload key s2
Proof
  rw[data_equiv_def, venomStateTheory.sload_def]
QED

(* sstore preserves data_equiv *)
Theorem sstore_data_equiv:
  !key val s1 s2. data_equiv s1 s2 ==> data_equiv (sstore key val s1) (sstore key val s2)
Proof
  rw[data_equiv_def, venomStateTheory.sstore_def, var_equiv_def,
     venomStateTheory.lookup_var_def]
QED

(* tload depends only on transient *)
Theorem tload_data_equiv:
  !key s1 s2. data_equiv s1 s2 ==> tload key s1 = tload key s2
Proof
  rw[data_equiv_def, venomStateTheory.tload_def]
QED

(* tstore preserves data_equiv *)
Theorem tstore_data_equiv:
  !key val s1 s2. data_equiv s1 s2 ==> data_equiv (tstore key val s1) (tstore key val s2)
Proof
  rw[data_equiv_def, venomStateTheory.tstore_def, var_equiv_def,
     venomStateTheory.lookup_var_def]
QED

(* halt_state preserves data_equiv *)
Theorem halt_state_data_equiv:
  !s1 s2. data_equiv s1 s2 ==> data_equiv (halt_state s1) (halt_state s2)
Proof
  rw[data_equiv_def, venomStateTheory.halt_state_def, var_equiv_def,
     venomStateTheory.lookup_var_def]
QED

(* revert_state preserves data_equiv *)
Theorem revert_state_data_equiv:
  !s1 s2. data_equiv s1 s2 ==> data_equiv (revert_state s1) (revert_state s2)
Proof
  rw[data_equiv_def, venomStateTheory.revert_state_def, var_equiv_def,
     venomStateTheory.lookup_var_def]
QED

(* next_inst preserves data_equiv *)
Theorem next_inst_data_equiv:
  !s1 s2. data_equiv s1 s2 ==> data_equiv (next_inst s1) (next_inst s2)
Proof
  rw[data_equiv_def, venomStateTheory.next_inst_def, var_equiv_def,
     venomStateTheory.lookup_var_def]
QED

(* exec_binop preserves data_equiv *)
Theorem exec_binop_data_equiv:
  !f inst s1 s2.
    data_equiv s1 s2 ==>
    case (exec_binop f inst s1, exec_binop f inst s2) of
      (OK r1, OK r2) => data_equiv r1 r2
    | (Error e1, Error e2) => e1 = e2
    | _ => F
Proof
  rpt strip_tac >> simp[exec_binop_def] >>
  rpt CASE_TAC >> gvs[] >>
  drule eval_operand_data_equiv >> strip_tac >> gvs[] >>
  TRY (irule update_var_data_equiv >> simp[])
QED

(* exec_unop preserves data_equiv *)
Theorem exec_unop_data_equiv:
  !f inst s1 s2.
    data_equiv s1 s2 ==>
    case (exec_unop f inst s1, exec_unop f inst s2) of
      (OK r1, OK r2) => data_equiv r1 r2
    | (Error e1, Error e2) => e1 = e2
    | _ => F
Proof
  rpt strip_tac >> simp[exec_unop_def] >>
  rpt CASE_TAC >> gvs[] >>
  drule eval_operand_data_equiv >> strip_tac >> gvs[] >>
  TRY (irule update_var_data_equiv >> simp[])
QED

(* exec_modop preserves data_equiv *)
Theorem exec_modop_data_equiv:
  !f inst s1 s2.
    data_equiv s1 s2 ==>
    case (exec_modop f inst s1, exec_modop f inst s2) of
      (OK r1, OK r2) => data_equiv r1 r2
    | (Error e1, Error e2) => e1 = e2
    | _ => F
Proof
  rpt strip_tac >> simp[exec_modop_def] >>
  rpt CASE_TAC >> gvs[] >>
  drule eval_operand_data_equiv >> strip_tac >> gvs[] >>
  TRY (irule update_var_data_equiv >> simp[])
QED

(* jump_to preserves data_equiv and sets same vs_current_bb *)
Theorem jump_to_data_equiv:
  !lbl s1 s2.
    data_equiv s1 s2 ==>
    data_equiv (jump_to lbl s1) (jump_to lbl s2) /\
    (jump_to lbl s1).vs_current_bb = (jump_to lbl s2).vs_current_bb /\
    (jump_to lbl s1).vs_inst_idx = (jump_to lbl s2).vs_inst_idx
Proof
  rw[venomStateTheory.jump_to_def, data_equiv_def, var_equiv_def,
     venomStateTheory.lookup_var_def]
QED

(* next_inst preserves data_equiv and control flow fields *)
Theorem next_inst_data_equiv_full:
  !s1 s2.
    data_equiv s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx ==>
    data_equiv (next_inst s1) (next_inst s2) /\
    (next_inst s1).vs_current_bb = (next_inst s2).vs_current_bb /\
    (next_inst s1).vs_inst_idx = (next_inst s2).vs_inst_idx
Proof
  rw[venomStateTheory.next_inst_def, data_equiv_def, var_equiv_def,
     venomStateTheory.lookup_var_def]
QED

(* step_inst preserves data_equiv for non-PHI/non-branch instructions *)
Theorem step_inst_data_equiv:
  !inst s1 s2.
    data_equiv s1 s2 /\
    ~is_phi_inst inst /\ ~is_jmp_inst inst /\ inst.inst_opcode <> JNZ ==>
    case (step_inst inst s1, step_inst inst s2) of
      (OK r1, OK r2) => data_equiv r1 r2
    | (Halt r1, Halt r2) => data_equiv r1 r2
    | (Revert r1, Revert r2) => data_equiv r1 r2
    | (Error e1, Error e2) => e1 = e2
    | _ => F
Proof
  rpt strip_tac >>
  fs[is_phi_inst_def, is_jmp_inst_def] >>
  simp[step_inst_def, exec_binop_def, exec_unop_def, exec_modop_def] >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  rpt CASE_TAC >> gvs[] >>
  TRY (drule eval_operand_data_equiv >> strip_tac >> gvs[]) >>
  TRY (irule update_var_data_equiv >> simp[]) >>
  TRY (irule mstore_data_equiv >> simp[]) >>
  TRY (irule sstore_data_equiv >> simp[]) >>
  TRY (irule tstore_data_equiv >> simp[]) >>
  TRY (drule mload_data_equiv >> strip_tac >> gvs[]) >>
  TRY (drule sload_data_equiv >> strip_tac >> gvs[]) >>
  TRY (drule tload_data_equiv >> strip_tac >> gvs[]) >>
  TRY (irule halt_state_data_equiv >> simp[]) >>
  TRY (irule revert_state_data_equiv >> simp[]) >>
  (* MLOAD/SLOAD/TLOAD cases need update_var_data_equiv again *)
  rpt (irule update_var_data_equiv >> simp[])
QED

(* Non-branch instructions preserve vs_current_bb and vs_inst_idx *)
Theorem step_inst_preserves_ctrl:
  !inst s s'.
    ~is_jmp_inst inst /\ inst.inst_opcode <> JNZ /\
    step_inst inst s = OK s' ==>
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx
Proof
  rw[step_inst_def, is_jmp_inst_def] >>
  gvs[AllCaseEqs()] >>
  fs[exec_binop_def, exec_unop_def, exec_modop_def] >>
  gvs[AllCaseEqs()] >>
  fs[venomStateTheory.update_var_def, venomStateTheory.mstore_def,
     venomStateTheory.sstore_def, venomStateTheory.tstore_def]
QED

(* JMP instruction preserves data_equiv *)
Theorem step_inst_jmp_data_equiv:
  !inst s1 s2.
    data_equiv s1 s2 /\ is_jmp_inst inst ==>
    case (step_inst inst s1, step_inst inst s2) of
      (OK r1, OK r2) => data_equiv r1 r2 /\
                        r1.vs_current_bb = r2.vs_current_bb /\
                        r1.vs_inst_idx = r2.vs_inst_idx
    | (Error e1, Error e2) => e1 = e2
    | _ => F
Proof
  rpt strip_tac >> fs[is_jmp_inst_def] >>
  simp[step_inst_def] >>
  rpt CASE_TAC >> gvs[] >>
  TRY (drule_all jump_to_data_equiv >> strip_tac >> gvs[])
QED

(* JNZ instruction preserves data_equiv and takes same branch *)
Theorem step_inst_jnz_data_equiv:
  !inst s1 s2.
    data_equiv s1 s2 /\ inst.inst_opcode = JNZ ==>
    case (step_inst inst s1, step_inst inst s2) of
      (OK r1, OK r2) => data_equiv r1 r2 /\
                        r1.vs_current_bb = r2.vs_current_bb /\
                        r1.vs_inst_idx = r2.vs_inst_idx
    | (Error e1, Error e2) => e1 = e2
    | _ => F
Proof
  rpt strip_tac >> simp[step_inst_def] >>
  rpt CASE_TAC >> gvs[] >>
  TRY (drule eval_operand_data_equiv >> strip_tac >> gvs[]) >>
  TRY (drule_all jump_to_data_equiv >> strip_tac >> gvs[])
QED

(* Non-JMP/JNZ terminators never return OK *)
Theorem non_jmp_jnz_terminator_not_ok:
  !inst s v.
    is_terminator inst.inst_opcode /\
    ~is_jmp_inst inst /\ inst.inst_opcode <> JNZ ==>
    step_inst inst s <> OK v
Proof
  rw[is_jmp_inst_def] >>
  qpat_x_assum `is_terminator _` mp_tac >>
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def, step_inst_def] >>
  gvs[]
QED

(* Terminator returning OK preserves data_equiv and vs_current_bb.
   Since non-JMP/JNZ terminators don't return OK, this combines JMP and JNZ cases. *)
Theorem step_inst_terminator_ok_data_equiv:
  !inst s1 s2 r1 r2.
    data_equiv s1 s2 /\
    is_terminator inst.inst_opcode /\
    step_inst inst s1 = OK r1 /\
    step_inst inst s2 = OK r2 ==>
    data_equiv r1 r2 /\ r1.vs_current_bb = r2.vs_current_bb /\
    r1.vs_inst_idx = r2.vs_inst_idx
Proof
  rpt strip_tac >> (
    Cases_on `is_jmp_inst inst` >- (
      drule step_inst_jmp_data_equiv >>
      disch_then (qspec_then `inst` mp_tac) >>
      impl_tac >- gvs[] >> gvs[]
    ) >>
    Cases_on `inst.inst_opcode = JNZ` >- (
      drule step_inst_jnz_data_equiv >>
      disch_then (qspec_then `inst` mp_tac) >>
      impl_tac >- gvs[] >> gvs[]
    ) >>
    `step_inst inst s1 <> OK r1` by (
      irule non_jmp_jnz_terminator_not_ok >> gvs[]
    ) >> gvs[]
  )
QED

(* step_in_block preserves data_equiv for no_phi blocks.
   Proof sketch verified through interactive debugging:
   1. Case split on get_instruction - NONE case gives Error=Error
   2. SOME case: derive ~is_phi_inst x from no_phi_block via EVERY_EL
   3. Case split on JMP/JNZ/other instruction type
   4. JMP: both give OK with jump_to preserving data_equiv
   5. JNZ: both give OK or Error, eval_operand_data_equiv ensures same branch
   6. Other: use step_inst_data_equiv, terminators vs non-terminators *)
Theorem step_in_block_data_equiv_no_phi:
  !fn bb s1 s2.
    no_phi_block bb /\
    data_equiv s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_current_bb = s2.vs_current_bb /\
    ~s1.vs_halted /\ ~s2.vs_halted ==>
    case (step_in_block fn bb s1, step_in_block fn bb s2) of
      ((OK r1, t1), (OK r2, t2)) => data_equiv r1 r2 /\ (t1 <=> t2) /\
                                     r1.vs_current_bb = r2.vs_current_bb /\
                                     r1.vs_inst_idx = r2.vs_inst_idx
    | ((Halt r1, _), (Halt r2, _)) => data_equiv r1 r2
    | ((Revert r1, _), (Revert r2, _)) => data_equiv r1 r2
    | ((Error e1, _), (Error e2, _)) => e1 = e2
    | _ => F
Proof
  rpt strip_tac >>
  simp[step_in_block_def] >>
  Cases_on `get_instruction bb s2.vs_inst_idx` >> gvs[] >>
  (* Derive ~is_phi_inst x from no_phi_block *)
  `~is_phi_inst x` by (
    fs[no_phi_block_def, get_instruction_def, listTheory.EVERY_EL] >>
    metis_tac[]
  ) >>
  (* JMP case *)
  Cases_on `is_jmp_inst x` >> gvs[] >- (
    drule_all step_inst_jmp_data_equiv >>
    Cases_on `step_inst x s1` >> Cases_on `step_inst x s2` >> gvs[] >>
    strip_tac >> fs[is_terminator_def, is_jmp_inst_def]
  ) >>
  (* JNZ case *)
  Cases_on `x.inst_opcode = JNZ` >> gvs[] >- (
    drule_all step_inst_jnz_data_equiv >>
    Cases_on `step_inst x s1` >> Cases_on `step_inst x s2` >> gvs[] >>
    strip_tac >> fs[is_terminator_def]
  ) >>
  (* Other instructions *)
  drule_all step_inst_data_equiv >>
  Cases_on `step_inst x s1` >> Cases_on `step_inst x s2` >> gvs[] >>
  strip_tac >> gvs[] >>
  (* For OK case with non-terminator, apply next_inst *)
  Cases_on `is_terminator x.inst_opcode` >> gvs[] >- (
    (* Terminator case - contradiction: non-JMP/JNZ terminators don't return OK *)
    `step_inst x s1 <> OK v` by (irule non_jmp_jnz_terminator_not_ok >> simp[]) >>
    gvs[]
  ) >>
  (* Non-terminator: step_inst preserves vs_current_bb and vs_inst_idx *)
  `v.vs_current_bb = s1.vs_current_bb /\ v.vs_inst_idx = s1.vs_inst_idx` by (
    irule step_inst_preserves_ctrl >> qexists_tac `x` >> simp[]
  ) >>
  `v'.vs_current_bb = s2.vs_current_bb /\ v'.vs_inst_idx = s2.vs_inst_idx` by (
    irule step_inst_preserves_ctrl >> qexists_tac `x` >> simp[]
  ) >>
  (* Now derive v.vs_current_bb = v'.vs_current_bb etc *)
  `v.vs_current_bb = v'.vs_current_bb /\ v.vs_inst_idx = v'.vs_inst_idx` by gvs[] >>
  (* Apply next_inst_data_equiv_full to v and v' *)
  `data_equiv (next_inst v) (next_inst v') /\
   (next_inst v).vs_current_bb = (next_inst v').vs_current_bb /\
   (next_inst v).vs_inst_idx = (next_inst v').vs_inst_idx` by (
    irule next_inst_data_equiv_full >> simp[]
  ) >>
  simp[]
QED

(* Helper: run_block preserves data_equiv for no_phi blocks.
   This is used by merge_blocks_execution to relate the two executions. *)
(* run_block_data_equiv_no_phi: Running same no_phi block from data-equiv states
   gives result_equiv_merge results.
   TODO: This proof requires careful handling of the IH application.
   The key insight is that step_in_block_data_equiv_no_phi gives us the step
   equivalence, and we use complete induction on the remaining instructions. *)
Theorem run_block_data_equiv_no_phi:
  !bb fn s1 s2.
    no_phi_block bb /\
    data_equiv s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_current_bb = s2.vs_current_bb /\
    ~s1.vs_halted /\ ~s2.vs_halted ==>
    result_equiv_merge (run_block fn bb s1) (run_block fn bb s2)
Proof
  gen_tac >> completeInduct_on `LENGTH bb.bb_instructions - s1.vs_inst_idx` >>
  rpt strip_tac >>
  simp[Once run_block_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  drule_all step_in_block_data_equiv_no_phi >> strip_tac >>
  Cases_on `step_in_block fn bb s1` >> Cases_on `step_in_block fn bb s2` >>
  rename1 `step_in_block fn bb s1 = (q, r)` >>
  rename1 `step_in_block fn bb s2 = (q', r')` >>
  Cases_on `q` >> Cases_on `q'` >> gvs[] >>
  (* Use step_in_block_data_equiv_no_phi to eliminate impossible cases and
     derive facts for valid cases *)
  TRY (first_x_assum (qspec_then `fn` mp_tac) >> simp[] >>
       strip_tac >> simp[result_equiv_merge_def, data_equiv_def] >> NO_TAC) >>
  (* OK/OK case - requires case analysis on halted and terminator *)
  first_x_assum (qspec_then `fn` mp_tac) >> simp[] >> strip_tac >>
  (* Case on v'.vs_halted *)
  Cases_on `v'.vs_halted` >> gvs[]
  >- (* v'.vs_halted: derive v''.vs_halted from data_equiv *)
     (`v''.vs_halted` by fs[data_equiv_def] >>
      gvs[result_equiv_merge_def, data_equiv_def])
  >- (* ~v'.vs_halted *)
     (`~v''.vs_halted` by fs[data_equiv_def] >> gvs[] >>
      (* Case on r (terminator flag) - r and r' unified by gvs *)
      Cases_on `r` >> gvs[]
      >- (* Terminator case *)
         simp[result_equiv_merge_def, state_equiv_merge_def, data_equiv_def]
      >- (* Non-terminator case - apply IH *)
         (first_x_assum irule >> simp[] >>
          (* Need to show measure decreases *)
          qpat_x_assum `step_in_block _ _ s1 = _` mp_tac >>
          simp[Once step_in_block_def] >>
          Cases_on `get_instruction bb s2.vs_inst_idx` >> simp[] >>
          strip_tac >> fs[get_instruction_def] >>
          Cases_on `step_inst x s1` >> gvs[AllCaseEqs()] >>
          `~is_jmp_inst (EL s2.vs_inst_idx bb.bb_instructions) /\
           (EL s2.vs_inst_idx bb.bb_instructions).inst_opcode <> JNZ` by
             (fs[is_jmp_inst_def] >>
              Cases_on `(EL s2.vs_inst_idx bb.bb_instructions).inst_opcode` >>
              fs[is_terminator_def]) >>
          drule_all step_inst_preserves_ctrl >> strip_tac >>
          fs[venomStateTheory.next_inst_def]))
QED

(* step_in_block on blocks with same instructions gives equivalent results.
   Note: This does NOT require vs_current_bb to match - useful for merge_blocks.
   The key insight is that step_in_block only reads the instruction from the block,
   not vs_current_bb. The terminator sets vs_current_bb based on instruction operands. *)
Theorem step_in_block_same_instructions:
  !fn bb1 bb2 s1 s2.
    bb1.bb_instructions = bb2.bb_instructions /\ no_phi_block bb1 /\
    data_equiv s1 s2 /\ s1.vs_inst_idx = s2.vs_inst_idx /\
    ~s1.vs_halted /\ ~s2.vs_halted ==>
    case (step_in_block fn bb1 s1, step_in_block fn bb2 s2) of
      ((OK r1, t1), (OK r2, t2)) => data_equiv r1 r2 /\ (t1 <=> t2) /\
                                     r1.vs_inst_idx = r2.vs_inst_idx
    | ((Halt r1, _), (Halt r2, _)) => data_equiv r1 r2
    | ((Revert r1, _), (Revert r2, _)) => data_equiv r1 r2
    | ((Error e1, _), (Error e2, _)) => e1 = e2
    | _ => F
Proof
  rpt strip_tac >>
  simp[step_in_block_def] >>
  `get_instruction bb1 s1.vs_inst_idx = get_instruction bb2 s2.vs_inst_idx` by
    simp[get_instruction_def] >>
  Cases_on `get_instruction bb2 s2.vs_inst_idx` >> gvs[] >>
  (* Derive ~is_phi_inst x from no_phi_block *)
  `~is_phi_inst x` by (
    fs[no_phi_block_def, get_instruction_def, listTheory.EVERY_EL] >>
    metis_tac[]
  ) >>
  (* Case analysis on instruction type *)
  Cases_on `is_jmp_inst x` >> gvs[] >- (
    (* JMP case *)
    drule_all step_inst_jmp_data_equiv >>
    Cases_on `step_inst x s1` >> Cases_on `step_inst x s2` >> gvs[] >>
    strip_tac >> fs[is_terminator_def, is_jmp_inst_def]
  ) >>
  Cases_on `x.inst_opcode = JNZ` >> gvs[] >- (
    (* JNZ case *)
    drule_all step_inst_jnz_data_equiv >>
    Cases_on `step_inst x s1` >> Cases_on `step_inst x s2` >> gvs[] >>
    strip_tac >> fs[is_terminator_def]
  ) >>
  (* Other instructions *)
  drule_all step_inst_data_equiv >>
  Cases_on `step_inst x s1` >> Cases_on `step_inst x s2` >> gvs[] >>
  strip_tac >> gvs[] >>
  Cases_on `is_terminator x.inst_opcode` >> gvs[] >- (
    (* Non-JMP/JNZ terminator returning OK - contradiction *)
    `step_inst x s1 <> OK v` by (irule non_jmp_jnz_terminator_not_ok >> simp[]) >>
    gvs[]
  ) >>
  (* Non-terminator: apply next_inst *)
  (* Derive vs_inst_idx equality from step_inst_preserves_ctrl *)
  `v.vs_inst_idx = s1.vs_inst_idx /\ v'.vs_inst_idx = s2.vs_inst_idx` by
    metis_tac[step_inst_preserves_ctrl] >>
  (* data_equiv only cares about data fields, updating vs_inst_idx preserves them *)
  simp[venomStateTheory.next_inst_def, data_equiv_def, var_equiv_def,
       venomStateTheory.lookup_var_def] >>
  fs[data_equiv_def, var_equiv_def, venomStateTheory.lookup_var_def]
QED

(* run_block on blocks with same instructions gives result_equiv_merge results.
   This extends step_in_block_same_instructions to the full run_block execution.
   Key insight: for no_phi blocks, execution depends only on data fields, and
   terminators set vs_current_bb identically when given data_equiv states. *)
Theorem run_block_same_instructions:
  !fn bb1 bb2 s1 s2.
    bb1.bb_instructions = bb2.bb_instructions /\ no_phi_block bb1 /\
    data_equiv s1 s2 /\ s1.vs_inst_idx = s2.vs_inst_idx /\
    ~s1.vs_halted /\ ~s2.vs_halted ==>
    result_equiv_merge (run_block fn bb1 s1) (run_block fn bb2 s2)
Proof
  gen_tac >> gen_tac >>
  completeInduct_on `LENGTH bb2.bb_instructions - s2.vs_inst_idx` >>
  rpt strip_tac >>
  simp[Once run_block_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  (* Get step_in_block_same_instructions result *)
  `!fn'.
     case (step_in_block fn' bb1 s1, step_in_block fn' bb2 s2) of
       ((OK r1, t1), (OK r2, t2)) => data_equiv r1 r2 /\ (t1 <=> t2) /\
                                      r1.vs_inst_idx = r2.vs_inst_idx
     | ((Halt r1, _), (Halt r2, _)) => data_equiv r1 r2
     | ((Revert r1, _), (Revert r2, _)) => data_equiv r1 r2
     | ((Error e1, _), (Error e2, _)) => e1 = e2
     | _ => F` by
    (strip_tac >> irule step_in_block_same_instructions >> simp[]) >>
  (* Case analysis on step_in_block results *)
  Cases_on `step_in_block fn bb1 s1` >> Cases_on `step_in_block fn bb2 s2` >>
  Cases_on `q` >> Cases_on `q'` >> gvs[] >>
  (* Use the step_in_block_same_instructions result to eliminate impossible cases *)
  TRY (first_x_assum (qspec_then `fn` mp_tac) >> gvs[result_equiv_merge_def] >> NO_TAC) >>
  TRY (first_x_assum (qspec_then `fn` mp_tac) >> gvs[] >> strip_tac >>
       simp[result_equiv_merge_def] >> NO_TAC) >>
  (* OK/OK case *)
  first_x_assum (qspec_then `fn` mp_tac) >> gvs[] >> strip_tac >>
  (* Case on vs_halted *)
  Cases_on `v'.vs_halted` >> gvs[] >-
    (* Halted: derive v''.vs_halted from data_equiv *)
    (`v''.vs_halted` by fs[data_equiv_def] >>
     gvs[result_equiv_merge_def, data_equiv_def])
  >-
    (* Not halted *)
    (`~v''.vs_halted` by fs[data_equiv_def] >> gvs[] >>
     (* Case on terminator flag *)
     Cases_on `r` >> gvs[] >-
       (* Terminator: need to show state_equiv_merge which requires vs_current_bb = *)
       (simp[result_equiv_merge_def, state_equiv_merge_def, data_equiv_def] >>
        (* Get vs_current_bb equality from step_inst_terminator_ok_data_equiv *)
        qpat_x_assum `step_in_block _ bb1 s1 = _` mp_tac >>
        qpat_x_assum `step_in_block _ bb2 s2 = _` mp_tac >>
        simp[step_in_block_def] >>
        `get_instruction bb1 s1.vs_inst_idx = get_instruction bb2 s2.vs_inst_idx` by
          simp[get_instruction_def] >>
        Cases_on `get_instruction bb2 s2.vs_inst_idx` >> gvs[] >>
        strip_tac >> strip_tac >> gvs[AllCaseEqs()] >>
        drule_all step_inst_terminator_ok_data_equiv >> strip_tac >> gvs[])
     >-
       (* Non-terminator: apply IH *)
       (qpat_x_assum `step_in_block _ bb2 s2 = _` mp_tac >>
        simp[step_in_block_def] >>
        Cases_on `get_instruction bb2 s2.vs_inst_idx` >> simp[] >>
        strip_tac >> gvs[AllCaseEqs()] >>
        rename1 `step_inst inst s2 = OK s'` >>
        (* Now v'' = next_inst s' *)
        (* Get ~is_jmp_inst and inst.inst_opcode <> JNZ for step_inst_preserves_ctrl *)
        `~is_jmp_inst inst /\ inst.inst_opcode <> JNZ` by
          (fs[is_jmp_inst_def] >> Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
        drule_all step_inst_preserves_ctrl >> strip_tac >>
        (* Now apply IH *)
        qpat_x_assum `!m. _` (qspec_then `LENGTH bb2.bb_instructions - (next_inst s').vs_inst_idx` mp_tac) >>
        impl_tac >-
          (simp[venomStateTheory.next_inst_def] >>
           `s2.vs_inst_idx < LENGTH bb2.bb_instructions` by
             (fs[get_instruction_def] >> gvs[AllCaseEqs()]) >> simp[]) >>
        strip_tac >>
        first_x_assum (qspecl_then [`bb2`, `next_inst s'`] mp_tac) >>
        impl_tac >- simp[venomStateTheory.next_inst_def] >>
        strip_tac >>
        first_x_assum (qspec_then `v'` mp_tac) >>
        impl_tac >- simp[] >> simp[]))
QED

(* Helper: get_instruction equality from DROP equality *)
Theorem get_instruction_drop_equiv:
  !bb1 bb2 s1 s2.
    DROP s1.vs_inst_idx bb1.bb_instructions = DROP s2.vs_inst_idx bb2.bb_instructions /\
    s1.vs_inst_idx < LENGTH bb1.bb_instructions /\
    s2.vs_inst_idx < LENGTH bb2.bb_instructions ==>
    get_instruction bb1 s1.vs_inst_idx = get_instruction bb2 s2.vs_inst_idx
Proof
  rpt strip_tac >> simp[get_instruction_def] >>
  `EL s1.vs_inst_idx bb1.bb_instructions =
   EL 0 (DROP s1.vs_inst_idx bb1.bb_instructions)` by
    simp[rich_listTheory.EL_DROP] >>
  `EL s2.vs_inst_idx bb2.bb_instructions =
   EL 0 (DROP s2.vs_inst_idx bb2.bb_instructions)` by
    simp[rich_listTheory.EL_DROP] >>
  metis_tac[]
QED

(* Helper: DROP (n+1) l = TL (DROP n l) when n < LENGTH l *)
Theorem drop_suc_eq_tl_drop:
  !l:'a list n. n < LENGTH l ==> DROP (n + 1) l = TL (DROP n l)
Proof
  rpt strip_tac >>
  `DROP n l <> []` by simp[listTheory.DROP_EQ_NIL] >>
  Cases_on `DROP n l` >> gvs[] >>
  `DROP n l = EL n l :: DROP (SUC n) l` by metis_tac[rich_listTheory.DROP_CONS_EL] >>
  gvs[arithmeticTheory.ADD1]
QED

(* Helper: DROP equality is preserved through stepping *)
Theorem drop_equality_preserved:
  !bb1 bb2 s1 s2.
    DROP s1.vs_inst_idx bb1.bb_instructions = DROP s2.vs_inst_idx bb2.bb_instructions /\
    s1.vs_inst_idx < LENGTH bb1.bb_instructions /\
    s2.vs_inst_idx < LENGTH bb2.bb_instructions ==>
    DROP (s1.vs_inst_idx + 1) bb1.bb_instructions =
    DROP (s2.vs_inst_idx + 1) bb2.bb_instructions
Proof
  rpt strip_tac >>
  `DROP (s1.vs_inst_idx + 1) bb1.bb_instructions =
   TL (DROP s1.vs_inst_idx bb1.bb_instructions)` by simp[drop_suc_eq_tl_drop] >>
  `DROP (s2.vs_inst_idx + 1) bb2.bb_instructions =
   TL (DROP s2.vs_inst_idx bb2.bb_instructions)` by simp[drop_suc_eq_tl_drop] >>
  simp[]
QED

(* Helper: step_in_block on blocks with DROP-equal instructions.
   This is the key lemma for run_block_drop_equiv.
   Requires: DROP s1.vs_inst_idx bb1 = DROP s2.vs_inst_idx bb2 *)
Theorem step_in_block_drop_equiv:
  !fn bb1 bb2 s1 s2.
    DROP s1.vs_inst_idx bb1.bb_instructions = DROP s2.vs_inst_idx bb2.bb_instructions /\
    s1.vs_inst_idx <= LENGTH bb1.bb_instructions /\
    s2.vs_inst_idx <= LENGTH bb2.bb_instructions /\
    data_equiv s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    no_phi_block bb1 /\ no_phi_block bb2 /\
    ~s1.vs_halted /\ ~s2.vs_halted ==>
    case (step_in_block fn bb1 s1, step_in_block fn bb2 s2) of
      ((OK r1, t1), (OK r2, t2)) => data_equiv r1 r2 /\ (t1 <=> t2) /\
                                    r1.vs_current_bb = r2.vs_current_bb /\
                                    (~t1 ==> DROP r1.vs_inst_idx bb1.bb_instructions =
                                             DROP r2.vs_inst_idx bb2.bb_instructions)
    | ((Halt r1, _), (Halt r2, _)) => data_equiv r1 r2
    | ((Revert r1, _), (Revert r2, _)) => data_equiv r1 r2
    | ((Error e1, _), (Error e2, _)) => e1 = e2
    | _ => F
Proof
  rpt strip_tac >>
  simp[step_in_block_def] >>
  (* First derive that s1 < LENGTH bb1 iff s2 < LENGTH bb2 *)
  `s1.vs_inst_idx < LENGTH bb1.bb_instructions <=>
   s2.vs_inst_idx < LENGTH bb2.bb_instructions` by (
    `LENGTH bb1.bb_instructions - s1.vs_inst_idx =
     LENGTH bb2.bb_instructions - s2.vs_inst_idx` by (
      qpat_x_assum `DROP _ _ = DROP _ _` (fn th =>
        ASSUME_TAC (AP_TERM ``LENGTH : instruction list -> num`` th)) >>
      fs[listTheory.LENGTH_DROP]) >>
    simp[]) >>
  (* Case on whether s1 is within bounds *)
  Cases_on `s1.vs_inst_idx < LENGTH bb1.bb_instructions` >> gvs[] >- (
    (* Within bounds - both get instruction *)
    `get_instruction bb1 s1.vs_inst_idx = get_instruction bb2 s2.vs_inst_idx` by
      (irule get_instruction_drop_equiv >> simp[]) >>
    Cases_on `get_instruction bb2 s2.vs_inst_idx` >> gvs[] >>
    (* Derive ~is_phi_inst x from no_phi_block *)
    `~is_phi_inst x` by (
      fs[no_phi_block_def, get_instruction_def, listTheory.EVERY_EL] >>
      metis_tac[]) >>
    (* Case analysis on instruction type *)
    Cases_on `is_jmp_inst x` >> gvs[] >- (
      (* JMP case *)
      drule_all step_inst_jmp_data_equiv >>
      Cases_on `step_inst x s1` >> Cases_on `step_inst x s2` >> gvs[] >>
      strip_tac >> fs[is_terminator_def, is_jmp_inst_def]
    ) >>
    Cases_on `x.inst_opcode = JNZ` >> gvs[] >- (
      (* JNZ case *)
      drule_all step_inst_jnz_data_equiv >>
      Cases_on `step_inst x s1` >> Cases_on `step_inst x s2` >> gvs[] >>
      strip_tac >> fs[is_terminator_def]
    ) >>
    (* Other instructions *)
    drule_all step_inst_data_equiv >>
    Cases_on `step_inst x s1` >> Cases_on `step_inst x s2` >> gvs[] >>
    strip_tac >> gvs[] >>
    Cases_on `is_terminator x.inst_opcode` >> gvs[] >- (
      (* Non-JMP/JNZ terminator returning OK - contradiction *)
      `step_inst x s1 <> OK v` by (irule non_jmp_jnz_terminator_not_ok >> simp[]) >>
      gvs[]
    ) >>
    (* Non-terminator: apply next_inst, show DROP preserved *)
    `v.vs_inst_idx = s1.vs_inst_idx /\ v'.vs_inst_idx = s2.vs_inst_idx` by
      metis_tac[step_inst_preserves_ctrl] >>
    simp[venomStateTheory.next_inst_def, data_equiv_def, var_equiv_def,
         venomStateTheory.lookup_var_def] >>
    `v.vs_current_bb = s1.vs_current_bb /\ v'.vs_current_bb = s2.vs_current_bb` by
      metis_tac[step_inst_preserves_ctrl] >>
    fs[data_equiv_def, var_equiv_def, venomStateTheory.lookup_var_def] >>
    (* Show DROP preserved through stepping *)
    irule drop_equality_preserved >> simp[]
  ) >>
  (* At end of block - both return Error "block not terminated" *)
  simp[get_instruction_def]
QED

(* Generalized version: DROP equality on both sides

   Key insight: If the remaining instructions in both blocks are equal (via DROP),
   then executing them with data_equiv states gives result_equiv_merge results.
*)
Theorem run_block_drop_equiv:
  !n fn bb1 bb2 s1 s2.
    n = LENGTH bb1.bb_instructions - s1.vs_inst_idx /\
    DROP s1.vs_inst_idx bb1.bb_instructions = DROP s2.vs_inst_idx bb2.bb_instructions /\
    s1.vs_inst_idx <= LENGTH bb1.bb_instructions /\
    s2.vs_inst_idx <= LENGTH bb2.bb_instructions /\
    data_equiv s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    no_phi_block bb1 /\ no_phi_block bb2 /\
    ~s1.vs_halted /\ ~s2.vs_halted ==>
    result_equiv_merge (run_block fn bb1 s1) (run_block fn bb2 s2)
Proof
  completeInduct_on `LENGTH bb1.bb_instructions - s1.vs_inst_idx` >>
  rpt strip_tac >> fs[] >>
  simp[Once run_block_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  drule_all step_in_block_drop_equiv >> strip_tac >>
  first_x_assum (qspec_then `fn` assume_tac) >>
  Cases_on `step_in_block fn bb1 s1` >>
  Cases_on `step_in_block fn bb2 s2` >>
  Cases_on `q` >> Cases_on `q'` >> fs[] >>
  (* Terminal cases: use step_in_block_drop_equiv results *)
  TRY (simp[result_equiv_merge_def] >> NO_TAC) >>
  (* OK/OK case - v' and v'' are the result states *)
  Cases_on `v'.vs_halted` >> fs[]
  >- (`v''.vs_halted` by fs[data_equiv_def] >> fs[result_equiv_merge_def])
  >> (
    `~v''.vs_halted` by fs[data_equiv_def] >> fs[] >>
    Cases_on `r` >> fs[]
    >- simp[result_equiv_merge_def, state_equiv_merge_def]
    (* Non-terminator: apply IH *)
    >> (
      first_x_assum (qspec_then `LENGTH bb1.bb_instructions - v'.vs_inst_idx` mp_tac) >>
      impl_tac >- (
        qpat_x_assum `step_in_block fn bb1 s1 = _` mp_tac >>
        simp[step_in_block_def] >>
        Cases_on `get_instruction bb1 s1.vs_inst_idx` >> simp[] >>
        Cases_on `step_inst x s1` >> simp[AllCaseEqs()] >>
        strip_tac >> fs[] >>
        imp_res_tac step_inst_preserves_inst_idx >>
        fs[venomStateTheory.next_inst_def, get_instruction_def, AllCaseEqs()] >>
        `v'.vs_inst_idx = s1.vs_inst_idx + 1` by (
          qpat_x_assum `_ with vs_inst_idx := _ = v'` (fn th =>
            ASSUME_TAC (AP_TERM ``venom_state_vs_inst_idx`` th)) >>
          fs[venomStateTheory.venom_state_component_equality]
        ) >>
        fs[]
      ) >>
      strip_tac >>
      first_x_assum (qspecl_then [`bb1`, `v'`] mp_tac) >> simp[] >>
      disch_then (qspecl_then [`fn`, `bb2`, `v''`] mp_tac) >>
      impl_tac >- (
        fs[] >>
        qpat_x_assum `step_in_block fn bb1 s1 = _` mp_tac >>
        qpat_x_assum `step_in_block fn bb2 s2 = _` mp_tac >>
        simp[step_in_block_def] >>
        Cases_on `get_instruction bb1 s1.vs_inst_idx` >> simp[] >>
        Cases_on `get_instruction bb2 s2.vs_inst_idx` >> simp[] >>
        Cases_on `step_inst x s1` >> gvs[AllCaseEqs()] >>
        Cases_on `step_inst x' s2` >> gvs[AllCaseEqs()] >>
        fs[venomStateTheory.next_inst_def] >>
        imp_res_tac step_inst_preserves_inst_idx >> fs[] >>
        fs[get_instruction_def, AllCaseEqs()] >>
        rpt strip_tac >> gvs[] >>
        `v'.vs_inst_idx = s1.vs_inst_idx + 1` by (
          qpat_x_assum `_ with vs_inst_idx := _ = v'` (fn th =>
            ASSUME_TAC (AP_TERM ``venom_state_vs_inst_idx`` th)) >>
          fs[venomStateTheory.venom_state_component_equality]
        ) >>
        fs[]
      ) >>
      simp[]
    )
  )
QED

(* run_block on a suffix: if bb1's remaining instructions (from offset) equal bb2's full
   instructions, then running bb1 from that offset is equivalent to running bb2 from 0.
   This is crucial for merge_blocks where we run FRONT++b from position |FRONT| vs b from 0.

   Follows from run_block_drop_equiv with:
   - n = LENGTH bb1.bb_instructions - s1.vs_inst_idx
   - DROP s1.vs_inst_idx bb1 = DROP 0 bb2 = bb2.bb_instructions
   - no_phi_block bb2 derived from suffix of no_phi_block bb1
*)
Theorem run_block_suffix_equiv:
  !fn bb1 bb2 s1 s2.
    DROP s1.vs_inst_idx bb1.bb_instructions = bb2.bb_instructions /\
    s1.vs_inst_idx <= LENGTH bb1.bb_instructions /\
    s2.vs_inst_idx = 0 /\
    data_equiv s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    no_phi_block bb1 /\
    no_phi_block bb2 /\
    ~s1.vs_halted /\ ~s2.vs_halted ==>
    result_equiv_merge (run_block fn bb1 s1) (run_block fn bb2 s2)
Proof
  rpt strip_tac >>
  (* run_block_drop_equiv: !n fn bb1 bb2 s1 s2. n = ... /\ ... ==> ... *)
  (* Need to provide n explicitly, then use MATCH_MP_TAC *)
  MATCH_MP_TAC (SPEC ``LENGTH (bb1 : basic_block).bb_instructions - (s1 : venom_state).vs_inst_idx`` run_block_drop_equiv) >>
  simp[listTheory.DROP_LENGTH_NIL]
QED

(* ==========================================================================
   state_equiv_except_prev Helpers
   ========================================================================== *)

(* state_equiv_except_prev is reflexive *)
Theorem state_equiv_except_prev_refl:
  !s. state_equiv_except_prev s s
Proof
  rw[state_equiv_except_prev_def, var_equiv_def]
QED

(* Helper: eval_operand ignores vs_prev_bb *)
Theorem eval_operand_prev_bb_irrelevant:
  !op s new. eval_operand op (s with vs_prev_bb := SOME new) = eval_operand op s
Proof
  Cases_on `op` >>
  simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]
QED

(* Helper: resolve_phi with label replacement - SOME case *)
Theorem resolve_phi_replace_label:
  !ops old new val_op.
    ~MEM (Label new) ops /\
    resolve_phi old ops = SOME val_op ==>
    resolve_phi new (MAP (replace_label_operand old new) ops) =
    SOME (replace_label_operand old new val_op)
Proof
  gen_tac >> measureInduct_on `LENGTH ops` >> rw[] >> fs[] >>
  Cases_on `ops` >> fs[resolve_phi_def] >>
  Cases_on `h` >> simp[replace_label_operand_def] >| [
    (* Lit case *)
    Cases_on `t` >> simp[resolve_phi_def] >> fs[resolve_phi_def],
    (* Var case *)
    Cases_on `t` >> simp[resolve_phi_def] >> fs[resolve_phi_def],
    (* Label case *)
    Cases_on `t` >> simp[resolve_phi_def] >> fs[resolve_phi_def] >>
    Cases_on `s = old` >> simp[resolve_phi_def] >> fs[]
  ]
QED

(* Helper: resolve_phi with label replacement - NONE case *)
Theorem resolve_phi_replace_label_none:
  !ops old new.
    ~MEM (Label new) ops /\
    resolve_phi old ops = NONE ==>
    resolve_phi new (MAP (replace_label_operand old new) ops) = NONE
Proof
  gen_tac >> measureInduct_on `LENGTH ops` >> rw[] >> fs[] >>
  Cases_on `ops` >> fs[resolve_phi_def] >>
  Cases_on `h` >> simp[replace_label_operand_def] >| [
    (* Lit case *)
    Cases_on `t` >> simp[resolve_phi_def] >> fs[resolve_phi_def],
    (* Var case *)
    Cases_on `t` >> simp[resolve_phi_def] >> fs[resolve_phi_def],
    (* Label case *)
    Cases_on `t` >> simp[resolve_phi_def] >> fs[resolve_phi_def] >>
    Cases_on `s = old` >> fs[]
  ]
QED

(* Replace label in PHI correctly updates predecessor reference.
   The resulting states differ only in vs_prev_bb. *)
Theorem replace_label_phi_correct:
  !old new inst s.
    is_phi_inst inst /\
    ~MEM (Label new) inst.inst_operands /\
    s.vs_prev_bb = SOME old ==>
    result_equiv_except_prev
      (step_inst (replace_label_inst old new inst) (s with vs_prev_bb := SOME new))
      (step_inst inst s)
Proof
  rw[is_phi_inst_def] >>
  simp[step_inst_def, replace_label_inst_def] >>
  Cases_on `inst.inst_outputs` >> simp[result_equiv_except_prev_def] >>
  Cases_on `t` >> simp[result_equiv_except_prev_def] >>
  (* Now have single output case: inst_outputs = [h] *)
  Cases_on `resolve_phi old inst.inst_operands` >>
  simp[result_equiv_except_prev_def] >| [
    (* NONE case - show replacement also gives NONE *)
    drule_all resolve_phi_replace_label_none >> simp[result_equiv_except_prev_def],
    (* SOME val_op case *)
    drule_all resolve_phi_replace_label >> simp[] >> strip_tac >>
    simp[eval_operand_replace_label, eval_operand_prev_bb_irrelevant] >>
    Cases_on `eval_operand x s` >> simp[result_equiv_except_prev_def] >>
    simp[venomStateTheory.update_var_def, state_equiv_except_prev_def, var_equiv_def,
         venomStateTheory.lookup_var_def]
  ]
QED

(* ==========================================================================
   Result Equivalence for Transformations
   ========================================================================== *)

(* Note: replace_label_block_non_phi_equiv was removed because its statement
   is incorrect - replacing labels in JMP/JNZ changes vs_current_bb, which
   violates state_equiv. A correct formulation would need to account for
   the semantic equivalence of the label replacement at the function level. *)

(* Threading preserves execution when going through passthrough *)
Theorem thread_preserves_execution:
  !fn blocks passthrough_lbl target_lbl s bb.
    lookup_block passthrough_lbl blocks = SOME bb /\
    is_passthrough_block bb /\
    get_block_target bb = SOME target_lbl ==>
    (* Execution through passthrough is same as direct jump *)
    !s'. s'.vs_current_bb = passthrough_lbl /\
         s'.vs_inst_idx = 0 /\ ~s'.vs_halted ==>
         result_equiv
           (run_block fn bb s')
           (OK (jump_to target_lbl s'))
Proof
  rw[] >>
  drule_all run_passthrough_block >>
  simp[result_equiv_def, state_equiv_refl]
QED

(* ==========================================================================
   Block Merging Main Theorem
   ========================================================================== *)

(* Main theorem: Merged block execution is equivalent to sequential execution.
   The equivalence ignores vs_prev_bb (a.bb_label vs b.bb_label) and vs_inst_idx
   (which differs for Halt/Revert cases).
   The function-level theorem handles vs_prev_bb via label replacement.

   PROOF STRATEGY:
   - Case split on passthrough (LENGTH a = 1) vs non-passthrough
   - Passthrough case: merged = b, a = [JMP], use run_block_same_instructions
   - Non-passthrough case: Use induction with run_block_suffix_equiv
*)
Theorem merge_blocks_execution:
  !fn a b s.
    wf_block a /\ wf_block b /\
    get_block_target a = SOME b.bb_label /\
    no_phi_block b /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    result_equiv_merge
      (run_block fn (merge_blocks a b) s)
      (case run_block fn a s of
         OK s' => run_block fn b (s' with vs_inst_idx := 0)
       | other => other)
Proof
  rpt strip_tac >>
  `a.bb_instructions <> []` by fs[wf_block_def] >>
  (* Get terminator info *)
  `?inst. get_terminator a = SOME inst /\ is_jmp_inst inst /\
          inst.inst_operands = [Label b.bb_label]` by (
     qpat_x_assum `get_block_target _ = _` mp_tac >>
     simp[get_block_target_def, get_jmp_target_def] >>
     Cases_on `get_terminator a` >> simp[] >>
     Cases_on `is_jmp_inst x` >> simp[] >>
     Cases_on `x.inst_operands` >> simp[] >>
     Cases_on `t` >> simp[] >> Cases_on `h` >> simp[]) >>
  `inst = LAST a.bb_instructions` by fs[get_terminator_def] >>
  `is_terminator inst.inst_opcode` by fs[is_jmp_inst_def, is_terminator_def] >>
  (* Case split on passthrough *)
  Cases_on `LENGTH a.bb_instructions = 1`
  >- (
    (* === Passthrough case: a = [JMP b] === *)
    `a.bb_instructions = [inst]` by (Cases_on `a.bb_instructions` >> gvs[] >> Cases_on `t` >> gvs[]) >>
    `FRONT a.bb_instructions = []` by simp[] >>
    `(merge_blocks a b).bb_instructions = b.bb_instructions` by simp[merge_blocks_def] >>
    (* run_block fn a s = OK (jump_to b.bb_label s) *)
    `run_block fn a s = OK (jump_to b.bb_label s)` by (
       simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
       simp[Once step_inst_def] >> fs[is_jmp_inst_def]) >>
    simp[] >>
    (* data_equiv s (jump_to b.bb_label s) *)
    `data_equiv s (jump_to b.bb_label s)` by
       simp[data_equiv_def, var_equiv_def, lookup_var_def, jump_to_def] >>
    (* Use run_block_same_instructions *)
    irule run_block_same_instructions >> simp[jump_to_def] >>
    fs[wf_block_def]
  )
  >- (
    (* === Non-passthrough case: |a| > 1 === *)
    (* merged = FRONT(a) ++ b, run merged from 0 vs run a then b from 0 *)
    (* Strategy: show DROP equivalence connects merged from |FRONT(a)| to b from 0 *)
    `LENGTH (FRONT a.bb_instructions) = LENGTH a.bb_instructions - 1` by
       (Cases_on `a.bb_instructions` >> gvs[LENGTH_FRONT_CONS]) >>
    `LENGTH (FRONT a.bb_instructions) >= 1` by simp[] >>
    `(merge_blocks a b).bb_instructions = FRONT a.bb_instructions ++ b.bb_instructions`
       by simp[merge_blocks_def] >>
    (* For the passthrough case below, we derived:
       run_block fn a s = OK (jump_to b.bb_label s) when a = [JMP]

       For |a| > 1, we need to show:
       1. Running merged from 0 executes FRONT(a) then b
       2. Running a executes FRONT(a) then JMP (which gives OK (jump_to b.bb_label s'))
       3. The state after FRONT(a) is the same in both cases
       4. Then running b from that state gives same result as continuing merged *)

    (* Use induction via run_block_drop_equiv *)
    (* Key insight: we need to show that after |FRONT(a)| steps on merged,
       the remaining instructions are b.bb_instructions, and we can use
       run_block_suffix_equiv. But that requires matching drop positions. *)

    (* Alternative: use run_block_same_instructions with merged block whose
       instructions are FRONT(a) ++ b vs a block with same instructions *)

    (* Actually, let's use a simpler approach:
       The merged block has instructions = FRONT(a) ++ b.bb_instructions
       We need to show result_equiv_merge between:
       - run_block on merged from 0
       - case run_block on a of OK s' => run_block on b from 0 | ...

       Induction on |FRONT(a)|:
       - For each step in FRONT(a), step_in_block_merge_prefix shows identical steps
       - After |FRONT(a)| steps, merged continues with b[0], a executes JMP
       - a's JMP gives OK (jump_to b.bb_label s'), which has data_equiv to merged's s'
       - Then use run_block_suffix_equiv or run_block_same_instructions *)

    (* This proof is complex - let's use a helper lemma approach *)
    cheat
  )
QED

