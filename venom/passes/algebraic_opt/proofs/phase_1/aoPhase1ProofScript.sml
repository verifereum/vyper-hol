(* Phase 1: Offset Canonicalization Correctness
 *
 * ao_handle_offset_inst converts ADD [Label l; Lit v] → OFFSET [Lit v; Label l].
 * Both map to exec_pure2 word_add in step_inst_base (word_add is commutative).
 * Hence run_blocks fn0 s = run_blocks fn s.
 *
 * TOP-LEVEL: ao_phase1_correct
 *)

Theory aoPhase1Proof
Ancestors
  algebraicOptDefs passSimulationProps
  venomExecSemantics venomState venomInst venomWf
Libs
  pairLib BasicProvers

Theorem ao_handle_offset_inst_id[local]:
  !inst.
    ~(inst.inst_opcode = ADD /\ ?l v. inst.inst_operands = [Label l; Lit v]) ==>
    ao_handle_offset_inst inst = inst
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = ADD`
  >- (fs[] >>
      rw[ao_handle_offset_inst_def] >>
      Cases_on `inst.inst_operands` >- simp[] >>
      rename1 `h :: t` >>
      Cases_on `h` >> simp[] >>
      Cases_on `t` >- simp[] >>
      rename1 `h2 :: t2` >>
      Cases_on `h2` >> simp[] >>
      Cases_on `t2` >- fs[] >>
      simp[])
  >- simp[ao_handle_offset_inst_def]
QED

Theorem step_inst_base_offset_eq[local]:
  !inst s.
    step_inst_base (ao_handle_offset_inst inst) s =
    step_inst_base inst s
Proof
  rw[] >>
  Cases_on `inst.inst_opcode = ADD /\ ?l v. inst.inst_operands = [Label l; Lit v]`
  >- (fs[] >>
      gvs[ao_handle_offset_inst_def] >>
      CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [step_inst_base_def])) >>
      CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV [step_inst_base_def])) >>
      simp[exec_pure2_def, eval_operand_def] >>
      Cases_on `FLOOKUP s.vs_labels l` >> gvs[] >>
      Cases_on `inst.inst_outputs` >> gvs[] >>
      simp[wordsTheory.WORD_ADD_COMM])
  >- (imp_res_tac ao_handle_offset_inst_id >> simp[])
QED

Theorem ao_handle_offset_not_invoke[local]:
  !inst. (ao_handle_offset_inst inst).inst_opcode = INVOKE <=>
         inst.inst_opcode = INVOKE
Proof
  gen_tac >>
  Cases_on `inst.inst_opcode = ADD /\ ?l v. inst.inst_operands = [Label l; Lit v]`
  >- (fs[] >> simp[ao_handle_offset_inst_def])
  >- (imp_res_tac ao_handle_offset_inst_id >> simp[])
QED

Theorem ao_handle_offset_inst_outputs:
  !inst. (ao_handle_offset_inst inst).inst_outputs = inst.inst_outputs
Proof
  gen_tac >>
  Cases_on `inst.inst_opcode = ADD /\ ?l v. inst.inst_operands = [Label l; Lit v]`
  >- (fs[] >> simp[ao_handle_offset_inst_def])
  >- (imp_res_tac ao_handle_offset_inst_id >> simp[])
QED

Theorem step_inst_offset_eq[local]:
  !fuel ctx inst s.
    step_inst fuel ctx (ao_handle_offset_inst inst) s =
    step_inst fuel ctx inst s
Proof
  rw[] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (`~(inst.inst_opcode = ADD /\ ?l v. inst.inst_operands = [Label l; Lit v])`
        by (fs[]) >>
      imp_res_tac ao_handle_offset_inst_id >> simp[])
  >- (simp[step_inst_non_invoke, ao_handle_offset_not_invoke, step_inst_base_offset_eq])
QED

Theorem ao_handle_offset_is_terminator[local]:
  !inst. is_terminator (ao_handle_offset_inst inst).inst_opcode =
         is_terminator inst.inst_opcode
Proof
  gen_tac >>
  Cases_on `inst.inst_opcode = ADD /\ ?l v. inst.inst_operands = [Label l; Lit v]`
  >- (fs[] >> simp[ao_handle_offset_inst_def, is_terminator_def])
  >- (imp_res_tac ao_handle_offset_inst_id >> simp[])
QED

Theorem exec_block_offset_eq[local]:
  !fuel ctx bb s.
    exec_block fuel ctx
      (bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) s =
    exec_block fuel ctx bb s
Proof
  rpt gen_tac >>
  `!n fu cx blk st.
     n = LENGTH blk.bb_instructions - st.vs_inst_idx ==>
     exec_block fu cx
       (blk with bb_instructions := MAP ao_handle_offset_inst blk.bb_instructions) st =
     exec_block fu cx blk st`
    suffices_by (
      strip_tac >>
      first_assum (qspecl_then
        [`LENGTH bb.bb_instructions - s.vs_inst_idx`,
         `fuel`, `ctx`, `bb`, `s`] mp_tac) >> simp[]) >>
  completeInduct_on `n` >> rw[] >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def, listTheory.EL_MAP, listTheory.LENGTH_MAP] >>
  Cases_on `st.vs_inst_idx < LENGTH blk.bb_instructions` >> simp[] >>
  simp[step_inst_offset_eq, ao_handle_offset_is_terminator]
QED

Theorem lookup_block_offset_fn[local]:
  !lbl fn.
    lookup_block lbl
      (MAP (\bb. bb with bb_instructions :=
          MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks) =
    OPTION_MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions)
      (lookup_block lbl fn.fn_blocks)
Proof
  rw[] >>
  mp_tac (ISPECL
    [``lbl : string``,
     ``fn.fn_blocks : basic_block list``,
     ``\(bb : basic_block). bb with bb_instructions :=
         MAP ao_handle_offset_inst bb.bb_instructions``]
    lookup_block_map) >>
  impl_tac >- simp[] >>
  simp[]
QED

Theorem ao_phase1_correct:
  !fuel ctx fn s.
    let fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks in
    run_blocks fuel ctx fn0 s = run_blocks fuel ctx fn s
Proof
  simp[LET_THM] >>
  Induct_on `fuel`
  >- simp[run_blocks_def] >>
  rpt gen_tac >>
  ONCE_REWRITE_TAC[run_blocks_def] >>
  simp[lookup_block_offset_fn] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[] >>
  simp[exec_block_offset_eq]
QED

val _ = export_theory();
