(*
 * Where an internal return can come from.
 *
 * Only RET, RETFMP and DRET produce an IntRet result: INVOKE consumes its
 * callee's.  So a function with none of them never returns IntRet, and a
 * context whose entry function has none never ends a run in IntRet.
 *
 * TOP-LEVEL: run_context_not_int_ret, run_context_not_ok.
 *)
Theory venomRetProps
Ancestors
  venomExecSemantics venomExecProps venomInst callLayoutDefs opcodeClass
  list

Theorem step_inst_IntRet_opcode[local]:
  step_inst fuel ctx inst s = IntRet v t ==>
  is_raw_return_opcode inst.inst_opcode
Proof
  simp[Once step_inst_def] >> IF_CASES_TAC
  >- simp[AllCaseEqs()] >>
  strip_tac >> drule step_inst_base_intret_opcodes >>
  simp[is_raw_return_opcode_def]
QED

Theorem MEM_fn_insts_blocks[local]:
  !bbs inst. MEM inst (fn_insts_blocks bbs) <=>
             ?bb. MEM bb bbs /\ MEM inst bb.bb_instructions
Proof
  Induct >> simp[fn_insts_blocks_def] >> metis_tac[]
QED

Theorem no_int_ret_block[local]:
  EVERY (\inst. ~MEM inst.inst_opcode [RET; RETFMP; DRET]) (fn_insts fn) /\
  MEM bb fn.fn_blocks ==>
  EVERY (\inst. ~is_raw_return_opcode inst.inst_opcode) bb.bb_instructions
Proof
  rw[fn_insts_def, EVERY_MEM, MEM_fn_insts_blocks, is_raw_return_opcode_def] >>
  metis_tac[]
QED

Theorem exec_block_not_int_ret_measure[local]:
  !n fuel ctx bb s v t.
    n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    EVERY (\inst. ~is_raw_return_opcode inst.inst_opcode) bb.bb_instructions ==>
    exec_block fuel ctx bb s <> IntRet v t
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  simp[Once exec_block_def, get_instruction_def] >>
  IF_CASES_TAC >> simp[] >>
  `~is_raw_return_opcode (EL s.vs_inst_idx bb.bb_instructions).inst_opcode` by
    gvs[EVERY_EL] >>
  Cases_on `step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s` >>
  simp[]
  >- (rw[] >> first_x_assum irule >> simp[] >>
      qexists_tac `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` >> simp[])
  >> metis_tac[step_inst_IntRet_opcode]
QED

Theorem exec_block_not_int_ret[local]:
  !fuel ctx bb s v t.
    EVERY (\inst. ~is_raw_return_opcode inst.inst_opcode) bb.bb_instructions ==>
    exec_block fuel ctx bb s <> IntRet v t
Proof
  metis_tac[exec_block_not_int_ret_measure]
QED

Theorem run_blocks_not_int_ret[local]:
  !fuel ctx fn s v t.
    EVERY (\inst. ~MEM inst.inst_opcode [RET; RETFMP; DRET]) (fn_insts fn) ==>
    run_blocks fuel ctx fn s <> IntRet v t
Proof
  Induct >- simp[Once run_blocks_def] >>
  rpt gen_tac >> strip_tac >> simp[Once run_blocks_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `EVERY (\inst. ~is_raw_return_opcode inst.inst_opcode) bb.bb_instructions` by
    metis_tac[no_int_ret_block, lookup_block_MEM] >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs >> simp[] >>
  rename1 `eval_phis _ _ = OK sp` >>
  Cases_on `exec_block fuel ctx bb
              (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  simp[]
  >- (rw[] >> simp[])
  >> metis_tac[exec_block_not_int_ret]
QED

Theorem run_blocks_not_ok[local]:
  !fuel ctx fn s t. run_blocks fuel ctx fn s <> OK t
Proof
  Induct >- simp[Once run_blocks_def] >>
  simp[Once run_blocks_unfold] >> rpt gen_tac >> BasicProvers.every_case_tac
QED

Theorem run_context_not_int_ret:
  (!name fn. ctx.ctx_entry = SOME name /\
             lookup_function name ctx.ctx_functions = SOME fn ==>
             EVERY (\inst. ~MEM inst.inst_opcode [RET; RETFMP; DRET]) (fn_insts fn)) ==>
  run_context fuel ctx s <> IntRet v t
Proof
  rw[run_context_def, run_function_def] >> BasicProvers.every_case_tac >> simp[] >>
  res_tac >> irule run_blocks_not_int_ret >> fs[]
QED

Theorem run_context_not_ok:
  run_context fuel ctx s <> OK t
Proof
  rw[run_context_def, run_function_def] >> BasicProvers.every_case_tac >>
  simp[run_blocks_not_ok]
QED
