(* A piece of deploy_unit_execution_correct (ctorDeployLowering).
   ADMITTED until proved. *)
Theory ctorDeployLoweringPrefix
Ancestors
  ctorDeployLoweringDefs o1PassContract vyperTypeContractSoundness
  vyperContext e2eDefs vyperInterpreter

Theorem deploy_prefix_short_parse:
  parse_code 0 FEMPTY [91w;96w;32w] =
    FEMPTY |+ (0, JumpDest) |+ (1, Push 1 [32w])
Proof
  simp[Once vfmContextTheory.parse_code_def, vfmOperationTheory.parse_opcode_cond_thm,
       vfmOperationTheory.opcode_def, wordsTheory.dimword_8] >>
  simp[Once vfmContextTheory.parse_code_def, vfmOperationTheory.parse_opcode_cond_thm,
       vfmOperationTheory.opcode_def, wordsTheory.dimword_8] >>
  simp[Once vfmContextTheory.parse_code_def] >> EVAL_TAC
QED

val prefix_parse_unfold_tac = CONV_TAC
  (LAND_CONV (ONCE_REWRITE_CONV [vfmContextTheory.parse_code_def]));
val prefix_parse_reduce_tac = CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss())
  [vfmOperationTheory.parse_opcode_cond_thm,
   vfmOperationTheory.opcode_def, wordsTheory.dimword_8]));
val prefix_parse_let_tac = CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss())
  [LET_THM, vfmOperationTheory.opcode_def, wordsTheory.dimword_8]));

Theorem deploy_prefix_safe_step_no_abort:
  !inst s fuel ctx a ss.
    MEM inst.inst_opcode [ALLOCA; ADD; DLOAD; MSTORE; JMP; CODECOPY; RETURN] ==>
    step_inst fuel ctx inst s <> Abort a ss
Proof
  rpt gen_tac >> simp[] >> strip_tac >>
  simp[Once venomExecSemanticsTheory.step_inst_def] >>
  pure_once_rewrite_tac[venomExecSemanticsTheory.step_inst_base_def] >>
  asm_rewrite_tac[] >>
  simp[venomExecSemanticsTheory.exec_alloca_def,
       venomExecSemanticsTheory.exec_pure2_def,
       venomExecSemanticsTheory.exec_read1_def,
       venomExecSemanticsTheory.exec_write2_def, LET_THM] >>
  simp[AllCaseEqs()]
QED

Theorem deploy_prefix_safe_exec_no_abort:
  !bb s fuel ctx a ss.
    EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; DLOAD; MSTORE; JMP; CODECOPY; RETURN])
      bb.bb_instructions ==> exec_block fuel ctx bb s <> Abort a ss
Proof
  rpt gen_tac >> qid_spec_tac `s` >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt gen_tac >> disch_tac >> disch_tac >>
  simp[Once venomExecSemanticsTheory.exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >- simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `MEM inst bb.bb_instructions /\ s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (gvs[venomInstTheory.get_instruction_def] >> simp[listTheory.EL_MEM]) >>
  `MEM inst.inst_opcode [ALLOCA; ADD; DLOAD; MSTORE; JMP; CODECOPY; RETURN]` by
    (qpat_x_assum `EVERY _ _` mp_tac >>
     rewrite_tac[listTheory.EVERY_MEM] >>
     disch_then (qspec_then `inst` mp_tac) >> simp[]) >>
  Cases_on `step_inst fuel ctx inst s` >> simp[]
  >- (Cases_on `is_terminator inst.inst_opcode` >- (Cases_on `v'.vs_halted` >> simp[]) >>
      simp[] >> first_x_assum irule >> simp[])
  >> qpat_x_assum `!y. _` kall_tac >>
  drule_all deploy_prefix_safe_step_no_abort >> metis_tac[]
QED

Theorem deploy_prefix_safe_block_no_abort:
  !bb s fuel ctx a ss.
    EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; DLOAD; MSTORE; JMP; CODECOPY; RETURN])
      bb.bb_instructions ==> run_block fuel ctx bb s <> Abort a ss
Proof
  rpt gen_tac >> disch_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    venomExecSemanticsTheory.eval_phis_ok_or_error_defs >>
  simp[venomExecSemanticsTheory.run_block_def] >>
  irule deploy_prefix_safe_exec_no_abort >> simp[]
QED

Theorem deploy_prefix_lookup_block_mem[local]:
  !lbl bbs bb. lookup_block lbl bbs = SOME bb ==> MEM bb bbs
Proof
  Induct_on `bbs` >> simp[venomInstTheory.lookup_block_def, listTheory.FIND_thm] >>
  rw[] >> disj2_tac >> first_x_assum irule >>
  fs[venomInstTheory.lookup_block_def] >> metis_tac[]
QED

Theorem deploy_prefix_safe_blocks_no_abort:
  !fuel fn s ctx a ss.
    EVERY (\bb. EVERY (\i.
      MEM i.inst_opcode [ALLOCA; ADD; DLOAD; MSTORE; JMP; CODECOPY; RETURN])
      bb.bb_instructions) fn.fn_blocks ==>
    run_blocks fuel ctx fn s <> Abort a ss
Proof
  Induct_on `fuel` >- simp[Once venomExecSemanticsTheory.run_blocks_def] >>
  rpt gen_tac >> disch_tac >>
  simp[venomExecSemanticsTheory.run_blocks_unfold] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >- simp[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[deploy_prefix_lookup_block_mem] >>
  `EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; DLOAD; MSTORE; JMP; CODECOPY; RETURN])
    bb.bb_instructions` by
    (qpat_x_assum `EVERY _ _` mp_tac >> rewrite_tac[listTheory.EVERY_MEM] >>
     disch_then (qspec_then `bb` mp_tac) >> simp[]) >>
  Cases_on `run_block fuel ctx bb s` >> simp[]
  >- (Cases_on `v.vs_halted` >> simp[] >> first_x_assum irule >> simp[])
  >> drule_all deploy_prefix_safe_block_no_abort >> metis_tac[]
QED

(* When the source fails before the constructor body (the value transfer
   into a non-payable constructor, the reentrancy lock), so does the unit:
   its payable check and lock come first too. *)
Theorem deploy_ctor_prefix_fail:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs exts ints fb cf.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    classify_functions tops = (exts, ints, fb, SOME cf) /\
    (!mut nr body am_c es0.
       ~deploy_ctor_start tops am tx (mut, nr, body, am_c, es0)) ==>
    ?fuel. !gobs.
      deploy_venom_result_rel tops runtime_bc tx
        (load_contract NONE gobs am tx [(NONE, tops)] [])
        (run_context fuel dunit.cu_context vs)
Proof
  cheat
QED
