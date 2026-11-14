Theory readonlyInvokeCopyFwdExecutionDataOperands
Ancestors
  readonlyInvokeCopyFwdExecutionMemoryWrites
  readonlyInvokeCopyFwdExecutionWriteGuards readonlyInvokeCopyFwdExecutionWriteClassification
  readonlyInvokeCopyFwdExecutionMemoryScalars readonlyInvokeCopyFwdExecutionOrdinary
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdAnalyzedOrigins
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdHistoryPhase
  o1LowerDloadOccurrence o1LowerDloadGhost o1PassContract unitShapeDefs
  allocaFrontierBound frameViewFacts codegenRel
  ptrDiscipline pointerConfinedDefs memLocDefs taintAgree
  contextCodegenRel venomWf venomExecSemantics venomExecProps venomMemProps
  venomState venomInst list finite_map words arithmetic


Theorem ricf_execution_data_copy_operands:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ricf_analyzed_map_origins vs C stk PG G tn fn inst s U B sites /\
  o1_ctx_shape C /\ opaque_use_ok fn /\
  ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
  EVERY wf_ssa C.ctx_functions /\ EVERY ricf_param_order_ok C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [CALLDATACOPY;DLOADBYTES;CODECOPY;RETURNDATACOPY] /\
  inst.inst_operands = [addr;srcop;lenop] /\
  eval_operand addr s = SOME dst /\ eval_operand srcop s = SOME src /\
  eval_operand lenop s = SOME szw ==>
  ?target. eval_operand addr t = SOME target /\
    (w2n szw = 0 \/ target = dst) /\
    eval_operand srcop t = SOME src /\ eval_operand lenop t = SOME szw
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `!op. MEM op inst.inst_operands ==> op_taint tn op = {}` by
    (rpt strip_tac >> spose_not_then assume_tac >> fs[taint_ok_def] >>
     qpat_x_assum `!op. MEM op _ /\ _ ==> _` (qspec_then `op` mp_tac) >> fs[MEM]) >>
  `!name. addr = Var name ==> ~retpc_var fn name` by
    (qx_gen_tac `name` >> disch_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> fs[MEM] >> metis_tac[active_inst_mem_fn_insts]) >>
  `mem_write_ops inst = SOME <|iao_ofst := addr; iao_size := SOME lenop;
      iao_max_size := SOME lenop|>` by fs[MEM, mem_write_ops_def] >>
  `MEM (w2n dst,w2n szw) (source_memory_write_ranges inst s)` by
    fs[MEM, source_memory_write_ranges_def, sized_source_write_range_def] >>
  `?target. eval_operand addr t = SOME target /\ (w2n szw = 0 \/ dst = target)` by
    (mp_tac (Q.INST [`x` |-> `dst:256 word`, `len` |-> `w2n (szw:256 word)`,
      `ops` |-> `<|iao_ofst := addr; iao_size := SOME lenop;
        iao_max_size := SOME lenop|>`] ricf_execution_write_address) >>
     impl_tac >- (simp[] >> metis_tac[MEM]) >> simp[]) >>
  `op_taint tn srcop = {} /\ op_taint tn lenop = {}` by metis_tac[MEM] >>
  `eval_operand srcop t = SOME src /\ eval_operand lenop t = SOME szw` by
    (conj_tac
     >- (mp_tac (Q.INST [`rt` |-> `tn`, `op` |-> `srcop`, `x` |-> `src:256 word`]
          ricf_execution_nonaddress_operand) >>
         impl_tac >- (fs[MEM, is_pointer_preserving_op_def] >>
           Cases_on `addr = srcop` >> Cases_on `srcop = lenop` >>
           simp[mem_read_ops_def, mem_write_ops_def]) >> simp[])
     >> mp_tac (Q.INST [`rt` |-> `tn`, `op` |-> `lenop`, `x` |-> `szw:256 word`]
          ricf_execution_nonaddress_operand) >>
        impl_tac >- (fs[MEM, is_pointer_preserving_op_def] >>
          Cases_on `addr = lenop` >> Cases_on `srcop = lenop` >>
          simp[mem_read_ops_def, mem_write_ops_def]) >> simp[]) >>
  qexists_tac `target` >> metis_tac[]
QED
