Theory readonlyInvokeCopyFwdExecutionCallOperands
Ancestors
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdExecutionReadClassification
  readonlyInvokeCopyFwdExecutionWriteClassification
  readonlyInvokeCopyFwdExecutionMemoryScalars
  readonlyInvokeCopyFwdExecutionExternal readonlyInvokeCopyFwdRel
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdMapCoverage
  readonlyInvokeCopyFwdAnalyzedOrigins readonlyInvokeCopyFwdReadonlyContract
  o1LowerDloadOccurrence internalReturnCopyFwdSim allocaFrontierBound
  pointerConfinedDefs ptrDiscipline memLocDefs frameViewFacts
  venomExecSemantics venomState venomInst codegenRel contextCodegenRel
  o1LowerDloadShared taintAgree frameRel venomCallOracleDefs extCallOracle
  o1PassContract finite_map list pred_set words

Theorem ricf_execution_call_family_operands:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ricf_mapped_support a B E PG G sites /\
  ricf_analyzed_map_origins vs C stk PG G tn fn inst s U B sites /\
  o1_ctx_shape C /\ ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
  EVERY wf_ssa C.ctx_functions /\ EVERY ricf_param_order_ok C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ mem_inv raw_mem_ok C vs /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ ~in_revert_forward fn s /\
  ((inst.inst_opcode = CALL /\ prefix = [gop;adop;vop]) \/
   (MEM inst.inst_opcode [STATICCALL;DELEGATECALL] /\ prefix = [gop;adop])) /\
  inst.inst_operands = prefix ++ [aop;azop;rop;rsop] /\
  IS_SOME (eval_operands prefix s) /\
  eval_operand aop s = SOME ao /\ eval_operand azop s = SOME az /\
  eval_operand rop s = SOME ro /\ eval_operand rsop s = SOME rs ==>
  (!op x. MEM op (prefix ++ [azop;rsop]) /\ eval_operand op s = SOME x ==>
    eval_operand op t = SOME x) /\
  ?ao' ro'. eval_operand aop t = SOME ao' /\ eval_operand rop t = SOME ro' /\
    read_memory (w2n ao) (w2n az) s = read_memory (w2n ao') (w2n az) t /\
    (w2n rs = 0 \/ ro = ro')
Proof
  strip_tac >> fs[MEM] >>
  `?prefix_values. eval_operands prefix s = SOME prefix_values` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `!op. MEM op inst.inst_operands ==> op_taint tn op = {}` by
    (rpt strip_tac >> gvs[taint_ok_def] >> metis_tac[]) >>
  `!op x. MEM op (prefix ++ [azop;rsop]) /\ eval_operand op s = SOME x ==>
    eval_operand op t = SOME x` by
    (rpt strip_tac >>
     mp_tac (Q.INST [`rt` |-> `tn`] ricf_execution_nonaddress_operand) >>
     (impl_tac >- (simp[Excl "FILTER"] >>
       gvs[Excl "FILTER", MEM, is_pointer_preserving_op_def,
         mem_read_ops_def, mem_write_ops_def] >>
       rpt strip_tac >> gvs[Excl "FILTER"] >>
       qpat_x_assum `FILTER _ _ = [_]` mp_tac >> simp[FILTER] >>
       rpt (IF_CASES_TAC >> simp[]))) >> simp[]) >>
  `(!name. aop = Var name ==> ~retpc_var fn name) /\
   (!name. rop = Var name ==> ~retpc_var fn name)` by
    (conj_tac >> rpt gen_tac >> strip_tac >>
     irule ordinary_operand_not_retpc >> simp[] >> qexists_tac `inst` >>
     gvs[MEM] >> metis_tac[active_inst_mem_fn_insts]) >>
  `?ao'. eval_operand aop t = SOME ao' /\
    read_memory (w2n ao) (w2n az) s = read_memory (w2n ao') (w2n az) t` by
    (mp_tac (Q.INST [`addr` |-> `aop`, `x` |-> `ao:256 word`,
       `len` |-> `w2n (az:256 word)`,
       `ops` |-> `<|iao_ofst := aop; iao_size := SOME azop;
         iao_max_size := SOME azop|>`] ricf_execution_observer_read) >>
     (impl_tac >- (gvs[MEM, eval_operands_def, AllCaseEqs()] >> simp[mem_read_ops_def,
       source_memory_read_ranges_def, memory_range_of_operands_def])) >> simp[]) >>
  `?ro'. eval_operand rop t = SOME ro' /\ (w2n rs = 0 \/ ro = ro')` by
    (mp_tac (Q.INST [`addr` |-> `rop`, `x` |-> `ro:256 word`,
       `len` |-> `w2n (rs:256 word)`,
       `ops` |-> `<|iao_ofst := rop; iao_size := NONE;
         iao_max_size := SOME rsop|>`] ricf_execution_write_address) >>
     (impl_tac >- (gvs[MEM, eval_operands_def, AllCaseEqs()] >> simp[mem_write_ops_def,
       source_memory_write_ranges_def, sized_source_write_range_def])) >> simp[]) >>
  gvs[] >> metis_tac[]
QED

Theorem ricf_execution_call_operands:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ricf_mapped_support a B E PG G sites /\
  ricf_analyzed_map_origins vs C stk PG G tn fn inst s U B sites /\
  o1_ctx_shape C /\ ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
  EVERY wf_ssa C.ctx_functions /\ EVERY ricf_param_order_ok C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ mem_inv raw_mem_ok C vs /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ ~in_revert_forward fn s /\
  ((inst.inst_opcode = CALL /\ prefix = [gop;adop;vop]) \/
   (inst.inst_opcode = STATICCALL /\ prefix = [gop;adop])) /\
  inst.inst_operands = prefix ++ [aop;azop;rop;rsop] /\
  IS_SOME (eval_operands prefix s) /\
  eval_operand aop s = SOME ao /\ eval_operand azop s = SOME az /\
  eval_operand rop s = SOME ro /\ eval_operand rsop s = SOME rs ==>
  (!op x. MEM op (prefix ++ [azop;rsop]) /\ eval_operand op s = SOME x ==>
    eval_operand op t = SOME x) /\
  ?ao' ro'. eval_operand aop t = SOME ao' /\ eval_operand rop t = SOME ro' /\
    read_memory (w2n ao) (w2n az) s = read_memory (w2n ao') (w2n az) t /\
    (w2n rs = 0 \/ ro = ro')
Proof
  strip_tac >> mp_tac ricf_execution_call_family_operands >>
  (impl_tac >- simp[]) >> simp[]
QED

Theorem ricf_execution_call_request_compatible:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  taint_within D C vs /\ active_inst fn inst s /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK u /\
  LENGTH s.vs_requests < LENGTH u.vs_requests /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n ao') (w2n az) t ==>
  ((computed_precompile (venom_call_request s addr value ao az static) /\
    computed_precompile (venom_call_request t addr value ao' az static) /\
    (venom_call_request s addr value ao az static).cr_target =
      (venom_call_request t addr value ao' az static).cr_target /\
    (venom_call_request s addr value ao az static).cr_data =
      (venom_call_request t addr value ao' az static).cr_data) \/
   request_agree_except D (venom_call_request s addr value ao az static)
     (venom_call_request t addr value ao' az static))
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
      (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
   tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
      (s.vs_transient s.vs_call_ctx.cc_address)` by
    (fs[taint_within_def] >> metis_tac[]) >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t` by
    fs[ricf_execution_invariant_def] >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by
    (qpat_x_assum `ricf_opaque_frame_agree _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ricf_opaque_frame_agree_def, ricf_frame_agree_def] >> strip_tac >>
     drule taint_agree_shared >> simp[ricf_opaque_view_def, ld_shared_agree_def]) >>
  `accounts_agree_except D s.vs_accounts t.vs_accounts /\
   transient_agree_except D s.vs_transient t.vs_transient` by
    metis_tac[ld_shared_accounts_observe, ld_shared_transient_observe] >>
  mp_tac (Q.INST [`X` |-> `ircf_dead (ricf_original_copy_ids C) s stk`,
    `PG` |-> `ricf_complete_params PG s.vs_params`]
    ricf_opaque_call_request_compatible) >> (impl_tac >- simp[]) >> simp[]
QED
