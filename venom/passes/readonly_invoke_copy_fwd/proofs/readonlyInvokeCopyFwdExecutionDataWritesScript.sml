Theory readonlyInvokeCopyFwdExecutionDataWrites
Ancestors
  readonlyInvokeCopyFwdExecutionDataCopies readonlyInvokeCopyFwdExecutionDataOperands
  readonlyInvokeCopyFwdExecutionEmptyWrites readonlyInvokeCopyFwdExecutionMemoryWrites
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

Theorem ricf_execution_data_write_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H certificates E sites maps targets tn /\
  ricf_analyzed_origins vs C stk PG G tn fn inst s a U B certificates sites maps /\
  ricf_certificate_readonly vs C log_of stk PG G tn fn inst s U B certificates /\
  o1_ctx_shape C /\ o1_fn_shape C fn /\ wf_ssa fn /\
  ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
  EVERY wf_ssa C.ctx_functions /\ EVERY ricf_param_order_ok C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [CALLDATACOPY;DLOADBYTES;CODECOPY] /\ step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) certificates E sites maps targets
      (step_taint inst s u tn)
Proof
  strip_tac >>
  `opaque_use_ok fn /\ fn_inst_wf fn` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
  `inst_wf inst` by
    (fs[fn_inst_wf_def, active_inst_def] >> metis_tac[MEM_EL]) >>
  `inst.inst_outputs = []` by gvs[MEM, inst_wf_def] >>
  qabbrev_tac `data = if inst.inst_opcode = CALLDATACOPY then s.vs_call_ctx.cc_calldata
    else if inst.inst_opcode = DLOADBYTES then s.vs_data_section else s.vs_code` >>
  `data = if inst.inst_opcode = CALLDATACOPY then t.vs_call_ctx.cc_calldata
    else if inst.inst_opcode = DLOADBYTES then t.vs_data_section else t.vs_code` by
    fs[Abbr `data`, ricf_execution_invariant_def, ricf_opaque_frame_agree_def,
      ricf_frame_agree_def, taint_agree_def, ricf_opaque_view_def,
      venom_state_component_equality] >>
  `?dop rop zop d r z. inst.inst_operands = [dop;rop;zop] /\
    eval_operand dop s = SOME d /\ eval_operand rop s = SOME r /\
    eval_operand zop s = SOME z /\
    u = write_memory_with_expansion (w2n d)
      (TAKE (w2n z) (DROP (w2n r) data ++ REPLICATE (w2n z) 0w)) s` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >>
     fs[MEM] >> gvs[Abbr `data`, step_inst_non_invoke,
       step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[]) >>
  `ricf_analyzed_map_origins vs C stk PG G tn fn inst s U B sites` by
    fs[ricf_analyzed_origins_def] >>
  mp_tac (Q.INST [`ledger` |-> `certificates`, `addr` |-> `dop`,
    `srcop` |-> `rop`, `lenop` |-> `zop`, `dst` |-> `d:256 word`,
    `src` |-> `r:256 word`, `szw` |-> `z:256 word`] ricf_execution_data_copy_operands) >>
  impl_tac >- (simp[] >> fs[MEM]) >>
  disch_then (qx_choose_then `q` (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac)))) >>
  qabbrev_tac `xs = TAKE (w2n z) (DROP (w2n r) data ++ REPLICATE (w2n z) 0w)` >>
  `step_inst fuel Ct inst t = OK (write_memory_with_expansion (w2n q) xs t)` by
    (gvs[MEM] >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs, Abbr `xs`]) >>
  qexists_tac `write_memory_with_expansion (w2n q) xs t` >> conj_tac >- simp[] >>
  Cases_on `w2n z = 0`
  >- (`z = 0w` by metis_tac[w2n_eq_0] >>
      `xs = []` by simp[Abbr `xs`] >>
      `step_prov PG G inst u = G /\ step_taint inst s u tn = tn /\
       occurrence_sites_step a B inst u = B` by
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`MEM inst.inst_opcode _`, `inst.inst_operands = _`, `inst.inst_outputs = _`,
           `eval_operand dop s = _`, `eval_operand rop s = _`,
           `eval_operand zop s = _`, `z = 0w`, `u = _`, `xs = []`] >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
         fs[MEM] >> simp[step_prov_def, set_prov_def, DRESTRICT_UNIV,
          occurrence_sites_step_def, step_taint_def, mem_taint_def,
          new_site_bytes_def, written_taint_def, step_writes_def,
          source_memory_write_ranges_def, sized_source_write_range_def,
          range_bytes_def, out_taint_def, set_var_taint_def, adopt_reset_def,
          store_taint_def, imm_taint_def, taint_component_equality, FLOOKUP_DEF,
          write_memory_with_expansion_def] >> SET_TAC[]) >>
      mp_tac (Q.INST [`ledger` |-> `certificates`, `dst` |-> `w2n (d:256 word)`,
        `target` |-> `w2n (q:256 word)`, `v` |->
          `write_memory_with_expansion (w2n (q:256 word)) [] t`] ricf_execution_empty_write_next) >>
      impl_tac >- (fs[MEM, Abbr `xs`, is_terminator_def]) >> simp[]) >>
  `q = d` by metis_tac[] >>
  qpat_x_assum `q = d` SUBST_ALL_TAC >>
  `MEM (w2n d,w2n z) (source_memory_write_ranges inst s)` by
    fs[MEM, source_memory_write_ranges_def, sized_source_write_range_def] >>
  `!gam. gam = ricf_phase_ranges 0 certificates \/
      MEM gam (ricf_phase_stack_ranges stk certificates) \/
      gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      ~(w2n d <= db+k /\ db+k < w2n d+w2n z) /\
      ~(w2n d <= sb+k /\ sb+k < w2n d+w2n z)` by
    (qx_gen_tac `gam` >> disch_tac >>
     qx_genl_tac [`db`,`sb`,`sz`,`k`] >>
     disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
     mp_tac (Q.INST [`off` |-> `w2n (d:256 word)`, `len` |-> `w2n (z:256 word)`]
       ricf_execution_write_ranges) >>
     impl_tac >- simp[] >> simp[]) >>
  qpat_x_assum `u = write_memory_with_expansion _ _ _` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`ledger` |-> `certificates`,
    `dst` |-> `w2n (d:256 word)`, `src` |-> `w2n (r:256 word)`,
    `len` |-> `w2n (z:256 word)`, `dstop` |-> `dop`, `srcop` |-> `rop`,
    `lenop` |-> `zop`] ricf_execution_data_copy_next) >>
  impl_tac >- (simp[Abbr `xs`, w2n_lt] >> metis_tac[ADD_COMM]) >> strip_tac >>
  gvs[step_prov_def, set_prov_def, DRESTRICT_UNIV, occurrence_sites_step_def]
QED
