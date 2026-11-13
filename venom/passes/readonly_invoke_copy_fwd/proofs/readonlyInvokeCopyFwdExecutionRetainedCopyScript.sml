Theory readonlyInvokeCopyFwdExecutionRetainedCopy
Ancestors
  readonlyInvokeCopyFwdExecutionWordWrites readonlyInvokeCopyFwdExecutionReadClassification
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

Theorem ricf_execution_retained_copy_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H certificates E sites maps targets tn /\
  ricf_analyzed_origins vs C stk PG G tn fn inst s a U B certificates sites maps /\
  ricf_certificate_readonly vs C log_of stk PG G tn fn inst s U B certificates /\
  o1_ctx_shape C /\ o1_fn_shape C fn /\ wf_ssa fn /\
  ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
  EVERY wf_ssa C.ctx_functions /\ EVERY ricf_param_order_ok C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ ricf_mapped_support a B E PG G sites /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [MCOPY] /\ step_inst fuel C inst s = OK u /\
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
  `inst.inst_opcode = MCOPY` by fs[MEM] >>
  `opaque_use_ok fn /\ fn_inst_wf fn` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
  `inst_wf inst` by
    (fs[fn_inst_wf_def, active_inst_def] >> metis_tac[MEM_EL]) >>
  `inst.inst_outputs = []` by gvs[MEM, inst_wf_def] >>
  `?dop rop zop d r z. inst.inst_operands = [dop;rop;zop] /\
    eval_operand dop s = SOME d /\ eval_operand rop s = SOME r /\
    eval_operand zop s = SOME z /\
    u = mcopy (w2n d) (w2n r) (w2n z) s` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >>
     fs[MEM] >> gvs[step_inst_non_invoke,
       step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[]) >>
  `ricf_analyzed_map_origins vs C stk PG G tn fn inst s U B sites` by
    fs[ricf_analyzed_origins_def] >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn dop = {} /\ op_taint tn rop = {} /\ op_taint tn zop = {}` by
    (gvs[MEM, taint_ok_def] >> metis_tac[]) >>
  `eval_operand zop t = SOME z` by
    (mp_tac (Q.INST [`ledger` |-> `certificates`, `op` |-> `zop`, `x` |-> `z:256 word`, `rt` |-> `tn`]
       ricf_execution_nonaddress_operand) >>
     (impl_tac >- (simp[MEM, is_pointer_preserving_op_def] >>
       Cases_on `zop = dop` >> Cases_on `zop = rop` >>
       gvs[mem_read_ops_def, mem_write_ops_def] >> rpt strip_tac >> gvs[])) >> simp[]) >>
  `!name. dop = Var name ==> ~retpc_var fn name` by
    (qx_gen_tac `name` >> disch_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> fs[MEM] >> metis_tac[active_inst_mem_fn_insts]) >>
  `!name. rop = Var name ==> ~retpc_var fn name` by
    (qx_gen_tac `name` >> disch_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> fs[MEM] >> metis_tac[active_inst_mem_fn_insts]) >>
  `?q. eval_operand dop t = SOME q /\ (w2n z = 0 \/ d = q)` by
    (mp_tac (Q.INST [`ledger` |-> `certificates`, `x` |-> `d:256 word`,
       `len` |-> `w2n (z:256 word)`, `addr` |-> `dop`,
       `ops` |-> `<|iao_ofst := dop; iao_size := SOME zop;
         iao_max_size := SOME zop|>`] ricf_execution_write_address) >>
     (impl_tac >- simp[MEM, mem_write_ops_def, source_memory_write_ranges_def,
       sized_source_write_range_def]) >> simp[]) >>
  `?tr. eval_operand rop t = SOME tr /\
    (!k. k < w2n z /\ w2n r+k NOTIN tn.t_mem ==>
      read_byte (w2n r+k) s.vs_memory = read_byte (w2n tr+k) t.vs_memory)` by
    (mp_tac (Q.INST [`ledger` |-> `certificates`, `x` |-> `r:256 word`,
       `len` |-> `w2n (z:256 word)`, `addr` |-> `rop`,
       `ops` |-> `<|iao_ofst := rop; iao_size := SOME zop;
         iao_max_size := SOME zop|>`] ricf_execution_read_bytes) >>
     (impl_tac >- simp[MEM, mem_read_ops_def, source_memory_read_ranges_def,
       memory_range_of_operands_def]) >> simp[]) >>
  `step_inst fuel Ct inst t = OK (mcopy (w2n q) (w2n tr) (w2n z) t)` by
    simp[MEM, step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  qexists_tac `mcopy (w2n q) (w2n tr) (w2n z) t` >> conj_tac >- simp[] >>
  Cases_on `w2n z = 0`
  >- (`z = 0w` by metis_tac[w2n_eq_0] >>
      `step_prov PG G inst u = G /\ step_taint inst s u tn = tn /\
       occurrence_sites_step a B inst u = B` by
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`MEM inst.inst_opcode _`, `inst.inst_operands = _`, `inst.inst_outputs = _`,
           `eval_operand dop s = _`, `eval_operand rop s = _`,
           `eval_operand zop s = _`, `z = 0w`, `u = _`] >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
         fs[MEM] >> simp[step_prov_def, set_prov_def, DRESTRICT_UNIV,
          occurrence_sites_step_def, step_taint_def, mem_taint_def,
          new_site_bytes_def, written_taint_def, step_writes_def,
          source_memory_write_ranges_def, sized_source_write_range_def,
          range_bytes_def, out_taint_def, set_var_taint_def, adopt_reset_def,
          store_taint_def, imm_taint_def, taint_component_equality, FLOOKUP_DEF,
          mcopy_def, read_memory_def, write_memory_with_expansion_def] >> SET_TAC[]) >>
      mp_tac (Q.INST [`ledger` |-> `certificates`, `dst` |-> `w2n (d:256 word)`,
        `target` |-> `w2n (q:256 word)`, `v` |->
          `mcopy (w2n (q:256 word)) (w2n (tr:256 word)) (w2n (z:256 word)) t`] ricf_execution_empty_write_next) >>
      impl_tac >- (fs[MEM, mcopy_def, read_memory_def, is_terminator_def]) >> simp[]) >>
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
  qpat_x_assum `u = mcopy _ _ _ _` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`ledger` |-> `certificates`,
    `dst` |-> `w2n (d:256 word)`, `src` |-> `w2n (r:256 word)`,
    `len` |-> `w2n (z:256 word)`, `dstop` |-> `dop`, `srcop` |-> `rop`,
    `lenop` |-> `zop`, `tgt` |-> `w2n (tr:256 word)`] ricf_execution_mcopy_next) >>
  impl_tac >- (simp[w2n_lt] >> metis_tac[ADD_COMM]) >> strip_tac >>
  gvs[step_prov_def, set_prov_def, DRESTRICT_UNIV, occurrence_sites_step_def, w2n_lt] >>
  metis_tac[]
QED
