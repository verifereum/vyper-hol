Theory readonlyInvokeCopyFwdExecutionExternalData
Ancestors
  readonlyInvokeCopyFwdExecutionMemoryWrites readonlyInvokeCopyFwdExecutionDataCopies
  readonlyInvokeCopyFwdExecutionEmptyWrites
  readonlyInvokeCopyFwdExecutionWriteGuards readonlyInvokeCopyFwdExecutionWriteClassification
  readonlyInvokeCopyFwdExecutionMemoryScalars readonlyInvokeCopyFwdExecutionOrdinary
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdAnalyzedOrigins
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdHistoryPhase
  o1LowerDloadOccurrence o1LowerDloadGhost o1LowerDloadJointRead1 o1LowerDloadShared o1PassContract unitShapeDefs
  allocaFrontierBound frameViewFacts codegenRel
  ptrDiscipline pointerConfinedDefs memLocDefs taintAgree
  contextCodegenRel venomWf venomExecSemantics venomExecProps venomMemProps
  venomState venomInst list finite_map words arithmetic


Theorem ricf_execution_ext_copy_operands[local]:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ricf_analyzed_map_origins vs C stk PG G tn fn inst s U B sites /\
  o1_ctx_shape C /\ opaque_use_ok fn /\
  ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
  EVERY wf_ssa C.ctx_functions /\ EVERY ricf_param_order_ok C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [EXTCODECOPY] /\
  inst.inst_operands = [accountop;addr;srcop;lenop] /\
  eval_operand accountop s = SOME account /\ eval_operand addr s = SOME dst /\
  eval_operand srcop s = SOME src /\
  eval_operand lenop s = SOME szw ==>
  ?target. eval_operand addr t = SOME target /\
    (w2n szw = 0 \/ target = dst) /\
    eval_operand srcop t = SOME src /\ eval_operand lenop t = SOME szw /\
    eval_operand accountop t = SOME account
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
           Cases_on `srcop = accountop` >>
           gvs[mem_read_ops_def, mem_write_ops_def]) >> simp[])
     >> mp_tac (Q.INST [`rt` |-> `tn`, `op` |-> `lenop`, `x` |-> `szw:256 word`]
          ricf_execution_nonaddress_operand) >>
        impl_tac >- (fs[MEM, is_pointer_preserving_op_def] >>
          Cases_on `addr = lenop` >> Cases_on `srcop = lenop` >>
          Cases_on `lenop = accountop` >>
          gvs[mem_read_ops_def, mem_write_ops_def]) >> simp[]) >>
  `op_taint tn accountop = {}` by metis_tac[MEM] >>
  `eval_operand accountop t = SOME account` by
    (mp_tac (Q.INST [`rt` |-> `tn`, `op` |-> `accountop`, `x` |-> `account:256 word`]
       ricf_execution_nonaddress_operand) >>
     (impl_tac >- (fs[MEM, is_pointer_preserving_op_def] >>
       Cases_on `addr = accountop` >> Cases_on `srcop = accountop` >>
       Cases_on `lenop = accountop` >> gvs[mem_read_ops_def, mem_write_ops_def])) >> simp[]) >>
  qexists_tac `target` >> metis_tac[]
QED

Theorem ricf_execution_external_data_next:
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
  MEM inst.inst_opcode [EXTCODECOPY] /\ step_inst fuel C inst s = OK u /\
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
  `!addr. (lookup_account addr s.vs_accounts).code =
    (lookup_account addr t.vs_accounts).code` by
    (`ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by
       fs[ricf_execution_invariant_def, ricf_opaque_frame_agree_def,
         ricf_frame_agree_def, taint_agree_def, ricf_opaque_view_def,
         ld_shared_agree_def] >>
     metis_tac[ld_shared_account_observations]) >>
  `?accountop dop rop zop account d r z.
    inst.inst_operands = [accountop;dop;rop;zop] /\ eval_operand accountop s = SOME account /\
    eval_operand dop s = SOME d /\ eval_operand rop s = SOME r /\
    eval_operand zop s = SOME z /\
    u = write_memory_with_expansion (w2n d)
      (TAKE (w2n z) (DROP (w2n r) (lookup_account (w2w account) s.vs_accounts).code ++ REPLICATE (w2n z) 0w)) s` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >>
     fs[MEM] >> gvs[step_inst_non_invoke,
       step_inst_base_opcode_eqs, AllCaseEqs()] >> metis_tac[]) >>
  `ricf_analyzed_map_origins vs C stk PG G tn fn inst s U B sites` by
    fs[ricf_analyzed_origins_def] >>
  mp_tac (Q.INST [`ledger` |-> `certificates`, `addr` |-> `dop`,
    `srcop` |-> `rop`, `lenop` |-> `zop`, `dst` |-> `d:256 word`,
    `src` |-> `r:256 word`, `szw` |-> `z:256 word`, `accountop` |-> `accountop`,
    `account` |-> `account:256 word`] ricf_execution_ext_copy_operands) >>
  impl_tac >- (simp[] >> fs[MEM]) >>
  disch_then (qx_choose_then `q` (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac assume_tac))))) >>
  qabbrev_tac `xs = TAKE (w2n z) (DROP (w2n r) (lookup_account (w2w account) s.vs_accounts).code ++ REPLICATE (w2n z) 0w)` >>
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
           `eval_operand accountop s = _`,
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
    `lenop` |-> `zop`, `accountop` |-> `accountop`,
    `account` |-> `account:256 word`] ricf_execution_extcodecopy_next) >>
  impl_tac >- (simp[Abbr `xs`, w2n_lt] >> fs[MEM] >> metis_tac[ADD_COMM]) >> strip_tac >>
  gvs[step_prov_def, set_prov_def, DRESTRICT_UNIV, occurrence_sites_step_def]
QED
