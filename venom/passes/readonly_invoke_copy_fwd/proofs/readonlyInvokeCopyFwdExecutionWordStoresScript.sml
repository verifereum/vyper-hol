Theory readonlyInvokeCopyFwdExecutionWordStores
Ancestors
  readonlyInvokeCopyFwdExecutionWordWrites
  readonlyInvokeCopyFwdExecutionWriteGuards readonlyInvokeCopyFwdExecutionWriteClassification
  readonlyInvokeCopyFwdExecutionMemoryScalars readonlyInvokeCopyFwdExecutionOrdinary
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdAnalyzedOrigins
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdHistoryPhase
  o1LowerDloadOccurrence o1LowerDloadGhost o1PassContract unitShapeDefs frameViewFacts allocaFrontierBound codegenRel
  ptrDiscipline pointerConfinedDefs memLocDefs taintAgree
  contextCodegenRel venomWf venomExecSemantics venomExecProps venomMemProps
  venomState venomInst list finite_map words arithmetic pred_set

Theorem ricf_execution_word_store_next:
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
  MEM inst.inst_opcode [MSTORE;ISTORE] /\ step_inst fuel C inst s = OK u /\
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
  `ssa_form fn /\ opaque_use_ok fn /\ fn_inst_wf fn` by
    fs[o1_fn_shape_def, fn_shape_ok_def, wf_ssa_def] >>
  `inst_wf inst` by
    (fs[fn_inst_wf_def, active_inst_def] >> metis_tac[MEM_EL]) >>
  `inst.inst_outputs = []` by gvs[MEM, inst_wf_def] >>
  `?addr value x w. inst.inst_operands = [addr;value] /\
    eval_operand addr s = SOME x /\ eval_operand value s = SOME w /\
    u = if inst.inst_opcode = MSTORE then mstore (w2n x) w s else istore (w2n x) w s` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >>
     fs[MEM] >> gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_write2_def,
       AllCaseEqs()] >> metis_tac[]) >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn addr = {}` by
    (spose_not_then assume_tac >> fs[taint_ok_def] >>
     qpat_x_assum `!op. MEM op _ /\ _ ==> _` (qspec_then `addr` mp_tac) >>
     fs[MEM] >> gvs[]) >>
  `!name. addr = Var name ==> ~retpc_var fn name` by
    (qx_gen_tac `name` >> disch_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> fs[MEM] >> metis_tac[active_inst_mem_fn_insts]) >>
  `mem_write_ops inst = SOME <|iao_ofst := addr; iao_size := SOME (Lit 32w); iao_max_size := SOME (Lit 32w)|>` by
    fs[MEM, mem_write_ops_def] >>
  `MEM (w2n x,32) (source_memory_write_ranges inst s)` by
    fs[MEM, source_memory_write_ranges_def, fixed_source_write_range_def] >>
  `eval_operand addr t = SOME x` by
    (mp_tac (Q.INST [`ledger` |-> `certificates`, `len` |-> `32`,
      `ops` |-> `<|iao_ofst := addr; iao_size := SOME (Lit 32w);
        iao_max_size := SOME (Lit 32w)|>`] ricf_execution_write_address_same) >>
     impl_tac >- (simp[] >> fs[ricf_analyzed_origins_def] >> metis_tac[MEM]) >> simp[]) >>
  `?y. eval_operand value t = SOME y /\ word_agree_except (op_taint tn value) w y` by
    (mp_tac (Q.INST [`ledger` |-> `certificates`, `rt` |-> `tn`,
      `op` |-> `value`, `x` |-> `w:256 word`] ricf_execution_nonaddress_value) >>
     impl_tac >- (fs[MEM, is_pointer_preserving_op_def] >>
       Cases_on `addr = value` >> simp[mem_read_ops_def, mem_write_ops_def]) >> simp[]) >>
  `op_taint tn value SUBSET count 32` by
    (simp[SUBSET_DEF] >> metis_tac[frame_reachable_op_taint_bounded]) >>
  `!gam. gam = ricf_phase_ranges 0 certificates \/
      MEM gam (ricf_phase_stack_ranges stk certificates) \/
      gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      ~(w2n x <= db+k /\ db+k < w2n x+32) /\
      ~(w2n x <= sb+k /\ sb+k < w2n x+32)` by
    (qx_gen_tac `gam` >> disch_tac >>
     qx_genl_tac [`db`,`sb`,`sz`,`k`] >>
     disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
     mp_tac (Q.INST [`off` |-> `w2n (x:256 word)`, `len` |-> `32`]
       ricf_execution_write_ranges) >>
     impl_tac >- simp[] >> simp[]) >>
  qexists_tac `if inst.inst_opcode = MSTORE then mstore (w2n x) y t
    else istore (w2n x) y t` >>
  fs[MEM] >> gvs[]
  >- (mp_tac (Q.INST [`ledger` |-> `certificates`, `dst` |-> `w2n (x:256 word)`, `x` |-> `w:256 word`,
        `y` |-> `y:256 word`, `m` |-> `op_taint tn value`] ricf_execution_mstore_next) >>
      impl_tac >- (simp[w2n_lt] >> metis_tac[]) >> strip_tac >>
      gvs[step_prov_def, set_prov_def, DRESTRICT_UNIV, occurrence_sites_step_def])
  >> mp_tac (Q.INST [`ledger` |-> `certificates`, `dst` |-> `w2n (x:256 word)`, `x` |-> `w:256 word`,
       `y` |-> `y:256 word`, `m` |-> `op_taint tn value`] ricf_execution_istore_next) >>
     impl_tac >- (simp[w2n_lt] >> metis_tac[]) >> strip_tac >>
     gvs[step_prov_def, set_prov_def, DRESTRICT_UNIV, occurrence_sites_step_def]
QED
