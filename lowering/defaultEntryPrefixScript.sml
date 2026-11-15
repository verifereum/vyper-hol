(* Arbitrary-calldata dispatch and passing-check boundary. *)
Theory defaultEntryPrefix
Ancestors
  entryChecksPassPtr entryPrefixPtr entryDispatchPtr
  entryDispatchProps moduleLowering moduleLoweringProps emitHelperProps
  fragGasOriginPtr fragGasPathMem ptrSafeRun ptrDiscipline contextCodegenRel
  compileEnv fragExec venomExecSemantics venomState venomInst list arithmetic

Theorem default_entry_checks_ptr_endpoint:
  compile_entry_checks m pay st = ((),st') /\ fn_has_code st st' fn /\
  fresh_vars_wrt st s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (pay \/ s.vs_call_ctx.cc_callvalue = 0w) /\
  (m <= 4 \/ m <= LENGTH s.vs_call_ctx.cc_calldata) /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
  ?u G' tn'.
    gas_path_mem ctx fn s 0 (OK u) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK u,G',tn')) /\
    vars_pc_only s u /\ fresh_vars_wrt st' u /\ ~u.vs_halted /\
    u.vs_current_bb = st'.cs_current_bb /\
    u.vs_inst_idx = LENGTH st'.cs_current_insts /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' u) ==>
         !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `m <= 4`
  >- (`compile_entry_checks 0 pay st = ((),st')` by
        (qpat_x_assum `compile_entry_checks _ _ _ = _` mp_tac >>
         simp[compile_entry_checks_def]) >>
      qpat_x_assum `compile_entry_checks m _ _ = _` kall_tac >>
      drule compile_entry_checks_ptr_endpoint >>
      disch_then (qspecl_then [`tn`, `s`, `lo`, `fn`, `ctx`, `PG`, `G`] mp_tac) >>
      simp[]) >>
  drule compile_entry_checks_ptr_endpoint >>
  disch_then (qspecl_then [`tn`, `s`, `lo`, `fn`, `ctx`, `PG`, `G`] mp_tac) >>
  simp[]
QED

Theorem default_entry_prefix_joint:
  compile_selector_dispatch_linear selectors fallback ds = ((),de) /\
  fn_has_code ds de fn /\ fn_inst_ids_distinct fn /\
  EVERY (\(sel,lbl). sel < 2 ** 32) selectors /\
  cs_extends de opened /\ de.cs_next_var <= opened.cs_next_var /\
  opened.cs_current_insts = [] /\
  compile_entry_checks m pay opened = ((),st) /\ fn_has_code opened st fn /\
  (!bb. lookup_block opened.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  (?bb. lookup_block opened.cs_current_bb fn.fn_blocks = SOME bb) /\
  linear_dispatch_target s.vs_call_ctx.cc_calldata selectors fallback =
    opened.cs_current_bb /\
  fresh_vars_wrt ds s /\ ~s.vs_halted /\
  s.vs_current_bb = ds.cs_current_bb /\
  s.vs_inst_idx = 0 /\ ds.cs_current_insts = [] /\
  allocas_from 0 s /\ ~ctx_has_dalloca ctx /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  (m <= 4 \/ m <= LENGTH s.vs_call_ctx.cc_calldata) /\
  (pay \/ s.vs_call_ctx.cc_callvalue = 0w) ==>
  ?u G2 tn2.
    gas_path_mem ctx fn s 0 (OK u) /\
    (!D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,[])
      (s,FEMPTY,entry_taint) [] (OK u,G2,tn2)) /\
    vars_pc_only s u /\ u.vs_gas_readings = s.vs_gas_readings /\
    fresh_vars_wrt st u /\ ~u.vs_halted /\
    u.vs_current_bb = st.cs_current_bb /\
    u.vs_inst_idx = LENGTH st.cs_current_insts /\
    tn2.t_mem = {} /\ tn2.t_stor = {} /\
    tn2.t_trans = {} /\ tn2.t_imm = {} /\
    (!D. (!fuel. ptr_safe_run D 0 fuel ctx fn [] G2 tn2 u) ==>
         !fuel. ptr_safe_blocks D 0 fuel ctx fn [] FEMPTY entry_taint s)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule compile_selector_dispatch_linear_ptr_endpoint >>
  disch_then (qspecl_then [`entry_taint`, `s`, `0`, `fn`, `ctx`, `[]`, `FEMPTY`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `vars_pc_only s t` >> rename1 `tn1.t_mem = entry_taint.t_mem` >>
  rename1 `ptr_safe_blocks _ _ _ _ _ _ G1 tn1 t` >>
  `t.vs_call_ctx = s.vs_call_ctx` by metis_tac[vars_pc_only_fields] >>
  `fresh_vars_wrt opened t` by
    (irule fresh_vars_wrt_mono >> qexists_tac `de` >> simp[]) >>
  `allocas_from 0 t` by
    (fs[allocas_from_def] >> metis_tac[vars_pc_only_fields]) >>
  drule default_entry_checks_ptr_endpoint >>
  disch_then (qspecl_then [`tn1`, `t`, `0`, `fn`, `ctx`, `[]`, `G1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `vars_pc_only t u` >> rename1 `tn2.t_mem = tn1.t_mem` >>
  rename1 `ptr_safe_run _ _ _ _ _ _ G2 tn2 u` >>
  qexistsl_tac [`u`, `G2`, `tn2`] >>
  `gas_path_mem ctx fn s 0 (OK u)` by metis_tac[gas_path_mem_then, ADD_0] >>
  `!D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,[])
    (s,FEMPTY,entry_taint) [] (OK u,G2,tn2)` by
    metis_tac[gas_origin_ptr_path_append, APPEND] >>
  `vars_pc_only s u` by metis_tac[vars_pc_only_trans] >>
  `u.vs_gas_readings = s.vs_gas_readings` by
    metis_tac[vars_pc_only_gas_readings] >>
  `tn2.t_mem = {} /\ tn2.t_stor = {} /\
   tn2.t_trans = {} /\ tn2.t_imm = {}` by simp[entry_taint_def] >>
  simp[] >> rpt strip_tac >>
  `!fuel. ptr_safe_blocks D 0 fuel ctx fn [] G1 tn1 t` by
    (irule ptr_safe_blocks_from_phi_free_run >> simp[] >>
     metis_tac[]) >>
  drule_all compile_selector_dispatch_linear_layout >> strip_tac >>
  irule entryValueRevertPtrTheory.ptr_safe_blocks_nonphi_run >>
  simp[] >>
  qexists_tac `mk_inst ds.cs_next_id CALLDATASIZE []
     [STRING #"%" (toString ds.cs_next_var)]` >>
  gvs[mk_inst_def]
QED
