(* Arbitrary-calldata dispatch and passing-check boundary. *)
Theory defaultEntryPrefix
Ancestors
  entryPtrSeamPrefix entryChecksPassPtr entryPrefixPtr entryDispatchPtr
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
  strip_tac >> Cases_on `m <= 4`
  >- (`compile_entry_checks 0 pay st = ((),st')` by
        (qpat_x_assum `compile_entry_checks _ _ _ = _` mp_tac >>
         simp[compile_entry_checks_def]) >>
      drule compile_entry_checks_ptr_endpoint >>
      disch_then (qspecl_then [`tn`, `s`, `lo`, `fn`, `ctx`, `PG`, `G`] mp_tac) >>
      simp[]) >>
  drule compile_entry_checks_ptr_endpoint >>
  disch_then (qspecl_then [`tn`, `s`, `lo`, `fn`, `ctx`, `PG`, `G`] mp_tac) >>
  simp[]
QED
