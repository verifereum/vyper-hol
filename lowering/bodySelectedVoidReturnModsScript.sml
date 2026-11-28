(* A void return reaches an empty internal RET on the linked callee frame. *)
Theory bodySelectedVoidReturnMods
Ancestors
  bodyFullPostsMods stmtSimReturn gasOutcomeFullCompose gasOutcomeFullBindMods bodyFullShared stateRelProj
  venomExecSemantics venomState compileEnv loweringPosts stmtLowering
  bodySim bodyInvSplit exprLoweringProps loweringStateRelDefs vyperState
  vyperInterpreter ptrDiscipline bodyFullShadowBodyInv bodyPtrDefs gasOutcome
  exprSimDefs gasContext gasShadow pair pred_set fragExec

Theorem void_return_compile[local]:
  stmt_env ce lctx NoneT (Return NONE) sa = (ce_out,sb) ==>
  compile_stmt ce lctx NoneT (Return NONE) sa = ((),sb)
Proof
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[]
QED

Theorem void_unlock_physical[local]:
  (return_unlock_state ce s).vs_data_section = s.vs_data_section /\
  (return_unlock_state ce s).vs_alloca_next = s.vs_alloca_next
Proof
  Cases_on `ce.ce_nonreentrant` >>
  rename1 `ce.ce_nonreentrant = (nr,info)` >> PairCases_on `info` >>
  Cases_on `nr` >> Cases_on `info1` >> Cases_on `info2` >>
  simp[return_unlock_state_def, tstore_def, sstore_def]
QED

Theorem void_return_immutable_frame[local]:
  same_frame ce site /\ immutable_frame_mods func site cx es s ==>
  immutable_frame_mods func ce cx (es with <|scopes := []; gas_obs := tail|>)
    (return_unlock_state site s)
Proof
  strip_tac >>
  `ce.ce_modules = site.ce_modules /\
   ce.ce_module_vars = site.ce_module_vars /\
   ce.ce_module_var_type = site.ce_module_var_type /\
   ce.ce_is_ctor = site.ce_is_ctor` by
    fs[same_frame_def, compile_env_component_equality] >>
  qpat_x_assum `same_frame _ _` kall_tac >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def,
     immutable_alloca_sep_mods_def] >>
  conj_tac
  >- (fs[immutables_rel_def, void_unlock_physical] >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_x_assum `!src tops. _ ==> immutable_alloca_sep _ _ _ _ _`
    (drule_then mp_tac) >>
  simp[immutable_alloca_sep_def, immutable_decl_sep_def, local_region_def,
       lookup_scopes_def, void_unlock_physical, return_unlock_state_frames] >>
  metis_tac[]
QED

Theorem void_return_result[local]:
  same_frame ce site /\ ce.ce_returns_count = 0 /\
  state_rel H func site cx es s ==>
  intret_q H func ce cx ret_tv NoneV
    (es with <|scopes := []; gas_obs := tail|>)
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
      (return_unlock_state site s))
Proof
  strip_tac >>
  `site.ce_nonreentrant = ce.ce_nonreentrant` by
    fs[same_frame_def, compile_env_component_equality] >>
  `return_unlock_state site s = return_unlock_state ce s` by
    simp[return_unlock_state_def] >>
  pop_assum SUBST1_TAC >> irule intret_q_intro >>
  simp[result_rel_def, intret_vals_match_def] >>
  `es with <|scopes := []; gas_obs := tail|> =
   (es with scopes := []) with gas_obs := tail` by simp[] >>
  pop_assum SUBST1_TAC >> REWRITE_TAC[state_rel_gas_obs] >>
  qexists_tac `s` >> simp[] >>
  drule_all_then ACCEPT_TAC constructor_exit_state_rel
QED

Theorem selected_void_return_frag_mods:
  same_frame ce site /\ ce.ce_return_pc = SOME (PtrVar (Var rpc) slot_size) /\
  ce.ce_returns_count = 0 /\
  ((FST ce.ce_nonreentrant /\ ~SND (SND (SND ce.ce_nonreentrant))) ==>
    ~cx.txn.is_static /\ FST (SND (SND ce.ce_nonreentrant))) /\
  (!H G tn tf s.
    dead_lo_ok_mods H (DF H) lo site cx /\
    tf.t_stor = tn.t_stor /\ tf.t_trans SUBSET tn.t_trans /\
    tf.t_imm = tn.t_imm /\ tf.t_mem = tn.t_mem /\
    ghost_inv_at_mods (DF H) lo NONE site cx es G tn s ==>
    stor_taint_ok_at (DF H) tf (return_unlock_state site s) /\
    !i. i < lo /\ i IN tf.t_mem ==>
      imm_section_dead_mods site (mem_bytes_at 0 lo (return_unlock_state site s).vs_memory) i) ==>
  stmt_frag_full_mods (DF,lo,NONE,ctx,shadow_ctx,PG,func,shadow_func) cx lctx
    (\H v ee gt r. intret_q H func ce cx ret_tv v ee r /\
      !ir u. r = IntRet ir u ==> immutable_frame_mods func ce cx (ee with scopes := []) u /\
        stor_taint_ok_at (DF H) (SND gt) u /\
        !i. i < lo /\ i IN (SND gt).t_mem ==>
          imm_section_dead_mods ce (mem_bytes_at 0 lo u.vs_memory) i)
    site (stmt_env site lctx NoneT (Return NONE))
    (stmt_env (gas_shadow_env T site) lctx NoneT (Return NONE))
    (eval_stmt cx (Return NONE)) es
Proof
  strip_tac >>
  `site.ce_return_pc = ce.ce_return_pc /\ site.ce_nonreentrant = ce.ce_nonreentrant` by
    fs[same_frame_def, compile_env_component_equality] >>
  `!sec i. imm_section_dead_mods site sec i = imm_section_dead_mods ce sec i` by
    (fs[same_frame_def, compile_env_component_equality, imm_section_dead_mods_def]) >>
  pure_rewrite_tac[stmt_frag_full_mods_def] >> rpt gen_tac >> strip_tac >>
  qpat_assum `stmt_env site lctx NoneT (Return NONE) sa = _`
    (assume_tac o MATCH_MP void_return_compile) >>
  qabbrev_tac `r = IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
                          (return_unlock_state site s0)` >>
  `?G' tn'.
    (!D. (?H. valid_horizon cx st0 H es.storage_trace) ==>
       gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s0,G0,tn0) [] (r,G',tn')) /\
    ((?H. valid_horizon cx st0 H es.storage_trace) ==>
       tn'.t_stor = tn0.t_stor /\ tn'.t_trans SUBSET tn0.t_trans /\
       tn'.t_imm = tn0.t_imm /\ tn'.t_mem = tn0.t_mem)` by
    (Cases_on `?H. valid_horizon cx st0 H es.storage_trace`
     >- (gvs[] >> rename1 `valid_horizon cx st0 H0 es.storage_trace` >>
         qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
         `allocas_from lo s0 /\ op_taint tn0 (Var rpc) = {}` by
           fs[ghost_inv_at_mods_def] >>
         drule_then (assume_tac o MATCH_MP state_rel_call_ctx_rel)
           stmt_state_rel_state_rel >>
         `s0.vs_call_ctx.cc_static = cx.txn.is_static` by fs[call_ctx_rel_def] >>
         `(FST site.ce_nonreentrant /\ ~SND (SND (SND site.ce_nonreentrant))) ==>
            ~s0.vs_call_ctx.cc_static` by fs[] >>
         drule_all_then (strip_assume_tac o
           Q.INST [`tn` |-> `tn0`, `G` |-> `G0`,
                   `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] o SPEC_ALL)
           compile_return_none_int_origin_ptr_taint >>
         qexistsl_tac [`G'`, `tn'`] >> fs[Abbr `r`]) >>
     simp[]) >>
  irule gas_outcome_full_mods_exit >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G'`, `es`, `r`, `INR (ReturnException NoneV)`, `tn'`] >>
  simp[Once evaluate_def, raise_def, Abbr `r`, exit_result_def, halt_exit_def] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
  conj_tac >- metis_tac[] >>
  simp[stmt_exit_ptr_def, return_unlock_state_frames] >> gen_tac >> disj2_tac >>
  conj_tac
  >- (drule_then assume_tac stmt_state_rel_state_rel >>
      irule void_return_result >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (irule void_return_immutable_frame >> goal_assum (drule_at Any) >> simp[]) >>
  rename1 `valid_horizon cx st0 H es.storage_trace` >>
  `tn'.t_stor = tn0.t_stor /\ tn'.t_trans SUBSET tn0.t_trans /\
   tn'.t_imm = tn0.t_imm /\ tn'.t_mem = tn0.t_mem` by
    (qpat_x_assum `(?H. valid_horizon _ _ H _) ==> _` irule >>
     qexists_tac `H` >> simp[]) >>
  qpat_x_assum `!H G tn tf s. _ ==> stor_taint_ok_at _ _ _ /\ _`
    (qspecl_then [`H`,`G0`,`tn0`,`tn'`,`s0`] mp_tac) >>
  simp[]
QED
