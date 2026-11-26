(* The selected buffered return: one forced read and one relayout/RET run. *)
Theory bodySelectedBufferReturnMods
Ancestors
  bodySelectedForcedReturnMods bodySelectedBufferReturnCutMods
  bodySelectedReturnWeakLayoutMods bodySelectedBufferReturnInputsMods
  bodySelectedBufferReturnRunMods bodySelectedBufferReturnFrameMods
  bodySelectedUnlockTaintMods
  gasOutcomeFullPostMods internalReturnMemoryExitFrame intCallReturnMem
  internalReturnMemoryFrame allocationGrowth loweringPosts
  exprSimHypsDefs stmtSimReturn bodyFullPostsMods bodyInvSplit
  immutableRegionTypingProps immutableLocationProps
  stateRelProj vyperStorageFootprint vyperState fragExec exprSimDefs bodyPtrDefs
  bodyFullShadowBodyInv bodyInvCodeProps exprBodyPreProps
  vyperTypeInvariants vyperTypeEvalSoundness vyperInterpreter
  compileEnv venomState valueEncoding loweringStateRelDefs
  vyperTypeEnvPreservation ptrDiscipline bodySim exprLoweringProps

(* Bounds apply to every qualified constructor location, not just the active module. *)
Theorem buffered_immutable_intervals[local]:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  env_consistent env cx mid /\
  dead_lo_ok_mods (H : (bool # bytes32 # type_value) list # num list) D lo cenv cx ==>
  !src name itv iv off.
    cenv.ce_is_ctor /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of NONE => FEMPTY
             | SOME imms => get_source_immutables src imms) name = SOME (itv,iv) ==>
    off + type_memory_size itv <= lo
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_then assume_tac contract_inv_cenv_modules >>
  qpat_assum `dead_lo_ok_mods _ _ _ _ _` (assume_tac o REWRITE_RULE [dead_lo_ok_mods_def]) >>
  drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
    contract_inv_immutable_section_layout >>
  `?bytes. immutable_region_mods mods src name off bytes` by metis_tac[] >>
  drule_all_then strip_assume_tac immutable_region_mods_type >>
  `evaluate_type (get_tenv cx) ty = SOME itv` by
    (qpat_assum `env_consistent env cx mid`
       (mp_tac o cj 3 o REWRITE_RULE [env_consistent_def]) >>
     simp[env_immutables_consistent_def] >>
     disch_then (mp_tac o Q.SPECL [`src`,`name`,`ty`,`itv`,`iv`] o cj 2) >>
     Cases_on `ALOOKUP mid.immutables cx.txn.target` >> gvs[]) >>
  qpat_assum `!src name off size. immutable_region_mods _ _ _ _ _ ==> _`
     (drule_then mp_tac) >> gvs[]
QED

Theorem buffered_return_exit_scope[local]:
  same_frame frame cenv /\ immutable_frame_mods func cenv cx mid u ==>
  immutable_frame_mods func frame cx (mid with <|scopes := []; gas_obs := tail|>) u
Proof
  strip_tac >>
  `frame.ce_modules = cenv.ce_modules /\ frame.ce_is_ctor = cenv.ce_is_ctor /\
   frame.ce_module_vars = cenv.ce_module_vars /\
   frame.ce_module_var_type = cenv.ce_module_var_type` by
     fs[same_frame_def, compile_env_component_equality] >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def] >>
  conj_tac >- (fs[immutables_rel_def] >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_x_assum `!src tops. _ ==> immutable_alloca_sep _ _ _ _ _`
    (qspecl_then [`src`,`tops`] (drule_then mp_tac)) >>
  simp_tac (srw_ss())
    [immutable_alloca_sep_def, immutable_decl_sep_def, local_region_def, lookup_scopes_def] >>
  strip_tac >> rpt conj_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  metis_tac[]
QED

Theorem selected_buffer_return_frag_mods:
  contract_inv mods exps ctx cenv cx /\
  same_frame frame cenv /\
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_returns_count = 0 /\
  ((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
    ~cx.txn.is_static /\ FST (SND (SND cenv.ce_nonreentrant))) /\
  lo <= w2n bw /\ ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  0 < type_memory_size tv /\ type_memory_size tv + 64 < dimword (:256) /\
  expr_sim_inv_mods mods cenv cx env es /\
  stmt_exprs_ok cenv (Return (SOME e)) /\
  IS_SOME (type_stmt env ty (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  expr_sim_full_mods
    (DF,lo,SOME (bw,type_memory_size tv),ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty e es ==>
  stmt_frag_full_mods
    (DF,lo,SOME (bw,type_memory_size tv),ctx,shadow_ctx,PG,func,shadow_func) cx lctx
    (\H v ee gt r. intret_q H func frame cx tv v ee r /\
      !ir u. r = IntRet ir u ==>
        (!mem. mem_agree_outside (SND gt).t_mem u.vs_memory mem ==>
          val_in_memory tv v (w2n bw) mem) /\
        immutable_frame_mods func frame cx (ee with scopes := []) u /\
        stor_taint_ok_at (DF H) (SND gt) u /\
        !i. i < lo /\ i IN (SND gt).t_mem ==>
          imm_section_dead_mods frame (mem_bytes_at 0 lo u.vs_memory) i)
    cenv (stmt_env cenv lctx ty (Return (SOME e)))
    (stmt_env (gas_shadow_env T cenv) lctx ty (Return (SOME (gas_shadow_expr e))))
    (eval_stmt cx (Return (SOME e))) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule (SIMP_RULE bool_ss [LET_THM] selected_forced_return_frag_with_entry_mods) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexists `\sa sb sha shb op sm shm. ?bp cap su sc.
    cenv.ce_return_buf = SOME (PtrVar (Var bp) cap) /\
    compile_return_unlock cenv sm = ((),su) /\
    compile_store_memory cenv op (Var bp) ty (lowered_value_type cenv e) su = ((),sc) /\
    emit_inst RET [Var rpc] [] sc = ((),sb) /\
    fn_has_code sm su func /\ fn_has_code su sc func /\ fn_has_code sc sb func` >>
  conj_tac
  >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
      qpat_assum `return_buf_frame _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [return_buf_frame_def]) >>
      drule_all_then strip_assume_tac selected_buffer_return_paired_cut_mods >>
      qexistsl [`op`,`sm`,`shm`] >> simp[] >>
      qexistsl [`bp`,`cap`,`su`,`sc`] >> asm_rewrite_tac[]) >>
  suspend "reached"
QED

Resume selected_buffer_return_frag_mods[reached]:
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    (`mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[listTheory.APPEND_NIL] >>
     qpat_assum `mid with gas_obs := [] = mid` (pure_rewrite_tac o single) >> simp[]) >>
  drule_all_then (qx_choose_then `stv` (qx_choose_then `ptv`
    (map_every assume_tac o CONJUNCTS))) selected_return_weak_layout_mods >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H0 mid.storage_trace` by fs[Abbr `H0`, storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  `allocas_from (w2n bw + type_memory_size tv) t` by metis_tac[pairTheory.PAIR_EQ] >>
  `((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
      ~cx.txn.is_static)` by metis_tac[] >>
  drule_all_then strip_assume_tac selected_buffer_return_inputs_mods >>
  `bp' = bp` by
    metis_tac[optionTheory.SOME_11, venomStateTheory.operand_11, compileEnvTheory.var_location_11] >>
  qpat_x_assum `bp' = bp` SUBST_ALL_TAC >>
  qpat_x_assum `op = Var src` SUBST_ALL_TAC >>
  drule_all (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`]
    selected_buffer_return_run_mods) >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`] strip_assume_tac) >>
  rename1 `r = IntRet _ _` >>
  irule gas_outcome_full_mods_exit >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gf`,`mid`,`r`,`INR (ReturnException v)`,`tf`] >>
  simp[raise_def, exit_result_def, halt_exit_def, stmt_exit_ptr_def, expr_exit_def] >>
  gen_tac >> disch_tac >>
  qabbrev_tac `fin = copied with
    <|vs_prev_bb := prev; vs_current_bb := sc.cs_current_bb;
      vs_inst_idx := LENGTH sc.cs_current_insts|>` >>
  `stmt_state_rel H ctx func cenv cx mid t /\
   ghost_inv_at_mods (DF H) lo (SOME (bw,type_memory_size tv)) cenv cx mid G tn t` by
    (qpat_assum `!K. valid_horizon _ _ K mid.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     fs[expr_post_mods_def, expr_post_def]) >>
  `env_consistent env cx mid` by
    (drule_then assume_tac expr_sim_inv_mods_env >>
     qpat_assum `bind _ _ _ = (INL v,mid)` mp_tac >>
     simp_tac (srw_ss()) [bind_def, AllCaseEqs()] >> strip_tac >>
     drule_then SUBST1_TAC read_result_state >>
     irule eval_expr_preserves_ec >> metis_tac[gas_obs_type_invariants]) >>
  qpat_assum `!K. dead_lo_ok_mods K _ _ _ _` (qspec_then `H` assume_tac) >>
  drule (REWRITE_RULE [GSYM AND_IMP_INTRO] buffered_immutable_intervals) >>
  disch_then drule >> disch_then drule >>
  disch_tac >>
  reverse conj_tac
  >- (disch_tac >>
      `allocas_below_fmp copied = allocas_below_fmp (return_unlock_state cenv t)` by
        (qpat_assum `copied with <|vs_vars := _; vs_memory := _|> = _`
          (mp_tac o AP_TERM ``allocas_below_fmp``) >>
         simp_tac (srw_ss()) [allocas_below_fmp_def]) >>
      `allocas_below_fmp fin = allocas_below_fmp copied` by
        simp_tac (srw_ss()) [Abbr `fin`, allocas_below_fmp_def] >>
      metis_tac[allocas_below_fmp_return_unlock_state]) >>
  qpat_assum `copied with <|vs_vars := _; vs_memory := _|> = _`
    (mp_tac o AP_TERM ``\s:venom_state. (s.vs_allocas,s.vs_alloca_next,s.vs_data_section,
                                         s.vs_accounts,s.vs_transient,s.vs_immutables,s.vs_call_ctx)``) >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  `frame.ce_nonreentrant = cenv.ce_nonreentrant /\
   frame.ce_modules = cenv.ce_modules /\ frame.ce_is_ctor = cenv.ce_is_ctor /\
   frame.ce_module_vars = cenv.ce_module_vars` by
    fs[same_frame_def, compile_env_component_equality] >>
  gen_tac >> conj_tac >- suspend "result" >>
  conj_tac >- suspend "physical" >>
  suspend "taint"
QED

Resume selected_buffer_return_frag_mods[result]:
  `!x. cenv.ce_imm_alloca = SOME (Var x) ==> lookup_var x copied = lookup_var x t` by
    (rpt strip_tac >> drule compile_return_unlock_shape >> strip_tac >>
     drule (cj 2 exprLoweringPropsTheory.compile_expr_grows) >> strip_tac >>
     first_x_assum irule >> fs[local_ptrs_reserved_def, not_fresh_at_def]) >>
  `cenv.ce_is_ctor ==> !name itv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP mid.immutables cx.txn.target of NONE => FEMPTY
              | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n bw) (type_memory_size tv)` by
    (rpt strip_tac >>
     `off + type_memory_size itv <= lo` by
       (qpat_assum `!lo H D src name itv iv off. _ ==> _` (irule o SPEC_ALL) >>
        simp[] >> conj_tac
        >- (qexistsl [`iv`,`name`,`cenv.ce_module`] >> asm_rewrite_tac[]) >>
        qexistsl [`DF H`,`H`] >> first_assum ACCEPT_TAC) >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `!tail. intret_mem_q H func frame cx tv bw v ((mid with gas_obs := tail) with scopes := [])
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> (copied with vs_inst_idx := LENGTH su.cs_current_insts))` by
    (irule (SRULE [] internal_return_memory_copy_exit_base) >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl [`cenv`,`ctx`,`sm.cs_next_id`,`t`] >>
     asm_rewrite_tac[] >> conj_tac
     >- (rpt gen_tac >> disch_tac >>
         qpat_assum `!a len. _ ==> mem_bytes_at _ _ copied.vs_memory = _` irule >> decide_tac) >>
     qpat_assum `copied with <|vs_vars := _; vs_memory := _|> = _` mp_tac >>
     simp_tac (srw_ss()) [venom_state_component_equality]) >>
  simp_tac (srw_ss()) [Abbr `fin`] >>
  qpat_assum `!tail. intret_mem_q _ _ _ _ _ _ _ _ _`
    (qspec_then `tail`
      (mp_tac o Q.INST [`bb` |-> `sc.cs_current_bb`,
                        `idx` |-> `LENGTH sc.cs_current_insts`] o
       MATCH_MP intret_mem_q_set_control)) >>
  simp_tac (srw_ss()) [intret_mem_q_def]
QED

Resume selected_buffer_return_frag_mods[physical]:
  `copied.vs_allocas = t.vs_allocas /\ copied.vs_alloca_next = t.vs_alloca_next /\
   copied.vs_data_section = t.vs_data_section` by
    (map_every (fn pat => qpat_x_assum pat mp_tac)
       [`copied.vs_allocas = _`,`copied.vs_alloca_next = _`,`copied.vs_data_section = _`] >>
     qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
     Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
     asm_simp_tac (srw_ss()) [return_unlock_state_def, tstore_def, sstore_def,
                              markerTheory.Abbrev_def, pairTheory.pair_case_thm, LET_THM]) >>
  simp_tac (srw_ss()) [Abbr `fin`] >>
  irule selected_buffer_return_frame_mods >>
  qexists `t` >>
  simp[allocation_growth_def, local_region_def, lookup_scopes_def] >>
  conj_tac
  >- (rpt strip_tac >>
      rename1 `ALOOKUP cenv.ce_modules qual = SOME tops` >>
      `off + type_memory_size tv' <= lo` by
        (qpat_assum `!lo H D src name itv iv off. _ ==> _` (irule o SPEC_ALL) >>
         simp[] >> conj_tac
         >- (qexistsl [`v'`,`name`,`qual`] >> asm_rewrite_tac[]) >>
         qexistsl [`DF H`,`H`] >> first_assum ACCEPT_TAC) >>
      qpat_assum `!a len. _ ==> mem_bytes_at _ _ copied.vs_memory = _` irule >>
      disj1_tac >> decide_tac) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `FLOOKUP t.vs_allocas _ = NONE` mp_tac >>
      qpat_assum `FLOOKUP t.vs_allocas _ = SOME _` (simp_tac (srw_ss()) o single)) >>
  irule buffered_return_exit_scope >> qexists `cenv` >> asm_rewrite_tac[]
QED

Resume selected_buffer_return_frag_mods[taint]:
  `((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
     FST (SND (SND cenv.ce_nonreentrant)))` by metis_tac[] >>
  `tf.t_stor = tn.t_stor /\ tf.t_trans SUBSET tn.t_trans /\ tf.t_imm = tn.t_imm` by metis_tac[] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`tf` |-> `tf with t_mem := tn.t_mem`] selected_unlock_exit_taint_mods)) >>
  disch_then strip_assume_tac >>
  simp_tac (srw_ss()) [Abbr `fin`] >>
  conj_tac
  >- (qpat_x_assum `stor_taint_ok_at _ _ _` mp_tac >> simp[stor_taint_ok_at_def]) >>
  rpt strip_tac >>
  `i < w2n bw` by decide_tac >>
  `i IN tn.t_mem` by metis_tac[] >>
  fs[imm_section_dead_mods_def]
QED

Finalise selected_buffer_return_frag_mods
