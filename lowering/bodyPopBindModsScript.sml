(* A Pop binds the reached write place to the suffix at that same cursor. *)
Theory bodyPopBindMods
Ancestors
  bodyWriteTargetStageMods bodyFullPostsMods exprSimPopNestedBase gasOutcomeFullBindMods
  gasOutcomeFullPostMods gasShadowCompileStmtHelpers gasShadowState
  stmtLoweringMono exprLoweringProps stmtSimProps haltExitProj
  fragExec gasExemptCertMods vyperStorageTrace vyperStorageFootprint
  bodyFullShared gasShadow context vyperInterpreter vyperState exprSimDefs
Libs monadsyntax

Theorem pop_eval_bind[local]:
  eval_expr cx (Pop ann bt) = bind (eval_target_place cx bt) (pop_place cx)
Proof
  simp[FUN_EQ_THM,Once evaluate_def,bind_def]
QED

Theorem pop_compile_cut[local]:
  compile_expr cenv ty (Pop ann bt) sa = (vv,sb) /\
  compile_get_target_ptr compile_expr cenv bt sa = (r,sm) ==>
  let loc = (case FST (SND r) of SOME l => l | NONE => LocMemory) in
  let et = (case SND (SND r) of SOME (ValPT (ArrayT t _)) => t
                               | _ => BaseT (IntT 256)) in
  ?elem.
    compile_dynarray_pop (FST r) (word_scale loc) (elem_size_in_location cenv loc et)
      cenv.ce_is_ctor cenv.ce_imm_alloca loc sm = (elem,sb) /\
    vv = LocatedValue ann (mk_ptr elem loc) /\ ci_mono sm sb
Proof
  PairCases_on `r` >> strip_tac >> simp[] >>
  qpat_x_assum `compile_expr cenv ty (Pop ann bt) sa = _` mp_tac >>
  simp[Once nested_pop_compile_eq] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  metis_tac[ci_mono_compile_dynarray_pop,pairTheory.SND]
QED

Theorem pop_paired_target_cut[local]:
  compile_expr cenv ty (Pop ann bt) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (Pop ann bt)) shadow_sa =
    (vv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?r sm shadow_sm.
    compile_get_target_ptr compile_expr cenv bt sa = (r,sm) /\
    compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
      (gas_shadow_target bt) shadow_sa = (r,shadow_sm) /\
    gas_shadow_state sm shadow_sm /\ ci_mono sa sm /\ ci_mono sm sb /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    fn_has_code shadow_sa shadow_sm shadow_func
Proof
  strip_tac >>
  Cases_on `compile_get_target_ptr compile_expr cenv bt sa` >>
  qmatch_asmsub_rename_tac `compile_get_target_ptr compile_expr cenv bt sa = (dst,sm)` >>
  Cases_on `compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
    (gas_shadow_target bt) shadow_sa` >>
  qmatch_asmsub_rename_tac `compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
    (gas_shadow_target bt) shadow_sa = (shadow_dst,shadow_sm)` >>
  `shadow_dst = dst /\ gas_shadow_state sm shadow_sm` by
    (irule gas_shadow_step >> rpt (first_assum (irule_at Any)) >>
     simp[gas_shadow_stmt_get_target_ptr_env]) >>
  qpat_x_assum `shadow_dst = dst` SUBST_ALL_TAC >>
  `ci_mono sa sm` by
    (qspecl_then [`bt`,`cenv`,`sa`] mp_tac ci_mono_compile_get_target_ptr >> simp[]) >>
  `ci_mono shadow_sa shadow_sm` by
    (qspecl_then [`gas_shadow_target bt`,`gas_shadow_env T cenv`,`shadow_sa`]
      mp_tac ci_mono_compile_get_target_ptr >> simp[]) >>
  `ci_mono sm sb` by
    (drule_all pop_compile_cut >> simp[LET_THM] >> strip_tac >> simp[]) >>
  `ci_mono shadow_sm shadow_sb` by
    (qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
       (assume_tac o REWRITE_RULE [gas_shadow_expr_def]) >>
     drule_all pop_compile_cut >> simp[LET_THM] >> strip_tac >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func /\ fn_has_code shadow_sm shadow_sb shadow_func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  qexistsl_tac [`dst`,`sm`,`shadow_sm`] >> simp[]
QED

Theorem pop_target_exit[local]:
  expr_exit (res : place + exception) r /\ halt_exit H cx ee res r ==>
  ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r /\
    halt_exit H cx ee (INR exc : eval_result + exception) r
Proof
  Cases_on `res` >> simp[expr_exit_def] >>
  simp[GSYM expr_exit_def,expr_exit_INR_type,halt_exit_INR_type]
QED

(* The continuation is called with the target's actual gas prefix, live
   place, and physical resources, all at one endpoint. *)
Theorem pop_place_bind[local]:
  write_place_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env bt es /\
  type_place_target env bt = SOME (Type aty) /\
  write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt es st0 sa sm shadow_sa shadow_sm dst s0 G0 tn0 /\
  gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
  (!marks p ee G tn t.
     (!tail. eval_target_place cx bt
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INL p,ee with gas_obs := tail)) /\
     storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
     (!id path. p = MemoryPlace id path ==>
        ?entry v. lookup_scopes id ee.scopes = SOME entry /\
                  evaluate_subscripts entry.type entry.value path = INL v) /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==>
        write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sm s0
          ee (PlaceR p) (Type aty) dst G0 tn0 G tn t) ==>
     gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cenv.ce_modules cx st0 (pop_place cx p) (ee,t,G,tn) Q
       (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
         (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_target_place cx bt) (pop_place cx)) (es,s0,G0,tn0) Q
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >>
  qpat_x_assum `write_place_sim_mods _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [write_place_sim_mods_def]) >>
  disch_then (qspecl_then [`st0`,`aty`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`dst`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ ChildQ ChildR` >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_place >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_place >> simp[])
  >~ [`storage_trace_frame (eval_target_place _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`!p. storage_trace_frame (pop_place _ p)`]
  >- simp[storage_trace_frame_pop_place] >>
  qexists `\H res ee G tn t. ChildQ H res ee G tn t /\ ee.gas_obs = []` >>
  conj_tac >- suspend "reached" >>
  irule gas_outcome_full_mods_post_source >> first_assum (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `ChildR`,Excl "AND_IMP_INTRO"] >>
  rpt gen_tac >> strip_tac >> irule pop_target_exit >> simp[]
QED

Resume pop_place_bind[reached]:
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `ChildQ (storage_trace_horizon ee.storage_trace) res ee G tn t /\ ee.gas_obs = []` by
    (first_x_assum drule >> simp[]) >>
  qpat_x_assum `ChildQ (storage_trace_horizon _) _ _ _ _ _` mp_tac >>
  simp[Abbr `ChildQ`,NoAsms] >>
  disch_then (qx_choose_then `p` (CONJUNCTS_THEN2 SUBST_ALL_TAC strip_assume_tac)) >>
  disj1_tac >> qexists `p` >> simp[] >>
  first_x_assum irule >> conj_tac
  >- (qexists `marks` >> first_assum ACCEPT_TAC) >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then (strip_assume_tac o BETA_RULE)) >> gvs[]
QED

Finalise pop_place_bind[local]

Theorem pop_vv_from_place_suffix_mods:
  type_place_target env bt = SOME (Type (ArrayT ann (Dynamic cap))) /\
  write_place_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env bt es /\
  (!st0 sa sm sb shadow_sa shadow_sm dst vv s0 G0 tn0 marks p ee G tn t.
     compile_expr cenv ty (Pop ann bt) sa = (vv,sb) /\
     ci_mono sa sm /\ ci_mono sm sb /\ fn_has_code sm sb func /\
     gas_admissible (eval_expr cx (Pop ann bt)) expr_vv_res_ok es /\
     write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
       cenv cx bt es st0 sa sm shadow_sa shadow_sm dst s0 G0 tn0 /\
     (!tail. eval_target_place cx bt
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INL p,ee with gas_obs := tail)) /\
     storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
     (!id path. p = MemoryPlace id path ==>
        ?entry v. lookup_scopes id ee.scopes = SOME entry /\
                  evaluate_subscripts entry.type entry.value path = INL v) /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==>
        write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sm s0
          ee (PlaceR p) (Type (ArrayT ann (Dynamic cap))) dst G0 tn0 G tn t) ==>
     gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cenv.ce_modules cx st0 (pop_place cx p) (ee,t,G,tn)
       (\H res ef G' tn' u. ?tv. res = INL tv /\
         vv_post_mods H ctx func cenv cx (Pop ann bt) es sa sb s0 ef tv vv u /\
         vv_store_bound cx (post_value_type cenv (Pop ann bt))
           (lowered_value_type cenv (Pop ann bt)) ef tv vv u /\
         u.vs_current_bb = sb.cs_current_bb /\
         u.vs_inst_idx = LENGTH sb.cs_current_insts /\
         alloca_history func u /\
         (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
         s0.vs_alloca_next <= u.vs_alloca_next /\
         ghost_inv_at_mods (DF H) lo d cenv cx ef G' tn' u /\
         ptr_vv_ok cx (post_value_type cenv (Pop ann bt)) tv vv ef G' tn' u /\
         (!v. tv = Value v /\ ~is_word_type (post_value_type cenv (Pop ann bt)) /\
              ~is_bytestring_type (post_value_type cenv (Pop ann bt)) ==>
              vv_own cenv cx (post_value_type cenv (Pop ann bt)) sa sb ef tv vv u /\
              (!t' ptr. vv = LocatedValue t' ptr ==> ptr.ptr_location = LocMemory)) /\
         (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
          ?v. read_result cx tv ef = (INL v,ef) /\
              !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (Pop ann bt)) = SOME rt /\
                     eval_operand (vv_operand vv) u = SOME w ==>
                     w2n w + type_memory_size rt <= lo /\
                     (!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==>
                            val_in_memory rt v (w2n w) mem)) /\
         (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv (Pop ann bt)) ==>
                   ptr_buf_ok cenv (Pop ann bt) op G' u) /\
         (!t' ptr. vv = LocatedValue t' ptr /\ ptr.ptr_location = LocMemory ==>
                   ptr_buf_ok cenv (Pop ann bt) ptr.ptr_operand G' u) /\
         ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')
       (\H res ef gt r. expr_exit res r /\ halt_exit H cx ef res r /\
         (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))) ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Pop ann bt) es
Proof
  strip_tac >> pure_rewrite_tac[expr_vv_sim_full_mods_def] >> rpt gen_tac >> strip_tac >>
  drule_all pop_paired_target_cut >>
  disch_then (qx_choosel_then [`dst`,`sm`,`shadow_sm`] strip_assume_tac) >>
  `write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx bt es st0 sa sm shadow_sa shadow_sm dst s0 G0 tn0` by
    (simp[write_target_entry_mods_def] >> conj_tac
     >- first_assum ACCEPT_TAC >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    (drule_then ACCEPT_TAC nested_pop_target_admissible) >>
  pure_rewrite_tac[pop_eval_bind] >> irule pop_place_bind >>
  rpt (first_assum (irule_at Any)) >>
  qx_genl_tac [`marks`,`p`,`ee`,`G`,`tn`,`t`] >> strip_tac >>
  qpat_assum `!st0 sa sm sb shadow_sa shadow_sm dst vv s0 G0 tn0 marks p ee G tn t. _`
    irule >> rpt (first_assum (irule_at Any)) >> qexists `marks` >> simp[]
QED
