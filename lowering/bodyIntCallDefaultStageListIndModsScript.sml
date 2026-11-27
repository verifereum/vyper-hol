(* List induction for selected defaults, conditional on the two caller-pin
   head rules. No expression implementation is used here. *)
Theory bodyIntCallDefaultStageListIndMods
Ancestors
  bodyIntCallDefaultHeadSpecMods bodyFullShared
  gasOutcomeFullPostMods gasSummaryCompose gasShadowCompileCallSupport
  gasShadowCompile freshWrites gasStorage vyperStorageTrace vyperStorageFootprint
  exprLoweringProps exprSimFullBundleProps exprSimHypsDefs fragGasOriginPtr
  fragGasPath fragExec compileEnv list vyperInterpreter vyperState gasSummary
  bodyFullPredsMods bodyIntCallStagePacketMods exprLowering fragFuel
Libs
  monadsyntax

Theorem default_cons_source[local]:
  bind (eval_exprs p (e::es)) f =
  bind (bind (eval_expr p e) (read_result p))
    (\v. bind (eval_exprs p es) (\xs. f (v::xs)))
Proof
  simp[Once evaluate_def, bind_assoc, bind_return]
QED

Theorem default_cons_observation[local]:
  gas_path ctx func s (LENGTH left) (OK t) /\
  (!tail. bind (eval_expr p e) (read_result p)
    (esi with gas_obs := gas_explicit left s.vs_gas_readings ++ tail) =
    (INL v,mid with gas_obs := tail)) /\
  (!tail. eval_exprs p es
    (mid with gas_obs := gas_explicit right t.vs_gas_readings ++ tail) =
    (INL xs,ee with gas_obs := tail)) ==>
  !tail. eval_exprs p (e::es)
    (esi with gas_obs := gas_explicit (left ++ right) s.vs_gas_readings ++ tail) =
    (INL (v::xs),ee with gas_obs := tail)
Proof
  strip_tac >> gen_tac >>
  drule_then (qspec_then `right` SUBST1_TAC) gas_explicit_append_path >>
  qpat_assum `!tail. bind _ _ _ = _`
    (qspec_then `gas_explicit right t.vs_gas_readings ++ tail` assume_tac) >>
  qpat_assum `!tail. eval_exprs _ _ _ = _` (qspec_then `tail` assume_tac) >>
  `eval_exprs p (e::es) = bind (bind (eval_expr p e) (read_result p))
      (\v. bind (eval_exprs p es) (\xs. return (v::xs)))` by
    simp[Once evaluate_def, bind_assoc] >>
  pop_assum SUBST1_TAC >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[vyperStateTheory.bind_def,pairTheory.UNCURRY,return_def]
QED

Theorem default_tail_source[local]:
  body_exprs_full_ok_mods mods exps p (e::es) /\
  EVERY (\e. expr_body_pre_mods mods cd p ed e esi) es /\
  expr_sim_inv_mods mods cd p ed mid /\
  (!tail. eval_expr p e
     (esi with gas_obs := obs ++ tail) = (INL raw,mid with gas_obs := tail)) /\
  read_result p raw mid = (INL v,mid) ==>
  body_exprs_full_ok_mods mods exps p es /\
  EVERY (\e. expr_body_pre_mods mods cd p ed e mid) es
Proof
  strip_tac >> conj_tac
  >- (qpat_x_assum `body_exprs_full_ok_mods _ _ _ (_::_)` mp_tac >>
      simp[Once body_exprs_full_ok_mods_def] >> strip_tac >>
      first_x_assum irule >>
      qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
      rpt (goal_assum (drule_at Any))) >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum (drule_then mp_tac) >> simp[expr_body_pre_mods_def]
QED

(* Factor the compiler before execution, without changing the module pin. *)
Theorem default_stage_cons_factor[local]:
  compile_stage_intcall_args cfn ce (e::es) (flag::flags) (dty::dtys) =
  comp_bind (compile_stage_intcall_args cfn ce [e] [flag] [dty])
    (\hs. comp_bind (compile_stage_intcall_args cfn ce es flags dtys)
      (\ts. comp_return (hs ++ ts)))
Proof
  Cases_on `flag` >>
  simp[compile_stage_intcall_args_def,comp_bind_assoc,comp_ignore_bind_def,
       comp_bind_return,LET_THM]
QED

Theorem default_stage_cons_cut[local]:
  compile_stage_intcall_args compile_expr ce (e::es) (flag::flags) (dty::dtys) a = (ops,z) ==>
  ?opn b rest.
    compile_stage_intcall_args compile_expr ce [e] [flag] [dty] a = ([opn],b) /\
    compile_stage_intcall_args compile_expr ce es flags dtys b = (rest,z) /\
    ops = opn::rest
Proof
  Cases_on `compile_stage_intcall_args compile_expr ce [e] [flag] [dty] a` >>
  rename1 `compile_stage_intcall_args _ _ [_] [_] [_] a = (hs,b)` >>
  Cases_on `compile_stage_intcall_args compile_expr ce es flags dtys b` >>
  rename1 `compile_stage_intcall_args _ _ es flags dtys b = (rest,z0)` >>
  `LENGTH hs = 1` by
    (qpat_x_assum `compile_stage_intcall_args _ _ [_] [_] [_] a = _` mp_tac >>
     Cases_on `flag` >>
     simp[compile_stage_intcall_args_def,comp_bind_def,comp_ignore_bind_def,
          comp_return_def,LET_THM] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[]) >>
  Cases_on `hs` >> gvs[] >>
  once_rewrite_tac[default_stage_cons_factor] >>
  simp[comp_bind_def,comp_return_def] >> strip_tac >> gvs[]
QED

Theorem default_stage_edge[local]:
  compile_stage_intcall_args compile_expr ce es flags tys a = (ops,b) ==>
  ci_mono a b
Proof
  strip_tac >>
  `ci_mono a (SND (compile_stage_intcall_args compile_expr ce es flags tys a))` by
    (irule ci_mono_compile_stage_intcall_args >> simp[compile_expr_ci_mono]) >>
  pop_assum mp_tac >> simp[]
QED

Theorem default_stage_split_code[local]:
  compile_stage_intcall_args compile_expr ce [e] [flag] [dty] a = ([opn],b) /\
  compile_stage_intcall_args compile_expr ce es flags dtys b = (rest,z) /\
  fn_has_code a z func ==>
  ci_mono a b /\ fn_has_code a b func /\ fn_has_code b z func
Proof
  strip_tac >>
  qpat_assum `compile_stage_intcall_args _ _ [e] _ _ a = _`
    (mp_then Any assume_tac default_stage_edge) >>
  qpat_assum `compile_stage_intcall_args _ _ es _ _ b = _`
    (mp_then Any assume_tac default_stage_edge) >>
  qspecl_then [`a`,`b`,`z`,`func`] mp_tac fn_has_code_split >> fs[ci_mono_def]
QED

Theorem default_stage_paired_cut[local]:
  compile_stage_intcall_args compile_expr ce (e::es) (flag::flags) (dty::dtys) si = (ops,sf) /\
  compile_stage_intcall_args compile_expr (gas_shadow_env T ce) (MAP gas_shadow_expr (e::es))
    (flag::flags) (dty::dtys) shi = (ops,shf) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (si,sf,shi,shf) ==>
  ?opn cut shcut rest. ops = opn::rest /\ ci_mono si cut /\
    compile_stage_intcall_args compile_expr ce [e] [flag] [dty] si = ([opn],cut) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
      [gas_shadow_expr e] [flag] [dty] shi = ([opn],shcut) /\
    compile_stage_intcall_args compile_expr ce es flags dtys cut = (rest,sf) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
      (MAP gas_shadow_expr es) flags dtys shcut = (rest,shf) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (si,cut,shi,shcut) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (cut,sf,shcut,shf)
Proof
  simp[MAP] >> strip_tac >>
  qpat_assum `compile_stage_intcall_args _ ce (e::es) _ _ si = _`
    (mp_then Any (qx_choosel_then [`opn`,`cut`,`rest`] strip_assume_tac) default_stage_cons_cut) >>
  qpat_assum `compile_stage_intcall_args _ _ (gas_shadow_expr _ :: _) _ _ shi = _`
    (mp_then Any (qx_choosel_then [`shop`,`shcut`,`shrest`] strip_assume_tac) default_stage_cons_cut) >>
  gvs[] >> drule_then strip_assume_tac expr_sim_full_code_fields >>
  `gas_shadow_state cut shcut` by
    (`gas_shadow_compiles (compile_stage_intcall_args compile_expr ce [e] [flag] [dty])
       (compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
          (MAP gas_shadow_expr [e]) [flag] [dty])` by
       (irule (SIMP_RULE std_ss []
         (Q.INST [`sh` |-> `T`] gas_shadow_compiles_stage_intcall_args_env)) >>
        simp[gas_shadow_compile_expr_env]) >>
     fs[MAP] >> drule_all gas_shadow_step >> simp[]) >>
  qpat_assum `compile_stage_intcall_args _ ce [e] _ _ si = _`
    (mp_then Any (drule_all_then strip_assume_tac) default_stage_split_code) >>
  qpat_assum `compile_stage_intcall_args _ _ [gas_shadow_expr e] _ _ shi = _`
    (mp_then Any (drule_all_then strip_assume_tac) default_stage_split_code) >>
  simp[expr_sim_full_code_def]
QED

Theorem default_stage_ready_tail[local]:
  intcall_default_cut_ready_mods (DF,lo,d,ctx,func) ce p st0
    (sa,es0,s0,G0,tn0) (si,esi,s,G,tn) pin /\
  ci_mono si cut /\
  intcall_stage_frame_mods (DF,lo,d,ctx,func) ce p st0
    (sa,es0,s0,G0,tn0) (cut,mid,t,G1,tn1) pin /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u) ==>
  intcall_default_cut_ready_mods (DF,lo,d,ctx,func) ce p st0
    (sa,es0,s0,G0,tn0) (cut,mid,t,G1,tn1) pin
Proof
  simp[intcall_default_cut_ready_mods_def,ci_mono_def] >> strip_tac >> simp[] >>
  conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `si` >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `si` >> simp[] >>
      qpat_assum `!x sz. ce.ce_return_buf = _ ==> _` irule >> qexists_tac `sz` >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `si` >> simp[] >>
      qpat_assum `!x sz. ce.ce_return_pc = _ ==> _` irule >> qexists_tac `sz` >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Theorem default_tail_horizon[local]:
  eval_exprs p es (mid with gas_obs := obs) = (INL xs,ee) /\
  valid_horizon p st0 H ee.storage_trace ==>
  valid_horizon p st0 H mid.storage_trace
Proof
  strip_tac >>
  `valid_horizon p st0 H (mid with gas_obs := obs).storage_trace` by
    (irule (INST_TYPE [``:'a`` |-> ``:value list``] valid_horizon_frame) >>
     qexistsl_tac [`eval_exprs p es`,`INL xs`,`ee`] >>
     simp[evaluate_storage_trace_frame]) >> fs[]
QED

Theorem intcall_default_stage_list_from_heads_mods:
  intcall_default_head_rule_mods (:'a) T /\ intcall_default_head_rule_mods (:'a) F ==>
  !es DF lo d ctx shadow_ctx PG func shadow_func mods exps ce p ed src tops ds
    st0 sa es0 s0 G0 tn0 si sf shi shf esi s G tn flags dtys newops ops ws vals ptys pflags pin
    (f : value list -> evaluation_state -> ('a + vyperState$exception) # evaluation_state) P Q R.
    let cd = ce with ce_module := src in
    intcall_default_slice_mods mods ce p ed src tops ds /\
    (!e. MEM e es ==> MEM e ds) /\
    contract_inv mods exps ctx cd p /\ module_body_inv mods src tops cd p /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    expr_sim_inv_mods mods cd p ed esi /\ body_const_cells_agree_mods mods p ed esi /\
    EVERY (\e. expr_body_pre_mods mods cd p ed e esi) es /\
    body_exprs_full_ok_mods mods exps p es /\
    LENGTH flags = LENGTH es /\ LENGTH dtys = LENGTH es /\
    EVERY (\ty. type_memory_bytes ce ty < 2 ** 64) dtys /\
    LIST_REL (type_widens_to (get_tenv p)) (MAP expr_type es) dtys /\
    (!j. j < LENGTH es /\ EL j flags ==> is_word_type (EL j dtys)) /\
    (!e dty ee ci vv cm.
       expr_body_pre_mods mods cd p ed e ee /\
       compile_expr ce (expr_type e) e ci = (vv,cm) /\
       ~is_word_type dty /\ ~is_bytestring_type dty /\
       type_widens_to (get_tenv p) (expr_type e) dty ==>
       vv_type vv = lowered_value_type ce e) /\
    compile_stage_intcall_args compile_expr ce es flags dtys si = (newops,sf) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T ce) (MAP gas_shadow_expr es)
      flags dtys shi = (newops,shf) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (si,sf,shi,shf) /\
    intcall_default_cut_ready_mods (DF,lo,d,ctx,func) ce p st0
      (sa,es0,s0,G0,tn0) (si,esi,s,G,tn) pin /\
    intcall_stage_ops_mods (lo,func) ce p sa (si,esi,s,G,tn) pin (ops,ws,vals,ptys,pflags) /\
    (!xs. storage_trace_frame (f xs)) /\
    gas_admissible (bind (eval_exprs p es) f) P esi /\
    (!exc. P (INR exc) ==> expr_res_ok (INR exc)) /\
    (!H exc ee gt r. expr_exit (INR exc : value + vyperState$exception) r /\
      halt_exit H p ee (INR exc : value + vyperState$exception) r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u) ==>
      R H (INR exc) ee gt r) /\
    (!marks xs mid t Gf tf.
       (!tail. eval_exprs p es
          (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
          (INL xs,mid with gas_obs := tail)) /\
       (!H. valid_horizon p st0 H mid.storage_trace ==>
         gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
           (s,G,tn) marks (OK t,Gf,tf)) /\
       gas_path ctx func s (LENGTH marks) (OK t) /\
       storage_trace_domain p st0 mid.storage_trace /\ LENGTH xs = LENGTH es /\
       expr_sim_inv_mods mods cd p ed mid /\ body_const_cells_agree_mods mods p ed mid /\
       (?ws1. intcall_stage_ops_mods (lo,func) ce p sa (sf,mid,t,Gf,tf) pin
         (ops ++ newops,ws1,vals ++ xs,ptys ++ dtys,pflags ++ flags)) /\
       intcall_stage_frame_mods (DF,lo,d,ctx,func) ce p st0
         (sa,es0,s0,G0,tn0) (sf,mid,t,Gf,tf) pin /\
       gas_admissible (f xs) P mid ==>
       gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         ce.ce_modules p st0 (f xs) (mid,t,Gf,tf) Q R) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      ce.ce_modules p st0 (bind (eval_exprs p es) f) (esi,s,G,tn) Q R
Proof
  strip_tac >> Induct
  >- suspend "nil" >>
  suspend "cons"
QED

Resume intcall_default_stage_list_from_heads_mods[nil]:
  simp[LET_THM, compile_stage_intcall_args_def,comp_return_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `bind (eval_exprs p []) f = f []` by simp[Once evaluate_def,bind_return] >>
  gvs[] >>
  `~s.vs_halted` by fs[intcall_default_cut_ready_mods_def,intcall_stage_frame_mods_def] >>
  Cases_on `storage_trace_domain p st0 esi.storage_trace`
  >- (qpat_assum `!marks mid t Gf tf. _ ==> gas_outcome_full_mods _ _ _ _ (f []) _ Q R`
       (qspecl_then [`[]`,`esi`,`s`,`G`,`tn`] mp_tac) >>
      simp[Once evaluate_def,return_def,gas_explicit_def,cj 1 gas_path_rules,
           cj 1 gas_origin_ptr_path_rules] >>
      impl_tac >- (conj_tac >- (qexists_tac `ws` >> first_assum ACCEPT_TAC) >>
                   fs[intcall_default_cut_ready_mods_def]) >> simp[]) >>
  irule gas_outcome_full_mods_bad_nil >> simp[] >> gen_tac >>
  Cases_on `f [] (esi with gas_obs := tail)` >> simp[] >>
  irule storage_trace_frame_preserves_bad_domain >>
  qexistsl_tac [`f []`,`q`,`esi with gas_obs := tail`] >> simp[]
QED

Resume intcall_default_stage_list_from_heads_mods[cons]:
  simp[LET_THM] >> rpt gen_tac >> strip_tac >>
  rename1 `body_exprs_full_ok_mods mods exps p (e::es)` >>
  namedCases_on `flags` ["", "flag flags"] >- fs[] >>
  namedCases_on `dtys` ["", "dty dtys"] >- fs[] >>
  fs[] >>
  rename1 `compile_stage_intcall_args _ _ (e::es) (flag::ft) (dty::dt) si = _` >>
  `!j. j < LENGTH es /\ EL j ft ==> is_word_type (EL j dt)` by
    (rpt strip_tac >>
     qpat_assum `!j. j < SUC (LENGTH es) /\ EL j (_::_) ==> _`
       (qspec_then `SUC j` (mp_tac o SIMP_RULE (srw_ss()) [EL])) >>
     disch_then irule >> simp[]) >>
  `flag ==> is_word_type dty` by
    (qpat_assum `!j. j < SUC (LENGTH es) /\ EL j (_::_) ==> _`
       (qspec_then `0` (mp_tac o SIMP_RULE (srw_ss()) [EL])) >>
     disch_then ACCEPT_TAC) >>
  drule_all_then (qx_choosel_then [`opn`,`cut`,`shcut`,`rest`] strip_assume_tac)
    (REWRITE_RULE [MAP] default_stage_paired_cut) >>
  qpat_x_assum `gas_admissible _ P esi`
    (assume_tac o PURE_REWRITE_RULE [default_cons_source]) >>
  pure_rewrite_tac[default_cons_source] >>
  qabbrev_tac `next = \v. bind (eval_exprs p es) (\xs. f (v::xs))` >>
  `!v. storage_trace_frame (next v)` by
    (simp[Abbr `next`] >> gen_tac >> irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame]) >>
  `intcall_default_head_rule_mods (:'a) flag` by (Cases_on `flag` >> simp[]) >>
  qpat_assum `intcall_default_head_rule_mods _ flag`
    (irule o SIMP_RULE std_ss [intcall_default_head_rule_mods_def,LET_THM]) >>
  qpat_assum `expr_sim_full_code _ (si,cut,shi,shcut)` (irule_at Any) >>
  qpat_assum `intcall_default_cut_ready_mods _ _ _ _ _ (si,esi,s,G,tn) pin` (irule_at Any) >>
  qpat_assum `intcall_stage_ops_mods _ _ _ _ (si,esi,s,G,tn) pin _` (irule_at Any) >>
  qpat_assum `intcall_default_slice_mods mods ce p ed src tops ds` (irule_at Any) >>
  qpat_assum `compile_stage_intcall_args _ ce [e] [flag] [dty] si = ([opn],cut)`
    (irule_at Any) >>
  qpat_assum `gas_admissible _ P esi` (irule_at Any) >>
  simp[] >>
  suspend "head_and_tail"
QED

Resume intcall_default_stage_list_from_heads_mods[head_and_tail]:
  qexists_tac `exps` >> simp[] >> reverse conj_tac
  >- (rpt strip_tac >> qpat_assum `!e dty ee ci vv cm. _` irule >>
      qpat_assum `compile_expr ce _ e si = _` (irule_at Any) >>
      qpat_assum `type_widens_to _ (expr_type e) y` (irule_at Any) >>
      qexists_tac `esi` >> simp[]) >>
  qx_genl_tac [`left`,`w`,`v`,`mid`,`t`,`G1`,`tn1`] >> strip_tac >>
  qhdtm_x_assum `intcall_default_head_success_mods`
    (strip_assume_tac o REWRITE_RULE [intcall_default_head_success_mods_def]) >>
  drule_all_then strip_assume_tac default_tail_source >>
  drule_all_then assume_tac default_stage_ready_tail >>
  FULL_SIMP_TAC std_ss [Abbr `next`] >>
  qpat_assum `!DF' lo' d' ctx' shadow_ctx' PG' func' mods' exps' ce' p' ed' src' tops' ds'. _`
    irule >>
  qpat_assum `expr_sim_full_code _ (cut,sf,shcut,shf)` (irule_at Any) >>
  qpat_assum `intcall_default_cut_ready_mods _ _ _ _ _ (cut,mid,t,G1,tn1) pin` (irule_at Any) >>
  qpat_assum `intcall_stage_ops_mods _ _ _ _ (cut,mid,t,G1,tn1) pin _` (irule_at Any) >>
  qpat_assum `intcall_default_slice_mods mods ce p ed src tops ds` (irule_at Any) >>
  qpat_assum `compile_stage_intcall_args _ ce es ft dt cut = (rest,sf)` (irule_at Any) >>
  qpat_assum `body_exprs_full_ok_mods mods exps p es` (irule_at Any) >>
  qpat_assum `gas_admissible (bind (eval_exprs p es) _) P mid` (irule_at Any) >>
  simp[] >>
  suspend "tail_return"
QED

Resume intcall_default_stage_list_from_heads_mods[tail_return]:
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_genl_tac [`right`,`xs`,`ee`,`u`,`Gf`,`tf`] >> strip_tac >>
  qpat_assum `!marks xs mid t Gf tf. _ ==> gas_outcome_full_mods _ _ _ _ (f xs) _ Q R`
    (qspecl_then [`left ++ right`,`v::xs`,`ee`,`u`,`Gf`,`tf`] mp_tac) >>
  impl_tac >-
   (conj_tac >-
     (irule default_cons_observation >> qexistsl_tac [`ctx`,`func`,`mid`,`t`] >> simp[]) >>
    conj_tac >-
     (gen_tac >> strip_tac >>
      qpat_assum `!tail. eval_exprs p es _ = _`
        (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL])) >>
      `valid_horizon p st0 H (ee with gas_obs := []).storage_trace` by simp[] >>
      drule_all_then assume_tac default_tail_horizon >>
      irule gas_origin_ptr_path_append >>
      qexistsl_tac [`G1`,`t`,`(OK t,G1,tn1)`,`tn1`] >> simp[]) >>
    conj_tac >-
     (rw[LENGTH_APPEND] >> irule gas_path_then >> qexists_tac `t` >> simp[]) >>
    simp[] >> qexists_tac `ws1` >>
    qpat_assum `intcall_stage_ops_mods _ _ _ _ (sf,ee,u,Gf,tf) pin _`
      (ACCEPT_TAC o PURE_REWRITE_RULE [GSYM APPEND_ASSOC,APPEND])) >>
  simp[]
QED

Finalise intcall_default_stage_list_from_heads_mods
