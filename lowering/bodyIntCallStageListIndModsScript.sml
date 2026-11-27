Theory bodyIntCallStageListIndMods
Ancestors
  bodyIntCallBufferHeadSpecMods bodyIntCallBufferCutsMods
  bodyIntCallStackHeadMods bodyIntCallStageSnocMods bodyFullIfExpReach
  gasShadowCompileStmtHelpers gasSummaryCompose gasOutcomeFullPostMods
  exprSimFullBundleProps exprSimMemorySource exprSimHypsDefs exprLoweringProps
  bodyFullShared bodyFullPredsMods bodyForcedStorageFrameMods
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  fragGasPath freshWrites venomExecSemantics list gasSummary
  emitHelper gasShadowCompileCallSupport bodyIntCallStagePacketMods
  venomState exprLowering compileEnv fragExec gasShadow
Libs
  monadsyntax

Theorem staged_cons_source[local]:
  bind (eval_exprs cx (e::es)) f =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v. bind (eval_exprs cx es) (\vs. f (v::vs)))
Proof
  simp[Once evaluate_def, bind_assoc, bind_return]
QED

Theorem staged_bind_success[local]:
  a x = (INL v,y) /\ k v y = r ==> vyperState$bind a k x = r
Proof
  strip_tac >> simp[vyperStateTheory.bind_def, pairTheory.UNCURRY]
QED

Theorem staged_cons_observation[local]:
  gas_path ctx func s (LENGTH left) (OK t) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (esi with gas_obs := gas_explicit left s.vs_gas_readings ++ tail) =
    (INL v, mid with gas_obs := tail)) /\
  (!tail. eval_exprs cx es
    (mid with gas_obs := gas_explicit right t.vs_gas_readings ++ tail) =
    (INL vs, ee with gas_obs := tail)) ==>
  !tail. eval_exprs cx (e::es)
    (esi with gas_obs := gas_explicit (left ++ right) s.vs_gas_readings ++ tail) =
    (INL (v::vs), ee with gas_obs := tail)
Proof
  strip_tac >> gen_tac >>
  drule_then (qspec_then `right` SUBST1_TAC) gas_explicit_append_path >>
  qpat_assum `!tail. bind _ _ _ = _`
    (qspec_then `gas_explicit right t.vs_gas_readings ++ tail` assume_tac) >>
  qpat_assum `!tail. eval_exprs _ _ _ = _` (qspec_then `tail` assume_tac) >>
  `eval_exprs cx (e::es) = bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (eval_exprs cx es) (\vs. return (v::vs)))` by
    simp[Once evaluate_def, bind_assoc] >>
  pop_assum SUBST1_TAC >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  irule staged_bind_success >>
  qpat_assum `bind _ _ _ = (INL v,_)` (irule_at Any) >>
  BETA_TAC >> irule staged_bind_success >>
  qpat_assum `eval_exprs _ _ _ = (INL vs,_)` (irule_at Any) >>
  simp[return_def]
QED

Theorem staged_tail_source[local]:
  body_exprs_full_ok_mods mods exps cx (e::es) /\
  EVERY (\e. expr_body_pre_mods mods cenv cx env e esi) es /\
  expr_sim_inv_mods mods cenv cx env mid /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (esi with gas_obs := obs ++ tail) = (INL v,mid with gas_obs := tail)) ==>
  body_exprs_full_ok_mods mods exps cx es /\
  EVERY (\e. expr_body_pre_mods mods cenv cx env e mid) es
Proof
  strip_tac >> conj_tac
  >- (qpat_x_assum `body_exprs_full_ok_mods _ _ _ (_::_)` mp_tac >>
      simp[Once body_exprs_full_ok_mods_def] >> strip_tac >>
      first_x_assum irule >>
      qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
      simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum (drule_then mp_tac) >>
  simp[expr_body_pre_mods_def]
QED

Theorem staged_stack_snoc[local]:
  intcall_stage_ops_mods (lo,func) cenv cx sa (cu,mid,t,G1,tn1) pin
    (ops,ws,vals,ptys,pflags) /\
  eval_operand op t = SOME w /\ op_taint tn1 op = {} /\ op_prov G1 op = NONE /\
  (!x. op = Var x ==> not_fresh_at cu x) /\
  (!rt. evaluate_type (get_tenv cx) dty = SOME rt ==>
     value_has_type rt v /\ val_wf rt v /\ val_footprint rt v <= type_memory_size rt /\
     w = typed_val_to_w256 rt v) ==>
  intcall_stage_ops_mods (lo,func) cenv cx sa (cu,mid,t,G1,tn1) pin
    (ops ++ [op],ws ++ [w],vals ++ [v],ptys ++ [dty],pflags ++ [T])
Proof
  strip_tac >> irule intcall_stage_ops_snoc_mods >>
  simp[] >> simp[intcall_stage_ops_mods_def,eval_operands_def] >>
  rpt strip_tac >> `j = 0` by decide_tac >> gvs[]
QED

Theorem staged_stack_single_cut[local]:
  compile_stage_intcall_args compile_expr ce (e::es) (T::flags) (ty::tys) a = (ops,z) ==>
  ?op b rest. lower_value compile_expr ce (expr_type e) e a = (op,b) /\
    compile_stage_intcall_args compile_expr ce es flags tys b = (rest,z) /\
    ops = op::rest
Proof
  Cases_on `compile_expr ce (expr_type e) e a` >>
  rename1 `compile_expr _ _ _ _ = (vv,i)` >>
  Cases_on `unwrap_value ce vv i` >>
  rename1 `unwrap_value _ _ _ = (op,b)` >>
  Cases_on `compile_stage_intcall_args compile_expr ce es flags tys b` >>
  simp[Once compile_stage_intcall_args_def,comp_bind_def,comp_return_def,lower_value_def]
QED

Theorem staged_stack_cut_code[local]:
  lower_value compile_expr ce ty e a = (op,b) /\
  compile_stage_intcall_args compile_expr ce es flags tys b = (rest,z) /\
  fn_has_code a z f ==>
  ci_mono a b /\ fn_has_code a b f /\ fn_has_code b z f
Proof
  strip_tac >>
  `ci_mono a b` by
    (qspecl_then [`ce`,`ty`,`e`,`a`] mp_tac ci_mono_lower_value_compile_expr >> simp[]) >>
  `ci_mono b z` by
    (qspecl_then [`compile_expr`,`ce`,`es`,`flags`,`tys`,`b`] mp_tac
       ci_mono_compile_stage_intcall_args >> simp[compile_expr_ci_mono]) >>
  qspecl_then [`a`,`b`,`z`,`f`] mp_tac fn_has_code_split >> fs[ci_mono_def]
QED

Theorem staged_stack_cut[local]:
  compile_stage_intcall_args compile_expr ce (e::es) (T::flags) (ty::tys) a = (ops,z) /\
  compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
    (MAP gas_shadow_expr (e::es)) (T::flags) (ty::tys) sa = (sops,sz) /\
  gas_shadow_state a sa /\ fn_has_code a z f /\ fn_has_code sa sz sf ==>
  ?op b sb rest.
    lower_value compile_expr ce (expr_type e) e a = (op,b) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sa = (op,sb) /\
    compile_stage_intcall_args compile_expr ce es flags tys b = (rest,z) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
      (MAP gas_shadow_expr es) flags tys sb = (rest,sz) /\
    ops = op::rest /\ sops = op::rest /\ gas_shadow_state b sb /\ ci_mono a b /\
    fn_has_code a b f /\ fn_has_code b z f /\ fn_has_code sa sb sf /\ fn_has_code sb sz sf
Proof
  simp[MAP] >> strip_tac >>
  qpat_assum `compile_stage_intcall_args _ ce (e::es) _ _ a = _`
    (mp_then Any (qx_choosel_then [`op`,`b`,`rest`] strip_assume_tac) staged_stack_single_cut) >>
  qpat_assum `compile_stage_intcall_args _ _ (gas_shadow_expr _ :: _) _ _ _ = _`
    (mp_then Any (qx_choosel_then [`sop`,`sb`,`srest`] strip_assume_tac) staged_stack_single_cut) >>
  fs[gas_shadow_expr_type] >>
  `gas_shadow_compiles (lower_value compile_expr ce (expr_type e) e)
      (lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e))` by
    irule gas_shadow_stmt_lower_value_env >>
  drule_all_then strip_assume_tac gas_shadow_step >> gvs[] >>
  `gas_shadow_compiles (compile_stage_intcall_args compile_expr ce es flags tys)
     (compile_stage_intcall_args compile_expr (gas_shadow_env T ce) (MAP gas_shadow_expr es) flags tys)` by
    (irule (SIMP_RULE std_ss []
       (Q.INST [`sh` |-> `T`] gas_shadow_compiles_stage_intcall_args_env)) >>
     simp[gasShadowCompileTheory.gas_shadow_compile_expr_env]) >>
  qpat_assum `gas_shadow_compiles (compile_stage_intcall_args _ _ _ _ _) _`
    (mp_then Any (drule_all_then strip_assume_tac) gas_shadow_step) >> gvs[] >>
  qpat_assum `lower_value _ ce _ e a = _`
    (mp_then Any (drule_all_then strip_assume_tac) staged_stack_cut_code) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _`
    (mp_then Any (drule_all_then strip_assume_tac) staged_stack_cut_code) >>
  metis_tac[]
QED

val stage_list_statement = ``
  !es DF lo d ctx shadow_ctx PG func shadow_func mods exps src tops cenv cx env
   st0 sa s0 es0 G0 tn0 si sf shi shf esi s G tn
   flags dtys newops ops ws vals ptys pflags pin
   (f : value list -> evaluation_state -> ('a + vyperState$exception) # evaluation_state) P Q R.
    contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree_mods mods cx env esi /\ expr_sim_inv_mods mods cenv cx env esi /\
    EVERY (\e. expr_body_pre_mods mods cenv cx env e esi) es /\
    body_exprs_full_ok_mods mods exps cx es /\
    LENGTH flags = LENGTH es /\ LENGTH dtys = LENGTH es /\
    EVERY (\ty. type_memory_bytes cenv ty < 2 ** 64) dtys /\
    LIST_REL (type_widens_to (get_tenv cx)) (MAP expr_type es) dtys /\
    (!j. j < LENGTH es /\ EL j flags ==> is_word_type (EL j dtys)) /\
    (!e dty ee ci vv cm.
       expr_body_pre_mods mods cenv cx env e ee /\
       compile_expr cenv (expr_type e) e ci = (vv,cm) /\
       ~is_word_type dty /\ ~is_bytestring_type dty /\
       type_widens_to (get_tenv cx) (expr_type e) dty ==>
       vv_type vv = lowered_value_type cenv e) /\
    compile_stage_intcall_args compile_expr cenv es flags dtys si = (newops,sf) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr es)
      flags dtys shi = (newops,shf) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (si,sf,shi,shf) /\
    local_ptrs_reserved cenv si /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
    (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
    (!xs. storage_trace_frame (f xs)) /\
    gas_admissible (bind (eval_exprs cx es) f) P esi /\
    (!err. P (INR err) ==> expr_vv_res_ok (INR err)) /\
    (!H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s) ==>
       R H res ee gt r) /\
    intcall_stage_ops_mods (lo,func) cenv cx sa (si,esi,s,G,tn) pin
      (ops,ws,vals,ptys,pflags) /\
    intcall_stage_frame_mods (DF,lo,d,ctx,func) cenv cx st0
      (sa,es0,s0,G0,tn0) (si,esi,s,G,tn) pin /\
    (!marks xs mid t Gf tf.
       (!tail. eval_exprs cx es
          (esi with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
          (INL xs,mid with gas_obs := tail)) /\
       gas_path ctx func s (LENGTH marks) (OK t) /\
       storage_trace_domain cx st0 mid.storage_trace /\ LENGTH xs = LENGTH es /\
       expr_sim_inv_mods mods cenv cx env mid /\ body_const_cells_agree_mods mods cx env mid /\
       (?ws1. intcall_stage_ops_mods (lo,func) cenv cx sa (sf,mid,t,Gf,tf) pin
         (ops ++ newops,ws1,vals ++ xs,ptys ++ dtys,pflags ++ flags)) /\
       intcall_stage_frame_mods (DF,lo,d,ctx,func) cenv cx st0
         (sa,es0,s0,G0,tn0) (sf,mid,t,Gf,tf) pin /\
       gas_admissible (f xs) P mid ==>
       gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         cenv.ce_modules cx st0 (f xs) (mid,t,Gf,tf) Q R) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (bind (eval_exprs cx es) f) (esi,s,G,tn) Q R``;

Theorem intcall_stage_list_from_buffer_head_mods:
  intcall_buffer_head_rule_mods (:'a) ==> ^stage_list_statement
Proof
  disch_tac >> Induct
  >- suspend "nil" >>
  rpt gen_tac >> strip_tac >>
  rename1 `body_exprs_full_ok_mods mods exps cx (e::es)` >>
  namedCases_on `flags` ["", "flag flags"] >- fs[] >>
  namedCases_on `dtys` ["", "dty dtys"] >- fs[] >>
  fs[] >>
  rename1 `compile_stage_intcall_args _ _ (e::es) (flag::ft) (dty::dt) si = _` >>
  suspend "cons"
QED

Resume intcall_stage_list_from_buffer_head_mods[nil]:
  rpt gen_tac >> strip_tac >>
  `bind (eval_exprs cx []) f = f []` by simp[Once evaluate_def,bind_return] >>
  gvs[compile_stage_intcall_args_def,comp_return_def] >>
  `~s.vs_halted` by fs[intcall_stage_frame_mods_def] >>
  Cases_on `storage_trace_domain cx st0 esi.storage_trace`
  >- (qpat_x_assum `!marks mid t Gf tf. _`
       (qspecl_then [`[]`,`esi`,`s`,`G`,`tn`] mp_tac) >>
      simp[Once evaluate_def,return_def,gas_explicit_def,cj 1 gas_path_rules] >>
      impl_tac >- (qexists_tac `ws` >> first_assum ACCEPT_TAC) >>
      simp[]) >>
  irule gas_outcome_full_mods_bad_nil >> simp[] >> gen_tac >>
  Cases_on `f [] (esi with gas_obs := tail)` >> simp[] >>
  irule gasStorageTheory.storage_trace_frame_preserves_bad_domain >>
  qexistsl_tac [`f []`,`q`,`esi with gas_obs := tail`] >> simp[]
QED

Resume intcall_stage_list_from_buffer_head_mods[cons]:
  `body_expr_full_ok_mods mods exps cx e` by fs[Once body_exprs_full_ok_mods_def] >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (drule_then strip_assume_tac expr_sim_full_code_fields >>
     qpat_assum `contract_inv mods exps ctx cenv cx` mp_tac >>
     qpat_assum `MEM func ctx.ctx_functions` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[body_inv_no_phi_mods]) >>
  `!j. j < LENGTH es /\ EL j ft ==> is_word_type (EL j dt)` by
    (rpt strip_tac >>
     qpat_assum `!j. j < SUC (LENGTH es) /\ EL j (_::_) ==> _`
       (qspec_then `SUC j` (mp_tac o SIMP_RULE (srw_ss()) [EL])) >>
     disch_then irule >> simp[]) >>
  `flag ==> is_word_type dty` by
    (qpat_assum `!j. j < SUC (LENGTH es) /\ EL j (_::_) ==> _`
       (qspec_then `0` (mp_tac o SIMP_RULE (srw_ss()) [EL])) >>
     disch_then ACCEPT_TAC) >>
  qpat_x_assum `gas_admissible _ P esi`
    (assume_tac o PURE_REWRITE_RULE [staged_cons_source]) >>
  pure_rewrite_tac[staged_cons_source] >>
  qabbrev_tac `next = \v. bind (eval_exprs cx es) (\xs. f (v::xs))` >>
  `!exc. P (INR exc) ==> expr_res_ok (INR exc)` by
    (gen_tac >> qpat_assum `!err. P (INR err) ==> expr_vv_res_ok _`
       (qspec_then `exc` (mp_tac o SIMP_RULE (srw_ss()) [exprSimDefsTheory.expr_vv_res_ok_def])) >>
     simp[exprSimDefsTheory.expr_res_ok_def] >> metis_tac[]) >>
  `!v. storage_trace_frame (next v)` by
    (simp[Abbr `next`] >> gen_tac >> irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame]) >>
  drule_then strip_assume_tac expr_sim_full_code_fields >>
  `!H exc ee gt r.
      expr_exit (INR exc : value + vyperState$exception) r /\
      halt_exit H cx ee (INR exc : value + vyperState$exception) r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u) ==>
      R H (INR exc) ee gt r` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!H res ee gt r. expr_exit res r /\ _ ==> R H res ee gt r` irule >>
     simp[] >> rpt conj_tac >>
     TRY (irule (iffLR (INST_TYPE [``:'a`` |-> ``:value``]
            (SPEC_ALL stmtSimPropsTheory.expr_exit_INR_type))) >> first_assum ACCEPT_TAC >> NO_TAC) >>
     irule (iffLR (INST_TYPE [``:'a`` |-> ``:value``] haltExitProjTheory.halt_exit_INR_type)) >>
     first_assum ACCEPT_TAC) >>
  `!cut shcut hop rest.
     newops = hop::rest /\ ci_mono si cut /\
     compile_stage_intcall_args compile_expr cenv es ft dt cut = (rest,sf) /\
     compile_stage_intcall_args compile_expr (gas_shadow_env T cenv)
       (MAP gas_shadow_expr es) ft dt shcut = (rest,shf) /\
     expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (cut,sf,shcut,shf) ==>
     !left v mid t G1 tn1 w.
       (!tail. bind (eval_expr cx e) (read_result cx)
         (esi with gas_obs := gas_explicit left s.vs_gas_readings ++ tail) =
         (INL v,mid with gas_obs := tail)) /\
       gas_path ctx func s (LENGTH left) (OK t) /\
       intcall_stage_frame_mods (DF,lo,d,ctx,func) cenv cx st0
         (sa,es0,s0,G0,tn0) (cut,mid,t,G1,tn1) pin /\
       intcall_stage_ops_mods (lo,func) cenv cx sa (cut,mid,t,G1,tn1) pin
         (ops ++ [hop],ws ++ [w],vals ++ [v],ptys ++ [dty],pflags ++ [flag]) /\
       body_const_cells_agree_mods mods cx env mid /\ expr_sim_inv_mods mods cenv cx env mid /\
       gas_admissible (next v) P mid /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
       (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u) ==>
       gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         cenv.ce_modules cx st0 (next v) (mid,t,G1,tn1) Q R` by suspend "reached_tail" >>
  Cases_on `flag`
  >- (drule_all_then (qx_choosel_then [`hop`,`cut`,`shcut`,`rest`] strip_assume_tac)
        (REWRITE_RULE [MAP] staged_stack_cut) >>
      `expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (si,cut,shi,shcut)` by
        simp[expr_sim_full_code_def] >>
      irule intcall_stage_stack_head_mods >>
      qpat_assum `expr_sim_full_code _ (si,cut,shi,shcut)` (irule_at Any) >>
      qpat_assum `expr_body_pre_mods mods cenv cx env e esi` (irule_at Any) >>
      qpat_assum `module_body_inv mods src tops cenv cx` (irule_at Any) >>
      qpat_assum `intcall_stage_frame_mods _ _ _ _ _ (si,esi,s,G,tn) pin` (irule_at Any) >>
      qpat_assum `intcall_stage_ops_mods _ _ _ _ (si,esi,s,G,tn) _ _` (irule_at Any) >>
      qpat_assum `type_widens_to _ (expr_type e) dty` (irule_at Any) >>
      qpat_assum `gas_admissible _ P esi` (irule_at Any) >>
      qpat_assum `contract_inv mods exps ctx cenv cx` (irule_at Any) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (irule staged_stack_snoc >> NO_TAC) >>
      TRY (first_x_assum ACCEPT_TAC >> NO_TAC) >>
      `expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (cut,sf,shcut,shf)` by
        simp[expr_sim_full_code_def] >>
      suspend "stack_callback") >>
  drule_all_then (qx_choosel_then [`vv`,`ci`,`buf`,`ca`,`opn`,`cu`,`ux`,`cut`,
    `rest`,`shci`,`shca`,`shcu`,`shcut`] strip_assume_tac)
    (REWRITE_RULE [MAP] intcall_stage_buffer_cuts_mods) >>
  `ci_mono si cut` by
    (irule ci_mono_trans >> qexists_tac `cu` >> simp[] >>
     irule ci_mono_trans >> qexists_tac `ca` >> simp[] >>
     irule ci_mono_trans >> qexists_tac `ci` >> simp[]) >>
  `~is_word_type dty /\ ~is_bytestring_type dty ==> vv_type vv = lowered_value_type cenv e` by
    (strip_tac >> qpat_assum `!e dty ee ci vv cm. _` irule >>
     conj_tac >- (qexistsl_tac [`si`,`ci`] >> simp[]) >>
     conj_tac >- (qexists_tac `dty` >> simp[]) >>
     qexists_tac `esi` >> simp[]) >>
  `intcall_buffer_head_input_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    mods exps src tops cenv cx env st0 (sa,es0,s0,G0,tn0) (si,esi,s,G,tn)
    pin (ops,ws,vals,ptys,pflags) e dty (shi,vv,ci,shci,buf,ca,opn,cu,cut)` by
    (Cases_on `ux` >> fs[intcall_buffer_head_input_mods_def,expr_sim_full_code_def,LET_THM] >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `intcall_buffer_head_rule_mods _` (irule o REWRITE_RULE [intcall_buffer_head_rule_mods_def]) >>
  qhdtm_assum `intcall_buffer_head_input_mods` (irule_at Any) >>
  qpat_assum `gas_admissible _ P esi` (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  `expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (cut,sf,shcut,shf)` by
    simp[expr_sim_full_code_def] >>
  suspend "buffer_callback"
QED

Resume intcall_stage_list_from_buffer_head_mods[reached_tail]:
  qx_genl_tac [`cut`,`shcut`,`hop`,`rest`] >> strip_tac >>
  qx_genl_tac [`left`,`v`,`mid`,`t`,`G1`,`tn1`,`w`] >> strip_tac >>
  drule_all_then strip_assume_tac staged_tail_source >>
  `si.cs_next_var <= cut.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv cut` by (irule local_ptrs_reserved_next_var >> qexists_tac `si` >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cut x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `si` >> simp[] >>
     qpat_assum `!x sz. cenv.ce_return_buf = _ ==> not_fresh_at si x` irule >> qexists_tac `sz` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cut x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `si` >> simp[] >>
     qpat_assum `!x sz. cenv.ce_return_pc = _ ==> not_fresh_at si x` irule >> qexists_tac `sz` >> simp[]) >>
  FULL_SIMP_TAC std_ss [Abbr `next`] >>
  last_assum irule >>
  qpat_assum `intcall_stage_frame_mods _ _ _ _ _ (cut,mid,t,G1,tn1) pin` (irule_at Any) >>
  qpat_assum `intcall_stage_ops_mods _ _ _ _ (cut,mid,t,G1,tn1) _ _` (irule_at Any) >>
  qpat_assum `expr_sim_full_code _ (cut,sf,shcut,shf)` (irule_at Any) >>
  qpat_assum `compile_stage_intcall_args _ cenv es ft dt cut = (rest,sf)` (irule_at Any) >>
  qpat_assum `module_body_inv mods src tops cenv cx` (irule_at Any) >>
  qpat_assum `contract_inv mods exps ctx cenv cx` (irule_at Any) >>
  qpat_assum `expr_sim_inv_mods mods cenv cx env mid` (irule_at Any) >>
  qpat_assum `gas_admissible (bind (eval_exprs cx es) _) P mid` (irule_at Any) >>
  rpt conj_tac >> BETA_TAC >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> qpat_assum `!xs. storage_trace_frame (f xs)` MATCH_ACCEPT_TAC) >>
  qx_genl_tac [`right`,`xs`,`ee`,`u`,`Gf`,`tf`] >> strip_tac >>
  qpat_assum `!marks xs mid t Gf tf. _ ==> gas_outcome_full_mods _ _ _ _ (f xs) _ Q R`
    (qspecl_then [`left ++ right`,`v::xs`,`ee`,`u`,`Gf`,`tf`] mp_tac) >>
  impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
    >- (irule staged_cons_observation >> qexistsl_tac [`ctx`,`func`,`mid`,`t`] >> simp[])
    >- (rw[LENGTH_APPEND] >> irule gas_path_then >> qexists_tac `t` >> simp[])
    >- simp[] >>
    qexists_tac `ws1` >>
    qpat_assum `intcall_stage_ops_mods _ _ _ _ (sf,ee,u,Gf,tf) pin _`
      (ACCEPT_TAC o PURE_REWRITE_RULE [GSYM APPEND_ASSOC,APPEND])) >>
  simp[]
QED

Resume intcall_stage_list_from_buffer_head_mods[stack_callback]:
  `is_word_type dty` by fs[] >>
  qexists_tac `hop` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt gen_tac >> strip_tac >> irule staged_stack_snoc >> simp[]) >>
  qx_genl_tac [`left`,`v`,`mid`,`t`,`G1`,`tn1`,`w`] >> strip_tac >>
  qpat_assum `!cut shcut hop rest. _ ==> _`
    (qspecl_then [`cut`,`shcut`,`hop`,`rest`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qspecl_then [`left`,`v`,`mid`,`t`,`G1`,`tn1`,`w`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[]
QED

Resume intcall_stage_list_from_buffer_head_mods[buffer_callback]:
  qx_genl_tac [`left`,`addr`,`v`,`mid`,`t`,`G1`,`tn1`] >> strip_tac >>
  qhdtm_x_assum `intcall_buffer_head_success_mods`
    (strip_assume_tac o REWRITE_RULE [intcall_buffer_head_success_mods_def]) >>
  qpat_assum `!cut shcut hop rest. _ ==> _`
    (qspecl_then [`cut`,`shcut`,`buf.buf_operand`,`rest`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qspecl_then [`left`,`v`,`mid`,`t`,`G1`,`tn1`,`n2w addr`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[]
QED

Finalise intcall_stage_list_from_buffer_head_mods
