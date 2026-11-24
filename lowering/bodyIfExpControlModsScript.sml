(* The condition and the selected arm share one counted path. *)
Theory bodyIfExpControlMods
Ancestors
  bodyIfExpTailMods bodyIfExpSuffixMods bodyIfExpConditionalMods
  bodyFullIfExpShadow bodyFullIfExpReach bodyAugGuardedPrefixMods
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  gasShadowCompileStmtHelpers gasShadowCompileHelpers gasShadowCompileConvert exprLoweringProps
  freshWrites
  bodyMemoryDefs contextRawReachable fragGasEmitCtrl
  vyperStorageTrace vyperStorageFootprint vyperEvalExprPreservesScopesDom
  vyperValue valueEncoding stmtSimProps bodyFullPostsMods bodyFullShadowBodyInv
  bodyInvSplit bodySimFull bodyPtrDefs fragExec fragGasOriginPtrExec fragGasOriginPtr
  loweringStateRelDefs exprSimDefs exprSimMemDefs exprSimIfExp
  context compileEnv exprLowering loweringPosts stmtSimDefs
  vyperAST vyperState vyperInterpreter venomState ptrDiscipline
  gasOutcomeFullMods gasContext gasSummary gasStorage gasShadow gasShadowState
  words list finite_map arithmetic allocaHistory emitHelper venomInst
Libs monadsyntax

Theorem ifexp_conditional_trace[local]:
  storage_trace_frame (bind (eval_expr cx e) (conditional_result cx))
Proof
  irule storage_trace_frame_bind_all >>
  simp[evaluate_storage_trace_frame, storage_trace_frame_conditional_result]
QED

Theorem ifexp_condition_trace[local]:
  storage_trace_frame (bind (eval_expr cx c) (read_result cx))
Proof
  irule storage_trace_frame_bind_all >>
  simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]
QED

Theorem ifexp_allocas_jump_mods[local]:
  allocas_below_fmp (jump_to lbl z) <=> allocas_below_fmp z
Proof
  simp[allocas_below_fmp_def,jump_to_def]
QED

Theorem ifexp_jump_frame_mods[local]:
  immutable_frame_mods func cenv cx ee (jump_to lbl s) <=>
  immutable_frame_mods func cenv cx ee s
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def,
       immutable_alloca_sep_mods_def, immutables_rel_def, immutable_alloca_sep_def,
       jump_to_def, local_region_def, lookup_var_def]
QED

Theorem ifexp_jump_ghost_mods[local]:
  ghost_inv_at_mods D lo d cenv cx ee G tn (jump_to lbl s) <=>
  ghost_inv_at_mods D lo d cenv cx ee G tn s
Proof
  simp[ghost_inv_at_mods_def, jump_to_def, ptr_covers_def, stor_taint_ok_at_def,
       lookup_var_def, allocas_from_def] >>
  Cases_on `d` >- simp[return_buf_ptr_def] >>
  PairCases_on `x` >> simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

Theorem ifexp_jnz_mods[local]:
  expr_post_mods (H : (bool # 256 word # type_value) list # num list)
    ctx func cenv cx c es sa sc s0 mid (BoolV sel) cop u /\
  expr_type c = BaseT BoolT /\
  emit_inst JNZ [cop; Label tl; Label el] [] sj = ((),sn) /\
  fn_has_code sj sn func /\ sj.cs_current_bb = sc.cs_current_bb /\
  sj.cs_current_insts = sc.cs_current_insts /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
  u.vs_inst_idx = LENGTH sc.cs_current_insts /\
  ghost_inv_at_mods D lo d cenv cx mid G tn u /\
  ptr_val_ok cx (post_value_type cenv c) (BoolV sel) cop G tn u /\
  post_value_type cenv c = BaseT BoolT ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (u,G,tn) [] (OK (jump_to (if sel then tl else el) u),G,tn)
Proof
  strip_tac >> irule emit_jnz_origin_ptr >> simp[] >>
  conj_tac >- fs[ghost_inv_at_mods_def] >>
  qexistsl [`cop`,`sj`,`sn`] >> simp[] >>
  fs[expr_post_mods_def, expr_post_def, expr_val_rel_def,
     ghost_inv_at_mods_def, ptr_val_ok_def, evaluate_type_def, is_word_type_def,
     typed_val_to_w256_def, val_to_w256_def]
QED

Theorem ifexp_condition_post_path[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q R ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn)
    (\H res ee G' tn' t. Q H res ee G' tn' t /\ ~t.vs_halted /\ ee.gas_obs = [] /\
       ?cm. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
         (s,G,tn) cm (OK t,G',tn')) R
Proof
  rw[Once gas_outcome_full_mods_def] >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> qexistsl [`res`,`ee`,`r`,`G'`,`tn'`] >>
      simp[] >> rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
      disj1_tac >> simp[] >> conj_tac
      >- (drule gas_origin_ptr_path_exec >> simp[exit_result_def] >> strip_tac) >>
      qexists `marks` >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

(* The suffix helper needs the fact that the conditional result is not
   an immutable place. Recover it from the same all-tail source run. *)
Theorem ifexp_arm_result_not_immutable[local]:
  bind (eval_expr cx e) (conditional_result cx) st = (INL tv,ee) ==>
  !src id ps. tv <> PlaceR (ImmutablePlace src id ps)
Proof
  simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
  drule ifexp_conditional_result_place >> simp[] >> strip_tac >> gvs[]
QED

val arm_exit = ``\(H : (bool # 256 word # type_value) list # num list) (res : eval_result + exception) ee (gt : (string |-> (num # num)) # taint) r. expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;

val arm_post = ``\(H : (bool # 256 word # type_value) list # num list) (res : eval_result + exception) ee G tn u. ?tv v. res = INL tv /\
  read_result cx tv ee = (INL v,ee) /\
  MAP FDOM mid.scopes = MAP FDOM ee.scopes /\
  expr_post_mods H ctx func cenv cx (IfExp t c a b) mid se sx (jump_to lbl z) ee v aop u /\
  (~is_word_type t ==>
    vv_at cenv cx t se sx ee tv (LocatedValue t (mk_ptr aop LocMemory)) u) /\
  (~is_word_type t ==>
    vv_place_ptr cenv cx ee u tv (LocatedValue t (mk_ptr aop LocMemory))) /\
  (!v. tv = Value v /\ ~is_word_type t /\ ~is_bytestring_type t ==>
    vv_own cenv cx t se sx ee tv (LocatedValue t (mk_ptr aop LocMemory)) u) /\
  expr_store_bound cx t v aop u /\
  u.vs_current_bb = sx.cs_current_bb /\
  u.vs_inst_idx = LENGTH sx.cs_current_insts /\ ~u.vs_halted /\
  alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (jump_to lbl z).vs_alloca_next <= u.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn u /\
  ptr_val_ok cx t v aop G tn u /\
  (~is_word_type t ==>
    !e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' aop G u) /\
  (~is_word_type t ==>
    !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
      eval_operand aop u = SOME w ==>
      type_memory_size rt = 0 \/ type_memory_size rt + w2n w <= u.vs_alloca_next) /\
  ghost_kept_at lo cenv mid se G1 tn1 (jump_to lbl z) G tn``;

val result_post = ``\(H : (bool # 256 word # type_value) list # num list) (res : eval_result + exception) ee G tn u. ?tv. res = INL tv /\
  vv_post_mods H ctx func cenv cx (IfExp t c a b) es sa sb s0 ee tv vv u /\
  vv_store_bound cx (post_value_type cenv (IfExp t c a b))
    (lowered_value_type cenv (IfExp t c a b)) ee tv vv u /\
  u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn u /\
  ptr_vv_ok cx (post_value_type cenv (IfExp t c a b)) tv vv ee G tn u /\
  (!v. tv = Value v /\ ~is_word_type (post_value_type cenv (IfExp t c a b)) /\
       ~is_bytestring_type (post_value_type cenv (IfExp t c a b)) ==>
       vv_own cenv cx (post_value_type cenv (IfExp t c a b)) sa sb ee tv vv u /\
       (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (IfExp t c a b)) = SOME rt /\
             eval_operand (vv_operand vv) u = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
               val_in_memory rt v (w2n w) mem)) /\
  (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv (IfExp t c a b)) ==>
    ptr_buf_ok cenv (IfExp t c a b) op G u) /\
  (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv (IfExp t c a b) p.ptr_operand G u) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

Theorem ifexp_attach_finish_mods[local]:
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx e) (conditional_result cx))
    (mid,jump_to lbl z,G1,tn1) (^arm_post) (^arm_exit) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    expr_post_mods H ctx func cenv cx c es sa sc s0 mid cv cop z) /\
  s0.vs_alloca_next <= z.vs_alloca_next /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> x <> rv) /\
  sa.cs_next_var <= sc.cs_next_var /\ sc.cs_next_var <= se.cs_next_var /\
  sa.cs_next_id <= sc.cs_next_id /\ sc.cs_next_id <= se.cs_next_id /\
  sx.cs_next_id <= sb.cs_next_id /\ sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
  emit_inst ASSIGN [aop] [rv] sx = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sx sy func /\ fn_has_code sy sz func /\
  vv = (if is_word_type t then StackValue t (Var rv)
        else LocatedValue t (mk_ptr (Var rv) LocMemory)) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx e) (conditional_result cx))
    (mid,jump_to lbl z,G1,tn1) (^result_post) (^arm_exit)
Proof
  strip_tac >> irule ifexp_outcome_zero_suffix_framed_mods >>
  conj_tac >- simp[ifexp_conditional_trace] >>
  qexists `\H res ee G tn u. (^arm_post) H res ee G tn u /\
    !tv src id ps. res = INL tv ==> tv <> PlaceR (ImmutablePlace src id ps)` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
      BETA_TAC >> simp[] >> rpt strip_tac
      >- (qexistsl [`tv`,`v`] >> simp[]) >>
      qpat_x_assum `res = INL (PlaceR (ImmutablePlace _ _ _))` SUBST_ALL_TAC >>
      `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
      qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
      pure_rewrite_tac[APPEND_NIL] >>
      qpat_x_assum `ee with gas_obs := [] = ee` (fn th => pure_rewrite_tac[th]) >>
      disch_then (mp_tac o MATCH_MP ifexp_arm_result_not_immutable) >> simp[]) >>
  qx_genl_tac [`res`,`ee`,`Gu`,`tnu`,`u`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL tv` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    expr_post_mods H ctx func cenv cx c es sa sc s0 mid cv cop z /\
    expr_post_mods H ctx func cenv cx (IfExp t c a b) mid se sx (jump_to lbl z) ee v aop u /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee Gu tnu u` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> (?tv' v'. _) /\ _`
       (drule_then strip_assume_tac) >> gvs[]) >>
  `!src id ps. tv <> PlaceR (ImmutablePlace src id ps)` by simp[] >>
  `~is_word_type t ==> ptr_buf_ok cenv (IfExp t c a b) aop Gu u` by
    (strip_tac >> first_x_assum irule >> simp[lowered_value_type_def, expr_type_def]) >>
  `z.vs_alloca_next <= u.vs_alloca_next` by fs[jump_to_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (mp_then Any mp_tac (Q.INST [`e` |-> `IfExp t c a b`, `explicit` |->
      `gas_explicit_sites ctx shadow_ctx`] ifexp_arm_finish_mods)) >>
  disch_then (qspecl_then [`xl`,`tv`,`tn1`,`tn0`,`sz`,`sy`,`shadow_ctx`,
    `sb`,`rv`,`PG`,`G1`,`G0`] mp_tac) >>
  `~not_fresh_at sa rv` by (qpat_assum `!x. not_fresh_at sa x ==> x <> rv` (qspec_then `rv` mp_tac) >> simp[NoAsms]) >>
  (impl_tac >- simp[expr_type_def, post_value_type_def, ADD_COMM]) >>
  strip_tac >> qexistsl [`z'`,`Gz`,`tf`] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (u,Gu,tnu) _ _ /\ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [LET_THM])) >>
  Cases_on `is_word_type t` >> fs[post_value_type_def, expr_type_def, vv_location_def, mk_ptr_def]
QED

(* The conversion supplier is called with the arm's actual compiled interval
   and with the full entry resources at the JNZ landing. *)
val reached_arm = ``!gs sel mid st0 se shadow_se av sea shadow_sea aop sx lbl z G1 tn1.
  let e = if sel then a else b in
  bind (eval_expr cx c) (read_result cx) (es with gas_obs := gs) = (INL (BoolV sel),mid) /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e mid /\
  expr_type e = t /\
  (!gs raw ee. eval_expr cx e (mid with gas_obs := gs) = (INL raw,ee) ==>
    eval_result_typed (env,cx,ee) raw (Type (expr_type e))) /\
  (!gs v ee. bind (eval_expr cx e) (read_result cx) (mid with gas_obs := gs) =
    (INL v,ee) ==> value_has_type rty v /\
    !ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
      value_has_type ptv v) /\
  compile_expr cenv ty e se = (av,sea) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_se = (av,shadow_sea) /\
  compile_ifexp_arm cenv t (lowered_value_type cenv e) av sea = (aop,sx) /\
  gas_shadow_state se shadow_se /\ gas_shadow_state sea shadow_sea /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code se sea func /\ fn_has_code shadow_se shadow_sea shadow_func /\
  fn_has_code sea sx func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv se /\
  se.cs_next_var <= sea.cs_next_var /\ se.cs_next_id <= sea.cs_next_id /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp (jump_to lbl z)) /\
  (!fn inst s. frag_reachable ctx func (jump_to lbl z) fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  gas_admissible (bind (eval_expr cx e) (conditional_result cx)) expr_vv_res_ok mid /\
  return_buf_frame d cenv se (jump_to lbl z) /\ alloca_history func (jump_to lbl z) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid (jump_to lbl z) /\
    immutable_frame_mods func cenv cx mid (jump_to lbl z) /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 (jump_to lbl z)) /\
  ~z.vs_halted /\ se.cs_current_bb = lbl /\ se.cs_current_insts = [] ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx e) (conditional_result cx))
    (mid,jump_to lbl z,G1,tn1) (^arm_post) (^arm_exit)``;

Theorem ifexp_vv_from_stages_mods:
  expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
  evaluate_type (get_tenv cx) t = SOME rty /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (BaseT BoolT) c es /\
  (!gs v mid. bind (eval_expr cx c) (read_result cx) (es with gas_obs := gs) = (INL v,mid) ==>
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty a mid /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty b mid /\
    (!e gs' raw ee. (e = a \/ e = b) /\
      eval_expr cx e (mid with gas_obs := gs') = (INL raw,ee) ==>
      eval_result_typed (env,cx,ee) raw (Type (expr_type e))) /\
    !e gs' v' ee. (e = a \/ e = b) /\
      bind (eval_expr cx e) (read_result cx) (mid with gas_obs := gs') = (INL v',ee) ==>
      value_has_type rty v' /\
      !ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
        value_has_type ptv v') /\
  (^reached_arm) ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty (IfExp t c a b) es
Proof
  strip_tac >> rewrite_tac[expr_vv_sim_full_mods_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!ty' e. gas_shadow_compiles (compile_expr cenv ty' e)
      (compile_expr (gas_shadow_env T cenv) ty' (gas_shadow_expr e))` by
    (rpt gen_tac >> irule gas_shadow_stmt_compile_expr_env) >>
  `!ty' e. gas_shadow_compiles (lower_value compile_expr cenv ty' e)
      (lower_value compile_expr (gas_shadow_env T cenv) ty' (gas_shadow_expr e))` by
    (rpt gen_tac >> irule gas_shadow_stmt_lower_value_env) >>
  `!rt at av. gas_shadow_compiles (compile_ifexp_arm cenv rt at av)
      (compile_ifexp_arm (gas_shadow_env T cenv) rt at av)` by
    simp[gas_shadow_compiles_ifexp_arm] >>
  drule_all ifexp_shadow_code_layout >> disch_then assume_tac >>
  `?cop sc shadow_sc.
    lower_value compile_expr cenv (BaseT BoolT) c sa = (cop,sc) /\
    lower_value compile_expr (gas_shadow_env T cenv) (BaseT BoolT)
      (gas_shadow_expr c) shadow_sa = (cop,shadow_sc) /\
    gas_shadow_state sc shadow_sc /\ fn_has_code sa sc func /\
    fn_has_code shadow_sa shadow_sc shadow_func` by
    (qpat_assum `!sel. ?cop. _` (qspec_then `T` strip_assume_tac) >>
     qexistsl [`cop`,`sc`,`shadow_sc`] >> simp[]) >>
  drule_then assume_tac ifexp_root_condition_admissible >>
  qpat_x_assum `expr_sim_full_mods _ _ _ _ c _`
    (qspecl_then [`st0`,`sa`,`sc`,`shadow_sa`,`shadow_sc`,`cop`,`s0`,`G0`,`tn0`] mp_tac o
     REWRITE_RULE [expr_sim_full_mods_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (mp_tac o MATCH_MP ifexp_condition_post_path) >> strip_tac >>
  rewrite_tac[ifexp_root_eval_forced] >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ condQ condR` >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ finalQ finalR` >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[ifexp_condition_trace]
  >- (gen_tac >> rpt IF_CASES_TAC >> simp[ifexp_conditional_trace,storage_trace_frame_raise]) >>
  qexists `condQ` >> reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ condQ condR` (irule_at Any) >>
      simp[Abbr `condR`,Abbr `finalR`] >> rpt strip_tac >>
      Cases_on `res` >- fs[expr_exit_def] >>
      simp[halt_exit_def] >>
      ONCE_REWRITE_TAC[INST_TYPE [beta |-> ``:value``] expr_exit_INR_type] >>
      fs[halt_exit_def]) >>
  suspend "branch"
QED

Resume ifexp_vv_from_stages_mods[branch]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`z`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> condQ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `condQ`] >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  `bind (eval_expr cx c) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    (`mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac [APPEND_NIL] >> simp[]) >>
  drule_all_then (qx_choose_then `sel` SUBST_ALL_TAC) ifexp_root_condition_bool >>
  qpat_assum `!gs v mid. bind _ _ _ = (INL v,mid) ==> _` (drule_then strip_assume_tac) >>
  drule_all_then assume_tac ifexp_root_branch_admissible >>
  qpat_x_assum `!sel. ?sj. _` (qspec_then `sel` strip_assume_tac) >>
  disj1_tac >> qexists `BoolV sel` >> simp[] >>
  `cop' = cop /\ sc' = sc` by
    (qpat_x_assum `lower_value compile_expr cenv _ c sa = (cop',sc')` mp_tac >> simp[]) >>
  qpat_x_assum `cop' = cop` SUBST_ALL_TAC >>
  qpat_x_assum `sc' = sc` SUBST_ALL_TAC >>
  qabbrev_tac `lbl = if sel then tl else el` >>
  `post_value_type cenv c = BaseT BoolT` by simp[is_word_type_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (z,G1,tn1) [] (OK (jump_to lbl z),G1,tn1)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> (?v. _) /\ _`
       (drule_then (strip_assume_tac o SIMP_RULE bool_ss [sumTheory.INL_11])) >>
     simp[Abbr `lbl`] >> irule ifexp_jnz_mods >>
     conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `expr_post_mods H _ _ _ _ c _ _ _ _ _ _ _ z` (irule_at Any) >>
     qpat_assum `emit_inst JNZ _ _ _ = _` (irule_at Any) >> simp[] >> qexists `d` >> simp[]) >>
  `gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cenv.ce_modules cx st0 (bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
     (mid,z,G1,tn1) finalQ finalR` suffices_by (Cases_on `sel` >> simp[]) >>
  irule augassign_zero_prefix_guarded_mods >>
  simp[ifexp_conditional_trace] >>
  qexistsl [`G1`,`jump_to lbl z`,`tn1`] >> simp[] >>
  suspend "landing"
QED

Resume ifexp_vv_from_stages_mods[landing]:
  `gas_origin_ptr_path
     (DF (storage_trace_horizon mid.storage_trace),lo,
      gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (z,G1,tn1) [] (OK (jump_to lbl z),G1,tn1)` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _`
       (drule_then assume_tac) >> first_assum ACCEPT_TAC) >>
  `!i. active_inst func i (jump_to lbl z) ==>
       frag_reachable ctx func s0 func i (jump_to lbl z)` by
    (rpt strip_tac >> irule ifexp_selected_entry_reachable >>
     qpat_assum `compile_expr cenv ty (if sel then a else b) se = (av,sea)` (irule_at Any) >>
     qpat_assum `compile_ifexp_arm cenv t _ av sea = (aop,sx)` (irule_at Any) >>
     qpat_assum `emit_inst ASSIGN [aop] [rv] sx = ((),sy)` (irule_at Any) >>
     qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) cm (OK z,G1,tn1)` (irule_at Any) >> simp[]) >>
  `!fn inst s. frag_reachable ctx func (jump_to lbl z) fn inst s ==>
       dalloca_fmp_headroom inst s` by
    (rpt strip_tac >>
     qpat_assum `!fn inst s. frag_reachable ctx func s0 fn inst s ==> _` irule >>
     qpat_assum `frag_reachable ctx func (jump_to lbl z) _ _ _`
       (irule_at Any o MATCH_MP frag_reachable_trans) >> simp[]) >>
  `sa.cs_next_var <= se.cs_next_var` by decide_tac >>
  `return_buf_frame d cenv se (jump_to lbl z)` by
    (simp[return_buf_frame_jump_to] >> irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >> simp[] >>
     qpat_assum `expr_post_mods _ _ _ _ _ c _ _ _ _ _ _ _ z` mp_tac >>
     simp[NoAsms,expr_post_mods_def,expr_post_def] >> strip_tac) >>
  `alloca_history func (jump_to lbl z)` by
    (irule alloca_history_jump >> simp[jump_to_def] >> qexists `z` >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid (jump_to lbl z) /\
    immutable_frame_mods func cenv cx mid (jump_to lbl z) /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 (jump_to lbl z)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> (?v. _) /\ _`
       (drule_then (strip_assume_tac o SIMP_RULE bool_ss [sumTheory.INL_11])) >>
     qpat_assum `expr_post_mods H _ _ _ _ c _ _ _ _ _ _ _ z` mp_tac >>
     simp[NoAsms,expr_post_mods_def,expr_post_def] >> strip_tac >>
     simp[stmt_state_rel_jump_to, ifexp_jump_frame_mods, ifexp_jump_ghost_mods]) >>
  qpat_assum `!gs sel mid st0 se shadow_se av sea shadow_sea aop sx lbl z G1 tn1. _`
    (qspecl_then [`gas_explicit marks s0.vs_gas_readings`,
      `sel`,`mid`,`st0`,`se`,`shadow_se`,`av`,`sea`,`shadow_sea`,
      `aop`,`sx`,`lbl`,`z`,`G1`,`tn1`] (mp_tac o CONV_RULE (DEPTH_CONV BETA_CONV) o REWRITE_RULE [LET_THM])) >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     SUBGOAL_THEN ``(if sel then a:expr else b) = a \/ (if sel then a else b) = b`` ASSUME_TAC
     >- (Cases_on `sel` >> simp[]) >>
     `(mid with gas_obs := []) = mid` by simp[evaluation_state_component_equality] >>
     `!x. not_fresh_at sa x ==> not_fresh_at se x` by
       (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
     conj_tac >- (Cases_on `sel` >> simp[]) >>
     conj_tac >- (Cases_on `sel` >> simp[]) >>
     conj_tac >-
       (qpat_assum `!e gs' raw ee. _ ==> eval_result_typed _ _ _`
          (qspec_then `if sel then a else b` mp_tac) >> simp[]) >>
     conj_tac >-
       (qpat_assum `!e gs' v' ee. _ ==> value_has_type _ _ /\ _`
          (qspec_then `if sel then a else b` mp_tac) >> simp[]) >>
     simp[ifexp_allocas_jump_mods] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >-
       (qpat_assum `gas_admissible _ _ (mid with gas_obs := [])` mp_tac >>
        qpat_assum `(mid with gas_obs := []) = mid` (fn th => pure_rewrite_tac [th]) >> simp[]) >>
     gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC)) >>
  strip_tac >> suspend "finish"
QED

Resume ifexp_vv_from_stages_mods[finish]:
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    expr_post_mods H ctx func cenv cx c es sa sc s0 mid (BoolV sel) cop z` by
    (gen_tac >> strip_tac >>
     `valid_horizon cx st0 H (es with gas_obs := gas_explicit marks s0.vs_gas_readings).storage_trace` by
       (irule (INST_TYPE [``:'a`` |-> ``:value``] valid_horizon_frame) >>
        qexistsl [`bind (eval_expr cx c) (read_result cx)`,`INL (BoolV sel)`,`mid`] >>
        simp[ifexp_condition_trace]) >>
     `valid_horizon cx st0 H es.storage_trace` by fs[] >>
     qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> (?v. _) /\ _`
       (drule_then (strip_assume_tac o SIMP_RULE bool_ss [sumTheory.INL_11])) >>
     simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `expr_post_mods _ _ _ _ _ c _ _ _ _ _ _ _ z` mp_tac >>
     simp[NoAsms,expr_post_mods_def,expr_post_def,locals_kept_def] >> strip_tac >> simp[]) >>
  qpat_assum `Abbrev (finalQ = _)` (fn th => pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
  qpat_assum `Abbrev (finalR = _)` (fn th => pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
  irule ifexp_attach_finish_mods >> simp[] >>
  qexistsl [`aop`,`cop`,`BoolV sel`,`rv`,`sc`,`se`,`sx`,`sy`,`sz`] >>
  simp[Abbr `finalR`] >>
  conj_tac >-
    (qpat_assum `!x. not_fresh_at _ x ==> x <> _` (qspec_then `rv` mp_tac) >>
     pure_rewrite_tac[REFL_CLAUSE,NOT_CLAUSES,IMP_CLAUSES]) >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (bind (eval_expr cx (if sel then a else b)) _) _ _ _`
    mp_tac >> simp[]
  >> (gvs[])
QED

Finalise ifexp_vv_from_stages_mods
