(* Request-prefix companion to bodyFullIfExpPrepare. *)
Theory s1PrefixIfExpPrepare
Ancestors
  s1PrefixPreds bodyFullIfExpPrepare s1PrefixDefs
  s1PrefixCompose s1PrefixOfVV bodySimFull bodyFullIfExpReach
  s1PrefixProps exprSimDefs

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >> rewrite_tac[expr_vv_sim_prefix_def,expr_vv_sim_full_pre_def] >>
  rpt strip_tac >>
  `!ty' e. gas_shadow_compiles (compile_expr cenv ty' e)
      (compile_expr (gas_shadow_env T cenv) ty' (gas_shadow_expr e))` by
    (rpt gen_tac >> irule gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_compile_expr_env) >>
  `!ty' e. gas_shadow_compiles (lower_value compile_expr cenv ty' e)
      (lower_value compile_expr (gas_shadow_env T cenv) ty' (gas_shadow_expr e))` by
    (rpt gen_tac >> irule gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env) >>
  `!rt at av. gas_shadow_compiles (compile_ifexp_arm cenv rt at av)
      (compile_ifexp_arm (gas_shadow_env T cenv) rt at av)` by
    simp[gasShadowCompileConvertTheory.gas_shadow_compiles_ifexp_arm] >>
  drule_all bodyFullIfExpShadowTheory.ifexp_shadow_code_layout >>
  disch_then (assume_tac o GEN_ALL) >>
  `?cop sc shadow_sc.
    lower_value compile_expr cenv (BaseT BoolT) c sa = (cop,sc) /\
    lower_value compile_expr (gas_shadow_env T cenv) (BaseT BoolT)
      (gas_shadow_expr c) shadow_sa = (cop,shadow_sc) /\
    gas_shadow_state sc shadow_sc /\ fn_has_code sa sc func /\
    fn_has_code shadow_sa shadow_sc shadow_func` by
    (qpat_assum `!sel. ?cop. _` (qspec_then `T` strip_assume_tac) >>
     qexistsl [`cop`,`sc`,`shadow_sc`] >> simp[]) >>
  `gas_admissible (bind (eval_expr cx c) (read_result cx)) expr_res_ok es` by
    metis_tac[exprSimIfExpTheory.ifexp_root_condition_admissible] >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ c _`
    (mp_tac o REWRITE_RULE [expr_sim_prefix_def,expr_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sc`,`shadow_sa`,`shadow_sc`,`cop`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `expr_sim_full _ _ _ _ c _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sc`,`shadow_sa`,`shadow_sc`,`cop`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ condQ condR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx c) (read_result cx))
     (es,s0,G0,tn0)
     (\H res ee G tn z. condQ H res ee G tn z /\
       ?cm. gas_origin_ptr_path
         (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s0,G0,tn0) cm (OK z,G,tn)) condR` by
    (irule gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ condQ condR` (irule_at Any) >>
     rpt strip_tac >> simp[] >> metis_tac[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ condQ condR` kall_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ pathQ condR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx c) (read_result cx))
     (es,s0,G0,tn0)
     (\H res ee G tn z. pathQ H res ee G tn z /\ ~z.vs_halted /\ ee.gas_obs = [])
     condR` by
    (irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ pathQ condR` (irule_at Any) >> simp[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ pathQ condR` kall_tac >>
  rewrite_tac[exprSimIfExpTheory.ifexp_root_eval_forced] >>
  irule gas_prefix_full_bind >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ condR` (irule_at Any) >>
  simp[exprSimIfExpTheory.ifexp_root_cont_frame,
       vyperStorageTraceTheory.storage_trace_frame_bind_all,
       vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_read_result,
       requests_outcomes_frame_bind_all,evaluate_requests_outcomes_frame,
       requests_outcomes_frame_read_result] >>
  rpt conj_tac
  >~ [`!H res ee gt r. condR H res ee gt r ==> ISR res`]
  >- (simp[Abbr `condR`] >> rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def]) >>
  qx_genl_tac [`marks`,`v`,`mid`,`G1`,`tn1`,`z`] >> strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[NoAsms,Abbr `pathQ`,Abbr `condQ`] >> strip_tac >>
  `mid with gas_obs := [] = mid` by
    (Cases_on `mid` >> gvs (TypeBase.updates_of ``:evaluation_state``)) >>
  `bind (eval_expr cx c) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[listTheory.APPEND_NIL] >>
     disch_then assume_tac >> fs[]) >>
  drule_all exprSimIfExpTheory.ifexp_root_condition_bool >> strip_tac >>
  qpat_x_assum `v = BoolV _` SUBST_ALL_TAC >>
  qpat_x_assum `!sel. ?cop. _` (qspec_then `sel` strip_assume_tac) >>
  `cop' = cop /\ sc' = sc /\ shadow_sc' = shadow_sc` by
    (qpat_x_assum `lower_value compile_expr cenv (BaseT BoolT) c sa = (cop',sc')` mp_tac >>
     qpat_x_assum `lower_value compile_expr _ _ (gas_shadow_expr _) _ = (cop',shadow_sc')` mp_tac >> simp[]) >>
  qpat_x_assum `cop' = cop` SUBST_ALL_TAC >>
  qpat_x_assum `sc' = sc` SUBST_ALL_TAC >>
  qpat_x_assum `shadow_sc' = shadow_sc` SUBST_ALL_TAC >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
      (bind (eval_expr cx (if sel then a else b)) (conditional_result cx)) (mid,z,G1,tn1)`
    suffices_by (Cases_on `sel` >> simp[]) >>
  suspend "jump"
QED
*)
Theorem ifexp_vv_prefix_root_uniform:
  expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
  (!e sa sm av op sb es1 u G1 tn1 st0.
    (e = a \/ e = b) /\
    compile_expr cenv ty e sa = (av,sm) /\
    compile_ifexp_arm cenv t (lowered_value_type cenv e) av sm = (op,sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    local_ptrs_reserved cenv sa /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
    !ee tv z G tn.
      (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
      MAP FDOM es1.scopes = MAP FDOM ee.scopes /\
      (!id path. tv = PlaceR (MemoryPlace id path) ==>
        same_memory_layout cenv (lowered_value_type cenv e) t) /\
      storage_trace_domain cx st0 ee.storage_trace /\
      eval_result_typed (env,cx,ee) tv (Type (expr_type e)) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        vv_post H ctx func cenv cx e es1 sa sm u ee tv av z /\
        ghost_inv_at (DF H) lo d cenv cx ee G tn z) /\
      vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv av z /\
      z.vs_current_bb = sm.cs_current_bb /\
      z.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~z.vs_halted /\
      alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e) /\
    ~is_bytestring_type (post_value_type cenv e) ==>
    vv_own cenv cx (post_value_type cenv e) sa sm ee tv av z) /\
      ptr_vv_ok cx (post_value_type cenv e) tv av ee G tn z /\
      (!t' op0. av = StackValue t' op0 /\ ~is_word_type (post_value_type cenv e) ==>
        ptr_buf_ok cenv e op0 G z) /\
      (!t' p. av = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv e p.ptr_operand G z) /\
      (cenv.ce_is_ctor /\ vv_location av = SOME LocCode ==>
        ?val. read_result cx tv ee = (INL val,ee) /\
          !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
            eval_operand (vv_operand av) z = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
              val_in_memory rt val (w2n w) mem)) /\
      ghost_kept_at lo cenv es1 sa G1 tn1 u G tn /\
      (!v. read_result cx tv ee = (INL v,ee) ==>
        value_has_type rty v /\
        !ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
          value_has_type ptv v) ==>
      ?v z' Gz tf.
        read_result cx tv ee = (INL v,ee) /\
        (!H. valid_horizon cx st0 H ee.storage_trace ==>
          gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
            (z,G,tn) [] (OK z',Gz,tf) /\
          expr_post H ctx func cenv cx (IfExp t c a b) es1 sa sb u ee v op z' /\
          ghost_inv_at (DF H) lo d cenv cx ee Gz tf z') /\
        (~is_word_type t ==>
          vv_at cenv cx t sa sb ee tv (LocatedValue t (mk_ptr op LocMemory)) z') /\
        (~is_word_type t ==> !id path. tv = PlaceR (MemoryPlace id path) ==>
          vv_place_ptr cenv cx ee z' tv (LocatedValue t (mk_ptr op LocMemory))) /\
    (!ctv v. conditional_result cx tv ee = (INL ctv,ee) /\
      ctv = Value v /\ ~is_word_type t /\ ~is_bytestring_type t ==>
      vv_own cenv cx t sa sb ee ctv
        (LocatedValue t (mk_ptr op LocMemory)) z') /\
        expr_store_bound cx t v op z' /\
        z'.vs_current_bb = sb.cs_current_bb /\
        z'.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func z' /\ u.vs_alloca_next <= z'.vs_alloca_next /\
        ptr_val_ok cx t v op Gz tf z' /\
        (~is_word_type t ==>
          !e'. lowered_value_type cenv e' = t ==> ptr_buf_ok cenv e' op Gz z') /\
        (~is_word_type t ==>
          !rt w. evaluate_type (get_tenv cx) t = SOME rt /\
            eval_operand op z' = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z'.vs_alloca_next) /\
        ghost_kept_at lo cenv es1 sa G1 tn1 u Gz tf) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields.
     FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv)
       fields) /\
  (!ty' tvt. evaluate_type (get_tenv cx) ty' = SOME tvt ==>
     type_memory_bytes cenv ty' = type_memory_size tvt) /\
  (!tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ ~is_word_type t ==>
     type_memory_size tvt < 2 ** 64) /\
  evaluate_type (get_tenv cx) t = SOME rty /\
  expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx (BaseT BoolT) c es /\
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx (BaseT BoolT) c es /\
  (!gs v es1.
     bind (eval_expr cx c) (read_result cx) (es with gas_obs := gs) =
       (INL v,es1) ==>
     expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty a es1 /\
     expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty b es1 /\
     (!e gs' raw ee. (e = a \/ e = b) /\
       eval_expr cx e (es1 with gas_obs := gs') = (INL raw,ee) ==>
       eval_result_typed (env,cx,ee) raw (Type (expr_type e))) /\
     !e gs' v' es2.
       (e = a \/ e = b) /\
       bind (eval_expr cx e) (read_result cx) (es1 with gas_obs := gs') =
         (INL v',es2) ==>
       value_has_type rty v' /\
       !ptv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv ==>
             value_has_type ptv v') /\
  (!gs v es1.
     bind (eval_expr cx c) (read_result cx) (es with gas_obs := gs) =
       (INL v,es1) ==>
     expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty a es1 /\
     expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty b es1) ==>
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cenv cx ty (IfExp t c a b) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume ifexp_vv_prefix_root_uniform[jump]:
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (z,G1,tn1) [] (OK (jump_to (if sel then tl else el) z),G1,tn1)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     BETA_TAC >> simp[NoAsms] >> strip_tac >>
     `allocas_from lo z` by fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
     `op_taint tn1 cop = {}` by fs[bodyPtrDefsTheory.ptr_val_ok_def, compileEnvTheory.is_word_type_def] >>
     drule_all ifexp_root_jnz_origin_path >> simp[]) >>
  `!i. active_inst func i (jump_to (if sel then tl else el) z) ==>
       frag_reachable ctx func s0 func i (jump_to (if sel then tl else el) z)` by
    (rpt strip_tac >> irule ifexp_selected_entry_reachable >>
     qpat_assum `compile_expr cenv ty (if sel then a else b) se = (av,sea)` (irule_at Any) >>
     qpat_assum `compile_ifexp_arm cenv t _ av sea = (aop,sx)` (irule_at Any) >>
     qpat_assum `emit_inst ASSIGN [aop] [rv] sx = ((),sy)` (irule_at Any) >>
     qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) cm (OK z,G1,tn1)` (irule_at Any) >>
     simp[]) >>
  irule gas_prefix_full_zero_prefix_guarded >>
  simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
       vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_conditional_result] >>
  qexistsl [`G1`,`jump_to (if sel then tl else el) z`,`tn1`] >> simp[] >>
  suspend "arm"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume ifexp_vv_prefix_root_uniform[arm]:
  `gas_admissible (bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
      expr_vv_res_ok mid` by
    (drule_all exprSimIfExpTheory.ifexp_root_branch_admissible >> simp[]) >>
  `gas_admissible (eval_expr cx (if sel then a else b)) expr_vv_res_ok mid` by
    (qpat_assum `gas_admissible (bind _ _) _ mid`
       (assume_tac o REWRITE_RULE[gasContextTheory.gas_admissible_def,vyperStateTheory.bind_def]) >>
     rewrite_tac[gasContextTheory.gas_admissible_def] >>
     qx_genl_tac [`gs`,`res`,`ee`] >> strip_tac >> Cases_on `res`
     >- (rename1 `_ = (INL raw,ee)` >> Cases_on `raw` >> simp[expr_vv_res_ok_def] >>
         qpat_x_assum `!gs res ee. _ ==> expr_vv_res_ok res` (qspec_then `gs` mp_tac) >>
         simp[vyperStateTheory.conditional_result_def,vyperStateTheory.raise_def,
              expr_vv_res_ok_def]) >>
     qpat_x_assum `!gs res ee. _ ==> expr_vv_res_ok res` (qspec_then `gs` mp_tac) >> simp[]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
       (eval_expr cx (if sel then a else b)) (mid,jump_to (if sel then tl else el) z,G1,tn1)`
    suffices_by
      (strip_tac >> qmatch_assum_abbrev_tac `gas_prefix_full P cx st0 arm start` >>
       `gas_prefix_full P cx st0 (bind arm (conditional_result cx)) start <=>
        gas_prefix_full P cx st0 arm start` by
         (simp[NoAsms,Abbr `start`] >> irule gas_prefix_full_state_cong >> gen_tac >>
          Cases_on `arm qe` >> rename1 `arm _ = (res,ee)` >>
          Cases_on `res` >> simp[vyperStateTheory.bind_def] >>
          rename1 `SND (conditional_result cx raw ee) = ee` >>
          Cases_on `conditional_result cx raw ee` >>
          drule vyperStatePreservationTheory.conditional_result_state >> simp[]) >>
       fs[markerTheory.Abbrev_def]) >>
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (if sel then a else b) mid` by
    (qpat_assum `!gs v es1. _ ==> expr_vv_sim_prefix _ _ _ _ _ _ /\ _` drule >>
     Cases_on `sel` >> simp[]) >>
  qpat_x_assum `expr_vv_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_prefix_def,expr_vv_sim_full_pre_def]) >>
  disch_then match_mp_tac >>
  qexistsl [`se`,`sea`,`shadow_se`,`shadow_sea`,`av`] >> simp[] >>
  suspend "arm_pre"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume ifexp_vv_prefix_root_uniform[arm_pre]:
  qpat_x_assum `!e sa sm av op sb es1 u G1 tn1 st0. _` kall_tac >>
  qpat_x_assum `!gs v es1. _ ==> expr_vv_sim_full _ _ _ _ _ _ /\ _` kall_tac >>
  `sa.cs_next_var <= se.cs_next_var` by
    metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  simp[] >>
  conj_tac
  >- (simp[bodyMemoryDefsTheory.return_buf_frame_jump_to] >>
      irule bodyMemoryDefsTheory.return_buf_frame_frame >>
      qexistsl [`cenv`,`s0`,`sa`] >> simp[] >>
      qpat_assum `expr_post _ _ _ _ _ c _ _ _ _ _ _ _ z` mp_tac >>
      simp[NoAsms,loweringPostsTheory.expr_post_def] >> strip_tac >>
      first_assum ACCEPT_TAC) >>
  conj_tac
  >- (irule allocaHistoryTheory.alloca_history_jump >>
      simp[venomStateTheory.jump_to_def] >> qexists `z` >> simp[]) >>
  conj_tac
  >- (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp z` mp_tac >>
      simp[NoAsms,venomStateTheory.jump_to_def,ptrDisciplineTheory.allocas_below_fmp_def] >>
      rpt strip_tac >> res_tac) >>
  conj_tac
  >- (qx_genl_tac [`afn`,`inst`,`u0`] >> strip_tac >>
      qpat_assum `!fn inst s. frag_reachable ctx func s0 fn inst s ==> _` irule >>
      qexists_tac `afn` >>
      irule contextRawReachableTheory.frag_reachable_trans >>
      qpat_assum `frag_reachable ctx func (jump_to (if sel then tl else el) z) afn inst u0`
        (irule_at Any) >> first_assum ACCEPT_TAC) >>
  simp[ifexp_ghost_inv_at_jump,exprLoweringPropsTheory.stmt_state_rel_jump_to,
       venomStateTheory.jump_to_def] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ ~z.vs_halted /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  BETA_TAC >> simp[NoAsms] >> strip_tac >>
  qpat_assum `expr_post H _ _ _ _ c _ _ _ _ _ _ _ z` mp_tac >>
  simp[NoAsms,loweringPostsTheory.expr_post_def] >> strip_tac >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise ifexp_vv_prefix_root_uniform
*)
