(* Composition of the ordinary AugAssign target and load/RHS prefixes. *)
Theory s1PrefixAugAssignOrdinary
Ancestors
  s1PrefixAugAssignOrdinaryTarget s1PrefixAugAssignOrdinaryLoad
  s1PrefixAugAssignOrdinaryLoadBoundary

Theorem augassign_ordinary_prefix:
  !cx aty bop t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func
   cenv env env' ret_ty lctx RetQ es.
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
     eval_target_place cx t s'' = (INL p,t') /\
     read_place cx p s'3' = (INL cur,t'') /\
     place_type_value cx p s'4' = (INL ptv,t'3') ==> body_expr_full_ok cx e) /\
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
     eval_target_place cx t s'' = (INL p,t') /\
     read_place cx p s'3' = (INL cur,t'') /\
     place_type_value cx p s'4' = (INL ptv,t'3') ==> body_expr_prefix_ok cx e) /\
  body_base_target_full_ok cx t /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (AugAssign aty t bop e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (AugAssign aty t bop e) ==> occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (AugAssign aty t bop e) = SOME env' /\
  stmt_exprs_ok cenv (AugAssign aty t bop e) /\
  call_evaluation_safe cx (int_calls_stmt (AugAssign aty t bop e)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ cenv ret_ty /\
  (?pt. supported_target_info tops bindings t = SOME pt) /\
  ~immutable_root cx t /\
  (!st0 sa ca shadow_sa shadow_ca r s0 G0 tn0.
    type_place_target env t = SOME (Type aty) /\
    compile_get_target_ptr compile_expr cenv t sa = (r,ca) /\
    compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
      (gas_shadow_target t) shadow_sa = (r,shadow_ca) /\
    gas_shadow_state sa shadow_sa /\
    gas_shadow_state ca shadow_ca /\
    gas_shadow_context ctx shadow_ctx /\
    ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa ca func /\
    fn_has_code shadow_sa shadow_ca shadow_func /\
    fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    gas_admissible (eval_target_place cx t) target_place_res_ok es /\
    return_buf_frame d cenv sa s0 /\
    alloca_history func s0 /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_target_place cx t) (es,s0,G0,tn0)) ==>
  stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (AugAssign aty t bop e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AugAssign aty t bop e)))
    (eval_stmt cx (AugAssign aty t bop e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule augassign_ordinary_prefix_from_target_cont >>
  simp[] >>
  reverse conj_tac
  >- (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      qexistsl_tac [`bindings`,`env`,`env'`,`tops`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `?pt. supported_target_info _ _ _ = SOME pt`
    (qx_choose_then `info` assume_tac) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all augassign_ordinary_load_stage_inputs >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule augassign_ordinary_load_rhs_prefix >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G0`,`bindings`,`ca`,`cenv`,`d`,`env`,`es`,`info`,`marks`,
                `r`,`s0`,`sa`,`sb`,`shadow_func`,`t`,`tn0`,`tops`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
