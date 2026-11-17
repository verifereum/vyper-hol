(* Word forcing uses the checked direct joint loaders, never the aggregate
   unwrap dispatcher.  Constructor robustness is retained as a producer input. *)
Theory bodyFullToplevelValue
Ancestors
  bodyFullUnwrapWord bodyFullUnwrapIdentity bodyFullToplevelSlotForce
  bodyFullToplevelCodeRuntimeForce bodyFullToplevelCodeCtorForce
  bodyFullToplevelVV bodyFullOfVV bodySimFull gasOutcomeFullCompose gasOutcomeFull
  gasShadowCompile exprSimMemorySource exprSimDefs gasExemptCert
  exprLoweringProps exprLowering compileEnv loweringPosts
  bodyPtrDefs exprSimMemDefs vyperStorageFootprint vyperAST context

Theorem toplevel_word_force_full:
  compile_expr cenv ty (TopLevelName ann nsid) sa =
    (LocatedValue ann p,sa) /\ is_word_type ann /\
  lower_value compile_expr cenv ty (TopLevelName ann nsid) sa = (op,sc) /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  fn_has_code sa sc func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x. vv_operand (LocatedValue ann p) = Var x ==> not_fresh_at sa x) /\
  evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sa s0 ee tv
       (LocatedValue ann p) s /\
     ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  vv_store_bound cx (expr_type (TopLevelName ann nsid))
    (lowered_value_type cenv (TopLevelName ann nsid)) ee tv (LocatedValue ann p) s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv (TopLevelName ann nsid)) tv
    (LocatedValue ann p) ee G tn s /\
  (cenv.ce_is_ctor /\ vv_location (LocatedValue ann p) = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val, ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
                eval_operand (vv_operand (LocatedValue ann p)) s = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v z G' tn'.
    read_result cx tv ee = (INL v, ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s, G, tn) [] (OK z, G', tn') /\
       expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sc s0 ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
    (~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
     vv_at cenv cx (post_value_type cenv (TopLevelName ann nsid)) sa sc ee tv
       (LocatedValue (post_value_type cenv (TopLevelName ann nsid)) (mk_ptr op LocMemory)) z) /\
    expr_store_bound cx (expr_type (TopLevelName ann nsid)) v op z /\
    z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv (TopLevelName ann nsid)) v op G' tn' z /\
    (~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
     ptr_buf_ok cenv (TopLevelName ann nsid) op G' z) /\
    (~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
            eval_operand op z = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    (!x. not_fresh_at sa x ==>
         lookup_var x z = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee ee sa s z /\
    ghost_kept_at lo cenv ee sa G tn s G' tn'
Proof
  strip_tac >>
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
   p.ptr_location = LocCode` by
    (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
     simp[compile_expr_def, expr_type_def] >>
     Cases_on `emit_inst INVALID [] [] sa` >> simp[] >>
     Cases_on `FLOOKUP cenv.ce_module_vars nsid` >> simp[] >>
     rename1 `SOME loc` >> Cases_on `loc` >> simp[mk_ptr_def] >>
     disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  `unwrap_value cenv (LocatedValue ann p) sa = (op,sc)` by
    gvs[lower_value_def, comp_bind_def] >>
  (Cases_on `p.ptr_location = LocCode`
   >- (mp_tac (Q.INST [`e` |-> `TopLevelName ann nsid`,
         `sm` |-> `sa`, `sb` |-> `sa`, `t` |-> `ann`,
         `vv` |-> `LocatedValue ann p`]
         (SPEC_ALL unwrap_code_word_origin_ptr)) >>
       (impl_tac >- gvs[expr_type_def, post_value_type_def]) >>
       strip_tac >> qexistsl [`v`, `z`, `G'`, `tn'`] >>
       gvs[expr_type_def, post_value_type_def]) >>
   mp_tac (Q.INST [`e` |-> `TopLevelName ann nsid`,
     `sm` |-> `sa`, `sb` |-> `sa`, `t` |-> `ann`,
         `vv` |-> `LocatedValue ann p`]
     (SPEC_ALL unwrap_slot_word_origin_ptr)) >>
   (impl_tac >- gvs[expr_type_def, post_value_type_def]) >>
   strip_tac >> qexistsl [`v`, `z`, `G'`, `tn'`] >>
   gvs[expr_type_def, post_value_type_def])
QED

val TOPLEVEL_FORCE_JOIN_TAC = fn th =>
  mp_tac (Q.INST [`vv` |-> `LocatedValue ann p`, `t` |-> `ann`,
    `sm` |-> `sa`, `sb` |-> `sa`, `ret` |-> `d`] (SPEC_ALL th)) >>
  (impl_tac >- gvs[post_value_type_def, expr_type_def]) >>
  strip_tac >> qexistsl_tac [`v`,`z`,`G'`,`tn'`] >>
  gvs[post_value_type_def, expr_type_def];

Theorem toplevel_name_force_full:
  compile_expr cenv ty (TopLevelName ann nsid) sa = (vv,sm) /\
  unwrap_value cenv vv sm = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sc func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
    ~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
    type_memory_bytes cenv (post_value_type cenv (TopLevelName ann nsid)) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sm s0 ee tv vv s /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  vv_store_bound cx (expr_type (TopLevelName ann nsid))
    (lowered_value_type cenv (TopLevelName ann nsid)) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv (TopLevelName ann nsid)) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
    ptr_buf_ok cenv (TopLevelName ann nsid) op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv (TopLevelName ann nsid) p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
        eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v z G' tn'.
    read_result cx tv ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G',tn') /\
      expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sc s0 ee v op z /\
      ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
    expr_store_bound cx (expr_type (TopLevelName ann nsid)) v op z /\
    z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv (TopLevelName ann nsid)) v op G' tn' z /\
    (~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
      ptr_buf_ok cenv (TopLevelName ann nsid) op G' z) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn'
Proof
  strip_tac >> Cases_on `vv`
  >- (rename1 `StackValue t0 op0` >>
      mp_tac (Q.INST [`e` |-> `TopLevelName ann nsid`, `sb` |-> `sm`,
        `vv` |-> `StackValue t0 op0`] (SPEC_ALL unwrap_stack_origin_ptr)) >>
      (impl_tac >- gvs[post_value_type_def, expr_type_def]) >>
      strip_tac >> qexistsl [`v`,`z`,`G'`,`tn'`] >>
      gvs[post_value_type_def, expr_type_def]) >>
  rename1 `LocatedValue t p` >>
  `compile_expr cenv ty (TopLevelName ann nsid) sm = (LocatedValue t p,sm)` by
    metis_tac[toplevel_located_compile_at] >>
  `sm = sa` by
    (drule toplevel_located_compile_at >>
     disch_then (qspec_then `sa` mp_tac) >> simp[]) >>
  `t = ann` by
    (qpat_x_assum `compile_expr _ _ _ sa = _` mp_tac >>
     simp[compile_expr_def, expr_type_def] >>
     Cases_on `emit_inst INVALID [] [] sa` >> simp[] >>
     Cases_on `FLOOKUP cenv.ce_module_vars nsid` >> simp[] >>
     rename1 `SOME loc` >> Cases_on `loc` >> simp[mk_ptr_def] >>
     rpt strip_tac >> gvs[]) >>
  gvs[] >>
  Cases_on `is_word_type ann`
  >- (`lower_value compile_expr cenv ty (TopLevelName ann nsid) sa = (op,sc)` by
        simp[lower_value_def, comp_bind_def] >>
      mp_tac (SPEC_ALL toplevel_word_force_full) >>
      (impl_tac >- gvs[post_value_type_def, expr_type_def]) >>
      strip_tac >> qexistsl [`v`,`z`,`G'`,`tn'`] >>
      gvs[post_value_type_def, expr_type_def]) >>
  Cases_on `p.ptr_location = LocCode`
  >- (Cases_on `cenv.ce_is_ctor`
      >- (TOPLEVEL_FORCE_JOIN_TAC toplevel_code_ctor_force_full) >>
      TOPLEVEL_FORCE_JOIN_TAC toplevel_code_runtime_force_full) >>
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` by
    (qpat_x_assum `compile_expr _ _ _ sa = _` mp_tac >>
     simp[compile_expr_def, expr_type_def] >>
     Cases_on `emit_inst INVALID [] [] sa` >> simp[] >>
     Cases_on `FLOOKUP cenv.ce_module_vars nsid` >> simp[] >>
     rename1 `SOME loc` >> Cases_on `loc` >> simp[mk_ptr_def] >>
     rpt strip_tac >> gvs[]) >>
  (Cases_on `type_slot_size rty = 1`
   >- TOPLEVEL_FORCE_JOIN_TAC bodyFullToplevelSlotSingleTheory.toplevel_slot_single_copy_full >>
   TOPLEVEL_FORCE_JOIN_TAC toplevel_slot_loop_copy_full)
QED

Theorem toplevel_name_value_from_vv:
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
        ~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
        type_memory_bytes cenv (post_value_type cenv (TopLevelName ann nsid)) = type_memory_size rt /\
        type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rty /\
  (!gs tv ee v. eval_expr cx (TopLevelName ann nsid) (es with gas_obs := gs) = (INL tv,ee) /\
     read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TopLevelName ann nsid) es ==>
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TopLevelName ann nsid) es
Proof
  strip_tac >> irule expr_sim_full_of_vv >> metis_tac[]
QED

Theorem toplevel_name_value_full:
  !DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env ty ann nsid es.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (TopLevelName ann nsid) es ==>
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (TopLevelName ann nsid) es
Proof
  rpt gen_tac >> strip_tac >>
  `expr_sim_pre cenv cx env (TopLevelName ann nsid) es` by
    simp[exprSimSourceTheory.expr_sim_pre_body, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  drule exprSimHypsTheory.well_typed_expr_type_evaluates >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  irule (Q.INST [`rty` |-> `x`] (SPEC_ALL toplevel_name_value_from_vv)) >>
  simp[post_value_type_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[post_value_type_def] >>
      drule_all exprSimHypsTheory.expr_body_pre_copy_ok >> simp[])
  >- (rpt strip_tac >>
      `expr_body_pre cenv cx env (TopLevelName ann nsid) (es with gas_obs := gs)` by
        simp[exprSimSourceTheory.expr_body_pre_gas_obs] >>
      drule exprSimSourceTheory.expr_body_pre_eval >>
      disch_then (qspecl_then [`INL v`,`ee`] mp_tac) >>
      simp[vyperStateTheory.bind_def] >> strip_tac >>
      qpat_x_assum `expr_sim_inv _ _ _ ee`
        (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE
          [exprSimHypsDefsTheory.expr_sim_inv_def]) >>
      disch_then (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE
        [vyperTypeInvariantsTheory.env_consistent_def]) >>
      disch_then (assume_tac o CONJUNCT1 o PURE_REWRITE_RULE
        [vyperTypeInvariantsTheory.env_context_consistent_def]) >>
      qpat_x_assum `expr_result_typed _ _ _` mp_tac >>
      simp[vyperTypeExprResultTheory.expr_result_typed_def,
           vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
           vyperTypeInvariantsTheory.value_result_typed_def])
  >- (irule toplevel_name_vv_full >> metis_tac[])
QED
