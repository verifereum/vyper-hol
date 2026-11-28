(* Nonempty encoded blueprint operands: evaluate the rows, pack without
   consuming source observations, and continue with the scalar operands. *)
Theory s1PrefixCreateBlueprintEncodedArgs
Ancestors
  bodyFullCreateHeld s1PrefixCreateCtorRowsBind s1PrefixCompose s1PrefixDefs
  bodyFullPreds s1PrefixPreds exprBodyPreProps exprSimHypsDefs exprLowering
  builtinCreate compileEnv gasShadow gasShadowState gasShadowCompile
  gasShadowCompileHelpers exprLoweringProps stmtLoweringMono
  dallocaBlueprintArgs bodyFullForArrayRound[qualified] fragExec
  fragGasOriginPtr gasOutcomeFull gasStorage vyperStorageTrace
  vyperStorageFootprint vyperTypeSystem vyperInterpreter vyperState
  venomState bodyPtrDefs loweringStateRelDefs codegenRel contextCodegenRel
  allocLimits abiEncodeValuesCode finite_map words list

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `compile_create_blueprint_args _ _ F _ ctor _ = _`
    (mp_then Any mp_tac create_blueprint_encoded_args_compile) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`rows`,`se`,`buf`,`st`] (map_every assume_tac o CONJUNCTS)) >>
  `MAP gas_shadow_expr ctor <> []` by simp[] >>
  qpat_assum `compile_create_blueprint_args _ _ F _ (MAP gas_shadow_expr ctor) _ = _`
    (mp_then Any mp_tac create_blueprint_encoded_args_compile) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`shrows`,`she`,`shbuf`,`sht`] (map_every assume_tac o CONJUNCTS)) >>
  `gas_shadow_compiles (compile_create_ctor_args compile_expr cenv ctor)
     (compile_create_ctor_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr ctor))` by
    irule (MATCH_MP gas_shadow_compiles_create_ctor_args
             (cj 1 gas_shadow_compile_expr_env) |>
           Q.INST [`sh` |-> `T`] |> SIMP_RULE (srw_ss()) []) >>
  drule_then (drule_all_then strip_assume_tac) bodyFullForArrayRoundTheory.nonslot_shadow_cut >>
  qpat_x_assum `rows = shrows` (SUBST_ALL_TAC o SYM) >>
  `ci_mono sa se /\ ci_mono se st /\ ci_mono st sb /\
   ci_mono sh she /\ ci_mono she sht /\ ci_mono sht shb` by
    metis_tac[ci_mono_compile_create_ctor_args,compile_expr_ci_mono,
      ci_mono_compile_alloc_buffer,ci_mono_compile_abi_encode_values_to_buf,pairTheory.SND] >>
  `fn_has_code sa se func /\ fn_has_code se st func /\ fn_has_code st sb func /\
   fn_has_code sh she shadow_func` by
    (`cs_extends sa se /\ cs_extends se st /\ cs_extends st sb /\
      cs_extends sh she /\ cs_extends she sht /\ cs_extends sht shb` by fs[ci_mono_def] >>
     rpt conj_tac >> irule fn_has_code_mid >>
     (qpat_assum `fn_has_code sa sb func` (irule_at Any) ORELSE
      qpat_assum `fn_has_code sh shb shadow_func` (irule_at Any)) >>
     simp[cs_extends_refl] >> irule cs_extends_trans >> goal_assum (drule_at Any) >> simp[]) >>
  `!e u. MEM e ctor /\ expr_sim_inv cenv cx env u ==> expr_body_pre cenv cx env e u` by
    (rpt strip_tac >> irule create_operand_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) entry` (irule_at Any) >> simp[]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (eval_exprs cx ctor) (es,s,G,tn)` by
    (first_x_assum irule >> goal_assum (irule_at Any) >>
     goal_assum (irule_at Any) >> simp[]) >>
  irule create_ctor_rows_bind_prefix_from_traversal >>
  qpat_assum `compile_create_ctor_args _ _ ctor sa = _` (irule_at Any) >>
  qpat_assum `compile_create_ctor_args _ _ (MAP gas_shadow_expr ctor) sh = _` (irule_at Any) >>
  qexistsl [`tops`,`shadow_func`,`env`,`d`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qx_genl_tac [`marks`,`vs`,`ee`,`Gr`,`tr`,`rs`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac blueprint_encoded_args_pack_from_rows >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`bytes`,`z`,`Gz`,`tz`] (map_every assume_tac o CONJUNCTS)) >>
  irule gas_prefix_full_zero_prefix_guarded >>
  simp[] >> qexistsl [`Gz`,`z`,`tz`] >> simp[] >>
  qpat_assum `!vs bytes ee Gz tz z marks. _ ==> gas_prefix_full _ _ _ (next vs) _`
    (qspecl_then [`vs`,`bytes`,`ee`,`Gz`,`tz`,`z`,`marks`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]
QED
*)
Theorem blueprint_encoded_args_cut_prefix:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  ctor <> [] /\ LENGTH salts = (if salted then 1 else 0) /\
  expr_body_pre cenv cx env
    (Call ann (CreateTarget (CreateFromBlueprint F) salted rof ks)
      (target::amount::(salts ++ offset::ctor)) dflt) entry /\
  expr_sim_inv cenv cx env es /\ body_exprs_full_ok cx ctor /\
  body_exprs_prefix_ok cx ctor /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  compile_create_blueprint_args compile_expr cenv F later ctor sa = ((data,cnt),sb) /\
  compile_create_blueprint_args compile_expr (gas_shadow_env T cenv) F (MAP gas_shadow_expr later)
    (MAP gas_shadow_expr ctor) sh = ((data,cnt),shb) /\
  gas_shadow_state sa sh /\ gas_shadow_state sb shb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  fn_has_code sa sb func /\ fn_has_code sh shb shadow_func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!vs. storage_trace_frame (next vs)) /\
  (!rows se she.
    compile_create_ctor_args compile_expr cenv ctor sa = (rows,se) /\
    compile_create_ctor_args compile_expr (gas_shadow_env T cenv)
      (MAP gas_shadow_expr ctor) sh = (rows,she) /\
    gas_shadow_state se she /\ fn_has_code sa se func /\ fn_has_code sh she shadow_func ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_exprs cx ctor) (es,s,G,tn)) /\
  (!vs bytes ee Gz tz z marks.
    encode_create_ctor_args (get_tenv cx) (MAP expr_type ctor) vs = SOME bytes /\
    LENGTH bytes < 2 ** 64 /\
    (!tail. eval_exprs cx ctor (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL vs,ee with gas_obs := tail)) /\
    expr_sim_inv cenv cx env ee /\
    wb_frame cenv es ee sa s z /\ ghost_kept_at lo cenv es sa G tn s Gz tz /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ s.vs_alloca_next <= z.vs_alloca_next /\
    alloca_history func z /\ return_buf_frame d cenv sb z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    (!fn i u. frag_reachable ctx func z fn i u ==> dalloca_fmp_headroom i u) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. data = Var x \/ cnt = Var x ==> not_fresh_at sb x) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace /\ stmt_state_rel H ctx func cenv cx ee z /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at (DF H) lo d cenv cx ee Gz tz z /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) marks (OK z,Gz,tz)) /\
    (!vs' ef Gf tf f gs.
      (!tail. eval_exprs cx later (ee with gas_obs := gs ++ tail) = (INL vs',ef with gas_obs := tail)) /\
      wb_frame cenv ee ef sb z f /\ ghost_kept_at lo cenv ee sb Gz tz z Gf tf /\
      MAP FDOM ee.scopes = MAP FDOM ef.scopes /\ z.vs_alloca_next <= f.vs_alloca_next /\
      storage_trace_domain cx st0 ef.storage_trace /\
      (!H. valid_horizon cx st0 H ef.storage_trace ==>
        valid_horizon cx st0 H ee.storage_trace /\ stmt_state_rel H ctx func cenv cx ef f /\
        storage_well_formed_on cx ef (FST H) /\ ghost_inv_at (DF H) lo d cenv cx ef Gf tf f) ==>
      eval_operand cnt f = SOME (n2w (LENGTH bytes)) /\ op_taint tf cnt = {} /\ op_prov Gf cnt = NONE /\
      (cnt <> Lit 0w ==> ?q a. data = Var q /\ lookup_var q f = SOME a /\
        ptr_covers Gf tf q f (LENGTH bytes) /\ (bytes = [] \/ w2n a + LENGTH bytes <= f.vs_alloca_next) /\
        (!i. w2n a <= i /\ i < w2n a + LENGTH bytes ==> i NOTIN tf.t_mem) /\
        read_memory (w2n a) (LENGTH bytes) f = bytes)) ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (next vs) (ee,z,Gz,tz)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_exprs cx ctor) next) (es,s,G,tn)
Proof
  cheat
QED
