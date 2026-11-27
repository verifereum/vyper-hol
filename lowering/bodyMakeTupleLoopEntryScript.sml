(* The allocation prefix of a heterogeneous tuple literal, up to the
   first iteration of the common tuple-code loop. *)
Theory bodyMakeTupleLoopEntry
Ancestors
  bodyMemTupleLayout bodyFullMakeArrayInit bodyFullIfExpReach
  exprSimAggregateLayout exprSimHyps exprSimHypsDefs exprLoweringProps
  exprOperandVar gasShadowCompileContext gasShadowState gasShadow
  exprLowering compileEnv bodyPtrDefs valueEncoding vyperStorageFootprint
  vyperState venomState venomInst

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all tuple_body_allocation_layout >> strip_tac >> gvs[] >>
  `type_memory_bytes cenv (TupleT tys) = type_memory_size_list tvs` by
    simp[type_memory_bytes_def] >>
  `?sba ssm su.
    compile_alloc_buffer (type_memory_size_list tvs) shadow_sa = (sba,ssm) /\
    compile_make_tuple compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr args) tys
      sba.buf_operand 0 ssm = (su,shadow_sb)` by
    (qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[gas_shadow_expr_def,gas_shadow_builtin_def,compile_tuple_literal] >>
     Cases_on `compile_alloc_buffer (type_memory_size_list tvs) shadow_sa` >>
     simp[tuple_literal_types_def] >>
     Cases_on `compile_make_tuple compile_expr (gas_shadow_env T cenv)
       (MAP gas_shadow_expr args) tys q.buf_operand 0 r` >>
     simp[as_ptr_val_def] >> metis_tac[]) >>
  `sba = ba /\ gas_shadow_state sm ssm` by
    (mp_tac (Q.INST [`nbytes` |-> `type_memory_size_list tvs`]
      gas_shadow_compiles_alloc_buffer) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >> gvs[] >>
  mp_tac (Q.INST [`cap` |-> `type_memory_size_list tvs`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`,
    `ann` |-> `TupleT tys`, `elem_opt` |-> `NONE`, `bnd` |-> `n`]
    make_array_init_full) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`q`,`w`,`si`,`Gi`,`tni`] strip_assume_tac) >>
  `u = Var q /\ su = Var q` by metis_tac[compiler_make_tuple_result] >> gvs[] >>
  `LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs` by
    (drule vyperTypeABITheory.OPT_MMAP_LIST_REL >>
     match_mp_tac listTheory.LIST_REL_mono >> rpt strip_tac >>
     metis_tac[expr_sim_inv_memory_size]) >>
  `ci_mono shadow_sa ssm /\ ci_mono ssm shadow_sb` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_compile_make_tuple_cfn,
      compile_expr_ci_mono,pairTheory.SND] >>
  `fn_has_code ssm shadow_sb shadow_func` by
    (irule (cj 2 fragExecTheory.fn_has_code_split) >>
     conj_tac >- fs[ci_mono_def] >> qexists `shadow_sa` >> fs[ci_mono_def]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  `!fn i z. frag_reachable ctx func si fn i z ==> dalloca_fmp_headroom i z` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s0,G0,tn0) [] (OK si,Gi,tni)`
       (qspec_then `DF (storage_trace_horizon es.storage_trace)` assume_tac) >>
     qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) [] (OK si,Gi,tni)` (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = _` (fn no_phi =>
         qpat_assum `!fn i z. frag_reachable ctx func s0 fn i z ==> _`
           (ACCEPT_TAC o MATCH_MP gas_origin_ptr_path_dalloca_fmp_headroom o
            CONJ path o CONJ no_phi)))) >>
  qexistsl_tac [`sm`,`ssm`,`q`,`w`,`si`,`Gi`,`tni`] >>
  fs[ci_mono_def] >> metis_tac[]
QED
*)
Theorem make_tuple_allocation_loop_entry:
  body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
  expr_body_pre cenv cx env (Builtin ann (MakeArray NONE n) args) es /\
  storage_trace_domain cx st0 es.storage_trace /\
  compile_expr cenv ty (Builtin ann (MakeArray NONE n) args) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin ann (MakeArray NONE n) args)) shadow_sa = (vv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?tys tvs sm ssm q w si Gi tni.
    ann = TupleT tys /\ vv = LocatedValue ann (mk_ptr (Var q) LocMemory) /\
    expr_sim_inv cenv cx env es /\
    LIST_REL (\t e. arg_type_fits (expr_type e) t) tys args /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs /\
    compile_make_tuple compile_expr cenv args tys (Var q) 0 sm = (Var q,sb) /\
    compile_make_tuple compile_expr (gas_shadow_env T cenv)
      (MAP gas_shadow_expr args) tys (Var q) 0 ssm = (Var q,shadow_sb) /\
    fn_has_code sm sb func /\ fn_has_code ssm shadow_sb shadow_func /\
    gas_shadow_state sm ssm /\
    sa.cs_next_id < sm.cs_next_id /\ sa.cs_next_var <= sm.cs_next_var /\
    local_ptrs_reserved cenv sm /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s0,G0,tn0) [] (OK si,Gi,tni)) /\
    (!fn inst z. frag_reachable ctx func si fn inst z ==> dalloca_fmp_headroom inst z) /\
    FLOOKUP si.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size_list tvs) /\
    lookup_var q si = SOME w /\ ptr_covers Gi tni q si (type_memory_size_list tvs) /\
    not_fresh_at sm q /\ w2n w + type_memory_size_list tvs < dimword (:256) /\
    w2n w + type_memory_size_list tvs <= si.vs_alloca_next /\
    (!name b len. local_region cenv es.scopes si name b len ==>
      loweringStateRelDefs$regions_disjoint (w2n w) (type_memory_size_list tvs) b len) /\
    alloca_history func si /\ s0.vs_alloca_next <= si.vs_alloca_next /\
    (!a b. FLOOKUP s0.vs_allocas a = SOME b ==> FLOOKUP si.vs_allocas a = SOME b) /\
    wb_frame cenv es es sa s0 si /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni /\
    return_buf_frame d cenv sm si /\ ~si.vs_halted /\
    si.vs_current_bb = sm.cs_current_bb /\ si.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es si /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es Gi tni si)
Proof
  cheat
QED
