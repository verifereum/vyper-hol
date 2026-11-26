(* Request-prefix composition of the shared tuple-code store loop. *)
Theory s1PrefixMakeTupleLoop
Ancestors
  s1PrefixMakeTupleSlot s1PrefixFrame s1PrefixDefs s1PrefixPreds
  bodyFullPreds exprSimWordArgs exprSimAggregateSource exprLowering
  gasShadowState gasShadowCompileContext vyperStorageTrace vyperInterpreter list

val _ = Parse.hide "base";

Theorem make_tuple_loop_prefix:
  !args tys dtvs off ps sa sb shadow_sa shadow_sb es s G tn.
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\ expr_sim_inv cenv cx env ebase /\
    csbase.cs_next_id <= aid /\ csbase.cs_next_id <= sa.cs_next_id /\
    csbase.cs_next_var <= sa.cs_next_var /\
    local_ptrs_reserved cenv csbase /\ local_ptrs_reserved cenv sa /\
    ctx_inst_ids_distinct ctx /\ fn_inst_ids_distinct func /\
    gas_shadow_context ctx shadow_ctx /\ gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    (!fn inst z. frag_reachable ctx func s fn inst z ==> dalloca_fmp_headroom inst z) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at csbase x) /\
    (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at csbase x) /\
    (!H. valid_horizon cx st0 H ebase.storage_trace ==>
         stmt_state_rel H ctx func cenv cx ebase sbase) /\
    storage_trace_domain cx st0 es.storage_trace /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    body_exprs_full_ok cx args /\ body_exprs_prefix_ok cx args /\
    (!e ee. MEM e args /\ expr_sim_inv cenv cx env ee ==>
            expr_body_pre cenv cx env e ee) /\
    expr_sim_inv cenv cx env es /\
    LIST_REL (\ty e. arg_type_fits (expr_type e) ty) tys args /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME dtvs /\
    LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv) tys dtvs /\
    off + type_memory_size_list dtvs <= cap /\
    make_tuple_buffer (DF,lo,d,ctx,func,cenv,cx,st0)
      (ebase,csbase,sbase,Gbase,tnbase) (q,aid,base,cap) sa es s G tn /\
    make_tuple_saved_slots base ps off s tn /\
    compile_make_tuple compile_expr cenv args tys (Var q) off sa = (Var q,sb) /\
    compile_make_tuple compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr args) tys
      (Var q) off shadow_sa = (Var q,shadow_sb) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
    fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_exprs cx args) (es,s,G,tn)
Proof
  Induct_on `args` >> rpt gen_tac >> strip_tac
  >- (irule gas_prefix_full_no_outcome >>
      simp[eval_exprs_nil, evaluate_storage_trace_frame] >>
      fs[make_tuple_buffer_def]) >>
  Cases_on `tys` >- fs[] >>
  Cases_on `dtvs` >- fs[] >>
  rename1 `OPT_MMAP _ (dty::tys) = SOME (dtv::dtvs)` >>
  drule_at (Pat `make_tuple_buffer _ _ _ _ _ _ _ _`) make_tuple_slot_cons_prefix >>
  disch_then (drule_at (Pat `OPT_MMAP _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_make_tuple _ _ (_::_) _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_make_tuple _ _ (MAP _ _) _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `body_const_cells_agree _ _ _ _`)) >>
  disch_then (drule_at (Pat `gas_shadow_function _ _`)) >>
  disch_then (drule_at (Pat `make_tuple_saved_slots _ _ _ _ _`)) >>
  disch_then irule >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `OPT_MMAP _ (_::_) = _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [OPT_MMAP_def]) >>
  qpat_x_assum `!tys dtvs off ps sa sb shsa shsb es s G tn. _ ==> _`
    (drule_at (Pat `compile_make_tuple _ _ (MAP _ _) _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_make_tuple _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `make_tuple_saved_slots _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `OPT_MMAP _ _ = _`)) >>
  disch_then irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      qpat_assum `!e ee. MEM e (_::_) /\ _ ==> _` irule >> simp[])
  >- (qpat_assum `off + type_memory_size_list (_::_) <= cap` mp_tac >>
      pure_rewrite_tac[typeLayoutPropsTheory.type_memory_size_list_sum,
                       MAP, SUM, arithmeticTheory.ADD_ASSOC] >> simp[NoAsms])
  >- (qpat_assum `LIST_REL _ (dty::tys) (_::args)` mp_tac >> simp[NoAsms])
  >> qpat_assum `LIST_REL _ (dty::tys) (dtv::dtvs)` mp_tac >> simp[NoAsms]
QED
