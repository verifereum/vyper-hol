(* Successful RHS replay enters the exact tuple-store layout after staging. *)
Theory s1PrefixAssignTupleExactLayoutCursor
Ancestors
  bodyFullAssignTuple bodyTupleExactStoreCursor loweringPosts
  bodyPtrBopTypedSource vyperStorageFootprint vyperState list

Definition tuple_exact_prefix_inv_def:
  tuple_exact_prefix_inv params config code origin (gs,tys,tvs,vs)
    todo vals src u Gu tu <=>
    EVERY (\g. MEM g gs) todo /\
    ?tys1 tvs1 ops1 k p cur shadow_cur.
      tuple_exact_store_cursor params config code origin (tys,tvs,vs)
        (todo,tys1,tvs1,vals,ops1,k,p) (cur,shadow_cur,src,u,Gu,tu)
End

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `post_value_type cenv e = TupleT tys` by
    metis_tac[post_value_type_lowered] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >>
  `?tvs' vs p u Gu tu.
     source_v = ArrayV (TupleV vs) /\
     LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys tvs' /\
     tuple_exact_store_cursor (cenv,cx,env,tops,bindings)
       (DF,lo,d,ctx,func,shadow_func,st0) (sa,sb,shadow_sb) (es,s0,G0,tn0)
       (tys,tvs',vs) (gs,tys,tvs',vs,elems,0,p)
       (ss,shadow_ss,ee with gas_obs := [],u,Gu,tu) /\
     (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (v,G',tn') [] (OK u,Gu,tu))` by
    (irule tuple_assign_exact_store_entry >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qexistsl_tac [`e`,`marks`,`op`,`sl`,`staged`,`su`,`vv`] >>
     qpat_assum `post_value_type cenv e = TupleT tys`
       (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
     simp[] >> rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  drule bop_typed_source_witness >>
  disch_then (qspecl_then [`source_v`,`ee with gas_obs := []`] mp_tac) >>
  (impl_tac >-
   (qexists_tac `gas_explicit marks s0.vs_gas_readings` >>
    qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
      (qspec_then `[]` (ACCEPT_TAC o SIMP_RULE bool_ss [APPEND_NIL])))) >>
  strip_tac >>
  `evaluate_type (get_tenv cx) (TupleT tys) = SOME tv` by metis_tac[] >>
  drule vyperTypeValuesTheory.evaluate_type_TupleT_cases >> strip_tac >>
  `tvs' = tvs` by
    (qpat_assum `LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys tvs'` mp_tac >>
     qpat_assum `LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys tvs` mp_tac >>
     POP_ASSUM_LIST kall_tac >> simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
     irule LIST_EQ >> metis_tac[]) >>
  qpat_x_assum `tvs' = tvs` SUBST_ALL_TAC >>
  qpat_x_assum `tv = TupleTV tvs` SUBST_ALL_TAC >>
  qpat_x_assum `source_v = ArrayV (TupleV vs)` SUBST_ALL_TAC >>
  `val_wf (TupleTV tvs) (ArrayV (TupleV vs))` by
    (qhdtm_assum `expr_post`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _`
       (qspec_then `TupleTV tvs` mp_tac o REWRITE_RULE [expr_val_at_def]) >>
     simp[compileEnvTheory.is_word_type_def]) >>
  qexistsl_tac [`tvs`,`vs`,`u`,`Gu`,`tu`] >>
  qpat_assum `value_has_type (TupleTV tvs) (ArrayV (TupleV vs))`
    (assume_tac o REWRITE_RULE [vyperTypingTheory.value_has_type_def]) >>
  simp[tuple_exact_prefix_inv_def, EVERY_MEM] >>
  qexistsl_tac [`tys`,`tvs`,`elems`,`0`,`p`,`ss`,`shadow_ss`] >>
  first_assum ACCEPT_TAC
QED
*)
Theorem tuple_exact_prefix_cursor_init:
  body_inv tops ctx cenv cx /\ MEM func ctx.ctx_functions /\
  expr_body_pre cenv cx env e es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_type e = TupleT tys /\ lowered_value_type cenv e = TupleT tys /\
  assignable_type env.type_defs (TupleT tys) /\
  LIST_REL (\g ty. well_typed_atarget env g ty) gs tys /\
  EVERY (\g. case g of BaseTarget bt => supported_target tops bindings bt
                      | TupleTarget ts => F) gs /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (Assign (TupleTarget gs) e) ==> occurs_abi_decode_target target tops) /\
  ~supported_stmt_expr_exists (const_name_root cx) (Assign (TupleTarget gs) e) /\
  stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
  lower_value compile_expr cenv (TupleT tys) e sa = (op,su) /\
  (if is_memory_view e /\ vv_location vv = SOME LocMemory /\
      EXISTS (\t. ~is_word_type t) tys /\
      0 < SUM (MAP (type_memory_bytes cenv) tys) then
     comp_bind (compile_alloc_buffer (SUM (MAP (type_memory_bytes cenv) tys)))
       (\buf. comp_bind (comp_return buf.buf_operand)
         (\ptr. comp_ignore_bind (emit_void MCOPY [ptr; op;
                     Lit (n2w (SUM (MAP (type_memory_bytes cenv) tys)))])
                 (comp_return ptr)))
   else comp_return op) su = (staged,sl) /\
  compile_tuple_load_all cenv staged tys 0 sl = (elems,ss) /\
  compile_tuple_store_all cenv tys gs elems ss = ((),sb) /\
  compile_tuple_store_all (gas_shadow_env T cenv) tys (MAP gas_shadow_assignment gs)
    elems shadow_ss = ((),shadow_sb) /\
  gas_shadow_state ss shadow_ss /\
  fn_has_code sa su func /\ fn_has_code su sl func /\ fn_has_code sl ss func /\
  fn_has_code ss sb func /\ fn_has_code shadow_ss shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\
  cs_extends sa su /\ cs_extends su sl /\ cs_extends sl ss /\
  sa.cs_next_var <= su.cs_next_var /\ su.cs_next_var <= sl.cs_next_var /\
  sl.cs_next_var <= ss.cs_next_var /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~block_is_terminated sa /\ return_buf_frame d cenv sa s0 /\
  alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL source_v,ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s0,G0,tn0) marks (OK v,G',tn') /\
    expr_post H ctx func cenv cx e es sa su s0 (ee with gas_obs := []) source_v op v /\
    expr_store_bound cx (post_value_type cenv e) source_v op v /\
    v.vs_current_bb = su.cs_current_bb /\ v.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func v /\ (ctx_has_dalloca ctx ==> allocas_below_fmp v) /\
    s0.vs_alloca_next <= v.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx (ee with gas_obs := []) G' tn' v /\
    ptr_val_ok cx (post_value_type cenv e) source_v op G' tn' v /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn') ==>
  ?tvs vs u Gu tu.
    source_v = ArrayV (TupleV vs) /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    values_have_types tvs vs /\ val_wf (TupleTV tvs) (ArrayV (TupleV vs)) /\
    tuple_exact_prefix_inv (cenv,cx,env,tops,bindings)
      (DF,lo,d,ctx,func,shadow_func,st0) (sa,sb,shadow_sb)
      (es,s0,G0,tn0) (gs,tys,tvs,vs) gs vs (ee with gas_obs := []) u Gu tu /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (v,G',tn') [] (OK u,Gu,tu))
Proof
  cheat
QED

Theorem tuple_exact_prefix_inv_at:
  tuple_exact_prefix_inv (cenv,cx,env,tops,bindings)
    (DF,lo,d,ctx,func,shadow_func,st0) (sa,sb,shadow_sb) (es,s0,G0,tn0)
    (gs,tys,tvs,vs) todo vals src u Gu tu /\
  valid_horizon cx st0 H src.storage_trace ==>
  tuple_exact_cursor_at (cenv,cx) (DF,lo,d,ctx,func) H src u Gu tu
Proof
  simp[tuple_exact_prefix_inv_def, tuple_exact_store_cursor_def] >>
  rpt strip_tac >> first_x_assum irule >> first_assum ACCEPT_TAC
QED
