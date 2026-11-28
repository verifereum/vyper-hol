(* Request prefix after the array expression has returned its snapshot. *)
Theory s1PrefixForArraySnapshot
Ancestors
  forCapturedArraySnapshot s1PrefixForArraySnapshotLoop s1PrefixCompose
  s1PrefixDefs vyperStorageTrace vyperInterpreter vyperState
  vyperTypeContract[qualified,ignore_grammar]
Libs monadsyntax

Theorem for_array_snapshot_continue_prefix:
  compile_stmt c lctx ret_ty (For id typ (Array e) n loop_body) sa = ((),sb) /\
  compile_stmt (gas_shadow_env T c) lctx ret_ty
    (gas_shadow_stmt (For id typ (Array e) n loop_body)) sha = ((),shb) /\
  compile_expr c (expr_type e) e sa = (vv,se) /\
  compile_expr (gas_shadow_env T c) (expr_type e) (gas_shadow_expr e) sha = (vv,she) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb func /\ fn_has_code sha shb shadow_func /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  body_inv tops ctx c cx /\ shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (For id typ (Array e) n loop_body) /\
  type_stmt env ret_ty (For id typ (Array e) n loop_body) = SOME env' /\
  stmt_exprs_ok c (For id typ (Array e) n loop_body) /\
  vyperTypeContract$stmt_loop_calls_ok [(NONE,tops)] (For id typ (Array e) n loop_body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ (Array e) n loop_body) ==> occurs_abi_decode_target target tops) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Array e) n loop_body)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx RetQ c ret_ty /\
  c.ce_alloca_locals /\ local_ptrs_reserved c sa /\ ci_mono sa se /\
  ret_pc_ok c sa s0 /\ return_buf_frame d c sa s0 /\ return_buf_sep d c em u /\
  (!H. dead_lo_ok H (DF H) lo c cx) /\
  (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t) /\
  ce_locals_declared c env /\ locals_alloc_ok c env /\ expr_body_pre c cx env e es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_type e = ArrayT typ bd /\ bound_length bd <= n /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  storage_trace_domain cx st0 em.storage_trace /\
  (!tail. eval_expr cx e (es with gas_obs := obs ++ tail) =
     (INL rv,em with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H em.storage_trace ==>
     for_array_expr_endpoint (DF,lo,d,ctx,func) c cx e (es,sa,s0,G0,tn0)
       (vv,se) H rv em Gu tu u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func c cx es s0) /\
  ((?av. rv = Value (ArrayV av)) \/ (?src name path. rv = PlaceR (ImmutablePlace src name path))) /\
  (!av. read_result cx rv em = (INL (ArrayV av),em) ==>
     for_nonslot_code_frame [(NONE,tops)] c cx env ctx func id e loop_body
       (case vv_location vv of NONE => LocMemory | SOME l => l) rv vv av em u) /\
  (!vs. (!tail. array_iterator_results cx (expr_type e) rv (em with gas_obs := tail) =
                  (INL vs,em with gas_obs := tail)) /\
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" em = (INL (),em) ==>
    body_for_full_ok cx tyv id loop_body vs /\ body_for_prefix_ok cx tyv id loop_body vs /\
    gas_admissible (eval_for cx tyv id loop_body vs) (stmt_res_ok lctx) em) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
    (bind (array_iterator_results cx (expr_type e) rv)
      (\items. ignore_bind (check (compatible_bound (Dynamic n) (LENGTH items)) "For too long")
                         (eval_for cx tyv id loop_body items)))
    (em,u,Gu,tu)
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  mp_tac (SPEC_ALL for_array_snapshot_length_setup) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  rename1 `!D. gas_origin_ptr_path (D,lo,_,ctx,func,PG) (u,Gu,tu) [] (OK tL,GL,tnL)` >>
  rename1 `vs = MAP Value xs` >>
  `body_for_full_ok cx tyv id loop_body vs /\ body_for_prefix_ok cx tyv id loop_body vs /\
   gas_admissible (eval_for cx tyv id loop_body vs) (stmt_res_ok lctx) em` by
    (qpat_assum `!vs. _ ==> body_for_full_ok _ _ _ _ _ /\ _` irule >> simp[return_def]) >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
     (eval_for cx tyv id loop_body vs) (em,tL,GL,tnL)` by
    (qpat_assum `for_nonslot_layout _ _ _ _ _ _ _`
       (mp_then (Pos hd) (mp_tac o SPEC_ALL)
         (Q.INST [`es0` |-> `es`, `dtv` |-> `tyv`, `stv` |-> `tyv`]
           (SPEC_ALL for_array_snapshot_loop_prefix))) >>
     (impl_tac >-
      (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
       (conj_tac >- (qexists_tac `obs` >> first_assum ACCEPT_TAC)) >>
       rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
     (eval_for cx tyv id loop_body vs) (em,u,Gu,tu)` by
    (irule gas_prefix_full_zero_prefix_guarded >>
     simp[NoAsms,cj 4 evaluate_storage_trace_frame] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`GL`,`tL`,`tnL`] >> simp[]) >>
  `!tail. bind (array_iterator_results cx (expr_type e) rv)
      (\items. ignore_bind (check (compatible_bound (Dynamic n) (LENGTH items)) "For too long")
                         (eval_for cx tyv id loop_body items)) (em with gas_obs := tail) =
     eval_for cx tyv id loop_body vs (em with gas_obs := tail)` by
    (qpat_assum `!tail. array_iterator_results _ _ _ _ = _` (fn extract =>
       qpat_assum `check _ "For too long" = return ()` (fn bound =>
         simp[NoAsms,bind_def,ignore_bind_def,return_def,extract,bound]))) >>
  qpat_assum `gas_prefix_full _ _ _ (eval_for _ _ _ _ _) (em,u,Gu,tu)` mp_tac >>
  pop_assum (fn replay => simp[NoAsms,gas_prefix_full_def,replay])
QED
