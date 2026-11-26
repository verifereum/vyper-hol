(* The linked calldata slice runs the offset, then one checked suffix. *)
Theory bodyCalldataSliceRouteMods
Ancestors
  bodyCalldataSliceInputsMods bodyCalldataSliceBindMods
  bodyCalldataSliceAbortMods bodyCalldataSliceSuccessMods
  bodyAggregateReadMods bodyAggregateReadPostMods bodyFullShared
  bodyFullPostsMods exprSimHash exprSimCalldataSlice gasShadowCompileStmtHelpers
  exprLowering context words vyperStorageFootprint compileEnv
  vyperInterpreter vyperContext vyperState loweringPosts
Libs monadsyntax

val ann = ``BaseT (BytesT (Dynamic m))``;
val E = ``Builtin ^ann (CalldataSlice n) [e]``;

Theorem calldata_slice_vv_route_mods[local]:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env ^E es /\
  expr_body_pre_mods mods cenv cx env e es /\ body_expr_full_ok_mods mods exps cx e /\
  expr_type e = BaseT (UintT 256) /\ 0 < n /\ n <= m ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty ^E es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[expr_vv_sim_full_mods_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choosel_then [`x`,`sm`,`shm`,`out`] strip_assume_tac)
    calldata_slice_compile_mods >>
  irule calldata_slice_bind_reached_mods >> reverse conj_tac
  >- (qpat_assum `lower_value compile_expr cenv (expr_type e) e sa = (x,sm)` (irule_at Any) >>
      qpat_assum `lower_value compile_expr _ _ (gas_shadow_expr e) _ = (x,shm)` (irule_at Any) >>
      qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
      qpat_assum `fn_has_code shadow_sa shm shadow_func` (irule_at Any) >>
      qpat_assum `module_body_inv mods src tops cenv cx` (irule_at Any) >>
      qpat_assum `contract_inv mods exps ctx cenv cx` (irule_at Any) >>
      qpat_assum `body_const_cells_agree_mods mods cx env es` (irule_at Any) >>
      rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> BETA_TAC >>
      qpat_x_assum `v = IntV (&a)` SUBST_ALL_TAC >>
      Cases_on `a+n < dimword (:256) /\ a+n <= LENGTH cx.txn.calldata`
      >- suspend "success" >> suspend "abort") >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
QED

Resume calldata_slice_vv_route_mods[success]:
  qpat_x_assum `a+n < dimword (:256) /\ a+n <= LENGTH cx.txn.calldata`
    (map_every assume_tac o CONJUNCTS) >>
  irule calldata_slice_success_outcome_mods >> asm_rewrite_tac[] >> rpt conj_tac
  >- (qexists_tac `marks` >> first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
        (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  qpat_assum `compile_slice_calldata _ _ _ sm = (out,sb)` (irule_at Any) >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >> first_assum ACCEPT_TAC
QED

Resume calldata_slice_vv_route_mods[abort]:
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H0 mid.storage_trace` by
    fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `stmt_state_rel H0 ctx func cenv cx mid t` by
    fs[expr_post_mods_def,expr_post_def] >>
  `n < dimword (:256)` by decide_tac >>
  asm_rewrite_tac[] >>
  irule (INST_TYPE [alpha |-> ``:256``] calldata_slice_abort_outcome_mods) >>
  asm_rewrite_tac[] >> conj_tac
  >- (qpat_assum `compile_slice_calldata _ _ _ sm = (out,sb)` (irule_at Any) >>
      asm_rewrite_tac[]) >>
  qexists_tac `H0` >> first_assum ACCEPT_TAC
QED

Finalise calldata_slice_vv_route_mods

(* The source success constructor is Value, independently of its gas list. *)
Theorem calldata_slice_eval_value[local]:
  eval_expr cx ^E es = (INL raw,ee) ==> ?v. raw = Value v
Proof
  `eval_expr cx ^E = bind (bind (eval_expr cx e) (read_result cx))
    (\v u. ((case builtin_result cx u.accounts ^ann (CalldataSlice n) [expr_type e] [v] of
               INL w => INL (Value w) | INR exc => INR exc),u))` by
    (irule eval_expr_unary_builtin_action >>
     simp[precompile_builtin_def,builtin_args_length_ok_def,is_self_codesize_def]) >>
  simp[bind_def,AllCaseEqs()] >> metis_tac[]
QED

Theorem calldata_slice_read_cut[local]:
  lower_value compile_expr cenv ty ^E sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^E) sha = (op,shb) /\
  gas_shadow_state sa sha ==>
  compile_expr cenv ty ^E sa = (LocatedValue ^ann (mk_ptr op LocMemory),sb) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^E) sha =
    (LocatedValue ^ann (mk_ptr op LocMemory),shb)
Proof
  strip_tac >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
  rename1 `lower_value _ _ _ e sa = (x,sm)` >>
  Cases_on `compile_slice_calldata x (Lit (n2w n)) (type_memory_bytes cenv ^ann) sm` >>
  rename1 `compile_slice_calldata _ _ _ sm = (out,bb)` >>
  `compile_expr cenv ty ^E sa = (LocatedValue ^ann (mk_ptr out LocMemory),bb)` by
    simp[compile_calldata_slice_parts,as_ptr_val_def,comp_return_def] >>
  Cases_on `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^E) sha` >>
  `gas_shadow_compiles (compile_expr cenv ty ^E)
     (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^E))` by
    MATCH_ACCEPT_TAC gas_shadow_stmt_compile_expr_env >>
  drule_all_then strip_assume_tac gas_shadow_step >>
  gvs[lower_value_def,comp_bind_def,unwrap_value_def,mk_ptr_def,is_word_type_def,comp_return_def]
QED

Theorem calldata_slice_value_route_mods[local]:
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty ^E es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty ^E es
Proof
  strip_tac >> irule materialized_value_from_vv_mods >>
  qpat_assum `expr_vv_sim_full_mods _ _ _ _ _ _` (irule_at Any) >>
  reverse conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_then ACCEPT_TAC calldata_slice_eval_value) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac calldata_slice_read_cut >>
  qexists_tac `LocatedValue ^ann (mk_ptr op LocMemory)` >> asm_rewrite_tac[] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `raw = Value v` SUBST_ALL_TAC >>
  `~is_word_type ^ann /\ (mk_ptr op LocMemory).ptr_location = LocMemory` by
    simp[is_word_type_def,mk_ptr_def] >>
  `ptr_buf_ok cenv ^E (mk_ptr op LocMemory).ptr_operand G t` by
    (qpat_assum `!b p. LocatedValue _ _ = LocatedValue b p /\ _ ==> ptr_buf_ok _ _ _ _ _`
       (qspecl_then [`^ann`,`mk_ptr op LocMemory`] mp_tac) >> simp[]) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) memory_buffer_read_post_mods >>
  fs[mk_ptr_def]
QED

Theorem calldata_slice_route_mods:
  (builtin_args_length_ok (CalldataSlice n) (LENGTH args) ==>
    body_exprs_full_ok_mods mods exps cx args) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin ann (CalldataSlice n) args) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann (CalldataSlice n) args) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann (CalldataSlice n) args) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choosel_then [`e`,`m`] strip_assume_tac) calldata_slice_operand_mods >>
  qpat_x_assum `args = [e]` SUBST_ALL_TAC >>
  qpat_x_assum `ann = BaseT (BytesT (Dynamic m))` SUBST_ALL_TAC >>
  reverse conj_asm2_tac
  >- (irule calldata_slice_vv_route_mods >> rpt (goal_assum (drule_at Any))) >>
  drule_then ACCEPT_TAC calldata_slice_value_route_mods
QED
