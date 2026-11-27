(* Close both linked simulations at the already materialized self.code result. *)
Theory bodySliceSelfSimPairMods
Ancestors
  bodySliceSelfRouteMods bodySliceCodeOperandPreMods bodySliceExternalSourceMods
  bodyAggregateReadMods bodyAggregateReadPostMods exprSimSliceSelfCode
  bodyFullPredsMods exprLoweringProps exprLowering exprBopLowering
  gasShadowCompileStmtHelpers compileEnv valueCopyBytes vyperInterpreter vyperState
  exprSimHypsDefs bodyFullShared context

val E = ``Builtin (BaseT (BytesT (Dynamic n))) (Slice n)
  [Builtin ct (Acc Code) [Builtin at (Env SelfAddr) []];start;len]``;

Triviality slice_self_child_sim:
  expr_body_pre_mods mods cenv cx env
    (Builtin a (Slice n) [Builtin ct (Acc Code) [addr];start;len]) es /\
  body_const_cells_agree_mods mods cx env ee /\
  expr_sim_inv_mods mods cenv cx env ee /\
  (e = start \/ e = len \/ e = addr) /\
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e ee /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e ee
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre_mods mods cenv cx env e ee` by
    (Cases_on `e = addr`
     >- (drule slice_external_source_mods >> simp[]) >>
     `code_slice_source (Slice n) [Builtin ct (Acc Code) [addr];start;len] =
        SOME (ct,addr)` by simp[code_slice_source_def] >>
     drule_all_then (map_every assume_tac o CONJUNCTS) slice_code_operand_pre_mods >>
     gvs[] >> first_x_assum irule >> simp[]) >>
  qpat_assum `body_expr_full_ok_mods _ _ _ _` (mp_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  disch_then (CONJUNCTS_THEN2 irule kall_tac) >>
  asm_rewrite_tac[] >> conj_tac
  >- (qexistsl_tac [`src`,`tops`] >> first_assum ACCEPT_TAC) >>
  qexists_tac `env` >> asm_rewrite_tac[]
QED

Triviality slice_self_eval_value:
  eval_expr cx ^E es = (INL raw,ee) ==> ?v. raw = Value v
Proof
  simp[slice_self_code_actions,bind_def,get_accounts_def,lift_sum_def,return_def,
       raise_def,AllCaseEqs()] >> metis_tac[]
QED

Triviality slice_self_read_cut:
  lower_value compile_expr cenv ty ^E sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^E) sha = (op,shb) /\
  gas_shadow_state sa sha ==>
  compile_expr cenv ty ^E sa = (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr op LocMemory),sb) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^E) sha =
    (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr op LocMemory),shb)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!bt xs. names_builtin bt xs ==> bt <> Slice n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `~names_builtin (Slice n) [Builtin ct (Acc Code) [Builtin at (Env SelfAddr) []];start;len]` by
    (first_x_assum (qspecl_then [`Slice n`,`[Builtin ct (Acc Code) [Builtin at (Env SelfAddr) []];start;len]`] mp_tac) >> simp[]) >>
  `?out b. compile_expr cenv ty ^E sa =
           (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr out LocMemory),b)` by
    (simp[compile_expr_builtin_dispatch,compile_builtin_dispatch_component_eq,
          is_self_code_def,lower_value_child_call] >>
     rpt (pairarg_tac >> simp[]) >>
     qmatch_goalsub_rename_tac `as_ptr_val _ LocMemory (compile_slice_code x y sz sc)` >>
     Cases_on `compile_slice_code x y sz sc` >> simp[as_ptr_val_def,mk_ptr_def]) >>
  Cases_on `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^E) sha` >>
  `gas_shadow_compiles (compile_expr cenv ty ^E)
     (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^E))` by
    MATCH_ACCEPT_TAC gas_shadow_stmt_compile_expr_env >>
  drule_all_then strip_assume_tac gas_shadow_step >>
  gvs[lower_value_def,comp_bind_def,unwrap_value_def,mk_ptr_def,comp_return_def,is_word_type_def]
QED

Triviality slice_self_read_from_vv:
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty ^E es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty ^E es
Proof
  strip_tac >> irule materialized_value_from_vv_mods >>
  qpat_assum `expr_vv_sim_full_mods _ _ _ _ _ _` (irule_at Any) >>
  reverse conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_then ACCEPT_TAC slice_self_eval_value) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac slice_self_read_cut >>
  qexists_tac `LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr op LocMemory)` >>
  asm_rewrite_tac[] >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `raw = Value v` SUBST_ALL_TAC >>
  `~is_word_type (BaseT (BytesT (Dynamic n))) /\ (mk_ptr op LocMemory).ptr_location = LocMemory` by
    simp[is_word_type_def,mk_ptr_def] >>
  `ptr_buf_ok cenv ^E (mk_ptr op LocMemory).ptr_operand G t` by
    (qpat_assum `!b p. LocatedValue _ _ = LocatedValue b p /\ _ ==> ptr_buf_ok _ _ _ _ _`
       (qspecl_then [`BaseT (BytesT (Dynamic n))`,`mk_ptr op LocMemory`] mp_tac) >> simp[]) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) memory_buffer_read_post_mods >>
  gvs[mk_ptr_def]
QED

Theorem slice_self_sim_pair_mods:
  code_slice_source (Slice n) args = SOME (ct,addr) /\
  is_self_code (Builtin ct (Acc Code) [addr]) /\
  (builtin_args_length_ok (Slice n) (LENGTH args) ==>
    case code_slice_source (Slice n) args of
      NONE => body_exprs_full_ok_mods mods exps cx args
    | SOME (code_ty,addr) =>
        body_exprs_full_ok_mods mods exps cx (TL args) /\
        (!s tail_vs t. eval_exprs cx (TL args) s = (INL tail_vs,t) ==>
           body_exprs_full_ok_mods mods exps cx [addr])) /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin a (Slice n) args) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
    (Builtin a (Slice n) args) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
    (Builtin a (Slice n) args) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_asm2_tac
  >- (drule_all_then (qx_choosel_then [`start`,`len`] strip_assume_tac) slice_code_operand_pre_mods >>
      qpat_x_assum `args = _` SUBST_ALL_TAC >>
      `!e. is_self_code e ==> ?ct at. e = Builtin ct (Acc Code) [Builtin at (Env SelfAddr) []]` by
        (ho_match_mp_tac is_self_code_ind >> simp[is_self_code_def]) >>
      first_x_assum (drule_then strip_assume_tac) >> gvs[] >>
      drule_then strip_assume_tac slice_external_source_mods >> gvs[] >>
      irule slice_self_read_from_vv >> first_assum ACCEPT_TAC) >>
  irule slice_self_from_tail_mods >> conj_tac
  >- (qexistsl_tac [`addr`,`ct`] >> asm_rewrite_tac[]) >>
  qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >>
  asm_rewrite_tac[] >> rpt gen_tac >> MATCH_ACCEPT_TAC slice_self_child_sim
QED
