(* Force the materialized result of the already checked external-code route. *)
Theory bodySliceExternalSimPairMods
Ancestors
  bodySliceExternalRouteMods bodySliceExternalSourceMods
  bodyAggregateReadMods bodyAggregateReadPostMods exprBopLowering
  bodyFullShared gasShadowCompileStmtHelpers exprLowering exprLoweringProps
  exprSimHypsDefs bodyFullPredsMods bodyFullPostsMods vyperInterpreter vyperAST
  compileEnv context

val ext_slice = ``Builtin (BaseT (BytesT (Dynamic n))) (Slice n)
                    [Builtin ct (Acc Code) [addr];start;len]``;

Theorem external_slice_read_cut[local]:
  ~is_self_code (Builtin ct (Acc Code) [addr]) /\
  lower_value compile_expr cenv ty ^ext_slice sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr ^ext_slice) sha = (op,shb) /\
  gas_shadow_state sa sha ==>
  compile_expr cenv ty ^ext_slice sa =
    (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr op LocMemory),sb) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^ext_slice) sha =
    (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr op LocMemory),shb)
Proof
  strip_tac >>
  Cases_on `compile_expr cenv ty ^ext_slice sa` >>
  Cases_on `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^ext_slice) sha` >>
  rename1 `compile_expr cenv ty ^ext_slice sa = (vv,sc)` >>
  rename1 `compile_expr _ _ (gas_shadow_expr ^ext_slice) sha = (hvv,shc)` >>
  `hvv = vv` by
    (irule (cj 1 gas_shadow_step) >>
     qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` (irule_at Any) >>
     qpat_assum `compile_expr cenv ty ^ext_slice sa = _` (irule_at Any) >>
     simp[gas_shadow_stmt_compile_expr_env]) >>
  qpat_x_assum `hvv = vv` SUBST_ALL_TAC >>
  `?out. vv = LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr out LocMemory)` by
    (`!bt xs. names_builtin bt xs ==> bt <> Slice n` by
       (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
     `~names_builtin (Slice n) [Builtin ct (Acc Code) [addr];start;len]` by metis_tac[] >>
     qpat_x_assum `compile_expr cenv ty ^ext_slice sa = _` mp_tac >>
     simp[compile_expr_builtin_dispatch,compile_builtin_dispatch_component_eq,
          lower_value_child_call,is_extcode_def,extcode_addr_expr_def] >>
     rpt (pairarg_tac >> simp[]) >> simp[as_ptr_val_pair] >>
     disch_then (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) kall_tac) >>
     qmatch_goalsub_abbrev_tac `mk_ptr out LocMemory` >>
     qexists_tac `out` >> simp[]) >>
  gvs[lower_value_def,comp_bind_def,unwrap_value_def,comp_return_def,mk_ptr_def,
      is_word_type_def]
QED

Theorem slice_external_sim_pair_mods:
  code_slice_source (Slice n) args = SOME (ct,addr) /\
  ~is_self_code (Builtin ct (Acc Code) [addr]) /\
  (builtin_args_length_ok (Slice n) (LENGTH args) ==>
   case code_slice_source (Slice n) args of
     NONE => body_exprs_full_ok_mods mods exps cx args
   | SOME (code_ty,ad) => body_exprs_full_ok_mods mods exps cx (TL args) /\
       (!s vs t. eval_exprs cx (TL args) s = (INL vs,t) ==>
                 body_exprs_full_ok_mods mods exps cx [ad])) /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin ann (Slice n) args) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann (Slice n) args) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann (Slice n) args) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> reverse conj_asm2_tac
  >- (irule slice_external_from_tail_mods >> conj_tac
      >- (qexistsl_tac [`addr`,`ct`] >> simp[]) >>
      qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  qpat_assum `code_slice_source _ _ = SOME _`
    (strip_assume_tac o REWRITE_RULE [code_slice_source_SOME]) >>
  qpat_x_assum `Slice n = Slice _`
    (SUBST_ALL_TAC o SYM o SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `args = _` SUBST_ALL_TAC >>
  drule_then (assume_tac o cj 2) slice_external_source_mods >>
  qpat_x_assum `ann = _` SUBST_ALL_TAC >>
  irule materialized_value_from_vv_mods >> asm_rewrite_tac[] >> reverse conj_tac
  >- (rpt strip_tac >> drule_then ACCEPT_TAC eval_expr_builtin_value) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac external_slice_read_cut >>
  qexists_tac `LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr op LocMemory)` >>
  asm_rewrite_tac[] >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `raw = Value v` SUBST_ALL_TAC >>
  `(mk_ptr op LocMemory).ptr_location = LocMemory` by simp[mk_ptr_def] >>
  `~is_word_type (BaseT (BytesT (Dynamic n)))` by simp[is_word_type_def] >>
  `ptr_buf_ok cenv ^ext_slice (mk_ptr op LocMemory).ptr_operand G t` by
    (qpat_assum `!t' p. LocatedValue _ _ = LocatedValue t' p /\ _ ==> ptr_buf_ok _ _ _ _ _`
       (qspecl_then [`BaseT (BytesT (Dynamic n))`,`mk_ptr op LocMemory`] mp_tac) >> simp[]) >>
  drule_all_then strip_assume_tac memory_buffer_read_post_mods >> fs[mk_ptr_def]
QED
