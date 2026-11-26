(* Read the already materialized result of ordinary Slice. *)
Theory bodySliceOrdinaryReadMods
Ancestors
  bodyAggregateReadMods bodyAggregateReadPostMods
  exprSimSliceSource exprSimHypsDefs exprBopLowering
  gasShadowCompileStmtHelpers bodyFullShared
  exprLowering compileEnv loweringPosts bodyFullPostsMods context valueCopyBytes
  vyperState vyperInterpreter
Libs monadsyntax

val E = ``Builtin ann (Slice n) [src;start;len]``;

Triviality ordinary_slice_eval_value:
  code_slice_source (Slice n) [src;start;len] = NONE /\
  eval_expr cx ^E es = (INL raw,ee) ==> ?v. raw = Value v
Proof
  strip_tac >>
  drule slice_eval_ordinary >>
  disch_then (fn th => qpat_assum `eval_expr _ _ _ = _`
    (mp_tac o PURE_ONCE_REWRITE_RULE [th])) >>
  simp[bind_def,get_accounts_def,lift_sum_def,return_def,raise_def,AllCaseEqs()] >>
  metis_tac[]
QED

Triviality ordinary_slice_read_cut:
  ~is_self_code src /\ ~is_extcode src /\
  is_bytestring_type ann /\
  lower_value compile_expr cenv ty ^E sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^E) sha = (op,shb) /\
  gas_shadow_state sa sha ==>
  compile_expr cenv ty ^E sa = (LocatedValue ann (mk_ptr op LocMemory),sb) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^E) sha =
    (LocatedValue ann (mk_ptr op LocMemory),shb)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!bt xs. names_builtin bt xs ==> bt <> Slice n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `~names_builtin (Slice n) [src;start;len]` by
    (first_x_assum (qspecl_then [`Slice n`,`[src;start;len]`] mp_tac) >> simp[]) >>
  `?out b. compile_expr cenv ty ^E sa = (LocatedValue ann (mk_ptr out LocMemory),b)` by
    (simp[compile_expr_builtin_dispatch,compile_builtin_dispatch_component_eq] >>
     Cases_on `is_bytestring_type (expr_type src)` >>
     simp[slice_dispatch_bytestring,slice_dispatch_fixed,lower_value_child_call] >>
     rpt (pairarg_tac >> simp[]) >>
     qmatch_goalsub_rename_tac `as_ptr_val ann LocMemory (compile_slice_data limit data x y sz endcs)` >>
     Cases_on `compile_slice_data limit data x y sz endcs` >> simp[as_ptr_val_def,mk_ptr_def]) >>
  Cases_on `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^E) sha` >>
  qmatch_asmsub_rename_tac `compile_expr _ _ (gas_shadow_expr _) sha = (svv,hb)` >>
  `gas_shadow_compiles (compile_expr cenv ty ^E)
     (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^E))` by
    MATCH_ACCEPT_TAC gas_shadow_stmt_compile_expr_env >>
  drule_all_then strip_assume_tac gas_shadow_step >>
  gvs[lower_value_def,comp_bind_def,unwrap_value_def,mk_ptr_def,comp_return_def,
      is_bytestring_word_type]
QED

Theorem slice_ordinary_read_from_vv_mods:
  code_slice_source (Slice n) [src;start;len] = NONE /\
  ~is_self_code src /\ ~is_extcode src /\
  ((ann = BaseT (BytesT (Dynamic n)) /\ ?bd. expr_type src = BaseT (BytesT bd)) \/
   (ann = BaseT (StringT n) /\ ?m. expr_type src = BaseT (StringT m))) /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty ^E es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty ^E es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `is_bytestring_type ann` by
    (qpat_assum `_ \/ _` strip_assume_tac >> simp[is_bytestring_type_def]) >>
  irule materialized_value_from_vv_mods >>
  qpat_assum `expr_vv_sim_full_mods _ _ _ _ _ _` (irule_at Any) >>
  reverse conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all ordinary_slice_eval_value >> simp[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac ordinary_slice_read_cut >>
  qexists_tac `LocatedValue ann (mk_ptr op LocMemory)` >> asm_rewrite_tac[] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `raw = Value v` SUBST_ALL_TAC >>
  `~is_word_type ann /\ (mk_ptr op LocMemory).ptr_location = LocMemory` by
    simp[valueCopyBytesTheory.is_bytestring_word_type,mk_ptr_def] >>
  `ptr_buf_ok cenv ^E (mk_ptr op LocMemory).ptr_operand G t` by
    (qpat_assum `!b p. LocatedValue _ _ = LocatedValue b p /\ _ ==> ptr_buf_ok _ _ _ _ _`
       (qspecl_then [`ann`,`mk_ptr op LocMemory`] mp_tac) >> simp[]) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) memory_buffer_read_post_mods >>
  gvs[mk_ptr_def,vyperASTTheory.expr_type_def]
QED
