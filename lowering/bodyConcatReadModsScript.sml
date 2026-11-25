(* Forcing a Concat result reuses its materialized buffer and landing. *)
Theory bodyConcatReadMods
Ancestors
  bodyAggregateReadMods bodyAggregateReadPostMods bodyFullShared
  bodyFullPostsMods exprSimHyps exprSimConcatResult exprLowering
  gasShadowCompile gasShadowState compileEnv context vyperInterpreter vyperState
Libs monadsyntax

Theorem concat_unwrap_buffer[local]:
  ~is_word_type a ==>
  unwrap_value cenv (LocatedValue a (base_ptr buf)) s = (buf.buf_operand,s)
Proof
  simp[unwrap_value_def,base_ptr_def,comp_return_def]
QED

Theorem concat_read_compile_cut[local]:
  lower_value compile_expr cenv ty (Builtin a (Concat n) args) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin a (Concat n) args)) sha = (op,shb) /\
  ~is_word_type a /\ gas_shadow_state sa sha ==>
  ?buf.
    compile_expr cenv ty (Builtin a (Concat n) args) sa =
      (LocatedValue a (base_ptr buf),sb) /\
    compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr (Builtin a (Concat n) args)) sha =
      (LocatedValue a (base_ptr buf),shb) /\ op = buf.buf_operand
Proof
  strip_tac >>
  Cases_on `compile_expr cenv ty (Builtin a (Concat n) args) sa` >>
  drule_then strip_assume_tac concat_compile_shape >>
  Cases_on `compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin a (Concat n) args)) sha` >>
  `gas_shadow_compiles (compile_expr cenv ty (Builtin a (Concat n) args))
    (compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr (Builtin a (Concat n) args)))` by
    irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
           Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
  drule_all_then strip_assume_tac gas_shadow_step >>
  gvs[lower_value_def,comp_bind_def,concat_unwrap_buffer] >>
  qexists_tac `buf` >> simp[]
QED

Theorem concat_eval_returns_value[local]:
  2 <= LENGTH args /\ eval_expr cx (Builtin a (Concat n) args) es = (INL raw,ee) ==>
  ?v. raw = Value v
Proof
  strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[eval_expr_concat_bind,bind_def,AllCaseEqs()] >>
  metis_tac[]
QED

Theorem concat_buffer_read_mods:
  2 <= LENGTH args /\
  (a = BaseT (BytesT (Dynamic n)) \/ a = BaseT (StringT n)) /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin a (Concat n) args) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin a (Concat n) args) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~is_word_type a` by fs[is_word_type_def] >>
  irule materialized_value_from_vv_mods >>
  asm_rewrite_tac[] >> reverse conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all_then ACCEPT_TAC concat_eval_returns_value) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choose_then `buf` strip_assume_tac) concat_read_compile_cut >>
  qexists_tac `LocatedValue a (base_ptr buf)` >> asm_rewrite_tac[] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `raw = Value v` SUBST_ALL_TAC >>
  qpat_x_assum `op = buf.buf_operand` SUBST_ALL_TAC >>
  `(base_ptr buf).ptr_location = LocMemory` by simp[base_ptr_def] >>
  `ptr_buf_ok cenv (Builtin a (Concat n) args) (base_ptr buf).ptr_operand G t` by
    (qpat_assum `!b p. LocatedValue _ _ = LocatedValue b p /\ _ ==> ptr_buf_ok _ _ _ _ _`
       (qspecl_then [`a`,`base_ptr buf`] mp_tac) >> simp[]) >>
  drule_all memory_buffer_read_post_mods >>
  fs[base_ptr_def]
QED
