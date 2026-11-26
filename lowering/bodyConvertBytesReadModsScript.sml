(* Forcing a bytestring Convert preserves the materialized memory result. *)
Theory bodyConvertBytesReadMods
Ancestors
  bodyAggregateReadMods bodyAggregateReadPostMods bodyFullShared
  exprSimConvert exprLowering compileEnv valueCopyBytes
  gasShadowCompileStmtHelpers gasShadowState context
Libs monadsyntax

Theorem bytes_convert_read_cut[local]:
  ~is_word_type dst /\
  (!sa. ?out sb. compile_expr ce ty e sa =
    (LocatedValue dst (mk_ptr out LocMemory),sb)) /\
  lower_value compile_expr ce ty e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha =
    (op,shb) /\ gas_shadow_state sa sha ==>
  compile_expr ce ty e sa = (LocatedValue dst (mk_ptr op LocMemory),sb) /\
  compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha =
    (LocatedValue dst (mk_ptr op LocMemory),shb)
Proof
  strip_tac >>
  qpat_x_assum `!sa. ?out sb. _` (qspec_then `sa` strip_assume_tac) >>
  Cases_on `compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha` >>
  rename1 `_ = (shadow_vv,shadow_end)` >>
  `gas_shadow_compiles (compile_expr ce ty e)
     (compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e))` by
    MATCH_ACCEPT_TAC gas_shadow_stmt_compile_expr_env >>
  drule_all_then strip_assume_tac gas_shadow_step >>
  qpat_x_assum `shadow_vv = _` SUBST_ALL_TAC >>
  qpat_x_assum `lower_value compile_expr ce ty e sa = _` mp_tac >>
  qpat_x_assum `lower_value compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def, unwrap_value_def, mk_ptr_def,
       comp_return_def] >>
  rpt strip_tac >> simp[]
QED

Theorem bytes_convert_read_mods:
  is_bytestring_type dst /\
  (!sa. ?out sb. compile_expr ce ty (TypeBuiltin dst Convert dst [e]) sa =
    (LocatedValue dst (mk_ptr out LocMemory),sb)) /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (TypeBuiltin dst Convert dst [e]) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (TypeBuiltin dst Convert dst [e]) es
Proof
  strip_tac >>
  `~is_word_type dst` by simp[valueCopyBytesTheory.is_bytestring_word_type] >>
  irule materialized_value_from_vv_mods >>
  qpat_assum `expr_vv_sim_full_mods _ _ _ _ _ _` (irule_at Any) >>
  reverse conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_then ACCEPT_TAC eval_expr_type_builtin_value) >>
  rpt gen_tac >> strip_tac >> drule_all_then strip_assume_tac bytes_convert_read_cut >>
  qexists_tac `LocatedValue dst (mk_ptr op LocMemory)` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `(mk_ptr op LocMemory).ptr_location = LocMemory` by simp[mk_ptr_def] >>
  `ptr_buf_ok ce (TypeBuiltin dst Convert dst [e]) (mk_ptr op LocMemory).ptr_operand G t` by
    (qpat_assum `_ ==> ptr_buf_ok _ _ _ _ _` (drule_then ACCEPT_TAC)) >>
  drule_all_then strip_assume_tac
    (SRULE [] (Q.INST [`e` |-> `TypeBuiltin dst Convert dst [e]`]
      memory_buffer_read_post_mods)) >>
  fs[mk_ptr_def]
QED
