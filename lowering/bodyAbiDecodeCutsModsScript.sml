(* The real and shadow compilation cuts for a single ABI decode operand. *)
Theory bodyAbiDecodeCutsMods
Ancestors
  exprSimHyps exprSimUnwrap exprSimAbiDecodeOblivious exprLowering exprLoweringProps
  compileEnv builtinAbi fragExec gasShadow gasShadowState
  gasShadowCompileBase gasShadowCompileStmtHelpers vyperAST vyperABI

Theorem abi_decode_compile_cuts[local]:
  compile_expr ce cty (TypeBuiltin ty (AbiDecode unwrap) ty [e]) sa = (vv,sb) /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\ fn_has_code sa sb fn ==>
  let wty = if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty in
  ?data start out.
    lower_value compile_expr ce (expr_type e) e sa = (data,start) /\
    lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce wty)
      (abi_static_size ce.ce_struct_fields wty)
      (abi_size_bound ce.ce_struct_fields wty)
      (type_memory_bytes ce wty) start = (out,sb) /\
    vv = LocatedValue ty (mk_ptr out LocMemory) /\
    fn_has_code sa start fn /\ fn_has_code start sb fn
Proof
  simp[LET_THM] >> strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_type_builtin_dispatch,
       Once (cj 3 compile_expr_raw_def), compile_type_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[oneline as_ptr_val_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `unwrap_value ce evv sm = (data,start)` >>
  drule_then strip_assume_tac (cj 1 compile_expr_extends) >>
  drule_then strip_assume_tac unwrap_value_extends >>
  `cs_extends sa start` by metis_tac[cs_extends_trans] >>
  drule_then strip_assume_tac lower_abi_decode_frag_facts >>
  drule_all_then strip_assume_tac fn_has_code_split >>
  simp[lower_value_def, comp_bind_def] >> metis_tac[]
QED

Theorem abi_decode_paired_cuts_mods:
  compile_expr ce cty (TypeBuiltin ty (AbiDecode unwrap) ty [e]) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T ce) cty
    (gas_shadow_expr (TypeBuiltin ty (AbiDecode unwrap) ty [e])) sha = (vv,shb) /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\ gas_shadow_state sa sha /\
  fn_has_code sa sb fn /\ fn_has_code sha shb shfn ==>
  let wty = if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty in
  ?data start shstart out.
    lower_value compile_expr ce (expr_type e) e sa = (data,start) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
      (gas_shadow_expr e) sha = (data,shstart) /\
    lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce wty)
      (abi_static_size ce.ce_struct_fields wty)
      (abi_size_bound ce.ce_struct_fields wty)
      (type_memory_bytes ce wty) start = (out,sb) /\
    lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce wty)
      (abi_static_size ce.ce_struct_fields wty)
      (abi_size_bound ce.ce_struct_fields wty)
      (type_memory_bytes ce wty) shstart = (out,shb) /\
    vv = LocatedValue ty (mk_ptr out LocMemory) /\ gas_shadow_state start shstart /\
    fn_has_code sa start fn /\ fn_has_code start sb fn /\
    fn_has_code sha shstart shfn /\ fn_has_code shstart shb shfn
Proof
  simp[LET_THM] >> strip_tac >>
  drule_all_then strip_assume_tac abi_decode_compile_cuts >>
  gvs[LET_THM] >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (assume_tac o SIMP_RULE (srw_ss()) [gas_shadow_expr_def]) >>
  `expr_type (gas_shadow_expr e) = BaseT (BytesT (Dynamic n))` by simp[] >>
  drule_all_then strip_assume_tac abi_decode_compile_cuts >>
  gvs[LET_THM] >>
  drule (REWRITE_RULE [gas_shadow_compiles_def]
    (Q.INST [`ty` |-> `expr_type e`, `sd` |-> `T`, `cenv` |-> `ce`]
      gas_shadow_stmt_lower_value_env)) >>
  disch_then (qspecl_then [`e`,`ce`] mp_tac) >>
  simp[] >> strip_tac >> gvs[contextTheory.mk_ptr_def]
QED
