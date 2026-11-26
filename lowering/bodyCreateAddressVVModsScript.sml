(* Creation produces a stack address, so the linked forced judgment can be
   unforced without a second execution. *)
Theory bodyCreateAddressVVMods
Ancestors
  bodyScalarStackVVMods exprBodyPreProps loweringPosts compileEnv
  exprSimSend exprLowering builtinCreate vyperInterpreter vyperCreate
  vyperLocalAccessFrame vyperTypeSystem vyperState vyperAST

Theorem create_address_vv_sim_full_mods:
  expr_body_pre_mods mods cenv cx env
    (Call ann (CreateTarget kind salted rof ks) args dflt) es /\
  expr_sim_full_mods (DF,lo,d,ctx,sh,PG,f,sf) cenv cx ty
    (Call ann (CreateTarget kind salted rof ks) args dflt) es ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,sh,PG,f,sf) cenv cx ty
    (Call ann (CreateTarget kind salted rof ks) args dflt) es
Proof
  strip_tac >>
  `ann = BaseT AddressT` by
    (drule expr_body_pre_mods_well_typed >> simp[Once well_typed_expr_def]) >>
  irule scalar_stack_vv_sim_full_mods >>
  simp[post_value_type_def, expr_type_def, is_word_type_def] >>
  conj_tac
  >- (gen_tac >> simp[compile_expr_call, compile_call_def, as_stack_val_def] >>
      Cases_on `compile_create_call compile_expr cenv kind salted rof args sa` >>
      simp[as_stack_val_def]) >>
  rpt gen_tac >> simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_exprs cx (create_operand_order kind salted args) s` >>
  rename1 `eval_exprs _ _ _ = (res, mid)` >>
  Cases_on `res` >> simp[] >>
  metis_tac[eval_create_operands_success_value]
QED
