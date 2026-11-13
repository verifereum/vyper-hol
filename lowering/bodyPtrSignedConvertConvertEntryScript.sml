Theory bodyPtrSignedConvertConvertEntry
Ancestors
  bodyPtrPreds exprSimHypsDefs vyperAST vyperTypeSystem exprLowering
  exprSimConvertFromBytes exprSimConvert exprLoweringProps exprOperandVar
  exprSimHyps bodyPtrSignedConvertSourceTyping valueEncoding compileEnv

(* An ill-typed arity never enters either simulation judgment. *)
Theorem convert_arity_body_expr_ptr_ok:
  !cx ann typ args.
    LENGTH args <> 1 ==>
    body_expr_ptr_ok cx (TypeBuiltin ann Convert typ args)
Proof
  rw[body_expr_ptr_ok_def] >>
  fs[expr_body_pre_def, well_typed_expr_def,
     well_typed_type_builtin_args_def]
QED

Theorem zero_capacity_convert_dispatch:
  is_bytestring_type (expr_type e) /\ is_word_type typ /\
  (lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
   lowered_value_type cenv e = BaseT (StringT 0)) /\
  lower_value compile_expr cenv (expr_type e) e sa = (v,sb) ==>
  compile_type_builtin_dispatch_body compile_expr cenv ann ty Convert typ [e] sa =
    (StackValue ann (Lit 0w),sb)
Proof
  simp[compile_type_builtin_dispatch_body_def]
QED

Theorem signed_convert_body_entry:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert typ [e]) es /\
  body_expr_ptr_ok cx e /\ is_bytestring_type (expr_type e) /\
  ((?b. typ = BaseT (IntT b)) \/ typ = BaseT DecimalT) ==>
  ann = typ /\ valid_conversion (expr_type e) typ /\
  well_formed_type env.type_defs typ /\
  expr_body_pre cenv cx env e es /\
  expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es /\
  expr_vv_sim_ptr d ctx PG func cenv cx (expr_type e) e es
Proof
  strip_tac >>
  `ann = typ /\ valid_conversion (expr_type e) typ /\
   well_formed_type env.type_defs typ` by
    (gvs[expr_body_pre_def, well_typed_expr_def,
         well_typed_type_builtin_args_def, type_builtin_result_ok_def] >> metis_tac[]) >>
  drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  qpat_x_assum `body_expr_ptr_ok _ _` mp_tac >>
  simp[body_expr_ptr_ok_def] >> metis_tac[]
QED

Theorem signed_convert_child_compile:
  lower_value compile_expr cenv ty (TypeBuiltin ann Convert typ [e]) sa = (op,sb) /\
  is_bytestring_type (expr_type e) /\
  ((?b. typ = BaseT (IntT b)) \/ typ = BaseT DecimalT) ==>
  ?x s1.
    lower_value compile_expr cenv (expr_type e) e sa = (x,s1) /\
    sa.cs_next_var <= s1.cs_next_var /\
    (if lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
        lowered_value_type cenv e = BaseT (StringT 0)
     then op = Lit 0w /\ sb = s1
     else compile_type_convert x (mk_convert_op (expr_type e) typ) s1 = (op,sb))
Proof
  strip_tac >>
  `is_word_type typ /\ (!n. typ <> FlagT n)` by
    gvs[is_word_type_def] >>
  drule_all lower_value_dynamic_convert >> strip_tac >>
  qexistsl_tac [`x`,`s1`] >> simp[] >>
  drule (cj 2 compile_expr_grows) >> simp[]
QED

Theorem signed_convert_normal_packet:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert typ [e]) es /\
  body_expr_ptr_ok cx e /\ is_bytestring_type (expr_type e) /\
  ((?b. typ = BaseT (IntT b)) \/ typ = BaseT DecimalT) /\
  local_ptrs_reserved cenv sa /\
  lower_value compile_expr cenv ty (TypeBuiltin ann Convert typ [e]) sa = (op,sb) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v, ee) ==>
  ?x s1 tv.
    lower_value compile_expr cenv (expr_type e) e sa = (x,s1) /\
    sa.cs_next_var <= s1.cs_next_var /\
    (!z. x = Var z ==> not_fresh_at s1 z) /\
    expr_body_pre cenv cx env e es /\
    expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
    value_has_type tv v /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv /\
    (if lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
        lowered_value_type cenv e = BaseT (StringT 0)
     then op = Lit 0w /\ sb = s1 /\ (v = BytesV [] \/ v = StringV [])
     else 64 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
          compile_type_convert x (mk_convert_op (expr_type e) typ) s1 = (op,sb))
Proof
  strip_tac >> (
  `expr_body_pre cenv cx env e es /\
   expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es` by
    metis_tac[signed_convert_body_entry] >>
  mp_tac signed_convert_child_compile >>
  disch_then (drule_at (Pos hd)) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  drule_all body_source_read_lowered_layout >> strip_tac >>
  qexistsl_tac [`x`,`s1`,`tv`] >> simp[] >>
  conj_tac >- metis_tac[compile_lower_value_var] >>
  Cases_on `lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
            lowered_value_type cenv e = BaseT (StringT 0)`
  >- (gvs[] >> metis_tac[body_source_lowered_zero_empty]) >>
  gvs[] >>
  qpat_x_assum `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _` kall_tac >>
  mp_tac body_source_lowered_nonzero_capacity >>
  (impl_tac >- asm_rewrite_tac[]) >> simp[])
QED
