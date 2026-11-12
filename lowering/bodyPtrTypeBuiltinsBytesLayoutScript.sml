Theory bodyPtrTypeBuiltinsBytesLayout
Ancestors exprSimConvertBytes exprSimConvertFromBytes exprLoweringProps
  exprBopLowering externalEntryShape exprLowering compileEnv

Theorem lower_value_bytestring_convert_parts:
  lower_value compile_expr cenv ty (TypeBuiltin ann Convert dst [e]) ca = (out,cb) /\
  is_bytestring_type (expr_type e) /\
  (is_bytestring_type dst \/ (is_word_type dst /\ !n. dst <> FlagT n)) ==>
  ?x sa. lower_value compile_expr cenv (expr_type e) e ca = (x,sa) /\
    (if is_bytestring_type dst then
       if type_memory_bytes cenv (lowered_value_type cenv e) < type_memory_bytes cenv dst
       then compile_bytestring_widen_copy (type_memory_bytes cenv dst) x
         (type_memory_bytes cenv (lowered_value_type cenv e)) sa = (out,cb)
       else compile_type_convert x (mk_convert_op (expr_type e) dst) sa = (out,cb)
     else if lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
             lowered_value_type cenv e = BaseT (StringT 0)
     then out = Lit 0w /\ cb = sa
     else compile_type_convert x (mk_convert_op (expr_type e) dst) sa = (out,cb))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> Cases_on `is_bytestring_type dst`
  >- (qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
      simp[Once lower_value_def, comp_bind_def, compile_convert_bytestring_shape] >>
      rpt (pairarg_tac >> gvs[]) >>
      Cases_on `type_memory_bytes cenv (lowered_value_type cenv e) < type_memory_bytes cenv dst` >>
      gvs[] >> rpt (pairarg_tac >> gvs[]) >>
      gvs[as_stack_val_pair, unwrap_value_def, comp_return_def, pairTheory.PAIR_FST_SND_EQ] >>
      metis_tac[]) >>
  gvs[] >> drule_all lower_value_dynamic_convert >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem bytestring_convert_suffix_extends:
  (if is_bytestring_type dst then
     if type_memory_bytes cenv (lowered_value_type cenv e) < type_memory_bytes cenv dst
     then compile_bytestring_widen_copy (type_memory_bytes cenv dst) x
       (type_memory_bytes cenv (lowered_value_type cenv e)) sa = (out,cb)
     else compile_type_convert x (mk_convert_op (expr_type e) dst) sa = (out,cb)
   else if lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
           lowered_value_type cenv e = BaseT (StringT 0)
   then out = Lit 0w /\ cb = sa
   else compile_type_convert x (mk_convert_op (expr_type e) dst) sa = (out,cb)) ==>
  cs_extends sa cb
Proof
  rpt IF_CASES_TAC >> strip_tac >> gvs[] >>
  metis_tac[cj 1 compile_bytestring_widen_copy_labels, cj 1 compile_type_convert_labels,
    cs_extends_refl, pairTheory.SND]
QED
