(* Lowering layout and capacity-preserving bytestring destination lifting. *)
Theory bodyMemTbConvertDestLift
Ancestors
  bodyMemTbConvertDestSummary bodyMemTbConvertDynamicLift
  exprSimConvertBytes exprLoweringProps exprOperandVar compileEnv
  exprSimMemDefs exprSimHyps exprSimHypsDefs exprSimDefs exprLowering
  loweringSlice freshWrites fragExec rich_list valueCopyBytes context

Theorem bytestring_convert_mem_layout[local]:
  lower_value compile_expr cenv ty (TypeBuiltin ann Convert dst [e]) sa = (op,sb) /\
  valid_conversion (expr_type e) dst /\
  is_bytestring_type dst /\ is_bytestring_type (expr_type e) /\
  is_bytestring_type (lowered_value_type cenv e) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa ==>
  ?x s1.
    lower_value compile_expr cenv (expr_type e) e sa = (x,s1) /\
    (if type_memory_bytes cenv (lowered_value_type cenv e) < type_memory_bytes cenv dst
     then compile_bytestring_widen_copy (type_memory_bytes cenv dst) x
            (type_memory_bytes cenv (lowered_value_type cenv e)) s1
     else compile_type_convert x (mk_convert_op (expr_type e) dst) s1) = (op,sb) /\
    cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
    sa.cs_next_id <= s1.cs_next_id /\
    cs_extends s1 sb /\ s1.cs_next_var <= sb.cs_next_var /\
    fn_has_code sa s1 func /\ fn_has_code s1 sb func /\
    local_ptrs_reserved cenv s1 /\
    (!z. x = Var z ==> not_fresh_at s1 z)
Proof
  strip_tac >> drule_all lower_value_convert_bytestring >> strip_tac >> gvs[] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `cs_extends s1 sb /\ s1.cs_next_var <= sb.cs_next_var /\
   s1.cs_next_id <= sb.cs_next_id` by
    (Cases_on `type_memory_bytes cenv (lowered_value_type cenv e) < type_memory_bytes cenv dst`
     >- (gvs[] >>
         `0 < type_memory_bytes cenv (lowered_value_type cenv e)` by
           metis_tac[bytestring_memory_bytes_positive] >>
         drule_all convert_widen_copy_parts >> strip_tac >>
         `ci_mono s1 mid` by
           metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
         `ci_mono mid sb` by
           metis_tac[ci_mono_emit_void, pairTheory.SND] >>
         gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
     gvs[] >> metis_tac[convert_bytestring_suffix_grows]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!z. x = Var z ==> not_fresh_at s1 z` by
    metis_tac[compile_lower_value_var] >>
  simp[]
QED
