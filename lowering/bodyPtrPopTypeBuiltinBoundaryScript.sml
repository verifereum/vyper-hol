Theory bodyPtrPopTypeBuiltinBoundary
Ancestors bodyPtrPopTypeWrapperBoundary bodyPtrPopConversionBoundary
  bodyPtrPopMaterialization bodyPtrPopAllocationBoundary
  bodyPtrPopCompileDomain bodyPtrPopBuiltinBoundary bodyPtrPopCompilerBoundary
  exprLowering supportedExprForms compileEnv emitHelper list

Theorem pop_convert_dispatch_boundary:
  (!aty s v t. pop_comp_boundary s /\ cfn cenv aty a s = (v,t) ==>
    pop_comp_boundary t) /\ pop_comp_boundary sa /\
  compile_type_builtin_dispatch_body cfn cenv vt ty Convert rt [a] sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_type_builtin_dispatch_body_def] >> rpt strip_tac >>
  pairarg_tac >> gnvs[] >>
  `pop_comp_boundary st1` by
    (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
     disch_then irule >> simp[] >> rpt strip_tac >>
     first_x_assum drule_all >> simp[]) >>
  qpat_x_assum `!aty s v t. _` kall_tac >>
  Cases_on `is_bytestring_type (expr_type a) /\ is_word_type rt /\
    (lowered_value_type cenv a = BaseT (BytesT (Dynamic 0)) \/
     lowered_value_type cenv a = BaseT (StringT 0))` >> gnvs[] >>
  Cases_on `is_bytestring_type (expr_type a) /\ is_bytestring_type rt /\
    type_memory_bytes cenv (lowered_value_type cenv a) < type_memory_bytes cenv rt` >> gnvs[]
  >- (Cases_on `compile_bytestring_widen_copy (type_memory_bytes cenv rt) v
        (type_memory_bytes cenv (lowered_value_type cenv a)) st1` >>
      gnvs[as_stack_val_def] >> drule_all pop_compile_bytestring_widen_copy_boundary >> simp[]) >>
  Cases_on `rt` >> gnvs[] >>
  qmatch_asmsub_abbrev_tac `compile_type_convert v cv st1` >>
  Cases_on `compile_type_convert v cv st1` >> gnvs[as_stack_val_def] >>
  drule_all pop_compile_type_convert_boundary >> simp[]
QED

Theorem pop_empty_dispatch_boundary:
  pop_comp_boundary sa /\
  compile_type_builtin_dispatch_body cfn cenv vt ty Empty rt args sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `is_word_type rt` >> simp[compile_type_builtin_dispatch_body_def] >>
  rpt strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  drule_all pop_compile_builtin_empty_complex_boundary >> simp[]
QED

Theorem pop_constant_type_dispatch_boundary:
  (tb = MaxValue \/ tb = MinValue \/ tb = Epsilon) /\ pop_comp_boundary sa /\
  compile_type_builtin_dispatch_body cfn cenv vt ty tb rt args sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  strip_tac >> gvs[compile_type_builtin_dispatch_body_def] >>
  Cases_on `type_bounds rt` >> gvs[]
QED

Theorem pop_decode_dispatch_boundary:
  (!aty s v t. pop_comp_boundary s /\ cfn cenv aty a s = (v,t) ==>
    pop_comp_boundary t) /\ pop_comp_boundary sa /\
  compile_type_builtin_dispatch_body cfn cenv vt ty (AbiDecode unwrap) rt [a] sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_type_builtin_dispatch_body_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st1` by (first_x_assum drule_all >> simp[]) >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st2` by (drule_all pop_unwrap_value_boundary >> simp[]) >>
  qmatch_asmsub_abbrev_tac `lower_abi_decode data_op info amin amax sz st2` >>
  Cases_on `lower_abi_decode data_op info amin amax sz st2` >> gvs[as_ptr_val_def] >>
  drule_all pop_lower_abi_decode_boundary >> simp[]
QED

Theorem pop_encode_single_dispatch_boundary:
  (!aty s v t. pop_comp_boundary s /\ cfn cenv aty a s = (v,t) ==>
    pop_comp_boundary t) /\ pop_comp_boundary sa /\
  compile_type_builtin_dispatch_body cfn cenv vt ty (AbiEncode F mid) rt [a] sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_type_builtin_dispatch_body_def] >> rpt strip_tac >>
  Cases_on `is_word_type (expr_type a)` >> gvs[]
  >- (pairarg_tac >> gvs[] >>
      `pop_comp_boundary st1` by
        (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
         disch_then irule >> simp[] >> rpt strip_tac >>
         first_x_assum drule_all >> simp[]) >>
      pairarg_tac >> gvs[] >>
      `pop_comp_boundary st2` by (drule_all pop_compile_alloc_buffer_boundary >> simp[]) >>
      pairarg_tac >> gvs[] >>
      `pop_comp_boundary st3` by
        (drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]) >>
      qmatch_asmsub_abbrev_tac `lower_abi_encode F method tmp info maxlen st3` >>
      Cases_on `lower_abi_encode F method tmp info maxlen st3` >> gvs[as_ptr_val_def] >>
      drule_all pop_lower_abi_encode_boundary >> simp[]) >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st1` by (first_x_assum drule_all >> simp[]) >>
  pairarg_tac >> gvs[] >>
  `pop_comp_boundary st2` by (drule_all pop_unwrap_value_boundary >> simp[]) >>
  qmatch_asmsub_abbrev_tac `lower_abi_encode F method src_op info maxlen st2` >>
  Cases_on `lower_abi_encode F method src_op info maxlen st2` >> gvs[as_ptr_val_def] >>
  drule_all pop_lower_abi_encode_boundary >> simp[]
QED

Theorem pop_supported_type_builtin_arity:
  supported_type_builtin_form tops vt tb rt args ==> LENGTH args <= 1
Proof
  Cases_on `args` >- simp[] >> rename1 `h::rest` >>
  Cases_on `rest` >- simp[] >>
  Cases_on `tb` >> simp[supported_type_builtin_form_def]
QED

Theorem pop_type_builtin_dispatch_boundary:
  supported_type_builtin_form tops vt tb rt args /\
  (!a aty s v t. MEM a args /\ pop_comp_boundary s /\
    cfn cenv aty a s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  compile_type_builtin_dispatch_body cfn cenv vt ty tb rt args sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  strip_tac >> drule pop_supported_type_builtin_arity >> strip_tac >>
  Cases_on `args`
  >- (Cases_on `tb` >> gvs[supported_type_builtin_form_def] >>
      FIRST [drule_all pop_empty_dispatch_boundary,
             drule_at (Pat `compile_type_builtin_dispatch_body _ _ _ _ _ _ _ _ = _`)
               pop_constant_type_dispatch_boundary] >> simp[]) >>
  rename1 `h::rest` >> Cases_on `rest` >> gvs[] >>
  Cases_on `tb` >> gvs[supported_type_builtin_form_def, AllCaseEqs()]
  >~ [`compile_type_builtin_dispatch_body _ _ _ _ (AbiEncode b mid) _ _ _ = _`]
  >- (Cases_on `mid` >> gvs[] >> drule_all pop_encode_single_dispatch_boundary >> simp[]) >>
  FIRST [drule_all pop_convert_dispatch_boundary,
         drule_all pop_decode_dispatch_boundary] >> simp[]
QED

Theorem pop_type_builtin_open_boundary:
  !cfn.
  (!cenv ty e sa r sb. pop_compile_domain tops e /\ pop_comp_boundary sa /\
    cfn cenv ty e sa = (r,sb) ==> pop_comp_boundary sb) ==>
  !cenv vt ty tb rt args sa r sb.
  supported_type_builtin_form tops vt tb rt args /\
  EVERY (supported_pure_expr tops) args /\ pop_comp_boundary sa /\
  compile_type_builtin_dispatch_body cfn cenv vt ty tb rt args sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  rpt strip_tac >>
  drule_at (Pat `compile_type_builtin_dispatch_body _ _ _ _ _ _ _ _ = _`)
    pop_type_builtin_dispatch_boundary >> disch_then irule >> simp[] >>
  reverse conj_tac >- (qexists `tops` >> simp[]) >>
  rpt strip_tac >> drule_all pop_domain_pure_argument >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED
