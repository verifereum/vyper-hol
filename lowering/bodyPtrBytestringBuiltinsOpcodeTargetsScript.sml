Theory bodyPtrBytestringBuiltinsOpcodeTargets
Ancestors bodyPtrBytestringBuiltinsOpcodeExpressions
          bodyPtrBytestringBuiltinsOpcodeSubscript
          bodyPtrBytestringBuiltinsOpcodeValues
          bodyPtrBytestringBuiltinsOpcodeState
          exprLowering supportedStmts supportedTargets supportedExprs vyperAST
Libs BasicProvers

Theorem no_extcode_name_target:
  !cfn ce id s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_get_target_ptr cfn ce (NameTarget id) s))
Proof
  rpt strip_tac >> simp[compile_get_target_ptr_def] >>
  TOP_CASE_TAC >> simp[no_extcode_fresh_ops] >>
  TOP_CASE_TAC >> simp[no_extcode_fresh_ops]
QED

Theorem no_extcode_subscript_target:
  !cfn ce bt idx.
    (!s. compiler_no_extcode s ==>
      compiler_no_extcode (SND (compile_get_target_ptr cfn ce bt s))) /\
    (!s. compiler_no_extcode s ==>
      compiler_no_extcode (SND (cfn ce (expr_type idx) idx s))) ==>
    !s. compiler_no_extcode s ==>
      compiler_no_extcode (SND (compile_get_target_ptr cfn ce (SubscriptTarget bt idx) s))
Proof
  rpt strip_tac >> simp[compile_get_target_ptr_def] >>
  irule no_extcode_bind >> simp[] >> rpt gen_tac >> strip_tac >>
  namedCases_on `SND (SND x)` ["", "pt"] >> simp[] >>
  TRY (Cases_on `pt` >> simp[]) >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_lower_value, no_extcode_keccak256_key,
      no_extcode_mapping_subscript, no_extcode_array_subscript,
      no_extcode_ptr_load, no_extcode_fresh_ops])
QED

Theorem no_extcode_attribute_target:
  !cfn ce bt field.
    (!s. compiler_no_extcode s ==>
      compiler_no_extcode (SND (compile_get_target_ptr cfn ce bt s))) ==>
    !s. compiler_no_extcode s ==>
      compiler_no_extcode (SND (compile_get_target_ptr cfn ce (AttributeTarget bt field) s))
Proof
  rpt strip_tac >> simp[compile_get_target_ptr_def] >>
  irule no_extcode_bind >> simp[] >> rpt gen_tac >> strip_tac >>
  irule no_extcode_bind >> simp[no_extcode_emit_op, no_extcode_fresh_ops]
QED

Theorem no_extcode_target_info:
  !bt tops bindings ce s.
    IS_SOME (supported_target_info tops bindings bt) /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_get_target_ptr compile_expr ce bt s))
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >> rpt gen_tac >>
  simp[no_extcode_name_target, no_extcode_toplevel_target] >>
  strip_tac >>
  gvs[supported_target_info_def, optionTheory.IS_SOME_EXISTS, AllCaseEqs()] 
  >> FIRST [irule no_extcode_subscript_target, irule no_extcode_attribute_target] >>
  simp[] >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >> TRY (rename1 `compiler_no_extcode (SND (compile_expr _ _ _ _))` >>
    irule no_extcode_compile_expr_supported >> simp[] >>
    qexists_tac `tops` >> gvs[supported_expr_def] >> NO_TAC) >>
  first_x_assum (qspec_then `b` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`tops`, `bindings`] mp_tac) >> simp[]
QED

Theorem no_extcode_target_supported:
  !tops bindings bt ce s.
    (supported_target tops bindings bt \/
     IS_SOME (supported_target_info tops bindings bt)) /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_get_target_ptr compile_expr ce bt s))
Proof
  rpt gen_tac >> strip_tac
  >- (Cases_on `bt` >> gvs[supported_target_def] >>
      simp[no_extcode_name_target, no_extcode_toplevel_target] >>
      TRY (rename1 `compile_get_target_ptr _ _ (SubscriptTarget bt idx)` >>
        Cases_on `bt` >> gvs[] >> irule no_extcode_subscript_target >>
        simp[no_extcode_toplevel_target] >> rpt strip_tac >>
        irule no_extcode_compile_expr_supported >> simp[] >>
        qexists_tac `tops` >> gvs[supported_expr_def] >> NO_TAC) >>
      Cases_on `b` >> gvs[] >> irule no_extcode_attribute_target >>
      simp[no_extcode_toplevel_target]) >>
  irule no_extcode_target_info >> simp[] >> metis_tac[]
QED
