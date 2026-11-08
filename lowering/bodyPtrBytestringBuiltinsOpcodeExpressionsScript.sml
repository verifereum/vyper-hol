Theory bodyPtrBytestringBuiltinsOpcodeExpressions
Ancestors bodyPtrBytestringBuiltinsOpcodeBodies
          bodyPtrBytestringBuiltinsOpcodeCallbacks
          bodyPtrBytestringBuiltinsOpcodeBuiltinBody
          bodyPtrBytestringBuiltinsOpcodeTypeBody exprLowering supportedExprs list

Theorem no_extcode_compile_weighted[local]:
  !n.
  (!tops ce ty e s. 2 * expr_size e + 2 = n /\
    (supported_pure_expr tops e \/ supported_place_expr tops e \/
     supported_effect_expr tops e \/ supported_effect_place_expr tops e) /\
    compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_expr ce ty e s))) /\
  (!tops ce rt ty bi es s. 2 * list_size expr_size es + 1 = n /\
    supported_builtin_form tops rt bi es /\ supported_pure_exprs tops es /\
    compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_builtin_dispatch ce rt ty bi es s))) /\
  (!tops ce vt ty tb rt es s. 2 * list_size expr_size es + 1 = n /\
    supported_type_builtin_form tops vt tb rt es /\ supported_pure_exprs tops es /\
    compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_type_builtin_dispatch ce vt ty tb rt es s)))
Proof
  completeInduct_on `n` >> rpt conj_tac >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)
  >- (once_rewrite_tac[compile_expr_raw_def] >>
      irule no_extcode_expr_body_supported >>
      simp[] >> qexists_tac `tops` >> simp[] >> rpt conj_tac >>
      rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
      IF_CASES_TAC >>
      simp[no_extcode_invalid_expr_call]
      >- (first_x_assum (qspec_then `2 * expr_size a + 2` mp_tac) >>
          simp[] >> metis_tac[])
      >- (first_x_assum (qspec_then `2 * list_size expr_size es + 1` mp_tac) >>
          simp[] >> metis_tac[]) >>
      first_x_assum (qspec_then `2 * list_size expr_size es + 1` mp_tac) >>
      simp[] >> metis_tac[])
  >- (once_rewrite_tac[compile_expr_raw_def] >>
      irule no_extcode_builtin_body_supported >> simp[] >>
      reverse conj_tac >- (qexists_tac `tops` >> simp[]) >>
      rpt gen_tac >> strip_tac >> IF_CASES_TAC >>
      simp[no_extcode_invalid_expr_call] >>
      first_x_assum (qspec_then `2 * expr_size e + 2` mp_tac) >>
      simp[] >> gvs[supported_pure_exprs_every, EVERY_MEM] >> metis_tac[])
  >> once_rewrite_tac[compile_expr_raw_def] >> simp[] >>
  irule no_extcode_type_body_supported >> simp[] >>
  reverse conj_tac >- (qexists_tac `tops` >> simp[]) >>
      rpt gen_tac >> strip_tac >> IF_CASES_TAC >>
      simp[no_extcode_invalid_expr_call] >>
      first_x_assum (qspec_then `2 * expr_size e + 2` mp_tac) >>
      simp[] >> gvs[supported_pure_exprs_every, EVERY_MEM] >> metis_tac[]
QED

Theorem no_extcode_compile_expr_supported:
  !tops ce ty e s.
    (supported_pure_expr tops e \/ supported_place_expr tops e \/
     supported_effect_expr tops e \/ supported_effect_place_expr tops e) /\
    compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_expr ce ty e s))
Proof
  rpt strip_tac >>
  qspec_then `2 * expr_size e + 2` mp_tac no_extcode_compile_weighted >>
  metis_tac[]
QED

Theorem no_extcode_compile_builtin_supported:
  !tops ce rt ty bi es s.
    supported_builtin_form tops rt bi es /\ supported_pure_exprs tops es /\
    compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_builtin_dispatch ce rt ty bi es s))
Proof
  rpt strip_tac >>
  qspec_then `2 * list_size expr_size es + 1` mp_tac no_extcode_compile_weighted >>
  metis_tac[]
QED

Theorem no_extcode_compile_type_builtin_supported:
  !tops ce vt ty tb rt es s.
    supported_type_builtin_form tops vt tb rt es /\ supported_pure_exprs tops es /\
    compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_type_builtin_dispatch ce vt ty tb rt es s))
Proof
  rpt strip_tac >>
  qspec_then `2 * list_size expr_size es + 1` mp_tac no_extcode_compile_weighted >>
  metis_tac[]
QED
