(* TOP-LEVEL: checked event-compatible field pairs supply physical
   strides and target value typing for tuple-copy composition. *)
Theory typedFieldsTypes
Ancestors
  vyperEventArgCompat
  typedCopyTypeContract typeLayoutProps typedCopyProducer vyperEventCompatibility
  compileVyper compileEnv vyperTypeContract vyperContext vyperTypeSystem vyperValue

Theorem checked_typed_field_pair:
  !tops in_deploy layouts addr art ctx func cenv fty aty ftv atv.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\ event_arg_compatible fty aty /\
    evaluate_type (type_env tops) fty = SOME ftv /\ evaluate_type (type_env tops) aty = SOME atv /\
    (!target_tv source_tv.
      evaluate_type (type_env tops) fty = SOME target_tv /\
      evaluate_type (type_env tops) aty = SOME source_tv ==>
      typed_copy_type_contract ctx func cenv fty aty target_tv source_tv) ==>
    type_memory_bytes cenv fty = type_memory_size ftv /\
    type_memory_bytes cenv aty = type_memory_size atv /\
    (!v. value_has_type atv v ==> value_has_type ftv v) /\
    typed_copy_type_contract ctx func cenv fty aty ftv atv
Proof
  rpt gen_tac >> strip_tac >>
  drule checked_contract_struct_args_unique >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tops`, `cenv`, `fty`, `ftv`] type_memory_bytes_evaluated) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tops`, `cenv`, `aty`, `atv`] type_memory_bytes_evaluated) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`fty`, `aty`] (CONJUNCT1 event_arg_compatible_value_has_type)) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >>
  disch_then (qspecl_then [`type_env tops`, `ftv`, `atv`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  asm_rewrite_tac [] >> first_x_assum irule >> simp[]
QED
