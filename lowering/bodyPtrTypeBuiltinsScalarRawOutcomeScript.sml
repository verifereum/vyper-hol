Theory bodyPtrTypeBuiltinsScalarRawOutcome
Ancestors
  bodyPtrTypeBuiltinsScalarSemantic bodyPtrTypeBuiltinsIntegerSemantic
  exprLowering exprLoweringProps compileEnv venomExecSemantics exprSimDefs
  valueEncoding loweringPosts

Theorem scalar_identity_actual_outcome:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  (case dst of FlagT name =>
    ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op src dst) = ConvIdentity /\
  evaluate_type (get_tenv cx) src = SOME tv /\ value_has_type tv v /\
  evaluate_type (get_tenv cx) dst = SOME tout /\
  compile_type_convert x ConvIdentity sa = (out,sb) /\
  eval_operand x s = SOME (typed_val_to_w256 tv v) ==>
  ?t vout. run_inst_seq (emitted_insts sa sb) s = OK t /\
    convert_result cx src dst v = INL vout /\ expr_val_rel cx dst vout out t
Proof
  strip_tac >> drule_all scalar_identity_semantic_packet >> strip_tac >>
  `is_word_type dst` by (irule (cj 2 scalar_source_word_types) >> metis_tac[optionTheory.IS_SOME_DEF]) >>
  gvs[compile_type_convert_def, comp_return_def, emitted_insts_refl,
      run_inst_seq_def] >>
  simp[expr_val_rel_def]
QED
