(* Semantic result-clamp outcome boundaries. *)
Theory bodyMemTbExtract32Clamp
Ancestors
  bodyMemTbExtract32IntClamp bodyMemTbExtract32FixedClamp
  bodyMemTbExtract32AddressClamp bodyMemTbExtract32Encoding
  exprSimArith vyperTypeSystem vyperValue valueEncoding exprLoweringProps arithmeticProps compileEnv list

Theorem extract32_clamp_success:
  LENGTH bs = 32 /\ extract32_result_base_ok bt /\
  well_formed_type tenv (BaseT bt) /\
  evaluate_extract32 bs 0 bt = INL v /\
  compile_clamp_basetype x (BaseT bt) sa = (op,sb) /\
  eval_operand x s = SOME (word_of_bytes_be bs) /\ fresh_vars_wrt sa s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (typed_val_to_w256 (BaseTV bt) v)
Proof
  strip_tac >> drule_all extract32_slice_encoding >> disch_then SUBST1_TAC >>
  Cases_on `bt` >> gvs[extract32_result_base_ok_def, extract32_slice_guards,
    well_formed_type_def, evaluate_type_def, AllCaseEqs()]
  >- (irule (extract32_int_clamp_ok |> Q.INST [`sg` |-> `F`] |> SIMP_RULE (srw_ss()) []) >>
      simp[] >> goal_assum (drule_at Any) >> qexists_tac `n` >>
      simp[in_type_range_within, type_bits_def, is_signed_type_def])
  >- (irule (extract32_int_clamp_ok |> Q.INST [`sg` |-> `T`] |> SIMP_RULE (srw_ss()) []) >>
      simp[] >> goal_assum (drule_at Any) >> qexists_tac `n` >>
      simp[in_type_range_within, type_bits_def, is_signed_type_def])
  >- (Cases_on `b` >> gvs[extract32_result_base_ok_def, extract32_slice_guards,
        well_formed_type_def, evaluate_type_def, AllCaseEqs()] >>
      irule extract32_fixed_clamp_ok >> simp[] >> goal_assum (drule_at Any) >>
      qexists_tac `n` >> simp[extract32_fixed_test] >>
      gvs[EVERY_MEM, EXISTS_MEM]) >>
  irule extract32_address_clamp_ok >> simp[] >>
  reverse conj_tac >- (qexists_tac `x` >> simp[]) >>
  drule extract32_address_test >> gvs[EVERY_MEM, EXISTS_MEM]
QED

Theorem extract32_clamp_revert:
  LENGTH bs = 32 /\ extract32_result_base_ok bt /\
  well_formed_type tenv (BaseT bt) /\
  evaluate_extract32 bs 0 bt = INR (RuntimeError msg) /\
  compile_clamp_basetype x (BaseT bt) sa = (op,sb) /\
  eval_operand x s = SOME (word_of_bytes_be bs) /\ fresh_vars_wrt sa s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  strip_tac >>
  Cases_on `bt` >> gvs[extract32_result_base_ok_def, extract32_slice_guards,
    well_formed_type_def, evaluate_type_def, AllCaseEqs()]
  >- (irule (extract32_int_clamp_abort |> Q.INST [`sg` |-> `F`] |> SIMP_RULE (srw_ss()) []) >>
      simp[] >> goal_assum (drule_at Any) >> qexists_tac `n` >>
      simp[in_type_range_within, type_bits_def, is_signed_type_def])
  >- (irule (extract32_int_clamp_abort |> Q.INST [`sg` |-> `T`] |> SIMP_RULE (srw_ss()) []) >>
      simp[] >> goal_assum (drule_at Any) >> qexists_tac `n` >>
      simp[in_type_range_within, type_bits_def, is_signed_type_def])
  >- (Cases_on `b` >> gvs[extract32_result_base_ok_def, extract32_slice_guards,
        well_formed_type_def, evaluate_type_def, AllCaseEqs()] >>
      `n < 32` by (Cases_on `n = 32`
        >- (`DROP 32 bs = []` by simp[DROP_EQ_NIL] >> gvs[]) >>
        decide_tac) >>
      irule extract32_fixed_clamp_revert >> simp[] >>
      goal_assum (drule_at Any) >>
      qexistsl_tac [`op`, `word_of_bytes_be bs`, `x`] >>
      simp[extract32_fixed_test] >> gvs[EVERY_MEM, EXISTS_MEM] >>
      goal_assum (drule_at Any) >> simp[]) >>
  irule extract32_address_clamp_revert >> simp[] >>
  qexistsl_tac [`op`, `word_of_bytes_be bs`, `x`] >> simp[] >>
  drule extract32_address_test >> gvs[EVERY_MEM, EXISTS_MEM] >>
  metis_tac[]
QED
