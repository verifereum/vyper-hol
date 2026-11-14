(* Source keyword interpretation at the checked raw-call prefix boundary. *)
Theory rawCallPrefixReadyPtr
Ancestors
  rawCallShapePtr rawCallPrefixPtr rawCallAllocatedFinishPtr vyperTypeExtCallSoundness
  exprSimSource exprSimSend vyperInterpreter exprSimWordArgs exprSimHash
  stmtSimReturn exprSimTypedAlloc abiEncoderWindowSource rawCallResultLayoutPtr

Theorem raw_call_prefix_data_word_bounds:
  stmt_state_rel H ctx func cenv cx es s /\
  expr_val_at cenv cx (BaseT (BytesT (Dynamic lim))) sd sa es (BytesV bs) data s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic lim))) =
    SOME (BaseTV (BytesT (Dynamic lim))) /\
  eval_operand data s = SOME (n2w b) /\ b < dimword(:256) ==>
  b+32 < dimword(:256) /\ LENGTH bs < dimword(:256)
Proof
  strip_tac >>
  `~is_word_type (BaseT (BytesT (Dynamic lim)))` by
    simp[compileEnvTheory.is_word_type_def] >>
  drule_all expr_val_at_bound >>
  simp[wordsTheory.w2n_n2w] >>
  mp_tac (Q.INST [`n` |-> `lim`] abi_encoder_window_bytes_footprint) >> decide_tac
QED

Theorem raw_call_selected_operand_checks:
  EVERY (\op. (!z. op = Var z ==> not_fresh_at sa z) /\
    (!l. op <> Label l) /\ op_taint tn op = {}) xs ==>
  (!z. (case ext_call_kwarg kw ks xs of NONE => Lit 0w | SOME op => op) = Var z ==>
    not_fresh_at sa z) /\
  (!l. (case ext_call_kwarg kw ks xs of NONE => Lit 0w | SOME op => op) <> Label l) /\
  op_taint tn (case ext_call_kwarg kw ks xs of NONE => Lit 0w | SOME op => op) = {}
Proof
  strip_tac >> Cases_on `ext_call_kwarg kw ks xs`
  >- simp[ptrDisciplineTheory.op_taint_def] >>
  drule ext_call_kwarg_member >>
  fs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem raw_call_optional_gas_operand_checks:
  (case go of SOME g => (g,sa) | NONE => emit_op GAS [] sa) = (gas_op,sb) /\
  go = ext_call_kwarg EKGas ks xs /\
  EVERY (\op. (!z. op = Var z ==> not_fresh_at sa z) /\ (!l. op <> Label l)) xs ==>
  (!z. gas_op = Var z ==> not_fresh_at sb z) /\ (!l. gas_op <> Label l)
Proof
  strip_tac >> Cases_on `ext_call_kwarg EKGas ks xs` >> gvs[]
  >- (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
      simp[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
        compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.fresh_var_def,
        compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
        compileEnvTheory.comp_return_def] >> rpt strip_tac >> gvs[] >>
      simp[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  drule ext_call_kwarg_member >> fs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem raw_call_prefix_address:
  value_has_type (BaseTV AddressT) av /\
  expr_val_rel cx (BaseT AddressT) av addr s ==>
  ?aw. eval_operand addr s = SOME aw /\ dest_AddressV av = SOME (w2w aw)
Proof
  simp[loweringPostsTheory.expr_val_rel_def,
    compileEnvTheory.is_word_type_def, vyperValueTheory.evaluate_type_def] >>
  strip_tac >> drule address_typed_dest >> simp[]
QED

Theorem raw_call_prefix_data_type:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  expr_sim_inv cenv cx env ee /\ expr_type d = BaseT (BytesT (Dynamic lim)) ==>
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic lim))) =
    SOME (BaseTV (BytesT (Dynamic lim)))
Proof
  strip_tac >>
  `expr_body_pre cenv cx env d ee` by
    (irule rawCallShapePtrTheory.expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  drule exprSimHypsTheory.expr_body_pre_type_evaluates >>
  simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()]
QED

Theorem raw_call_prefix_keyword_source:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  eval_exprs cx (a::d::kws) es = (INL (av::BytesV bs::kvs),ee) ==>
  ?ed. expr_sim_inv cenv cx env ed /\ eval_exprs cx kws ed = (INL kvs,ee)
Proof
  strip_tac >>
  drule rawCallShapePtrTheory.raw_call_pre_operands >> simp[] >> strip_tac >>
  drule eval_exprs_cons_cases >> strip_tac >> gvs[] >>
  Cases_on `rr` >> gvs[] >>
  `expr_sim_inv cenv cx env es` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `expr_body_pre cenv cx env a es` by
    (irule rawCallShapePtrTheory.expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  drule_all expr_body_pre_base_result >> strip_tac >>
  qpat_x_assum `eval_exprs cx (d::kws) _ = _` (mp_tac o MATCH_MP eval_exprs_cons_cases) >>
  strip_tac >> gvs[] >> Cases_on `rr` >> gvs[] >>
  `expr_body_pre cenv cx env d es1` by
    (irule rawCallShapePtrTheory.expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  drule_all expr_body_pre_base_result >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem raw_call_prefix_amount:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  eval_exprs cx (a::d::kws) es = (INL (av::BytesV bs::kvs),ee) /\
  typed_args_post H ctx func cenv cx ed sm th ee kws xs kvs s ==>
  ?amount. raw_call_value flags.rcf_kws kvs = SOME amount /\
    eval_operand (case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME x => x) s = SOME (n2w amount) /\
    amount < dimword(:256) /\ (flags.rcf_is_static ==> amount = 0) /\
    LENGTH kvs = LENGTH flags.rcf_kws
Proof
  strip_tac >> drule_all raw_call_prefix_keyword_source >> strip_tac >>
  drule_all raw_call_keywords_decode >> strip_tac >>
  qexists_tac `amount` >> simp[]
QED

Theorem raw_call_prefix_result_capacity:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) args dflt) es /\
  0 < flags.rcf_max_outsize ==>
  32+((flags.rcf_max_outsize+31) DIV 32)*32 < dimword(:256) /\
  type_memory_bytes cenv (lowered_value_type cenv
    (Call ann (RawCallTarget flags) args dflt)) =
    (if flags.rcf_revert_on_failure then 32 else 64) +
      ((flags.rcf_max_outsize+31) DIV 32)*32 /\
  (~flags.rcf_revert_on_failure ==>
    64+((flags.rcf_max_outsize+31) DIV 32)*32 < dimword(:256))
Proof
  strip_tac >> drule rawCallShapePtrTheory.raw_call_pre_flags >> strip_tac >>
  Cases_on `flags.rcf_revert_on_failure`
  >- (gvs[vyperTypeSystemTheory.raw_call_return_type_def] >>
      drule raw_call_bytes_pre_capacity >>
      simp[raw_call_bytes_type_capacity]) >>
  gvs[vyperTypeSystemTheory.raw_call_return_type_def] >>
  drule raw_call_tuple_pre_capacity >>
  simp[raw_call_tuple_type_capacity] >> decide_tac
QED
