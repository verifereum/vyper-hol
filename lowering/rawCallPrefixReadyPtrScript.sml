(* Source keyword interpretation at the checked raw-call prefix boundary. *)
Theory rawCallPrefixReadyPtr
Ancestors
  rawCallPrefixPtr rawCallAllocatedFinishPtr vyperTypeExtCallSoundness
  exprSimSource exprSimSend vyperInterpreter exprSimWordArgs exprSimHash
  stmtSimReturn exprSimTypedAlloc abiEncoderWindowSource rawCallResultLayoutPtr

Theorem raw_call_keywords_post:
  !ks xs vs.
    typed_args_post ctx func cenv cx es sa s0 es' ks xs vs s /\
    EVERY (\e. expr_type e = BaseT (UintT 256)) ks ==>
    LIST_REL (\x v. eval_operand x s = SOME
      (typed_val_to_w256 (BaseTV (UintT 256)) v)) xs vs
Proof
  Induct >> rpt gen_tac >> Cases_on `xs` >> Cases_on `vs` >>
  simp[exprSimPrecompilesTheory.typed_args_post_def,
    vyperValueTheory.evaluate_type_def] >>
  strip_tac >> gvs[vyperValueTheory.evaluate_type_def] >>
  first_x_assum irule >> simp[exprSimPrecompilesTheory.typed_args_post_def] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem raw_call_value_operand:
  !ks xs vs.
    LIST_REL (\x v. eval_operand x s = SOME
      (typed_val_to_w256 (BaseTV (UintT 256)) v)) xs vs /\
    EVERY (value_has_type (BaseTV (UintT 256))) vs ==>
    ?amount. raw_call_value ks vs = SOME amount /\
      eval_operand (case ext_call_kwarg EKValue ks xs of
        NONE => Lit 0w | SOME x => x) s = SOME (n2w amount) /\
      amount < dimword (:256)
Proof
  Induct >- simp[raw_call_value_def, ext_call_kwarg_def, venomStateTheory.eval_operand_def] >>
  rpt gen_tac >> Cases_on `xs` >> Cases_on `vs` >>
  simp[raw_call_value_def, ext_call_kwarg_def, venomStateTheory.eval_operand_def] >>
  strip_tac >> gvs[] >> Cases_on `h = EKValue` >> gvs[]
  >- (drule uint256_typed_dest >> simp[wordsTheory.w2n_lt] >>
      qspec_then `(typed_val_to_w256 (BaseTV (UintT 256)) h''):bytes32`
        mp_tac wordsTheory.w2n_lt >> simp[]) >>
  first_x_assum drule_all >> simp[raw_call_value_def]
QED

Theorem raw_call_keyword_values:
  !ks es vs es'.
    EVERY (\e. expr_type e = BaseT (UintT 256) /\
      !st. expr_sim_inv cenv cx env st ==> expr_body_pre cenv cx env e st) ks /\
    expr_sim_inv cenv cx env es /\ eval_exprs cx ks es = (INL vs,es') ==>
    EVERY (value_has_type (BaseTV (UintT 256))) vs /\
    LENGTH vs = LENGTH ks /\ expr_sim_inv cenv cx env es'
Proof
  Induct >- simp[eval_exprs_nil] >>
  rpt gen_tac >> simp[] >> strip_tac >>
  drule eval_exprs_cons_cases >> strip_tac >> gvs[] >>
  Cases_on `rr` >> gvs[] >>
  `expr_body_pre cenv cx env h es` by metis_tac[] >>
  drule_all expr_body_pre_base_result >> strip_tac >>
  qpat_x_assum `!es vs es'. _` drule_all >> simp[]
QED

Theorem raw_call_keywords_decode:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  expr_sim_inv cenv cx env es2 /\
  eval_exprs cx kws es2 = (INL kvs,es') /\
  typed_args_post ctx func cenv cx es0 sa s0 es' kws xs kvs s ==>
  ?amount. raw_call_value flags.rcf_kws kvs = SOME amount /\
    eval_operand (case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME x => x) s = SOME (n2w amount) /\
    amount < dimword (:256) /\
    (flags.rcf_is_static ==> amount = 0) /\
    LENGTH kvs = LENGTH flags.rcf_kws /\ expr_sim_inv cenv cx env es'
Proof
  strip_tac >> drule rawCallShapePtrTheory.raw_call_pre_flags >> simp[] >> strip_tac >>
  drule rawCallShapePtrTheory.raw_call_kwargs_types >> strip_tac >>
  `EVERY (\e. expr_type e = BaseT (UintT 256) /\
    !st. expr_sim_inv cenv cx env st ==> expr_body_pre cenv cx env e st) kws` by
    (simp[listTheory.EVERY_MEM] >> rpt gen_tac >> strip_tac >> conj_tac
     >- fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     irule rawCallShapePtrTheory.expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  drule_all raw_call_keyword_values >> strip_tac >>
  drule_all raw_call_keywords_post >> strip_tac >>
  drule_all raw_call_value_operand >>
  disch_then (qspec_then `flags.rcf_kws` strip_assume_tac) >>
  `LENGTH kvs = LENGTH flags.rcf_kws` by decide_tac >>
  qexists_tac `amount` >> fs[] >> strip_tac >>
  `~MEM EKValue flags.rcf_kws` by fs[vyperTypeSystemTheory.raw_call_kws_ok_def] >>
  gvs[raw_call_value_def, ext_call_kwarg_not_mem]
QED

Theorem raw_call_prefix_data_word_bounds:
  stmt_state_rel ctx func cenv cx es s /\
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
  typed_args_post ctx func cenv cx ed sm th ee kws xs kvs s ==>
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
