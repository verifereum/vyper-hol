Theory createSizeBlueprintPayloadResultMods
Ancestors
  createSizeExitBlueprint createExprSizeExitDefsMods
  createSizeIndexedRun
  gasShadowCompileBase
  e2eDefs exprSimFullBundleProps fragExec fragGasOrigin gasExplicitSites gasSummary
  s1PrefixDefs venomExecSemantics venomInst venomState vyperCreate vyperInterpreter
  vyperState relation list words pair builtinCreate arithmetic exprLowering vfmConstants
  loweringShapeRules compileEnv createSizeItinerary exprLoweringProps exprBodyPreProps
  freshWrites rich_list exprSimHypsDefs createSizeBlueprintOffsetMods bodyPtrDefs loweringPosts
  context vyperAST vyperStorageFootprint allocLimits createSizeStraightPrefix
  ghostPcTransportPtr integer_word createCtorSegmentArrival loweringStateRelDefs
  ptrDiscipline emitHelperProps dallocaBlueprintArgs bodySim loweringShapeDefs
  createSizeBlueprintExtent createOperandSizeReject createExprSizeExitDefs
  createSizeBlueprintKeywordReplayMods createSizeBlueprintKeywordsMods
  createSizeBlueprintRawKeywordsMods createSizeBlueprintAbiKeywordsMods createSizeBlueprintDispatchMods
  createSizeOperandPreMods createSizePrefixReplayMods

Theorem blueprint_raw_payload_result_adapter_mods:
  (
    (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
    ?bs qp Gp tnp. ctors = [raw_e] /\
      bind (eval_exprs cx (amount::((if hs then [salt_e] else []) ++ [off_e])))
        (\kvs. eval_create_operands cx (CreateFromBlueprint T) hs rof
          (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::BytesV bs::kvs)) qp = (res,srcout) /\
      valid_horizon cx st0 H qp.storage_trace /\
      eval_operand len (Obs j) = SOME (n2w (LENGTH bs)) /\
      (!x. len = Var x ==> not_fresh_at cprep x) /\
      eval_operand target_op (Obs j) = SOME aw /\
      (!x. target_op = Var x ==> not_fresh_at cprep x) /\
      expr_sim_inv_mods mods ce cx env qp /\ local_ptrs_reserved ce cprep /\
      (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
      (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
      return_buf_frame depr ce cprep (Obs j) /\ alloca_history func (Obs j) /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp (Obs j)) /\
      (!f i z. frag_reachable ctx func (Obs j) f i z ==> dalloca_fmp_headroom i z) /\
      (!h. valid_horizon cx st0 h qp.storage_trace ==>
        stmt_state_rel h ctx func ce cx qp (Obs j) /\
        immutable_frame_mods func ce cx qp (Obs j) /\ storage_well_formed_on cx qp (FST h) /\
        ghost_inv_at_mods (DF h) lo depr ce cx qp Gp tnp (Obs j)) /\
      ~(Obs j).vs_halted /\ (Obs j).vs_current_bb = cprep.cs_current_bb /\
      (Obs j).vs_inst_idx = LENGTH cprep.cs_current_insts /\
      qp.gas_obs = gas_explicit (R j) (Obs j).vs_gas_readings ++ tail
  ) ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?cvs bs qp Gp tnp.
    LENGTH cvs = LENGTH ctors /\
    cvs = [BytesV bs] /\
    bind (eval_exprs cx (amount::((if hs then [salt_e] else []) ++ [off_e])))
      (\kvs. eval_create_operands cx (CreateFromBlueprint T) hs rof
        (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs))) qp = (res,srcout) /\
    eval_operand len (Obs j) = SOME (n2w (LENGTH bs)) /\
    (!x. len = Var x ==> not_fresh_at cprep x) /\
    eval_operand target_op (Obs j) = SOME aw /\
    (!x. target_op = Var x ==> not_fresh_at cprep x) /\
    expr_sim_inv_mods mods ce cx env qp /\ local_ptrs_reserved ce cprep /\
    (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
    (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
    return_buf_frame depr ce cprep (Obs j) /\ alloca_history func (Obs j) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp (Obs j)) /\
    (!f i z. frag_reachable ctx func (Obs j) f i z ==> dalloca_fmp_headroom i z) /\
    (!h. valid_horizon cx st0 h qp.storage_trace ==>
      stmt_state_rel h ctx func ce cx qp (Obs j) /\
      immutable_frame_mods func ce cx qp (Obs j) /\ storage_well_formed_on cx qp (FST h) /\
      ghost_inv_at_mods (DF h) lo depr ce cx qp Gp tnp (Obs j)) /\
    qp.gas_obs = gas_explicit (R j) (Obs j).vs_gas_readings ++ tail
Proof
  disch_then (DISJ_CASES_THEN2 assume_tac
    (qx_choosel_then [`bytes`,`paystate`,`payG`,`paytn`] strip_assume_tac))
  >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >>
  qexists_tac `[BytesV bytes]` >> qexists_tac `bytes` >>
  qexists_tac `paystate` >> qexists_tac `payG` >> qexists_tac `paytn` >>
  conj_tac >- (qpat_assum `ctors = [raw_e]` (simp_tac (srw_ss()) o single)) >>
  rpt conj_tac >>
  (first_assum ACCEPT_TAC ORELSE
   (simp_tac bool_ss [APPEND] >> first_assum ACCEPT_TAC))
QED

Theorem blueprint_abi_payload_result_adapter_mods:
  (
    (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
    ?cvs ps g tn1.
      LENGTH cvs = LENGTH ctors /\ eval_exprs cx ctors p = (INL cvs,ps) /\
      bind (eval_exprs cx (amount::((if hs then [salt_e] else []) ++ [off_e])))
        (\kvs. eval_create_operands cx (CreateFromBlueprint F) hs rof
          (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs))) ps = (res,srcout) /\
      valid_horizon cx st0 H ps.storage_trace /\
      (?bs. encode_create_ctor_args (get_tenv cx) (MAP expr_type ctors) cvs = SOME bs /\
        eval_operand len (Obs j) = SOME (n2w (LENGTH bs))) /\
      (!x. len = Var x ==> not_fresh_at cprep x) /\
      eval_operand target_op (Obs j) = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at cprep x) /\
      expr_sim_inv_mods mods ce cx env ps /\ local_ptrs_reserved ce cprep /\
      (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
      (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
      return_buf_frame depr ce cprep (Obs j) /\ alloca_history func (Obs j) /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp (Obs j)) /\
      (!f i z. frag_reachable ctx func (Obs j) f i z ==> dalloca_fmp_headroom i z) /\
      (!h. valid_horizon cx st0 h ps.storage_trace ==>
        stmt_state_rel h ctx func ce cx ps (Obs j) /\
        immutable_frame_mods func ce cx ps (Obs j) /\ storage_well_formed_on cx ps (FST h) /\
        ghost_inv_at_mods (DF h) lo depr ce cx ps g tn1 (Obs j)) /\
      ~(Obs j).vs_halted /\ (Obs j).vs_current_bb = cprep.cs_current_bb /\
      (Obs j).vs_inst_idx = LENGTH cprep.cs_current_insts /\
      ps.gas_obs = gas_explicit (R j) (Obs j).vs_gas_readings ++ tail
  ) ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?cvs bs qp Gp tnp.
    LENGTH cvs = LENGTH ctors /\
    encode_create_ctor_args (get_tenv cx) (MAP expr_type ctors) cvs = SOME bs /\
    bind (eval_exprs cx (amount::((if hs then [salt_e] else []) ++ [off_e])))
      (\kvs. eval_create_operands cx (CreateFromBlueprint F) hs rof
        (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs))) qp = (res,srcout) /\
    eval_operand len (Obs j) = SOME (n2w (LENGTH bs)) /\
    (!x. len = Var x ==> not_fresh_at cprep x) /\
    eval_operand target_op (Obs j) = SOME aw /\
    (!x. target_op = Var x ==> not_fresh_at cprep x) /\
    expr_sim_inv_mods mods ce cx env qp /\ local_ptrs_reserved ce cprep /\
    (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
    (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at cprep x) /\
    return_buf_frame depr ce cprep (Obs j) /\ alloca_history func (Obs j) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp (Obs j)) /\
    (!f i z. frag_reachable ctx func (Obs j) f i z ==> dalloca_fmp_headroom i z) /\
    (!h. valid_horizon cx st0 h qp.storage_trace ==>
      stmt_state_rel h ctx func ce cx qp (Obs j) /\
      immutable_frame_mods func ce cx qp (Obs j) /\ storage_well_formed_on cx qp (FST h) /\
      ghost_inv_at_mods (DF h) lo depr ce cx qp Gp tnp (Obs j)) /\
    qp.gas_obs = gas_explicit (R j) (Obs j).vs_gas_readings ++ tail
Proof
  disch_then (DISJ_CASES_THEN2 assume_tac
   (qx_choosel_then [`cvs`,`ps`,`g`,`tn1`] (map_every assume_tac o CONJUNCTS)))
  >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `?bs. encode_create_ctor_args _ _ cvs = SOME bs /\ _`
    (qx_choose_then `bytes` (map_every assume_tac o CONJUNCTS)) >>
  disj2_tac >>
  qexists_tac `cvs` >> qexists_tac `bytes` >>
  qexists_tac `ps` >> qexists_tac `g` >> qexists_tac `tn1` >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
