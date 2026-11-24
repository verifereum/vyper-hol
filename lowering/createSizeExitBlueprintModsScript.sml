Theory createSizeExitBlueprintMods
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

Theorem blueprint_raw_payload_result_mods[local]:
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
  cheat
QED

Theorem blueprint_abi_payload_result_mods[local]:
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
  cheat
QED

Theorem create_size_exit_blueprint_mods:
  !mods exps cx ty raw hs rof ks args d.
    EVERY (create_operand_completed_ok_mods mods exps cx) (create_operand_order (CreateFromBlueprint raw) hs args) ==>
    create_expr_size_exit_mods mods exps cx (Call ty (CreateTarget (CreateFromBlueprint raw) hs rof ks) args d)
Proof
  cheat
QED
