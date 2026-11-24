Theory createSizeBlueprintAbiKeywordsMods
Ancestors
  createSizeBlueprintAbiKeywords createExprSizeExitDefsMods
  bodySingletonCallSupport[qualified,ignore_grammar]
  gasShadowCompileBase
  abiEncoderProps e2eDefs exprSimFullBundleProps fragExec fragGasOrigin fragGasOriginPtr
  gasExplicitSites gasSummary venomExecSemantics venomInst venomState vyperCreate vyperState
  relation list words createMarkedPath pair bodyFullIfExpReach arithmetic exprLowering
  stmtLoweringMono vfmConstants compileEnv exprLoweringProps fragFuel exprBodyPreProps
  vyperStorageTrace freshWrites rich_list exprSimHypsDefs bodyPtrDefs loweringPosts context
  bodyInvCodeProps vyperAST vyperStorageFootprint vyperTypeCallGraph integer_word
  createCtorSegmentArrival bodyFullExtCallPosAggregate bodyFullHashKeccakFixed
  loweringStateRelDefs ptrDiscipline createCtorObservedSilence createCtorPayloadLengthMods
  bodyFullExtCallDirectState bodyPtrMakeArrayEmission bodySim loweringShapeDefs
  createExprSizeExitDefs createSizePrefixReplayMods createSizeCopyReplayMods
  createSizeBlueprintKeywordReplayMods createSizeRawReplayMods createSizeBlueprintRawScalarsMods
  createSizeCtorValueRowMods createSizeObservedPrefix createSizeRawObserved
  createSizeCtorRowsReplayMods createSizeRawEncoderReplayMods createSizeOperandPreMods

Theorem create_blueprint_abi_keyword_entry_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ shadow_body_inv_mods mods exps ctx shctx /\
  expr_body_pre_mods mods ce cx env (Call ann (CreateTarget (CreateFromBlueprint F) hs rof ks) args df) entry /\
  args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
  EVERY (create_operand_completed_ok_mods mods exps cx) (create_operand_order (CreateFromBlueprint F) hs args) /\
  MEM func ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  later = amount::((if hs then [salt] else []) ++ [off]) /\
  eval_operand target_op (St 0) = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at (C 0) x) /\
  local_ptrs_reserved ce (C 0) /\ (!K. dead_lo_ok_mods K (DF K) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  return_buf_frame d ce (C 0) (St 0) /\ alloca_history func (St 0) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp (St 0)) /\
  (!f i z. frag_reachable ctx func (St 0) f i z ==> dalloca_fmp_headroom i z) /\
  (!K. valid_horizon cx st0 K p0.storage_trace ==>
    stmt_state_rel K ctx func ce cx p0 (St 0) /\
    immutable_frame_mods func ce cx p0 (St 0) /\ storage_well_formed_on cx p0 (FST K) /\
    ghost_inv_at_mods (DF K) lo d ce cx p0 G0 tn0 (St 0)) /\
  expr_sim_inv_mods mods ce cx env p0 /\ ~(St 0).vs_halted /\
  (St 0).vs_current_bb = (C 0).cs_current_bb /\ (St 0).vs_inst_idx = LENGTH (C 0).cs_current_insts /\
  LENGTH svs = LENGTH ctors /\
  se = C (LENGTH ctors) /\ s = St (LENGTH ctors) /\
  compile_create_ctor_args compile_expr ce ctors (C 0) = (svs,se) /\
  compile_create_blueprint_args compile_expr ce F later ctors (C 0) = ((data,len),en) /\
  (!i. i < LENGTH ctors ==>
    compile_expr ce (expr_type (EL i ctors)) (EL i ctors) (C i) = (V i,M i) /\
    compile_expr (gas_shadow_env T ce) (expr_type (EL i ctors)) (gas_shadow_expr (EL i ctors)) (Sh i) = (V i,SM i) /\
    compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) ctors))
      (ext_call_arg_value (lowered_value_type ce (EL i ctors)) (V i)) (M i) =
      (EL i svs,C (SUC i)) /\
    (St (SUC i)).vs_current_bb = (C (SUC i)).cs_current_bb /\
    (St (SUC i)).vs_inst_idx = LENGTH (C (SUC i)).cs_current_insts /\
    R i = (Chunk i ++ Snap i) ++ R (SUC i) /\
    create_expr_prefix (C i) (M i) (gas_explicit_sites ctx shctx) ctx func
      (St i) (Chunk i) (Mid i) /\
    (Mid i).vs_current_bb = (M i).cs_current_bb /\
    (Mid i).vs_inst_idx = LENGTH (M i).cs_current_insts /\
    create_expr_prefix (M i) (C (SUC i)) (gas_explicit_sites ctx shctx) ctx func
      (Mid i) (Snap i) (St (SUC i)) /\
    fn_has_code (M i) (C (SUC i)) func /\ ci_mono (C 0) (C i) /\
    (is_word_type (lowered_value_type ce (EL i ctors)) ==>
      compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) ctors))
        (ext_call_arg_value (lowered_value_type ce (EL i ctors)) (V i)) (SM i) =
        (EL i svs,Sh (SUC i)) /\
      expr_sim_full_code (ctx,shctx,func,shfunc) (C i,C (SUC i),Sh i,Sh (SUC i))) /\
    (~is_word_type (lowered_value_type ce (EL i ctors)) ==>
      expr_sim_full_code (ctx,shctx,func,shfunc) (C i,M i,Sh i,SM i))) /\
  (ctors = [] ==> t = St 0 /\ R 0 = rest) /\
  (ctors <> [] ==>
    capacity = abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) ctors)) /\
    capacity < dimword (:256) /\
    compile_alloc_buffer capacity se = (buf,a) /\ fn_has_code se a func /\
    su.vs_current_bb = a.cs_current_bb /\ su.vs_inst_idx = LENGTH a.cs_current_insts /\
    create_expr_prefix se a (gas_explicit_sites ctx shctx) ctx func s am su /\
    compile_abi_encode_values_to_buf ce buf.buf_operand (ZIP (svs,MAP (lowered_value_type ce) ctors))
      a = (len,en) /\ fn_has_code a en func /\
    create_expr_prefix a en (gas_explicit_sites ctx shctx) ctx func su encmarks t /\
    t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    R (LENGTH ctors) = am ++ encmarks ++ rest /\
    c 0 = en /\ r 0 = t /\ r n = bad /\
    (!k. k < n ==> (c k).cs_next_id <= (c (SUC k)).cs_next_id /\
      create_expr_prefix (c k) (c (SUC k)) (gas_explicit_sites ctx shctx) ctx func
        (r k) (chunk k) (r (SUC k))) /\
    lookup_block bad.vs_current_bb func.fn_blocks = SOME bbad /\
    get_instruction bbad bad.vs_inst_idx = SOME dispatch /\
    ((dispatch.inst_opcode = CREATE /\ dispatch.inst_operands = [value;offop;sz]) \/
     (dispatch.inst_opcode = CREATE2 /\ dispatch.inst_operands = [value;offop;sz;salto])) /\
    eval_operand sz bad = SOME w /\ 2 * max_code_size < w2n w) /\
  bind (eval_exprs cx (ctors ++ later))
    (\vs. eval_create_operands cx (CreateFromBlueprint F) hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::vs)) p0 = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p0.gas_obs = gas_explicit (R 0) (St 0).vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?cvs p G tn.
    LENGTH cvs = LENGTH ctors /\ eval_exprs cx ctors p0 = (INL cvs,p) /\
    bind (eval_exprs cx (amount::((if hs then [salt] else []) ++ [off])))
      (\kvs. eval_create_operands cx (CreateFromBlueprint F) hs rof
        (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs))) p = (res,out) /\
    valid_horizon cx st0 H p.storage_trace /\
    (?bs. encode_create_ctor_args (get_tenv cx) (MAP expr_type ctors) cvs = SOME bs /\
      eval_operand len t = SOME (n2w (LENGTH bs))) /\
    (!x. len = Var x ==> not_fresh_at en x) /\
    eval_operand target_op t = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at en x) /\
    expr_sim_inv_mods mods ce cx env p /\ local_ptrs_reserved ce en /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at en x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at en x) /\
    return_buf_frame d ce en t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx func t f i z ==> dalloca_fmp_headroom i z) /\
    (!K. valid_horizon cx st0 K p.storage_trace ==>
      stmt_state_rel K ctx func ce cx p t /\
      immutable_frame_mods func ce cx p t /\ storage_well_formed_on cx p (FST K) /\
      ghost_inv_at_mods (DF K) lo d ce cx p G tn t) /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    p.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail
Proof
  cheat
QED
