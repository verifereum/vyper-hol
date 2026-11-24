Theory createSizeRawPayloadReplayMods
Ancestors
  createSizeRawPayloadReplay createExprSizeExitDefsMods
  gasShadowCompileBase
  e2eDefs exprSimFullBundleProps fragExec fragGasOrigin gasExplicitSites gasSummary
  venomExecSemantics venomInst venomState vyperCreate vyperState relation list words
  createMarkedPath pair arithmetic exprLowering stmtLoweringMono vfmConstants compileEnv
  exprLoweringProps vyperStorageTrace rich_list exprSimHypsDefs gasCount bodyPtrDefs
  loweringPosts context fragGasPath vyperAST vyperStorageFootprint integer_word
  createCtorSegmentArrival loweringStateRelDefs ptrDiscipline createCtorObservedSilence
  bodySim createExprSizeExitDefs createSizePrefixReplayMods createSizeBlueprintKeywordReplayMods
  createSizeRawReplayMods createSizeCtorRowsReplayMods createSizeRawEncoderReplayMods createSizeRawTotalMods
  createSizeBlueprintAbiKeywordsMods createSizeOperandPreMods

Theorem create_raw_payload_at_cuts_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods module_src tops ce cx /\ shadow_body_inv_mods mods exps ctx shctx /\
  expr_body_pre_mods mods ce cx env
    (Call ann (CreateTarget RawCreate hs rof ks) (e::av::(args ++ (if hs then [saltE] else []))) df) entry /\
  EVERY (create_operand_completed_ok_mods mods exps cx)
    (create_operand_order RawCreate hs (e::av::(args ++ (if hs then [saltE] else [])))) /\
  tys = MAP expr_type (e::av::(args ++ (if hs then [saltE] else []))) /\
  lit = blueprint_literal_offset cx hs (e::av::(args ++ (if hs then [saltE] else []))) /\
  bind (eval_exprs cx (args ++ av::(if hs then [saltE] else [])))
      (\vs. eval_create_operands cx RawCreate hs rof tys lit (BytesV code::vs)) p0 = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  (!K. dead_lo_ok_mods K (DF K) lo ce cx) /\
  p0.gas_obs = gas_explicit (R 0) (St 0).vs_gas_readings ++ tail /\
  expr_sim_inv_mods mods ce cx env p0 /\ return_buf_frame d ce (C 0) (St 0) /\
  alloca_history func (St 0) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp (St 0)) /\
  (!f i z. frag_reachable ctx func (St 0) f i z ==> dalloca_fmp_headroom i z) /\
  ~(St 0).vs_halted /\ (St 0).vs_current_bb = (C 0).cs_current_bb /\
  (St 0).vs_inst_idx = LENGTH (C 0).cs_current_insts /\ local_ptrs_reserved ce (C 0) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C 0) x) /\
  (!K. valid_horizon cx st0 K p0.storage_trace ==>
    stmt_state_rel K ctx func ce cx p0 (St 0) /\
    immutable_frame_mods func ce cx p0 (St 0) /\ storage_well_formed_on cx p0 (FST K) /\
    ghost_inv_at_mods (DF K) lo d ce cx p0 G0 tn0 (St 0)) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  explicit = gas_explicit_sites ctx shctx /\
  lenop = Var lvar /\ not_fresh_at (C 0) lvar /\
  lookup_var lvar (St 0) = SOME (n2w (LENGTH code)) /\
  uval.vs_current_bb = cv.cs_current_bb /\ uval.vs_inst_idx = LENGTH cv.cs_current_insts /\
  (if args = [] then
     cv = C 0 /\ uval = St 0 /\ size_op = lenop /\ R 0 = kwmarks
   else
     LENGTH svs = LENGTH args /\
     compile_create_ctor_args compile_expr ce args (C 0) = (svs,C (LENGTH args)) /\
     EVERY (source_body_call_supported cx) (int_calls_exprs args) /\
     sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\ fn_inst_ids_distinct func /\
     (!i. i < LENGTH args ==>
       compile_expr ce (expr_type (EL i args)) (EL i args) (C i) = (V i,M i) /\
       compile_expr (gas_shadow_env T ce) (expr_type (EL i args)) (gas_shadow_expr (EL i args)) (Sh i) = (V i,SM i) /\
       compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) args))
         (ext_call_arg_value (lowered_value_type ce (EL i args)) (V i)) (M i) =
           (EL i svs,C (SUC i)) /\
       compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) args))
         (ext_call_arg_value (lowered_value_type ce (EL i args)) (V i)) (SM i) =
           (EL i svs,Sh (SUC i)) /\
       expr_sim_full_code (ctx,shctx,func,shfunc) (C i,M i,Sh i,SM i) /\
       expr_sim_full_code (ctx,shctx,func,shfunc) (C i,C (SUC i),Sh i,Sh (SUC i)) /\
       (C 0).cs_next_var <= (C i).cs_next_var /\
       (St (SUC i)).vs_labels = (St i).vs_labels /\
       ~(St (SUC i)).vs_halted /\ (St (SUC i)).vs_current_bb = (C (SUC i)).cs_current_bb /\
       (St (SUC i)).vs_inst_idx = LENGTH (C (SUC i)).cs_current_insts /\
       R i = (Chunk i ++ Snap i) ++ R (SUC i) /\
       create_expr_prefix (C i) (C (SUC i)) explicit ctx func
         (St i) (Chunk i ++ Snap i) (St (SUC i)) /\
       create_expr_prefix (C i) (M i) explicit ctx func (St i) (Chunk i) (Mid i) /\
       ~(Mid i).vs_halted /\ (Mid i).vs_current_bb = (M i).cs_current_bb /\
       (Mid i).vs_inst_idx = LENGTH (M i).cs_current_insts /\
       create_expr_prefix (M i) (C (SUC i)) explicit ctx func (Mid i) (Snap i) (St (SUC i)) /\
       (if exprs_can_mutate ce (DROP (SUC i) args) then
          fn_has_code (M i) (C (SUC i)) func /\
          RTC (\p q. (p.vs_current_bb,p.vs_inst_idx) <>
                  ((C (SUC i)).cs_current_bb,LENGTH (C (SUC i)).cs_current_insts) /\
                 ?j ms. ctor_segment_fetch func p = SOME j /\
                   (M i).cs_next_id <= j.inst_id /\ j.inst_id < (C (SUC i)).cs_next_id /\
                   gas_origin_edge F explicit ctx func p ms (OK q)) (Mid i) (St (SUC i)) /\
          (?j. ctor_segment_fetch func (St (SUC i)) = SOME j /\ j.inst_opcode <> PHI /\
               (C (SUC i)).cs_next_id <= j.inst_id)
        else ~is_word_type (lowered_value_type ce (EL i args)) ==> Mid i = St (SUC i))) /\
     se = C (LENGTH args) /\ s = St (LENGTH args) /\
     capacity = prefix_bound + abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) /\
     capacity < dimword (:256) /\ w2n (n2w (LENGTH code):bytes32) <= prefix_bound /\
     not_fresh_at (C 0) src /\ lookup_var src (St 0) = SOME p /\
     ptr_covers G0 tn0 src (St 0) (w2n (n2w (LENGTH code):bytes32)) /\
     op_taint tn0 (Var lvar) = {} /\ w2n p + w2n (n2w (LENGTH code):bytes32) <= (St 0).vs_alloca_next /\
     compile_alloc_buffer capacity se = (buf,a) /\ fn_has_code se a func /\
     gas_origin_edge F explicit ctx func s am (OK su) /\
     compile_copy_memory_dynamic buf.buf_operand (Var src) (Var lvar) a = ((),b) /\ fn_has_code a b func /\
     emit_op ADD [buf.buf_operand;Var lvar] b = (dst_op,st) /\ fn_has_code b st func /\
     gas_origin_edge F explicit ctx func su bm (OK sv) /\ gas_origin_edge F explicit ctx func sv cm (OK u) /\
     compile_abi_encode_values_to_buf ce dst_op (ZIP (svs,MAP (lowered_value_type ce) args))
       st = (alen,en) /\ fn_has_code st en func /\
     create_expr_prefix st en explicit ctx func u encmarks t /\
     (t.vs_current_bb,t.vs_inst_idx) = (en.cs_current_bb,LENGTH en.cs_current_insts) /\
     emit_op ADD [lenop;alen] en = (size_op,cv) /\ fn_has_code en cv func /\
     create_expr_prefix en cv explicit ctx func t dm uval /\
     R (LENGTH args) = am ++ bm ++ cm ++ encmarks ++ dm ++ kwmarks /\
     c 0 = en /\ r 0 = t /\ r n = bad /\
     (!k. k < n ==>
       (c k).cs_next_id <= (c (SUC k)).cs_next_id /\
       create_expr_prefix (c k) (c (SUC k)) explicit ctx func (r k) (chunk k) (r (SUC k))) /\
     lookup_block bad.vs_current_bb func.fn_blocks = SOME bbad /\
     get_instruction bbad bad.vs_inst_idx = SOME dispatch /\
     ((dispatch.inst_opcode = CREATE /\ dispatch.inst_operands = [value;off;sz]) \/
      (dispatch.inst_opcode = CREATE2 /\ dispatch.inst_operands = [value;off;sz;salt])) /\
     eval_operand sz bad = SOME w /\ 2 * max_code_size < w2n w) ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?cvs payload ee G tn.
    LENGTH cvs = LENGTH args /\
    encode_create_ctor_args (get_tenv cx) (MAP expr_type args) cvs = SOME payload /\
    bind (eval_exprs cx (av::(if hs then [saltE] else [])))
      (\kvs. eval_create_operands cx RawCreate hs rof tys lit (BytesV code::(cvs ++ kvs))) ee = (res,out) /\
    valid_horizon cx st0 H ee.storage_trace /\
    ee.gas_obs = gas_explicit kwmarks uval.vs_gas_readings ++ tail /\
    expr_sim_inv_mods mods ce cx env ee /\ return_buf_frame d ce cv uval /\ alloca_history func uval /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp uval) /\
    (!f i z. frag_reachable ctx func uval f i z ==> dalloca_fmp_headroom i z) /\
    ~uval.vs_halted /\ uval.vs_current_bb = cv.cs_current_bb /\
    uval.vs_inst_idx = LENGTH cv.cs_current_insts /\ local_ptrs_reserved ce cv /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cv x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cv x) /\
    (!K. valid_horizon cx st0 K ee.storage_trace ==>
      stmt_state_rel K ctx func ce cx ee uval /\
      immutable_frame_mods func ce cx ee uval /\ storage_well_formed_on cx ee (FST K) /\
      ghost_inv_at_mods (DF K) lo d ce cx ee G tn uval) /\
    (if args = [] then payload = [] /\ size_op = lenop /\ cv = C 0 /\ uval = St 0
     else (!x v. not_fresh_at (C 0) x /\ lookup_var x (St 0) = SOME v ==> lookup_var x t = SOME v) /\
       eval_operand alen t = SOME (n2w (LENGTH payload)) /\
       eval_operand size_op uval = SOME (n2w (LENGTH code + LENGTH payload)) /\
       (!x. size_op = Var x ==> not_fresh_at cv x) /\ dm = [])
Proof
  cheat
QED
