Theory createSizeBlueprintDispatchMods
Ancestors
  createSizeBlueprintDispatch createExprSizeExitDefsMods
  gasShadowCompileBase
  abiEncoderProps e2eDefs exprSimFullBundleProps fragExec gasExplicitSites gasSummary
  s1PrefixDefs venomInst venomState vyperCreate vyperState relation list words pair
  builtinCreate arithmetic exprLowering vfmConstants compileEnv createSizeItinerary
  exprLoweringProps exprBodyPreProps rich_list exprSimHypsDefs vyperTypeSystem bodyPtrDefs
  loweringPosts context vyperAST vyperStorageFootprint vyperValue exprSimSend integer_word
  createCtorSegmentArrival loweringStateRelDefs ptrDiscipline bodySim
  createSizeBlueprintOuterPairedCode createSizeBlueprintRawPayloadCode
  createSizeBlueprintAbiPayloadCode createExprSizeExitDefs createSizePrefixCutsMods
  createSizeBlueprintAddressMods createSizeBlueprintObserved

Theorem create_blueprint_payload_inputs_at_dispatch_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ shadow_body_inv_mods mods exps ctx shctx /\
  expr_body_pre_mods mods ce cx env (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) es /\
  expr_vv_sim_full_pre_mods (DF,lo,d,ctx,shctx,(PG : (num # num) option list),fnc,shfnc)
    ce cx ty (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) es
    (st0,sa,sb,hsa,hsb,vv,s0,G0,tn0) /\
  EVERY (create_operand_completed_ok_mods mods exps cx) (create_operand_order (CreateFromBlueprint raw) hs args) /\
  create_expr_prefix sa sb (gas_explicit_sites ctx shctx) ctx fnc s0 marks s /\
  (s.vs_current_bb <> sb.cs_current_bb \/ s.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
  lookup_block s.vs_current_bb fnc.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_id IN frag_ids sa sb /\
  (!x. MEM x (fn_insts fnc) /\ x.inst_id IN frag_ids sa sb /\
       MEM x.inst_opcode [CREATE;CREATE2] ==> x.inst_id <= inst.inst_id) /\
  ((inst.inst_opcode = CREATE /\ inst.inst_operands = [value;offop;sz]) \/
   (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [value;offop;sz;saltop])) /\
  eval_operand sz s = SOME w /\ 2 * max_code_size < w2n w /\
  eval_expr cx (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) = (res,out) /\
  valid_horizon cx st0 H out.storage_trace ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?target amount salt off ctors later target_op ca cprep cm cn cb cf sc
   sca scprep scm scn scb data len offset_op code prep app salt_op
   C Obs M R n j av aw p G tn.
    args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
    later = amount::((if hs then [salt] else []) ++ [off]) /\
    dest_AddressV av = SOME (w2w aw) /\ eval_operand target_op (Obs 1) = SOME aw /\
    (!x. target_op = Var x ==> not_fresh_at ca x) /\
    bind (eval_exprs cx (ctors ++ later))
      (\vs. eval_create_operands cx (CreateFromBlueprint raw) hs rof
        (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::vs)) p = (res,out) /\
    p.gas_obs = gas_explicit (R 1) (Obs 1).vs_gas_readings ++ tail /\
    valid_horizon cx st0 H p.storage_trace /\ expr_sim_inv_mods mods ce cx env p /\
    local_ptrs_reserved ce ca /\ (!h. dead_lo_ok_mods h (DF h) lo ce cx) /\
    (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at ca x) /\
    (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at ca x) /\
    return_buf_frame d ce ca (Obs 1) /\ alloca_history fnc (Obs 1) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp (Obs 1)) /\
    (!f i z. frag_reachable ctx fnc (Obs 1) f i z ==> dalloca_fmp_headroom i z) /\
    (!h. valid_horizon cx st0 h p.storage_trace ==>
      stmt_state_rel h ctx fnc ce cx p (Obs 1) /\
      immutable_frame_mods fnc ce cx p (Obs 1) /\ storage_well_formed_on cx p (FST h) /\
      ghost_inv_at_mods (DF h) lo d ce cx p G tn (Obs 1)) /\
    C 1 = ca /\ C j = cprep /\ C (SUC j) = cm /\ C (j+2) = cn /\
    C (j+3) = cb /\ C (j+4) = cf /\ C n = sc /\ j = SUC (LENGTH prep) /\ j+4 <= n /\
    n = j+4+LENGTH app /\ (!i. i < LENGTH app ==> C (j+5+i) = EL i app) /\
    Obs n = s /\ R n = [] /\
    (!i. i <= n ==> ~(Obs i).vs_halted /\
      (Obs i).vs_current_bb = (C i).cs_current_bb /\
      (Obs i).vs_inst_idx = LENGTH (C i).cs_current_insts /\
      ?x. ctor_segment_fetch fnc (Obs i) = SOME x /\ x.inst_opcode <> PHI /\
        (C i).cs_next_id <= x.inst_id) /\
    (!i k. i <= k /\ k <= n ==> ci_mono (C i) (C k) /\ fn_has_code (C i) (C k) fnc) /\
    (!i. i < n ==> (C i).cs_next_id <= (C (SUC i)).cs_next_id /\
      create_expr_prefix (C i) (C (SUC i)) (gas_explicit_sites ctx shctx) ctx fnc
        (Obs i) (M i) (Obs (SUC i)) /\ R i = M i ++ R (SUC i) /\
      (C i = C (SUC i) ==> Obs (SUC i) = Obs i /\ M i = [])) /\
    compile_create_blueprint_args compile_expr ce raw later ctors ca = ((data,len),cprep) /\
    compile_create_blueprint_args compile_expr (gas_shadow_env T ce) raw (MAP gas_shadow_expr later)
      (MAP gas_shadow_expr ctors) sca = ((data,len),scprep) /\
    expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cprep,sca,scprep) /\
    lower_value compile_expr ce (expr_type amount) amount cprep = (value,cm) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type amount) (gas_shadow_expr amount) scprep = (value,scm) /\
    expr_sim_full_code (ctx,shctx,fnc,shfnc) (cprep,cm,scprep,scm) /\
    (if hs then ?sop. salt_op = SOME sop /\
      lower_value compile_expr ce (expr_type salt) salt cm = (sop,cn) /\
      lower_value compile_expr (gas_shadow_env T ce) (expr_type salt) (gas_shadow_expr salt) scm = (sop,scn) /\
      expr_sim_full_code (ctx,shctx,fnc,shfnc) (cm,cn,scm,scn)
     else salt_op = NONE /\ cn = cm /\ scn = scm) /\
    ((?oty i. origin_fold_value off = Literal oty (IntL i) /\
       offset_op = Lit (i2w i) /\ cb = cn /\ scb = scn) \/
     (lower_value compile_expr ce (expr_type off) off cn = (offset_op,cb) /\
      lower_value compile_expr (gas_shadow_env T ce) (expr_type off) (gas_shadow_expr off) scn = (offset_op,scb) /\
      expr_sim_full_code (ctx,shctx,fnc,shfnc) (cn,cb,scn,scb))) /\
    compile_create_blueprint_check (is_int_literal (origin_fold_value off)) target_op offset_op cb = (code,cf) /\
    create_blueprint_append_itinerary target_op offset_op code data len cf app offop sz /\
    (if raw then
      ?e v saved raw_op c0 c1 c2 c3 h0 ssaved h1 h2.
        ctors = [e] /\ prep = [c0;c1;c2;c3;cprep] /\
        j = 6 /\ C 2 = c0 /\ C 3 = c1 /\ C 4 = c2 /\ C 5 = c3 /\
        R 1 = M 1 ++ (M 2 ++ (M 3 ++ (M 4 ++ M 5 ++ R j))) /\
        compile_expr ce (expr_type e) e ca = (v,c0) /\
        compile_snapshot_vv ce (exprs_can_mutate ce later) v c0 = (saved,c1) /\
        unwrap_value ce saved c1 = (raw_op,c2) /\
        emit_op MLOAD [raw_op] c2 = (len,c3) /\ emit_op ADD [raw_op;Lit 32w] c3 = (data,cprep) /\
        compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sca = (v,h0) /\
        compile_snapshot_vv ce (exprs_can_mutate ce (MAP gas_shadow_expr later)) v h0 = (ssaved,h1) /\
        unwrap_value ce ssaved h1 = (raw_op,h2) /\
        expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,c0,sca,h0) /\
        expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,c2,sca,h2) /\
        fn_has_code c0 c1 fnc /\ fn_has_code c2 cprep fnc
     else if ctors = [] then j = 1 /\ cprep = ca /\ data = Lit 0w /\ len = Lit 0w
     else ?vals k cs mid vvs buf a hk ha hcs hmid q.
       q = 1+2*LENGTH ctors /\ j = q+2 /\ C q = k /\ C (SUC q) = a /\
       R q = M q ++ M (SUC q) ++ R j /\
       compile_create_ctor_args compile_expr ce ctors ca = (vals,k) /\
       create_itinerary_ctor_rows ce ctors vals ca k cs mid vvs /\
       compile_alloc_buffer (abi_size_bound ce.ce_struct_fields
         (TupleT (MAP (lowered_value_type ce) ctors))) k = (buf,a) /\
       compile_abi_encode_values_to_buf ce buf.buf_operand
         (ZIP (vals,MAP (lowered_value_type ce) ctors)) a = (len,cprep) /\
       data = buf.buf_operand /\
       expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,k,sca,hk) /\
       expr_sim_full_code (ctx,shctx,fnc,shfnc) (k,a,hk,ha) /\
       expr_sim_full_code (ctx,shctx,fnc,shfnc) (a,cprep,ha,scprep) /\
       (!i. i <= LENGTH ctors ==> C (1+2*i) = EL i cs) /\
       (!i. i < LENGTH ctors ==>
         C (SUC (1+2*i)) = EL i mid /\
         R (1+2*i) = (M (1+2*i) ++ M (SUC (1+2*i))) ++ R (1+2*SUC i) /\
         create_expr_prefix (EL i cs) (EL (SUC i) cs) (gas_explicit_sites ctx shctx) ctx fnc
           (Obs (1+2*i)) (M (1+2*i) ++ M (SUC (1+2*i))) (Obs (1+2*SUC i)) /\
         compile_expr (gas_shadow_env T ce) (expr_type (EL i ctors)) (gas_shadow_expr (EL i ctors)) (EL i hcs) =
           (EL i vvs,EL i hmid) /\
         compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) ctors))
           (ext_call_arg_value (lowered_value_type ce (EL i ctors)) (EL i vvs)) (EL i hmid) =
           (EL i vals,EL (SUC i) hcs) /\
         expr_sim_full_code (ctx,shctx,fnc,shfnc) (EL i cs,EL i mid,EL i hcs,EL i hmid) /\
         expr_sim_full_code (ctx,shctx,fnc,shfnc) (EL i cs,EL (SUC i) cs,EL i hcs,EL (SUC i) hcs)))
Proof
  cheat
QED
