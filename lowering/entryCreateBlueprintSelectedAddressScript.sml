Theory entryCreateBlueprintSelectedAddress
Ancestors
  entryCreateBlueprintReadCut bodyFullPreds
  vyperTypeExprSoundness vyperTyping loweringStateRelDefs vyperValue
  valueEncoding vyperCreate exprBodyPreProps createSizeOperandPre
  vyperTypeSystem vyperInterpreter createSizeCopyReplay list loweringPosts compileEnv
  s1PrefixDefs exprSimFullBundleProps exprSimSource bodyPtrDefs
  vyperStorageFootprint ptrDiscipline venomState pair
  createSizeBlueprintKeywordReplay vyperStorageTrace exprOperandVar

Theorem selected_blueprint_address_word[local]:
  value_runtime_typed env (BaseT AddressT) v /\
  expr_val_rel cx (BaseT AddressT) v op t ==>
  ?aw. dest_AddressV v = SOME (w2w aw) /\ eval_operand op t = SOME aw
Proof
  Cases_on `v` >>
  simp[value_runtime_typed_def, vyperValueTheory.evaluate_type_def,
       value_has_type_def, expr_val_rel_def, is_word_type_def,
       typed_val_to_w256_def, dest_AddressV_def] >>
  rpt strip_tac >>
  rename1 `word_of_bytes_be bytes = w2w _` >>
  qspec_then `bytes` mp_tac
    (venomMemPropsTheory.w2w_word_of_bytes_be_pad_left
     |> INST_TYPE [alpha |-> ``:160``, beta |-> ``:256``]) >>
  simp[dividesTheory.compute_divides, fcpLib.INDEX_CONV ``dimindex(:160)``] >>
  disch_then (rewrite_tac o single o SYM) >> wordsLib.WORD_DECIDE_TAC
QED

Theorem selected_blueprint_address_source[local]:
  expr_body_pre ce cx env (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
  later = amount::((if hs then [salt] else []) ++ [off]) /\
  eval_expr cx (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df)
    (es with gas_obs := readings) = (res,out) ==>
  expr_type target = BaseT AddressT /\
  expr_body_pre ce cx env target (es with gas_obs := readings) /\
  body_const_cells_agree [(NONE,tops)] cx env (es with gas_obs := readings) /\
  bind (bind (eval_expr cx target) (read_result cx))
    (\av. bind (eval_exprs cx (ctors ++ later))
      (\vs. eval_create_operands cx (CreateFromBlueprint raw) hs rof
        (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::vs)))
    (es with gas_obs := readings) = (res,out)
Proof
  strip_tac >> drule expr_body_pre_static_facts >> strip_tac >>
  conj_tac
  >- (Cases_on `hs` >> gvs[well_typed_expr_def,create_arg_types_ok_def]) >>
  conj_tac
  >- (irule create_call_operand_body_pre >>
      qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  conj_tac >- simp[] >>
  qpat_assum `eval_expr _ (Call _ _ _ _) _ = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC [evaluate_def] >>
  Cases_on `hs` >> simp[create_operand_order_def,create_copy_source_cons]
QED

(* Replay the address at the first observed exit, before constructor arguments. *)
Theorem blueprint_agreed_address_at_cut:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,(PG : (num # num) option list),fnc,shfnc)
    ce cx ty (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) es
    (st0,sa,sb,shadow_sa,shadow_sb,vv,s0,G0,tn0) /\
  args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
  later = amount::((if hs then [salt] else []) ++ [off]) /\
  lower_value compile_expr ce (expr_type target) target sa = (target_op,ca) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type target)
    (gas_shadow_expr target) shadow_sa = (target_op,sca) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (sa,ca,shadow_sa,sca) /\
  create_expr_prefix sa ca (gas_explicit_sites ctx shctx) ctx fnc s0 chunk u /\
  u.vs_current_bb = ca.cs_current_bb /\ u.vs_inst_idx = LENGTH ca.cs_current_insts /\
  (!start. expr_body_pre ce cx env target start /\
    body_const_cells_agree [(NONE,tops)] cx env start /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,fnc,shfnc) ce cx (expr_type target) target start
      (st0,sa,ca,shadow_sa,sca,target_op,s0,G0,tn0) ==>
    gas_completed_operand (DF,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
      tops cx st0 sa ca (bind (eval_expr cx target) (read_result cx)) (start,s0,G0,tn0)
      (expr_sim_full_post (DF,lo,d,ctx,fnc) ce cx target (start,sa,ca,s0,target_op,G0,tn0))) /\
  eval_expr cx (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df)
    (es with gas_obs := gas_explicit (chunk ++ rest) s0.vs_gas_readings ++ tail) = (res,out) /\
  valid_horizon cx st0 H out.storage_trace ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?av aw p G tn.
    dest_AddressV av = SOME (w2w aw) /\ eval_operand target_op u = SOME aw /\
    (!x. target_op = Var x ==> not_fresh_at ca x) /\
    bind (eval_exprs cx (ctors ++ later))
      (\vs. eval_create_operands cx (CreateFromBlueprint raw) hs rof
        (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::vs)) p = (res,out) /\
    p.gas_obs = gas_explicit rest u.vs_gas_readings ++ tail /\
    valid_horizon cx st0 H p.storage_trace /\ expr_sim_inv ce cx env p /\
    body_const_cells_agree [(NONE,tops)] cx env p /\
    local_ptrs_reserved ce ca /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
    return_buf_frame d ce ca u /\ alloca_history fnc u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_fmp_headroom i z) /\
    (!h. valid_horizon cx st0 h p.storage_trace ==>
      stmt_state_rel h ctx fnc ce cx p u /\ storage_well_formed_on cx p (FST h) /\
      ghost_inv_at (DF h) lo d ce cx p G tn u) /\
    ~u.vs_halted /\ u.vs_current_bb = ca.cs_current_bb /\ u.vs_inst_idx = LENGTH ca.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all selected_blueprint_address_source >> strip_tac >>
  qabbrev_tac `start = es with gas_obs := gas_explicit (chunk ++ rest) s0.vs_gas_readings ++ tail` >>
  qmatch_asmsub_abbrev_tac `bind (bind (eval_expr cx target) (read_result cx)) k start = _` >>
  `!av. storage_trace_frame (k av)` by
    simp[Abbr `k`, blueprint_read_list_frame, storage_trace_frame_create_operands] >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[expr_vv_sim_full_pre_def]) >>
  `start.gas_obs = gas_explicit (chunk ++ rest) s0.vs_gas_readings ++ tail` by simp[Abbr `start`] >>
  `!h. valid_horizon cx st0 h start.storage_trace ==>
       stmt_state_rel h ctx fnc ce cx start s0 /\ storage_well_formed_on cx start (FST h) /\
       ghost_inv_at (DF h) lo d ce cx start G0 tn0 s0` by
    (qx_gen_tac `h` >>
     `storage_well_formed_on cx start (FST h) <=> storage_well_formed_on cx es (FST h)` by
       (irule storage_well_formed_on_backends >> simp[Abbr `start`]) >>
     `ghost_inv_at (DF h) lo d ce cx start G0 tn0 s0 <=>
      ghost_inv_at (DF h) lo d ce cx es G0 tn0 s0` by simp[Abbr `start`,ghost_inv_at_def] >>
     `stmt_state_rel h ctx fnc ce cx start s0 <=> stmt_state_rel h ctx fnc ce cx es s0` by
       simp[Abbr `start`] >>
     `start.storage_trace = es.storage_trace` by simp[Abbr `start`] >>
     asm_rewrite_tac[]) >>
  `expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,fnc,shfnc) ce cx (expr_type target) target start
      (st0,sa,ca,shadow_sa,sca,target_op,s0,G0,tn0) ==>
   gas_completed_operand (DF,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
      tops cx st0 sa ca (bind (eval_expr cx target) (read_result cx)) (start,s0,G0,tn0)
      (expr_sim_full_post (DF,lo,d,ctx,fnc) ce cx target (start,sa,ca,s0,target_op,G0,tn0))` by
    (strip_tac >> first_assum irule >> simp[]) >>
  drule_all blueprint_read_at_cut_from_replay >>
  strip_tac >- (disj1_tac >> qexists_tac `err` >> simp[]) >>
  rename1 `k av p = (res,out)` >>
  `body_const_cells_agree [(NONE,tops)] cx env p` by
    (irule body_const_cells_agree_expr_read >>
     goal_assum (drule_at Any) >>
     drule expr_body_pre_static_facts >> simp[]) >>
  `post_value_type ce target = BaseT AddressT` by simp[is_word_type_def] >>
  `?aw. dest_AddressV av = SOME (w2w aw) /\ eval_operand target_op u = SOME aw` by
    (irule selected_blueprint_address_word >> simp[] >> metis_tac[]) >>
  `!x. target_op = Var x ==> not_fresh_at ca x` by
    metis_tac[compile_lower_value_var] >>
  drule_all blueprint_keyword_mono >> strip_tac >>
  disj2_tac >> qexistsl_tac [`av`,`aw`,`p`,`G'`,`tn'`] >> fs[Abbr `k`] >>
  first_assum ACCEPT_TAC
QED
