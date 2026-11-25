Theory createSizeRawPayloadRowsMods
Ancestors
  createSizeCtorRowsReplayMods createCtorRowCutsMods createSizeOperandPreMods
  createSizeBlueprintAbiKeywords createSizeBlueprintKeywordReplay
  createSizePrefixReplay createCtorObservedSilence fragGasOrigin venomInst
  vyperStorageTrace vyperStorageFootprint vyperCreate list exprLoweringProps
  relation createMarkedPath pair

Theorem create_raw_payload_replay_rows_mods:
  args <> [] /\
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ shadow_body_inv_mods mods exps ctx shctx /\
  expr_body_pre_mods mods ce cx env
    (Call ann (CreateTarget RawCreate hs rof ks) (e::av::(args ++ (if hs then [saltE] else []))) df) entry /\
  EVERY (create_operand_completed_ok_mods mods exps cx)
    (create_operand_order RawCreate hs (e::av::(args ++ (if hs then [saltE] else [])))) /\
  (!i s vs s'. i < LENGTH args /\ ~exprs_can_mutate ce (DROP (SUC i) args) /\
    eval_exprs cx (DROP (SUC i) args) s = (INL vs,s') ==>
    !tr. get_storage cx s' tr = get_storage cx s tr) /\
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
     else ~is_word_type (lowered_value_type ce (EL i args)) ==> Mid i = St (SUC i))) ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?vs E Gf tf. E 0 = p0 /\ LENGTH vs = LENGTH args /\
    eval_exprs cx args p0 = (INL vs,E (LENGTH args)) /\
    bind (eval_exprs cx (av::(if hs then [saltE] else [])))
      (\kvs. eval_create_operands cx RawCreate hs rof tys lit (BytesV code::(vs ++ kvs)))
      (E (LENGTH args)) = (res,out) /\
    valid_horizon cx st0 H (E (LENGTH args)).storage_trace /\
    (!i. i <= LENGTH args ==>
      (E i).gas_obs = gas_explicit (R i) (St i).vs_gas_readings ++ tail /\
      expr_sim_inv_mods mods ce cx env (E i) /\ return_buf_frame d ce (C i) (St i) /\
      alloca_history func (St i) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp (St i)) /\
      (!f j z. frag_reachable ctx func (St i) f j z ==> dalloca_fmp_headroom j z) /\
      ~(St i).vs_halted /\ (St i).vs_current_bb = (C i).cs_current_bb /\
      (St i).vs_inst_idx = LENGTH (C i).cs_current_insts) /\
    (!K. valid_horizon cx st0 K (E (LENGTH args)).storage_trace ==>
      stmt_state_rel K ctx func ce cx (E (LENGTH args)) (St (LENGTH args)) /\
      immutable_frame_mods func ce cx (E (LENGTH args)) (St (LENGTH args)) /\
      storage_well_formed_on cx (E (LENGTH args)) (FST K) /\
      ghost_inv_at_mods (DF K) lo d ce cx (E (LENGTH args)) Gf tf (St (LENGTH args))) /\
    (!i. i < LENGTH args ==>
      bind (eval_expr cx (EL i args)) (read_result cx) (E i) = (INL (EL i vs),E (SUC i)) /\
      expr_body_pre_mods mods ce cx env (EL i args) (E i) /\
      (?tv ann. evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
        evaluate_type (get_tenv cx) (expr_type (EL i args)) = SOME ann /\
        arg_type_fits (lowered_value_type ce (EL i args)) (expr_type (EL i args)) /\
        value_has_type tv (EL i vs) /\ value_has_type ann (EL i vs)) /\
      (!g h. (!K. valid_horizon cx st0 K (E i).storage_trace ==>
          stmt_state_rel K ctx func ce cx (E i) (St i) /\
          storage_well_formed_on cx (E i) (FST K) /\
          ghost_inv_at_mods (DF K) lo d ce cx (E i) g h (St i)) ==>
        (is_word_type (lowered_value_type ce (EL i args)) ==>
          ?g' h'. !K op. valid_horizon cx st0 K (E (SUC i)).storage_trace /\
            lower_value compile_expr ce (expr_type (EL i args)) (EL i args) (C i) =
              (op,C (SUC i)) ==>
            expr_sim_full_post_mods (DF,lo,d,ctx,func) ce cx (EL i args)
              (E i,C i,C (SUC i),St i,op,g,h) K (INL (EL i vs) : value + exception)
              ((E (SUC i)) with gas_obs := []) g' h' (St (SUC i))) /\
        (~is_word_type (lowered_value_type ce (EL i args)) ==>
          ?g' h' raw. eval_expr cx (EL i args) (E i) = (INL raw,E (SUC i)) /\
          !K. valid_horizon cx st0 K (E (SUC i)).storage_trace ==>
            vv_post_mods K ctx func ce cx (EL i args) (E i) (C i) (M i) (St i)
              ((E (SUC i)) with gas_obs := []) raw (V i) (Mid i) /\
            vv_store_bound cx (post_value_type ce (EL i args)) (lowered_value_type ce (EL i args))
              ((E (SUC i)) with gas_obs := []) raw (V i) (Mid i) /\
            ptr_vv_ok cx (post_value_type ce (EL i args)) raw (V i)
              ((E (SUC i)) with gas_obs := []) g' h' (Mid i) /\
            alloca_history func (Mid i) /\ (St i).vs_alloca_next <= (Mid i).vs_alloca_next /\
            ghost_inv_at_mods (DF K) lo d ce cx ((E (SUC i)) with gas_obs := []) g' h' (Mid i) /\
            ghost_kept_at lo ce (E i) (C i) g h (St i) g' h' /\
            (!tag op. V i = StackValue tag op /\ ~is_word_type (post_value_type ce (EL i args)) ==>
              ptr_buf_ok ce (EL i args) op g' (Mid i)) /\
            (!tag p. V i = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
              ptr_buf_ok ce (EL i args) p.ptr_operand g' (Mid i)) /\
            (ce.ce_is_ctor /\ vv_location (V i) = SOME LocCode ==>
              ?val. read_result cx raw ((E (SUC i)) with gas_obs := []) =
                (INL val,(E (SUC i)) with gas_obs := []) /\
              !rt w. evaluate_type (get_tenv cx) (post_value_type ce (EL i args)) = SOME rt /\
                eval_operand (vv_operand (V i)) (Mid i) = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside h'.t_mem (Mid i).vs_memory mem ==>
                  val_in_memory rt val (w2n w) mem))))) /\
    (!i. i < LENGTH args /\ ~exprs_can_mutate ce (DROP (SUC i) args) ==>
      !tr. get_storage cx (E (LENGTH args)) tr = get_storage cx (E (SUC i)) tr)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `k = \vs. bind (eval_exprs cx (av::(if hs then [saltE] else [])))
    (\kvs. eval_create_operands cx RawCreate hs rof tys lit (BytesV code::(vs ++ kvs)))` >>
  `bind (eval_exprs cx args) k p0 = (res,out)` by
    (qpat_assum `bind (eval_exprs cx (args ++ _)) _ p0 = _`
       (mp_tac o REWRITE_RULE [blueprint_abi_bind_append]) >> simp[Abbr `k`]) >>
  `!vs. storage_trace_frame (k vs)` by
    simp[Abbr `k`,evaluate_storage_trace_frame,storage_trace_frame_bind_all,
         storage_trace_frame_create_operands] >>
  mp_tac (SPEC_ALL (INST_TYPE [alpha |-> ``:eval_result``] create_ctor_rows_at_cuts_mods)) >>
  (impl_tac >- suspend "row_premises") >> strip_tac
  >- (disj1_tac >> qexists_tac `err` >> simp[]) >>
  disj2_tac >> qexistsl [`vs`,`E`,`Gf`,`tf`] >> asm_rewrite_tac[] >>
  conj_tac
  >- (qunabbrev_tac `k` >>
      qpat_assum `_ (E (LENGTH args)) = (res,out)`
        (ACCEPT_TAC o CONV_RULE (DEPTH_CONV BETA_CONV))) >>
  suspend "suffix_storage"
QED

Resume create_raw_payload_replay_rows_mods[row_premises]:
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (qpat_x_assum `EVERY (create_operand_completed_ok_mods mods exps cx) _` mp_tac >>
      Cases_on `hs` >> simp[create_operand_order_def,EVERY_APPEND,DROP_PREFIX,TAKE_APPEND1] >>
      metis_tac[EVERY_MEM,EL_MEM])
  >- (rpt strip_tac >> irule create_call_operand_body_pre_mods >> simp[EL_MEM] >>
      goal_assum (drule_at Any) >> simp[EL_MEM]) >>
  qx_gen_tac `i` >> disch_tac >>
  qpat_assum `!i. i < LENGTH args ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  drule_all blueprint_keyword_mono >> strip_tac >>
  qpat_assum `explicit = _` (fn he => rule_assum_tac (PURE_REWRITE_RULE[he])) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  strip_tac >> fs[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  disch_tac >> irule ctor_observed_cut_silent >>
  qexistsl [`ctx`,`((C (SUC i)).cs_current_bb,LENGTH (C (SUC i)).cs_current_insts)`,
    `gas_explicit_sites ctx shctx`,`func`,`St (SUC i)`,`Mid i`] >>
  rpt conj_tac >> TRY (simp[] >> NO_TAC) >>
  irule RTC_MONOTONE >>
  qpat_assum `create_expr_prefix (M i) (C (SUC i)) _ _ _ _ _ _`
    (irule_at Any o REWRITE_RULE [create_expr_prefix_marked]) >>
  simp[create_marked_edge_def,create_prefix_step_def,FORALL_PROD,PAIR_EQ] >> metis_tac[]
QED

Resume create_raw_payload_replay_rows_mods[suffix_storage]:
  qx_gen_tac `i` >> strip_tac >>
  `SUC i <= LENGTH args` by decide_tac >>
  `eval_exprs cx (DROP (SUC i) args) (E (SUC i)) =
     (INL (DROP (SUC i) vs), E (LENGTH args))` by
    (irule ctor_rows_source_mods >> rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     gen_tac >> disch_tac >>
     qpat_assum `!j. j < LENGTH args ==> vyperState$bind _ _ (E j) = _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  qpat_assum `!i s vs s'. _ ==> !tr. get_storage _ _ tr = _`
    (qspecl_then [`i`,`E (SUC i)`,`DROP (SUC i) vs`,`E (LENGTH args)`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Finalise create_raw_payload_replay_rows_mods
