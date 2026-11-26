(* The reached packing join uses the paired positional compiler cuts. *)
Theory bodyAbiEncodePackReachedMods
Ancestors
  bodyAbiEncodePositionalCutsMods bodyAbiEncodePackFoldMods
  bodyAbiEncodePosHeadRunMods bodyAbiEncodePackConsReachedMods
  bodyAbiEncodePosHeadPostMods bodyAbiEncodePackedPostMods bodyFullPredsMods
  bodyCallSupport vyperTypeContract vyperTypeCallGraph exprSimFullBundleProps
  gasOutcomeFullMods gasExplicitSites gasOriginPtrLabels gasShadowCompileBase gasShadow
  exprSimWordArgs exprSimMemDefs exprSimDefs exprLowering bodyPtrDefs bodyFullPostsMods
  vyperState vyperInterpreter vyperStorageFootprint vyperStorageTrace stmtSimProps list

(* The deployment callback transports only the earlier read at the selected slot. *)
Theorem abi_encode_pack_reached_mods:
  contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  (cx.in_deploy ==> exports_ok cx.layouts cx.txn.target mods exps /\
                   IS_SOME (check_contract F cx.layouts cx.txn.target mods)) /\
  (!H. dead_lo_ok_mods H (DF H) lo ce cx) /\
  body_exprs_full_ok_mods mods exps cx args /\
  EVERY (source_body_call_supported cx) (int_calls_exprs args) /\
  EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_exprs args) /\
  (!e es'. MEM e args /\ expr_sim_inv_mods mods ce cx env es' ==>
     expr_body_pre_mods mods ce cx env e es') /\
  (!e. MEM e args ==> type_alloc_ok ce (lowered_value_type ce e)) /\
  compile_abi_encode_args compile_expr ce args sa = (svs,sb) /\
  compile_abi_encode_args compile_expr (gas_shadow_env T ce)
    (MAP gas_shadow_expr args) sha = (svs,shb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,sha,shb) /\
  body_const_cells_agree_mods mods cx env es /\ expr_sim_inv_mods mods ce cx env es /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es s0 /\ immutable_frame_mods func ce cx es s0 /\
     storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (eval_exprs cx args)
    (\res:value list + exception. case res of INL vs => T | INR ex => expr_res_ok (INR ex)) es /\
  (!pre e xs vs0 obs0 ea a sm ss b vv sv ul s Ga ta marks mid t Gm tm reads vs ee u G tn H
      p tr w tv v.
     cx.in_deploy /\ xs <> [] /\ ~exprs_can_mutate ce xs /\
     args = pre ++ e::xs /\
     (!tail. eval_exprs cx pre (es with gas_obs := obs0 ++ tail) = (INL vs0,ea with gas_obs := tail)) /\
     compile_expr ce (expr_type e) e a = (vv,sm) /\
     compile_snapshot_vv ce (exprs_can_mutate ce xs)
       (ext_call_arg_value (lowered_value_type ce e) vv) sm = (sv,ss) /\
     compile_abi_encode_args compile_expr ce xs ss = (ul,b) /\
     (!tail. vyperState$bind (eval_expr cx e) (read_result cx)
       (ea with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) = (INL v,mid with gas_obs := tail)) /\
     (!tail. eval_exprs cx xs (mid with gas_obs := reads ++ tail) = (INL vs,ee with gas_obs := tail)) /\
     mid.gas_obs = [] /\ ee.gas_obs = [] /\
     valid_horizon cx st0 H ea.storage_trace /\ valid_horizon cx st0 H mid.storage_trace /\
     valid_horizon cx st0 H ee.storage_trace /\
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (s,Ga,ta) marks (OK t,Gm,tm) /\
     abi_encode_pos_head_post_mods mods DF lo d ctx func ce cx env
       e a sm ss vv sv (exprs_can_mutate ce xs) ea s Ga ta H (INL v) mid Gm tm t /\
     abi_encode_packed_post_mods mods DF lo d ctx func ce cx env
       xs ul ss b mid t Gm tm H (INL vs : value list + exception) ee G tn u /\
     ~is_word_type (lowered_value_type ce e) /\ sv = LocatedValue (lowered_value_type ce e) p /\
     p.ptr_location = slot_loc tr /\ eval_operand p.ptr_operand t = SOME w /\
     evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
     read_storage_slot cx tr w tv mid = (INL v,mid) ==>
     read_storage_slot cx tr w tv ee = (INL v,ee)) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    mods cx st0 (eval_exprs cx args) (es,s0,G0,tn0)
    (abi_encode_packed_post_mods mods DF lo d ctx func ce cx env args svs sa sb es s0 G0 tn0)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
                    (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`root` |-> `es`] abi_encode_pack_fold_mods) >>
  impl_tac >- suspend "rules" >>
  disch_then (qspecl_then [`args`,`[]`,`[]`,`[]`,`svs`,`sa`,`sb`,`sha`,`shb`,
                           `es`,`s0`,`G0`,`tn0`] mp_tac) >>
  simp[eval_exprs_nil] >> disch_then irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC
QED

Resume abi_encode_pack_reached_mods[rules]:
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all_then (qx_choosel_then [`v0`,`sm`,`shm`,`sv`,`ss`,`shs`,`rest`] strip_assume_tac)
        (SIMP_RULE (srw_ss()) [] positional_paired_cuts) >>
      qexistsl_tac [`v0`,`sm`,`shm`,`sv`,`ss`,`shs`,`rest`] >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> irule abi_encode_pos_head_run_mods >>
      qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
      qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
      qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` (irule_at Any) >>
      qpat_assum `expr_sim_full_code _ _` (irule_at Any) >> simp[] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  suspend "finish"
QED

Resume abi_encode_pack_reached_mods[finish]:
  rpt gen_tac >> strip_tac >>
  irule abi_encode_pack_cons_reached_mods >>
  qhdtm_assum `abi_encode_pos_head_post_mods` (irule_at Any) >>
  qpat_assum `abi_encode_packed_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (irule_at Any) >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `!tail. eval_exprs cx xs _ = _`
    (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL])) >>
  qpat_assum `eval_exprs cx xs _ = _` (irule_at Any) >>
  asm_rewrite_tac [] >>
  qpat_x_assum `args = _` (SUBST_ALL_TAC o REWRITE_RULE [GSYM APPEND_ASSOC,APPEND]) >>
  conj_tac
  >- (irule abi_encode_suffix_call_keys_mods >> qexistsl_tac [`e`,`pre`] >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (irule abi_encode_suffix_call_keys_mods >> qexistsl_tac [`e`,`pre`] >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `!H. valid_horizon _ _ H es'.storage_trace ==> _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  suspend "slot_read"
QED

Resume abi_encode_pack_reached_mods[slot_read]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!pre e xs vs0 obs0 ea a sm ss b vv sv ul s Ga ta marks mid t Gm tm reads vs ee u G tn H p tr w tv v. _`
    irule >>
  qhdtm_assum `abi_encode_pos_head_post_mods` (irule_at Any) >>
  qhdtm_assum `abi_encode_packed_post_mods` (irule_at Any) >>
  qhdtm_assum `gas_origin_ptr_path` (irule_at Any) >>
  qpat_assum `sv = LocatedValue _ _` (irule_at Any) >>
  qexistsl_tac [`vs0`,`reads`,`pre`,`obs0`] >> simp[]
QED

Finalise abi_encode_pack_reached_mods
