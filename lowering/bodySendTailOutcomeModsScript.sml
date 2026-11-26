(* Linked Send suffix: preserve immutable and ghost frames through CALL/ASSERT. *)
Theory bodySendTailOutcomeMods
Ancestors
  bodyFullSendTail bodyFullPostsMods bodyFullShadowBodyInv bodyForRangeScalarFrameMods
  bodyFullShared bodyInvSplit bodyPtrDefs bodyFullHashKeccakFixed allocaHistory
  gasOutcomeFullMods gasOutcomeFullPostMods gasOutcomeFull gasSummary gasStorage gasContext
  fragGasOriginPtr fragExec exprSendPtr exprSimSend exprLoweringProps loweringPosts
  loweringStateRelDefs localPtrsProps compileEnv venomMemProofs ghostPcTransportPtr
  venomExecProofs venomExecSemantics venomState venomInst list

Theorem send_tail_path_certified_mods[local]:
  expr_has_effect e /\
  emit_op CALL [gas; addr; value; Lit 0w; Lit 0w; Lit 0w; Lit 0w] sm = (success,s3) /\
  emit_void ASSERT [success] s3 = (void,sb) /\ fn_has_code sm sb fn /\
  fn_inst_ids_distinct fn /\ alloca_history fn s /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!H. valid_horizon cx st0 H es'.storage_trace ==>
     stmt_state_rel H ctx fn cenv cx es1 s /\
     storage_well_formed_on cx es' (FST H) /\
     immutable_frame_mods fn cenv cx es1 s /\
     ghost_inv_at_mods (DF H) lo d cenv cx es1 G tn s) /\
  wb_frame cenv es es1 sa s0 s /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  outcomes_accounts_typed es1.outcomes /\ accounts_runtime_well_typed es1.accounts /\
  op_taint tn gas = {} /\ op_taint tn addr = {} /\ op_taint tn value = {} /\
  eval_operand gas s = SOME gw /\
  w2n gw = (case OPTION_BIND (ext_call_kwarg EKGas [EKGas] gas_vs) dest_NumV of
               NONE => 0 | SOME g => g) /\
  eval_operand addr s = SOME aw /\ dest_AddressV to_v = SOME (w2w aw) /\
  eval_operand value s = SOME vw /\ dest_NumV amount_v = SOME (w2n vw) /\
  LENGTH gas_vs = (if has_gas then 1 else 0) /\
  (do tv <- eval_send cx has_gas (to_v::amount_v::gas_vs);
      read_result cx tv od) es1 = (res,es') /\
  post_value_type cenv e = expr_type e /\ expr_type e = NoneT ==>
  ?G' tn' r. !H. valid_horizon cx st0 H es'.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (r,G',tn') /\
    ((?z. r = OK z /\ res = INL NoneV /\
      expr_post_mods H ctx fn cenv cx e es sa sb s0 es' NoneV (Lit 0w) z /\
      ghost_inv_at_mods (DF H) lo d cenv cx es' G' tn' z /\
      ghost_kept_at lo cenv es1 sm G tn s G' tn' /\
      z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history fn z /\ z.vs_alloca_next = s.vs_alloca_next /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp z)) \/
     (exit_result r /\ expr_exit res r /\ halt_exit H cx es' res r /\
      create_size_exit_ok ctx res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)))
Proof
  strip_tac >> (* linked path split *)
  reverse (Cases_on `?H0. valid_horizon cx st0 H0 es'.storage_trace`)
  >- (qexistsl_tac [`G`,`tn`,`ARB`] >> metis_tac[]) >>
  pop_assum (qx_choose_then `H0` assume_tac) >>
  drule_all call_assert_code_lookup >> strip_tac >>
  drule_all send_tail_shape >> strip_tac >>
  `~not_fresh_at sm out /\ ~not_fresh_at sa out` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qabbrev_tac `inst = mk_inst sm.cs_next_id CALL
    [gas;addr;value;Lit 0w;Lit 0w;Lit 0w;Lit 0w] [out]` >>
  `inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
   inst.inst_operands = [gas;addr;value;Lit 0w;Lit 0w;Lit 0w;Lit 0w] /\
   get_instruction bb s.vs_inst_idx = SOME inst /\
   get_instruction bb (SUC s.vs_inst_idx) =
     SOME (mk_inst (sm.cs_next_id + 1) ASSERT [Var out] []) /\
   lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   out = STRING #"%" (toString sm.cs_next_var)` by
    (simp[Abbr `inst`,mk_inst_def] >> gvs[]) >>
  `es'.scopes = es1.scopes /\ es'.immutables = es1.immutables` by
    (drule eval_send_read >> strip_tac >>
     drule vyperCallOutcomeFrameTheory.eval_send_preserves_non_accounts >> simp[]) >>
  `!H. valid_horizon cx st0 H es'.storage_trace ==>
    stmt_state_rel H ctx fn cenv cx es1 s /\ stor_taint_ok_at (DF H) tn s` by
    (rpt strip_tac >> res_tac >> fs[ghost_inv_at_mods_def]) >>
  `allocas_from lo s` by
    (res_tac >> fs[ghost_inv_at_mods_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (qpat_assum `!H. valid_horizon _ _ H es'.storage_trace ==>
      stmt_state_rel H ctx fn cenv cx es1 s /\ stor_taint_ok_at (DF H) tn s`
       (qspec_then `H0` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o CONJUNCT1)) >>
  drule_all send_read_checked_tail_full_uniform >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`]
    (DISJ_CASES_THEN2 (CONJUNCTS_THEN2 assume_tac strip_assume_tac) strip_assume_tac))
  >- suspend "halt" >>
  gvs[] >- suspend "normal" >> suspend "failed"
QED

Resume send_tail_path_certified_mods[halt]:
  `create_size_exit_ok ctx res (Abort ExHalt_abort (halt_state (set_returndata [] s)))` by
    (pure_rewrite_tac[createSizeExitTheory.create_size_exit_ok_def] >> strip_tac >>
     `MEM fn ctx.ctx_functions` by
       (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
          (qspec_then `H0` mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
        drule stateRelProjTheory.stmt_state_rel_alloca_room >>
        simp[alloca_room_def] >> metis_tac[venomInstTheory.lookup_function_MEM]) >>
     drule_all createSizeExitTheory.oversized_create_abort_at_cursor >> simp[]) >>
  qexistsl_tac [`G`,`tn`,
    `Abort ExHalt_abort (halt_state (set_returndata [] s))`] >>
  qpat_x_assum `res = _ \/ res = _` strip_assume_tac >>
  rpt strip_tac >> res_tac >>
  gvs[fragExecTheory.exit_result_def,exprSimDefsTheory.expr_exit_def,
       exprSimDefsTheory.halt_exit_def]
QED

Resume send_tail_path_certified_mods[failed]:
  qmatch_asmsub_abbrev_tac `step_inst_base inst s = OK u` >>
  qexistsl_tac [`step_prov PG G inst u`,`step_taint inst s u tn`,
    `Abort Revert_abort (revert_state
      (set_returndata [] (u with vs_inst_idx := SUC s.vs_inst_idx)))`] >>
  rpt strip_tac >> res_tac >>
  gvs[fragExecTheory.exit_result_def,exprSimDefsTheory.expr_exit_def,
       exprSimDefsTheory.halt_exit_def]
QED

Resume send_tail_path_certified_mods[normal]:
  qmatch_asmsub_abbrev_tac `step_inst_base inst s = OK u` >>
  `stmt_state_rel H0 ctx fn cenv cx es1 s` by metis_tac[] >>
  `ghost_kept_at lo cenv es1 sm G tn s (step_prov PG G inst u)
     (step_taint inst s u tn)` by
    (drule_all send_call_runtime_frame >> strip_tac >>
     irule callStepPtrTheory.call_ghost_kept_at >> metis_tac[]) >>
  `u.vs_current_bb = s.vs_current_bb /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_allocas = s.vs_allocas` by
    (simp[Abbr `u`,update_var_def] >>
     qpat_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `alloca_history fn (u with vs_inst_idx := SUC (SUC s.vs_inst_idx))` by
    (`alloca_inv s` by fs[stmt_state_rel_def] >>
     `alloca_history fn (u with vs_inst_idx := SUC s.vs_inst_idx)` by
       (qspecl_then [`fn`,`s`,`bb`,`inst`,`u`] mp_tac alloca_history_base_step >>
        simp[Abbr `inst`,is_terminator_def]) >>
     `alloca_inv (u with vs_inst_idx := SUC s.vs_inst_idx)` by
       (irule alloca_inv_fields >> qexists_tac `s` >> simp[]) >>
     `eval_operand (Var (STRING #"%" (toString sm.cs_next_var))) (u with vs_inst_idx := SUC s.vs_inst_idx) = SOME 1w` by
       (fs[eval_operand_def,lookup_var_def] >> first_assum ACCEPT_TAC) >>
     `step_inst_base (mk_inst (sm.cs_next_id + 1) ASSERT [Var (STRING #"%" (toString sm.cs_next_var))] [])
        (u with vs_inst_idx := SUC s.vs_inst_idx) =
        OK (u with vs_inst_idx := SUC s.vs_inst_idx)` by
       (simp[mk_inst_def] >> drule step_assert_behavior >> simp[]) >>
     qspecl_then [`fn`,`u with vs_inst_idx := SUC s.vs_inst_idx`,`bb`,
       `mk_inst (sm.cs_next_id + 1) ASSERT [Var (STRING #"%" (toString sm.cs_next_var))] []`,
       `u with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac alloca_history_base_step >>
     simp[mk_inst_def,is_terminator_def]) >>
  qexistsl_tac [`step_prov PG G inst u`,`step_taint inst s u tn`,
    `OK (u with vs_inst_idx := SUC (SUC s.vs_inst_idx))`] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> state_rel _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> storage_well_formed_on _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `stmt_state_rel H ctx fn cenv cx es1 s` by metis_tac[] >>
  conj_tac >- simp[] >>
  qabbrev_tac `z = u with vs_inst_idx := SUC (SUC s.vs_inst_idx)` >>
  `expr_post H ctx fn cenv cx e es sa sb s0 es' NoneV (Lit 0w) z` by
    (simp[Abbr `z`,Abbr `u`] >> irule send_tail_none_post >> simp[] >>
     conj_tac >- (qexists_tac `sm` >> simp[]) >>
     qexistsl_tac [`es1`,`s`] >> simp[]) >>
  `!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s` by
    (rpt strip_tac >>
     `x <> STRING #"%" (toString sm.cs_next_var)` by
       fs[loweringStateRelDefsTheory.not_fresh_at_def] >>
     `lookup_var x u = lookup_var x s` by
       (drule_all send_call_runtime_frame >> strip_tac >> metis_tac[]) >>
     simp[Abbr `z`,lookup_var_def] >> metis_tac[lookup_var_def]) >>
  `z.vs_memory = s.vs_memory /\ z.vs_allocas = s.vs_allocas /\
   z.vs_alloca_next = s.vs_alloca_next /\
   z.vs_data_section = s.vs_data_section` by
    (simp[Abbr `z`] >>
     drule_all send_call_runtime_frame >> strip_tac >>
     `~is_terminator inst.inst_opcode` by simp[Abbr `inst`,is_terminator_def] >>
     qspecl_then [`inst`,`s`,`u`] mp_tac
       venomInstProofs1Theory.step_inst_base_preserves_all >>
     impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC) >>
     metis_tac[venomMemProofsTheory.step_inst_base_preserves_alloca_fields]) >>
  `immutable_frame_mods fn cenv cx es' z` by
    (drule_all immutable_frame_mods_exterior_frame >> simp[]) >>
  `expr_post_mods H ctx fn cenv cx e es sa sb s0 es' NoneV (Lit 0w) z` by
    (simp[expr_post_mods_def] >> metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (qpat_assum `expr_post H ctx fn cenv cx e es sa sb s0 es' NoneV (Lit 0w) z`
       (ACCEPT_TAC o MATCH_MP
         bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o
         CONJUNCT1 o REWRITE_RULE[expr_post_def])) >>
  `ghost_inv_at_mods (DF H) lo d cenv cx es' (step_prov PG G inst u)
      (step_taint inst s u tn) z` by
    (`!n p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==>
       p <> STRING #"%" (toString sm.cs_next_var)` by
       (rpt strip_tac >>
        `not_fresh_at sm p` by
          (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
        fs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[]) >>
     `!p sz. p <> STRING #"%" (toString sm.cs_next_var) ==>
        (ptr_covers (step_prov PG G inst u)
          (step_taint inst s u tn) p z sz <=> ptr_covers G tn p s sz)` by
       (rpt strip_tac >>
        `lookup_var p u = lookup_var p s` by
          (drule_all send_call_runtime_frame >> metis_tac[]) >>
        simp[Abbr `z`, lookup_var_def] >>
        irule callStepPtrTheory.call_ptr_covers >> simp[]) >>
     `stor_taint_ok_at (DF H) (step_taint inst s u tn) u` by
       (irule send_call_stor_taint_at >> metis_tac[]) >>
     `u.vs_fmp = s.vs_fmp` by
       (drule_all send_call_runtime_frame >> metis_tac[]) >>
     `(step_taint inst s u tn).t_mem = tn.t_mem` by
       (irule callStepPtrTheory.call_zero_region_memory_taint >> metis_tac[]) >>
     `z.vs_memory = s.vs_memory` by simp[Abbr `z`] >>
     gvs[ghost_inv_at_mods_def, ptrDisciplineTheory.allocas_from_def] >>
     simp[] >> reverse (rpt conj_tac)
     >- metis_tac[]
     >- (rpt strip_tac >>
         `x <> STRING #"%" (toString sm.cs_next_var)` by
           (`not_fresh_at sm x` by
              (irule exprLoweringPropsTheory.local_ptrs_reserved_imm_base >> metis_tac[]) >>
            fs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[]) >>
         `FLOOKUP G x = NONE /\ op_taint tn (Var x) = {}` by metis_tac[] >>
         metis_tac[callStepPtrTheory.call_old_variable_ghost])
     >- (gvs[Abbr `z`, stor_taint_ok_at_def] >> metis_tac[])
     >- (rpt strip_tac >>
         `not_fresh_at sm x` by metis_tac[] >>
         `x <> STRING #"%" (toString sm.cs_next_var)` by
           (fs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[]) >>
         `op_taint tn (Var x) = {}` by metis_tac[] >>
         metis_tac[callStepPtrTheory.call_old_variable_ghost])
     >- (Cases_on `d` >- simp[return_buf_ptr_def] >>
         rename1 `return_buf_ptr (SOME pair) _ _ _ _` >>
         PairCases_on `pair` >> gvs[return_buf_ptr_def] >> metis_tac[])
     >- (rpt strip_tac
         >- (`p <> STRING #"%" (toString sm.cs_next_var)` by metis_tac[] >>
             `not_fresh_at sm p` by
               (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
             `ptr_covers G tn p s sz` by metis_tac[] >>
             metis_tac[])
         >- (rpt strip_tac >>
             `not_fresh_at sm p` by
               (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
             `lookup_var p z = lookup_var p s` by
               (qpat_assum `!x. not_fresh_at sm x ==>
                  lookup_var x z = lookup_var x s`
                  (qspec_then `p` assume_tac) >>
                qpat_assum `not_fresh_at sm p ==>
                  lookup_var p z = lookup_var p s`
                  (fn th => irule th) >> first_assum ACCEPT_TAC) >>
             metis_tac[]))) >>
  qexists_tac `z` >> simp[] >> fs[Abbr `z`]
QED

Finalise send_tail_path_certified_mods[local]

Theorem send_tail_path_full_mods[local]:
  expr_has_effect e /\
  emit_op CALL [gas; addr; value; Lit 0w; Lit 0w; Lit 0w; Lit 0w] sm = (success,s3) /\
  emit_void ASSERT [success] s3 = (void,sb) /\ fn_has_code sm sb fn /\
  fn_inst_ids_distinct fn /\ alloca_history fn s /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!H. valid_horizon cx st0 H es'.storage_trace ==>
     stmt_state_rel H ctx fn cenv cx es1 s /\
     storage_well_formed_on cx es' (FST H) /\
     immutable_frame_mods fn cenv cx es1 s /\
     ghost_inv_at_mods (DF H) lo d cenv cx es1 G tn s) /\
  wb_frame cenv es es1 sa s0 s /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  outcomes_accounts_typed es1.outcomes /\ accounts_runtime_well_typed es1.accounts /\
  op_taint tn gas = {} /\ op_taint tn addr = {} /\ op_taint tn value = {} /\
  eval_operand gas s = SOME gw /\
  w2n gw = (case OPTION_BIND (ext_call_kwarg EKGas [EKGas] gas_vs) dest_NumV of
               NONE => 0 | SOME g => g) /\
  eval_operand addr s = SOME aw /\ dest_AddressV to_v = SOME (w2w aw) /\
  eval_operand value s = SOME vw /\ dest_NumV amount_v = SOME (w2n vw) /\
  LENGTH gas_vs = (if has_gas then 1 else 0) /\
  (do tv <- eval_send cx has_gas (to_v::amount_v::gas_vs);
      read_result cx tv od) es1 = (res,es') /\
  post_value_type cenv e = expr_type e /\ expr_type e = NoneT ==>
  ?G' tn' r. !H. valid_horizon cx st0 H es'.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (r,G',tn') /\
    ((?z. r = OK z /\ res = INL NoneV /\
      expr_post_mods H ctx fn cenv cx e es sa sb s0 es' NoneV (Lit 0w) z /\
      ghost_inv_at_mods (DF H) lo d cenv cx es' G' tn' z /\
      ghost_kept_at lo cenv es1 sm G tn s G' tn' /\
      z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history fn z /\ z.vs_alloca_next = s.vs_alloca_next /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp z)) \/
     (exit_result r /\ expr_exit res r /\ halt_exit H cx es' res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)))
Proof
  strip_tac >> drule_all send_tail_path_certified_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`G'`,`tn'`,`r`] >>
  qx_gen_tac `H` >> strip_tac >>
  first_x_assum (qspec_then `H` mp_tac) >>
  simp[] >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  simp[]
QED

Theorem send_tail_outcome_full_mods:
  expr_has_effect e /\
  emit_op CALL [gas;addr;value;Lit 0w;Lit 0w;Lit 0w;Lit 0w] sm = (success,s3) /\
  emit_void ASSERT [success] s3 = (void,sb) /\ fn_has_code sm sb fn /\
  fn_inst_ids_distinct fn /\ alloca_history fn s /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    stmt_state_rel H ctx fn cenv cx es1 s /\
    storage_well_formed_on cx es1 (FST H) /\
    immutable_frame_mods fn cenv cx es1 s /\
    ghost_inv_at_mods (DF H) lo d cenv cx es1 G tn s) /\
  wb_frame cenv es es1 sa s0 s /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  outcomes_accounts_typed es1.outcomes /\ accounts_runtime_well_typed es1.accounts /\
  op_taint tn gas = {} /\ op_taint tn addr = {} /\ op_taint tn value = {} /\
  eval_operand gas s = SOME gw /\
  w2n gw = (case OPTION_BIND (ext_call_kwarg EKGas [EKGas] gas_vs) dest_NumV of
               NONE => 0 | SOME g => g) /\
  eval_operand addr s = SOME aw /\ dest_AddressV to_v = SOME (w2w aw) /\
  eval_operand value s = SOME vw /\ dest_NumV amount_v = SOME (w2n vw) /\
  LENGTH gas_vs = (if has_gas then 1 else 0) /\
  post_value_type cenv e = expr_type e /\ expr_type e = NoneT /\ es1.gas_obs = [] ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,fn,PG) mods cx st0
    (do tv <- eval_send cx has_gas (to_v::amount_v::gas_vs); read_result cx tv od)
    (es1,s,G,tn)
    (\H res ee G' tn' z. res = INL NoneV /\
      expr_post_mods H ctx fn cenv cx e es sa sb s0 ee NoneV (Lit 0w) z /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' z /\
      ghost_kept_at lo cenv es1 sm G tn s G' tn' /\
      z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history fn z /\ z.vs_alloca_next = s.vs_alloca_next /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp z))
    (\H res ee gt r. exprSimDefs$expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >>
  qabbrev_tac `src = do tv <- eval_send cx has_gas (to_v::amount_v::gas_vs);
                       read_result cx tv od` >>
  Cases_on `src es1` >> rename1 `src es1 = (res,ee)` >>
  `ee.gas_obs = es1.gas_obs /\
   !gs. src (es1 with gas_obs := gs) = (res,ee with gas_obs := gs)` by
    (fs[Abbr `src`,SF ETA_ss] >>
     qspec_then `read_result cx` mp_tac (GEN_ALL sendSourceFrameTheory.send_bind_gas_frame) >>
     simp[vyperStateTheory.read_result_def,vyperStateTheory.return_def,SF ETA_ss] >>
     disch_then drule >> simp[]) >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `(do tv <- eval_send cx has_gas (to_v::amount_v::gas_vs);
       read_result cx tv od) es1 = (res,ee)` by fs[Abbr `src`] >>
  reverse (Cases_on `storage_trace_domain cx st0 ee.storage_trace`)
  >- (irule gas_outcome_full_mods_bad_nil >> fs[Abbr `src`]) >>
  `storage_trace_frame src` by
    (simp[Abbr `src`] >>
     irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
     simp[vyperStorageTraceTheory.storage_trace_frame_send,
          vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx fn cenv cx es1 s /\
    storage_well_formed_on cx ee (FST H) /\
    immutable_frame_mods fn cenv cx es1 s /\
    ghost_inv_at_mods (DF H) lo d cenv cx es1 G tn s` by
    (qx_gen_tac `H` >> strip_tac >>
     `valid_horizon cx st0 H es1.storage_trace` by
       metis_tac[vyperStorageFootprintTheory.valid_horizon_frame] >>
     qpat_assum `!H. valid_horizon _ _ H es1.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (drule eval_send_read >> strip_tac >>
       irule vyperFiniteStoragePreservationTheory.eval_send_preserves_storage_well_formed_on >>
       conj_tac >- fs[vyperStorageFootprintTheory.valid_horizon_def] >>
       qexistsl_tac [`has_gas`,`r`,`es1`,`to_v::amount_v::gas_vs`] >> simp[]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     first_assum ACCEPT_TAC) >>
  drule_all send_tail_path_certified_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  rewrite_tac[gas_outcome_full_mods_def] >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
  simp[gas_explicit_def] >>
  qx_gen_tac `H` >> strip_tac >>
  first_x_assum (qspec_then `H` mp_tac) >>
  simp[] >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  simp[]
QED
