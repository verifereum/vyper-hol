(* The Send transfer and its success check form one installed suffix. *)
Theory entryCreateSendSuffix
Ancestors
  entryCreateEffectFocus entryCreatePathScope exprSimSend createSizeCutCode
  emitHelper emitHelperProps exprLoweringProps fragExec abiEncoderProps
  exprSimAbiGasBridge venomExecSemantics venomInst compileEnv list rich_list
  entryCreateAdminSequence entryCreateFocusSpec createSizePrefixReplay
  entryCreateCompletedCut createMarkedPath fragGasOrigin fragGasSeq fragGasEmitCtrl
  fragGasSeqPtr exprSendPtr memSafeRun gasEvents gasCount venomExecProofs venomState
  callStepPtr instMemFrontier instIdxIndep relation venomInstProps arithmetic

Theorem create_send_effect_code:
  emit_op CALL ops sm = (success,s3) /\ emit_void ASSERT [success] s3 = ((),sb) ==>
  create_cut_code {} sm sb /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code sm sb)
Proof
  strip_tac >> conj_tac
  >- (irule create_cut_code_join >> qexists_tac `s3` >> conj_tac
      >- (qpat_assum `emit_op _ _ _ = _` (fn th =>
             mp_tac (REWRITE_RULE [th,pairTheory.SND]
               (Q.INST [`exits` |-> `{}`,`opc` |-> `CALL`,`ops` |-> `ops`,`a` |-> `sm`]
                 create_cut_code_emit_op)) >> simp[create_cut_targets_def])) >>
      qpat_assum `emit_void _ _ _ = _` (fn th =>
        mp_tac (REWRITE_RULE [th,pairTheory.SND]
          (Q.INST [`exits` |-> `{}`,`opc` |-> `ASSERT`,`ops` |-> `[success]`,`a` |-> `s3`]
            create_cut_code_emit_void)) >> simp[create_cut_targets_def])) >>
  fs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, fresh_id_def, fresh_var_def, emit_def, frag_code_def,
     emitted_insts_def, emitted_blocks_def, mk_inst_def, DROP_LENGTH_APPEND,
     APPEND_ASSOC] >>
  gvs[] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND]
QED

Theorem create_send_effect_cut:
  body_inv tops ctx ce cx /\ MEM func ctx.ctx_functions /\ fn_has_code sm sb func /\
  emit_op CALL ops sm = (success,s3) /\ emit_void ASSERT [success] s3 = ((),sb) ==>
  create_operand_cut sm sb explicit ctx func tops cx st0 source (es,s)
Proof
  strip_tac >> drule_all create_send_effect_code >> strip_tac >>
  irule create_effect_suffix_cut >> metis_tac[]
QED

Theorem create_send_effect_layout:
  emit_op CALL ops sm = (success,s3) /\ emit_void ASSERT [success] s3 = ((),sb) ==>
  ?out. success = Var out /\
    sb.cs_current_bb = sm.cs_current_bb /\
    sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
    emitted_insts sm sb =
      [mk_inst sm.cs_next_id CALL ops [out];
       mk_inst (sm.cs_next_id + 1) ASSERT [Var out] []] /\
    sb.cs_next_id = sm.cs_next_id + 2
Proof
  rw[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND]
QED

Theorem create_send_effect_ok_scope:
  emit_op CALL ops sm = (Var out,s3) /\ emit_void ASSERT [Var out] s3 = ((),sb) /\
  fn_has_code sm sb fn /\ create_operand_at sm s /\ ~s.vs_halted /\
  step_inst_base (mk_inst sm.cs_next_id CALL ops [out]) s = OK u /\
  eval_operand (Var out) u = SOME 1w ==>
  create_operand_full_scope sm sb E C fn s []
    (OK (u with vs_inst_idx := SUC (SUC s.vs_inst_idx)))
Proof
  strip_tac >> drule_all create_send_effect_layout >> strip_tac >> gvs[] >>
  `LENGTH sb.cs_current_insts = SUC (SUC s.vs_inst_idx)` by
    fs[create_operand_at_def] >>
  pop_assum (rewrite_tac o single o SYM) >> irule create_admin_sequence_scope >>
  fs[frag_ids_def, mk_inst_def, is_terminator_def, run_inst_seq_def] >>
  drule step_assert_behavior >> simp[]
QED

(* Read the first edge of the already checked semantic path. Its memory
   condition is retained; no second model of CALL's outcome is introduced. *)
Theorem send_origin_edge_step[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
  gas_origin_edge M E C fn s marks result ==>
  marks = [] /\
  (case step_inst_base i s of
     OK u => result = OK (u with vs_inst_idx := SUC s.vs_inst_idx)
   | other => result = other)
Proof
  rw[gas_origin_edge_def] >> gvs[step_inst_non_invoke, gas_events_step_def] >>
  Cases_on `step_inst_base i s` >> gvs[exit_result_def]
QED

Theorem send_origin_path_exit_cases[local]:
  gas_origin_path M E C fn s [] r /\ exit_result r ==>
  gas_origin_edge M E C fn s [] r \/
    ?v. gas_origin_edge M E C fn s [] (OK v) /\ gas_origin_path M E C fn v [] r
Proof
  rpt strip_tac >>
  qpat_x_assum `gas_origin_path _ _ _ _ _ _ _` (strip_assume_tac o ONCE_REWRITE_RULE[gas_origin_path_cases]) >>
  gvs[exit_result_def] >> metis_tac[]
QED

Theorem create_send_effect_abort_scope:
  emit_op CALL ops sm = (Var out,s3) /\ emit_void ASSERT [Var out] s3 = ((),sb) /\
  fn_has_code sm sb fn /\ create_operand_at sm s /\
  gas_origin_path T E C fn s [] (Abort reason z) ==>
  (step_inst_base (mk_inst sm.cs_next_id CALL ops [out]) s = Abort reason z \/
   ?u. step_inst_base (mk_inst sm.cs_next_id CALL ops [out]) s = OK u /\
       eval_operand (Var out) u = SOME 0w) ==>
  create_operand_full_scope sm sb E C fn s [] (Abort reason z)
Proof
  strip_tac >>
  drule_all create_send_effect_layout >> strip_tac >> gvs[] >>
  drule_all call_assert_code_lookup >> strip_tac >> gvs[] >>
  `LENGTH sb.cs_current_insts = SUC (SUC s.vs_inst_idx)` by fs[create_operand_at_def] >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
     get_instruction bb s.vs_inst_idx = SOME (mk_inst sm.cs_next_id CALL ops [out]) /\
     get_instruction bb (SUC s.vs_inst_idx) =
       SOME (mk_inst (sm.cs_next_id + 1) ASSERT [Var out] [])` by
     fs[create_operand_at_def] >>
  `exit_result (Abort reason z)` by simp[exit_result_def] >>
  drule_all send_origin_path_exit_cases >>
  disch_then (DISJ_CASES_THEN2 assume_tac strip_assume_tac)
  >- (disch_tac >> irule (SIMP_RULE (srw_ss()) []
       (Q.INST [`left` |-> `[]`,`last` |-> `[]`] create_operand_full_scope_terminal)) >>
      simp[] >> qexists_tac `s` >> simp[]) >>
  strip_tac >>
  `?u. step_inst_base (mk_inst sm.cs_next_id CALL ops [out]) s = OK u /\
       eval_operand (Var out) u = SOME 0w /\
       v = u with vs_inst_idx := SUC s.vs_inst_idx` by
    (drule_at (Pat `gas_origin_edge _ _ _ _ _ _ _`) send_origin_edge_step >>
     fs[mk_inst_def,is_terminator_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >> gvs[] >>
  qabbrev_tac `v = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `step_inst 0 C (mk_inst sm.cs_next_id CALL ops [out]) s = OK u` by
    simp[step_inst_non_invoke,mk_inst_def] >>
  `v.vs_current_bb = s.vs_current_bb /\ v.vs_inst_idx = SUC s.vs_inst_idx /\
    eval_operand (Var out) v = SOME 0w` by
    (drule step_preserves_control_flow >>
     simp[Abbr `v`,mk_inst_def,is_terminator_def,eval_operand_def,lookup_var_def] >>
     fs[eval_operand_def,lookup_var_def]) >>
  `step_inst_base (mk_inst (sm.cs_next_id + 1) ASSERT [Var out] []) v =
     Abort Revert_abort (revert_state (set_returndata [] v))` by
    (simp[mk_inst_def] >> drule step_assert_behavior >> simp[]) >>
  `gas_origin_edge T E C fn v [] (Abort reason z)` by
    (drule_at (Pat `gas_origin_path _ _ _ _ v _ _`) send_origin_path_exit_cases >>
     simp[] >> strip_tac >>
     rename1 `gas_origin_edge T E C fn v [] (OK w)` >>
     `lookup_block v.vs_current_bb fn.fn_blocks = SOME bb' /\
      get_instruction bb' v.vs_inst_idx =
        SOME (mk_inst (sm.cs_next_id + 1) ASSERT [Var out] [])` by simp[] >>
     drule_at (Pat `gas_origin_edge _ _ _ _ _ _ _`)
       (Q.INST [`s` |-> `v`,`result` |-> `OK w`] send_origin_edge_step) >>
     fs[mk_inst_def,is_terminator_def]) >>
  irule (SIMP_RULE (srw_ss()) []
    (Q.INST [`left` |-> `[]`,`last` |-> `[]`] create_operand_full_scope_terminal)) >>
  simp[] >> qexists_tac `v` >> simp[] >>
  simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
  simp[create_marked_edge_def,create_prefix_step_def,frag_ids_def] >>
  qpat_assum `gas_origin_edge T E C fn s [] (OK v)` mp_tac >>
  simp[NoAsms,gas_origin_edge_def] >> metis_tac[]
QED
