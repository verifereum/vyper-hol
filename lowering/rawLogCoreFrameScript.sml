(* RawLog's LOG step and state/frame facts, in a light theory so the joint
 * raw_log proof can import them without exprSimRawLog's cone. Moved from
 * exprSimRawLog, statements unchanged. *)
Theory rawLogCoreFrame
Ancestors
  extCallOracleStep loweringPosts exprLoweringProps loweringStateRelDefs
  vyperEvent venomExecSemantics venomMemDefs venomState list

Theorem raw_log_state_rel:
  stmt_state_rel H ctx func cenv cx es s ==>
  stmt_state_rel H ctx func cenv cx
    (es with logs := es.logs ++ [ev])
    (s with vs_logs := s.vs_logs ++ [ev])
Proof
  strip_tac >>
  gvs[stmt_state_rel_def, state_rel_def, immutable_base_zero_alt, logs_rel_eq,
      local_ptrs_rel_def, local_region_def, local_backed_def,
      storage_rel_def, transient_rel_def, accounts_rel_def,
      immutables_rel_def, immutable_alloca_sep_def,
      alloca_room_def, fmp_room_def, pending_alloca_size_def, alloca_inv_def,
      lookup_var_def, contract_storage_def, contract_transient_def,
      allocas_non_overlapping_def, alloca_next_valid_def] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem raw_log_core_step:
  inst.inst_opcode = LOG /\
  inst.inst_operands = Lit (n2w (LENGTH ops)) ::
    (REVERSE ops ++ [sz; pop]) /\
  LENGTH ops < dimword (:256) /\
  eval_operand pop s = SOME off /\ eval_operand sz s = SOME len /\
  eval_operands ops s = SOME topics /\ ~s.vs_call_ctx.cc_static ==>
  step_inst_base inst s =
    OK (s with vs_logs := s.vs_logs ++
      [<| logger := w2w s.vs_call_ctx.cc_address; topics := topics;
          data := TAKE (w2n len)
            (DROP (w2n off) s.vs_memory ++ REPLICATE (w2n len) 0w) |>])
Proof
  strip_tac >>
  simp[step_inst_base_def, rich_listTheory.REVERSE_APPEND,
       wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]
QED

Theorem raw_log_wb_frame:
  wb_frame cenv es es' sa s0 s /\ es''.scopes = es'.scopes ==>
  wb_frame cenv es es'' sa s0 (s with vs_logs := logs)
Proof
  strip_tac >>
  qpat_x_assum `wb_frame _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[wb_frame_def, locals_kept_def, popped_kept_def] >>
  qpat_x_assum `es''.scopes = _` (fn th => pure_rewrite_tac[th]) >>
  simp[lookup_var_def] >> strip_tac >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem raw_log_core_frame:
  inst.inst_opcode = LOG /\
  inst.inst_operands = Lit (n2w (LENGTH ops)) ::
    (REVERSE ops ++ [sz; pop]) /\ LENGTH ops < dimword (:256) /\
  eval_operand pop s = SOME off /\ eval_operand sz s = SOME len /\
  eval_operands ops s = SOME (MAP event_value_to_word vals) /\
  TAKE (w2n len) (DROP (w2n off) s.vs_memory ++
    REPLICATE (w2n len) 0w) = bytes /\
  stmt_state_rel H ctx func cenv cx es s /\ wb_frame cenv es0 es sa s0 s ==>
  ?t. step_inst_base inst s = OK t /\
    stmt_state_rel H ctx func cenv cx
      (es with logs := es.logs ++
        [encode_raw_event_values cx.txn.target vals bytes]) t /\
    wb_frame cenv es0 (es with logs := es.logs ++ [encode_raw_event_values cx.txn.target vals bytes]) sa s0 t
Proof
  strip_tac >>
  `~s.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all raw_log_core_step >>
  disch_then SUBST1_TAC >>
  `s.vs_call_ctx.cc_address = cx.txn.target` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  simp[encode_raw_event_values_def, encode_raw_event_def] >>
  conj_tac >- (irule raw_log_state_rel >> simp[]) >>
  irule raw_log_wb_frame >> simp[] >> qexists_tac `es` >> simp[]
QED
