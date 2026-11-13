(* Counted memory-safe SHA256 suffixes. Semantic facts are reused from the
   task-permitted S1 overlay; all memory checks are proved here. *)
Theory bodyMemBiSha256Compose
Ancestors
  bodyMemBiSha256Suffix bodyExprForceMemory exprSimHash exprSimHashBoundary exprSimMemDefs allocaHistoryFragment
  fragGasSeqMem exprSimProps exprLoweringProps exprOperandVar exprSimWordArgs
  venomMemDefs compileEnv loweringStateRelDefs vyperTypeSystem fragGasSeqAbort fragGasMode
  exprSimPrecompiles fragExec vyperState exprSimDefs exprSimVVFrame venomInstProps venomExecSemantics venomMemProps venomMemProofs
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext fragGasPath
  exprSimSource exprSimHypsDefs exprSimHyps vyperTyping builtinSimple exprLowering

Theorem sha256_typed_suffix_mem_ok:
  expr_post H ctx func cenv cx e es sa sm s0 es' v x s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  (if is_bytestring_type (expr_type e) then compile_sha256_bytes x sm
   else case expr_type e of
     BaseT (BytesT (Fixed m)) => compile_sha256_bytesm x m sm
   | _ => compile_sha256_word x sm) = (op,sb) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sa /\
  expr_store_bound cx (expr_type e) v x s ==>
  run_inst_seq_mem_ok (emitted_insts sm sb) s
Proof
  strip_tac >>
  `!z. x = Var z ==> not_fresh_at sm z` by
    (drule_at (Pos hd) compile_lower_value_var >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es' s` by metis_tac[expr_post_state] >>
  `alloca_next_valid s` by fs[stmt_state_rel_def, alloca_inv_def] >>
  Cases_on `bty` >> gvs[is_bytes_or_string_type_def] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  gvs[is_bytestring_type_def]
  >~ [`expr_type e = BaseT (BytesT bd)`]
  >- (Cases_on `bd` >> gvs[is_bytestring_type_def]
      >- ( `n <= 32` by (fs[vyperValueTheory.evaluate_type_def] >> gvs[AllCaseEqs()]) >>
           drule_all hash_fixed_post_view >> strip_tac >>
           irule compile_sha256_bytesm_mem_ok >>
           simp[] >>
           reverse conj_tac >- (qexistsl [`n`,`op`,`w`,`x`] >> simp[]) >>
           drule_all (SRULE [] (Q.INST [`sha` |-> `T`] hash_fixed_alloca_code)) >> strip_tac >>
           fs[stmt_state_rel_def] >>
           rpt gen_tac >> strip_tac
           >- (qpat_x_assum `!inst n base sz. _` (fn coh =>
                 qpat_assum `MEM (mk_inst sm.cs_next_id ALLOCA _ _) _`
                   (mp_then (Pos hd) (mp_tac o SIMP_RULE (srw_ss())
                     [venomInstTheory.mk_inst_def]) coh)) >>
               disch_then (qspecl_then [`base'`,`cap`] mp_tac) >>
               gvs[wordsTheory.dimword_def]) >>
           qpat_x_assum `!inst n base sz. _` (fn coh =>
             qpat_assum `MEM (mk_inst (sm.cs_next_id + 2) ALLOCA _ _) _`
               (mp_then (Pos hd) (mp_tac o SIMP_RULE (srw_ss())
                 [venomInstTheory.mk_inst_def]) coh)) >>
           disch_then (qspecl_then [`base'`,`cap`] mp_tac) >>
           gvs[wordsTheory.dimword_def]) >>
      drule hash_dynamic_post_view >> simp[] >> strip_tac >>
      `b < dimword (:256)` by decide_tac >>
      `b + 32 + LENGTH l <= s.vs_alloca_next` by
        (qpat_x_assum `expr_store_bound _ _ _ _ _` mp_tac >>
         simp[expr_store_bound_def, is_word_type_def, val_store_size_def] >>
         qspec_then `LENGTH l` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
         decide_tac) >>
      irule compile_sha256_bytes_mem_ok >>
      simp[] >>
      reverse conj_tac
      >- (qexistsl [`b`,`LENGTH l`,`op`,`x`] >> simp[] >> decide_tac) >>
      suspend "memory_capacity") >>
  drule hash_string_post_view >> simp[] >> strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `b + 32 + LENGTH s' <= s.vs_alloca_next` by
    (qpat_x_assum `expr_store_bound _ _ _ _ _` mp_tac >>
     simp[expr_store_bound_def, is_word_type_def, val_store_size_def] >>
     qspec_then `LENGTH s'` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
     decide_tac) >>
  irule compile_sha256_bytes_mem_ok >> simp[] >>
  reverse conj_tac
  >- (qexistsl [`b`,`LENGTH s'`,`op`,`x`] >> simp[] >> decide_tac) >>
  suspend "memory_capacity"
QED

Resume sha256_typed_suffix_mem_ok[memory_capacity]:
  markerLib.RESUME_TAC >>
  drule_all hash_sha256_memory_alloca_code >> strip_tac >>
  fs[stmt_state_rel_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!inst n base sz. _` (fn coh =>
    qpat_assum `MEM (mk_inst (sm.cs_next_id + 2) ALLOCA _ _) _`
      (mp_then (Pos hd) (mp_tac o SIMP_RULE (srw_ss())
        [venomInstTheory.mk_inst_def]) coh)) >>
  disch_then (qspecl_then [`base'`,`cap`] mp_tac) >>
  gvs[wordsTheory.dimword_def]
QED

Finalise sha256_typed_suffix_mem_ok

Theorem sha256_step_base_alloca_next_mono[local]:
  !i s t. i.inst_opcode <> INVOKE /\ step_inst_base i s = OK t ==>
    s.vs_alloca_next <= t.vs_alloca_next
Proof
  rpt strip_tac >> Cases_on `i.inst_opcode = ALLOCA`
  >- (irule venomMemPropsTheory.step_inst_alloca_alloca_next_mono >>
      qexistsl [`ARB`,`0`,`i`] >>
      simp[step_inst_non_invoke, venomInstTheory.is_alloca_op_def]) >>
  `t.vs_alloca_next = s.vs_alloca_next` suffices_by simp[] >>
  irule venomMemProofsTheory.step_inst_base_preserves_alloca_next >>
  qexists `i` >> simp[]
QED

Theorem sha256_run_inst_seq_alloca_next_mono:
  !code s t.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
    run_inst_seq code s = OK t ==> s.vs_alloca_next <= t.vs_alloca_next
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  drule_all sha256_step_base_alloca_next_mono >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem sha256_typed_effectful_path_mem:
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
     expr_post H ctx func cenv cx e es sa sm s0 es1 v x s) /\
  valid_horizon cx st0 H es1.storage_trace /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  (if is_bytestring_type (expr_type e) then compile_sha256_bytes x sm
   else case expr_type e of
     BaseT (BytesT (Fixed m)) => compile_sha256_bytesm x m sm
   | _ => compile_sha256_word x sm) = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  (do precompile_call_success Sha256; return (Value r) od) es1 = (res,es2) /\
  builtin_result cx es1.accounts (BaseT (BytesT (Fixed 32)))
    Sha256 [expr_type e] [v] = INL r /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  expr_store_bound cx (expr_type e) v x s /\ alloca_history func s ==>
  ?n rr. gas_marked_path T ctx func s n rr /\
    ((?t rv. rr = OK t /\ res = INL rv /\
        (!H. valid_horizon cx st0 H es2.storage_trace ==>
           vv_post H ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])
             es sa sb s0 es2 rv (StackValue (BaseT (BytesT (Fixed 32))) op) t) /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next) \/
     (exit_result rr /\ expr_exit res rr))
Proof
  strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then assume_tac) >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) s` by
    (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
       sha256_typed_suffix_mem_ok >> simp[]) >>
  drule_at (Pos hd) sha256_typed_suffix_shape >> simp[] >> strip_tac >>
  pop_assum (qspecl_then [`x`,`sm`,`sb`,`op`] mp_tac) >>
  (impl_tac >- (qpat_x_assum `(if _ then _ else _) = (op,sb)` mp_tac >> simp[])) >>
  strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sm sb ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sm sb) = LENGTH sb.cs_current_insts` by
    (gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND, same_blocks_def] >>
     simp[listTheory.DROP_APPEND, listTheory.DROP_LENGTH_TOO_LONG]) >>
  `es1.outcomes = SOME s.vs_outcomes` by
    (drule expr_post_state >> simp[stmt_state_rel_def, state_rel_def]) >>
  Cases_on `s.vs_outcomes`
  >- (gvs[ignore_bind_def, bind_def, sha256_source_outcome_step] >> suspend "abort") >>
  rename1 `s.vs_outcomes = outcome::remaining` >>
  Cases_on `outcome.co_success`
  >- suspend "success" >>
  gvs[ignore_bind_def, bind_def, sha256_source_outcome_step] >> suspend "abort"
QED

Resume sha256_typed_effectful_path_mem[abort]:
  markerLib.RESUME_TAC >>
  drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) sha256_typed_fail_run >>
  simp[] >> strip_tac >>
  `isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[rich_listTheory.IS_PREFIX_APPEND] >>
  drule_at (Pat `run_inst_seq _ _ = _`)
    (Q.SPEC `T` run_inst_seq_abort_gas_path) >> simp[] >>
  disch_then (qspecl_then [`ctx`,`func`,`bb`] mp_tac) >> simp[] >>
  strip_tac >> goal_assum drule >>
  simp[exit_result_def, expr_exit_def]
QED
Resume sha256_typed_effectful_path_mem[success]:
  gvs[ignore_bind_def, bind_def, sha256_source_outcome_step, return_def] >>
  drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) sha256_typed_post_run >>
  simp[] >> strip_tac >> gvs[] >>
  `!H'. valid_horizon cx st0 H' es1.storage_trace ==>
     vv_post H' ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])
       es sa sb s0 (es1 with outcomes := SOME remaining) (Value r)
       (StackValue (BaseT (BytesT (Fixed 32))) op) t` by
    (rpt strip_tac >>
     qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
     drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`) sha256_typed_post_run >>
     simp[] >> strip_tac >> gvs[]) >>
  `isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[rich_listTheory.IS_PREFIX_APPEND] >>
  drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_path_mem >> simp[] >>
  disch_then (qspecl_then [`ctx`,`func`,`bb`] mp_tac) >> simp[] >>
  strip_tac >>
  `alloca_inv s` by
    (drule expr_post_state >> simp[stmt_state_rel_def, state_rel_def]) >>
  `alloca_history func
     (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb))` by
    (irule alloca_history_run_inst_seq >> goal_assum (drule_at Any) >>
     fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    (irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_current_bb`
       run_inst_seq_preserves_field)) >> goal_assum (drule_at Any) >>
     rpt strip_tac >> fs[listTheory.EVERY_MEM] >>
     metis_tac[step_preserves_control_flow, step_inst_non_invoke]) >>
  rewrite_tac[gas_marked_path_def] >> goal_assum drule >>
  fs[vv_post_inst_idx, same_blocks_def] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  metis_tac[sha256_run_inst_seq_alloca_next_mono]
QED
Finalise sha256_typed_effectful_path_mem

(* Memory counterpart of exprSimHash.expr_sim_suffix; the operand's
   store bound and allocation history remain available to the continuation. *)
Theorem sha256_expr_sim_mem_suffix:
  expr_sim_mem ctx func cenv cx ty e es /\
  lower_value compile_expr cenv ty e sa = (op, sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\
  alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!H exc ee r. expr_exit (INR exc : value + exception) r ==>
     R H (INR exc) ee r) /\
  (!v. storage_trace_frame (k v)) /\
  (!gs v ee t.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
       (INL v, ee) /\ ee.gas_obs = [] /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==>
        expr_post H ctx func cenv cx e es sa sm s0 ee v op t) /\
     (?H. valid_horizon cx st0 H ee.storage_trace) /\
     expr_store_bound cx (expr_type e) v op t /\ alloca_history func t /\
     s0.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted /\
     t.vs_current_bb = sm.cs_current_bb /\
     t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
     ?marks. gas_summary_at T (ctx, func) marks (k v) (ee, t)
       (\res ee t. !H. valid_horizon cx st0 H ee.storage_trace ==>
          Q H res ee t)
       (\res ee r. !H. valid_horizon cx st0 H ee.storage_trace ==>
          R H res ee r)) ==>
  gas_outcome T (cx_tops cx) (ctx, func) cx st0
    (bind (bind (eval_expr cx e) (read_result cx)) k) (es, s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `op`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> BETA_TAC >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_bind_left >> simp[])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o SIMP_RULE (srw_ss()) [gas_summary_at_def]) >>
      (reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
       >- (qexists_tac `marks` >> disj1_tac >>
           irule gasStorageTheory.gas_bad_storage_at_bind_left >> simp[] >>
           irule gasStorageTheory.gas_bad_storage_at_counted_prefix >>
           qexistsl_tac [`ctx`, `es_end`, `func`, `T`, `r`, `res`] >>
           simp[])) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by
        fs[vyperStorageFootprintTheory.storage_trace_domain_def]
      >- (`?v. res = INL v` by metis_tac[] >> gvs[] >>
          `bind (eval_expr cx e) (read_result cx)
             (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
             (INL v, es_end with gas_obs := [])` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
               (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
             strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
          `~t.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          `t.vs_current_bb = sm.cs_current_bb /\
           t.vs_inst_idx = LENGTH sm.cs_current_insts /\
           expr_store_bound cx (expr_type e) v op t /\ alloca_history func t /\
           s0.vs_alloca_next <= t.vs_alloca_next` by metis_tac[] >>
          qpat_x_assum `!gs v ee t. _`
            (qspecl_then [`gas_explicit marks s0.vs_gas_readings`, `v`,
                          `es_end with gas_obs := []`, `t`] mp_tac) >>
          (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
          rename1 `gas_summary_at T _ right _ _ _ _` >>
          qexists_tac `marks ++ right` >> disj2_tac >> disj1_tac >>
          qpat_x_assum `gas_summary_at T _ right _ _ _ _`
            (mp_tac o REWRITE_RULE [gas_summary_at_def]) >>
          disch_then (qx_choosel_then [`fres`, `fin`, `fr`]
            (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
          drule_all gas_marked_exec_bind_normal >> strip_tac >>
          rewrite_tac[gas_summary_at_def] >>
          qexistsl_tac [`fres`, `fin`, `fr`] >> asm_rewrite_tac[])
      >> Cases_on `res`
      >- (qpat_x_assum `!H. valid_horizon _ _ H _ ==> expr_exit _ _`
            (drule_then mp_tac) >> simp[]) >>
      rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
      qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INR exc`, `es_end`, `r`] >> conj_tac
      >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      BETA_TAC >> disj2_tac >> simp[] >> rpt strip_tac >>
      first_x_assum irule >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  qabbrev_tac `a = bind (eval_expr cx e) (read_result cx)` >>
  `ignore_bind (bind a k) (return ()) =
   bind a (\v. ignore_bind (k v) (return ()))` by
    simp[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  pop_assum SUBST1_TAC >>
  metis_tac[gas_exempt_cert_error_value]
QED

Theorem compile_typed_sha256_unary_vv_sim_mem:
  expr_body_pre cenv cx env (Builtin ann Sha256 [e]) es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es /\ expr_type e = BaseT bty /\
  (!sa sb vv. compile_expr cenv ty (Builtin ann Sha256 [e]) sa = (vv,sb) ==>
    ?x sm. lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
      code x sm = (vv,sb)) /\
  (!x. cs_appends (code x)) /\
  (!st0 sa sm sb x vv s0 v gs es1 s res es2.
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    code x sm = (vv,sb) /\ fn_has_code sm sb func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    local_ptrs_reserved cenv sm /\
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
      (INL v,es1) /\
    value_has_type (BaseTV bty) v /\ expr_sim_inv cenv cx env es1 /\
    expr_vv_res_ok res /\
    (case builtin_result cx es1.accounts ann Sha256 [expr_type e] [v] of
       INR exc => (INR exc,es1)
     | INL w => (do precompile_call_success Sha256; return (Value w) od) es1) =
       (res,es2) /\
    (!H. valid_horizon cx st0 H es1.storage_trace ==>
       expr_post H ctx func cenv cx e es sa sm s0 es1 v x s) /\
    (?H. valid_horizon cx st0 H es1.storage_trace) /\
    expr_store_bound cx (expr_type e) v x s /\ alloca_history func s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?n r. gas_marked_path T ctx func s n r /\
      ((?t rv. r = OK t /\ res = INL rv /\
          (!H. valid_horizon cx st0 H es2.storage_trace ==>
             vv_post H ctx func cenv cx (Builtin ann Sha256 [e]) es sa sb s0 es2
               rv vv t) /\
          vv_store_bound cx ann (lowered_value_type cenv (Builtin ann Sha256 [e]))
            es2 rv vv t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next) \/
       (exit_result r /\ expr_exit res r))) ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin ann Sha256 [e]) es
Proof
  strip_tac >> rewrite_tac[expr_vv_sim_mem_def] >> rpt strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >>
     disch_then irule >> gvs[expr_body_pre_def]) >>
  qpat_x_assum `!sa sb vv. _` drule >> strip_tac >>
  `cs_appends (code x)` by simp[] >>
  drule_all hash_unary_suffix_cut >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `gas_admissible (eval_expr _ _) _ _`
    (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
  rewrite_tac[eval_expr_sha256_action] >> strip_tac >>
  irule sha256_expr_sim_mem_suffix >>
  first_assum (irule_at (Pat `expr_sim_mem _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> irule expr_exit_INR_cast >> simp[]) >>
  conj_tac >- simp[exprSimHashTheory.sha256_continuation_frame] >>
  rpt strip_tac >>
  drule_at (Pat `bind _ _ _ = _`)
    (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_base_result) >>
  disch_then (qspecl_then [`env`, `cenv`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `case builtin_result cx ee.accounts ann Sha256 [expr_type e] [v] of
              INR exc => (INR exc,ee)
            | INL w => (do precompile_call_success Sha256;
                           return (Value w) od) ee` >>
  rename1 `_ = (res, es2)` >>
  `expr_vv_res_ok res` by
    (qpat_x_assum `!gs res ee. _` (qspec_then `gs` mp_tac) >> simp[bind_def] >>
     disch_then irule >> gvs[]) >>
  qpat_assum `expr_type e = _` (fn th =>
    rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  qpat_x_assum `!st0 sa sm sb x vv s0 v gs es1 s res es2. _`
    (drule_all o SIMP_RULE bool_ss [PULL_EXISTS]) >> strip_tac >>
  drule sha256_continuation_gas_obs >> strip_tac >>
  `es2 with gas_obs := [] = es2` by
    (first_x_assum (qspec_then `[]` mp_tac) >>
     `ee with gas_obs := [] = ee` by
       simp[evaluation_state_component_equality] >>
     pop_assum SUBST1_TAC >>
     qpat_x_assum `_ = (res, es2)` SUBST1_TAC >>
     simp[] >> metis_tac[]) >>
  qexists `REPLICATE n F` >>
  rewrite_tac[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl [`res`, `es2`, `r`] >>
  simp[vyperASTTheory.expr_type_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem compile_sha256_typed_vv_sim_mem:
  expr_body_pre cenv cx env (Builtin ann Sha256 [e]) es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin ann Sha256 [e]) es
Proof
  strip_tac >>
  `is_bytes_or_string_type (expr_type e) /\ ann = BaseT (BytesT (Fixed 32))` by
    (irule (SRULE [] (Q.INST [`b` |-> `Sha256`,
       `ts` |-> `[expr_type e]`] hash_builtin_types)) >>
     gvs[expr_body_pre_def, well_typed_expr_def]) >>
  `?bty. expr_type e = BaseT bty` by
    (Cases_on `expr_type e` >> gvs[is_bytes_or_string_type_def]) >>
  irule compile_typed_sha256_unary_vv_sim_mem >> simp[] >>
  qexistsl [`\x sm. as_stack_val ann
    (if is_bytestring_type (expr_type e) then compile_sha256_bytes x sm
     else case expr_type e of
       BaseT (BytesT (Fixed m)) => compile_sha256_bytesm x m sm
     | _ => compile_sha256_word x sm)`, `env`] >> simp[] >>
  reverse conj_tac
  >- (conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
          simp[compile_hash_singleton] >> pairarg_tac >> simp[] >> metis_tac[]) >>
      conj_tac >- (gen_tac >> ho_match_mp_tac cs_appends_stack_value >> simp[SF ETA_ss] >>
      Cases_on `bty` >> gvs[is_bytes_or_string_type_def,
        is_bytestring_type_def, hash_suffix_appends, SF ETA_ss] >>
      rename1 `expr_type e = BaseT (BytesT bd)` >>
      Cases_on `bd` >> gvs[is_bytestring_type_def, hash_suffix_appends, SF ETA_ss]) >>
      gvs[]) >>
  rpt strip_tac >>
  qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_stack_val _ compiled` >>
  Cases_on `compiled` >> simp[as_stack_val_def] >> strip_tac >>
  gvs[markerTheory.Abbrev_def] >>
  `expr_body_pre cenv cx env e es1` by
    (irule expr_body_pre_builtin_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ _ _`)) >> simp[]) >>
  `evaluate_type (get_tenv cx) (BaseT bty) = SOME (BaseTV bty)` by
    (drule expr_body_pre_type_evaluates >>
     simp[vyperValueTheory.evaluate_type_def] >>
     Cases_on `bty` >> gvs[AllCaseEqs()] >>
     rename1 `expr_type e = BaseT (BytesT bd)` >>
     Cases_on `bd` >> gvs[AllCaseEqs()]) >>
  drule (CONV_RULE (DEPTH_CONV ETA_CONV)
    exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom) >>
  simp[] >> strip_tac >>
  drule_at (Pos hd) sha256_typed_builtin_result >> simp[] >>
  disch_then (qspecl_then [`v`, `cx`, `es1.accounts`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  drule_at (Pos hd) sha256_typed_effectful_path_mem >>
  disch_then (drule_at (Pat `valid_horizon _ _ _ _`)) >> simp[] >>
  disch_then (qspecl_then [`r`,`q`] mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  strip_tac >> goal_assum drule >>
  gvs[vyperASTTheory.expr_type_def, vv_store_bound_stack_word, is_word_type_def]
QED

Theorem compile_sha256_typed_sim_mem:
  expr_body_pre cenv cx env (Builtin ann Sha256 [e]) es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_sim_mem ctx func cenv cx ty (Builtin ann Sha256 [e]) es
Proof
  strip_tac >>
  `is_bytes_or_string_type (expr_type e) /\ ann = BaseT (BytesT (Fixed 32))` by
    (irule (SRULE [] (Q.INST [`b` |-> `Sha256`,
       `ts` |-> `[expr_type e]`] hash_builtin_types)) >>
     gvs[expr_body_pre_def, well_typed_expr_def]) >>
  irule body_expr_sim_mem_of_vv_sim_mem >>
  simp[vyperASTTheory.expr_type_def, is_word_type_def] >>
  conj_tac >- metis_tac[] >>
  irule compile_sha256_typed_vv_sim_mem >> metis_tac[]
QED
