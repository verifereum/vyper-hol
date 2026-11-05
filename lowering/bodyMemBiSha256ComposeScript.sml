(* Counted memory-safe SHA256 suffixes. Semantic facts are reused from the
   task-permitted S1 overlay; all memory checks are proved here. *)
Theory bodyMemBiSha256Compose
Ancestors
  bodyMemBiSha256Suffix exprSimHash exprSimMemDefs allocaHistoryFragment
  fragGasSeqMem exprSimProps exprLoweringProps exprOperandVar exprSimWordArgs
  venomMemDefs compileEnv vyperTypeSystem fragGasSeqAbort fragGasMode
  exprSimPrecompiles fragExec vyperState exprSimDefs exprSimVVFrame venomInstProps venomExecSemantics venomMemProps venomMemProofs

Theorem sha256_typed_suffix_mem_ok:
  expr_post ctx func cenv cx e es sa sm s0 es' v x s /\
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
  `stmt_state_rel ctx func cenv cx es' s` by metis_tac[expr_post_state] >>
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
  expr_post ctx func cenv cx e es sa sm s0 es1 v x s /\
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
        vv_post ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Sha256 [e])
          es sa sb s0 es2 rv (StackValue (BaseT (BytesT (Fixed 32))) op) t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next) \/
     (exit_result rr /\ expr_exit res rr))
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) s` by
    (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
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
  drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`) sha256_typed_fail_run >>
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
  drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`) sha256_typed_post_run >>
  simp[] >> strip_tac >> gvs[] >>
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
