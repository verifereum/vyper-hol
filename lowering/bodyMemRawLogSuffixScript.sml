(* Frontier checks for the straight-line RawLog continuations. *)
Theory bodyMemRawLogSuffix
Ancestors
  bodySimRawLog instMemFrontier fragExecMem bodyMemBiKeccakBounds
  exprSimOperators exprOperandVar words finite_map ASCIInumbers
  emitHelper compileEnv exprLoweringProps emitHelperProps list rich_list
  venomInst venomState venomExecSemantics

Theorem raw_log_dynamic_suffix_mem_ok:
  emit_op MLOAD [x] sm = (len,s1) /\
  emit_op ADD [x; Lit 32w] s1 = (payload_op,s2) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len;payload_op]) [] s2 = (u,sb) /\
  (!v. x = Var v ==> not_fresh_at sm v) /\
  eval_operand x s = SOME (n2w b) /\
  mload b s = n2w n /\ LENGTH (ops:operand list) <= 4 /\
  b + 32 < dimword (:256) /\ n < dimword (:256) /\
  b + 32 <= s.vs_alloca_next /\
  (n = 0 \/ b + 32 + n <= s.vs_alloca_next) ==>
  run_inst_seq_mem_ok (emitted_insts sm sb) s
Proof
  simp[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  gnvs[] >>
  `!k. LENGTH sm.cs_current_insts - (LENGTH sm.cs_current_insts + k) = 0`
    by decide_tac >>
  simp[emitted_insts_def, DROP_APPEND] >>
  rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- simp[below_frontier_MLOAD] >>
  drule step_MLOAD_local >>
  disch_then (qspecl_then [`STRING #"%" (toString sm.cs_next_var)`,
                          `sm.cs_next_id`] assume_tac) >> simp[] >>
  `eval_operand x (update_var (STRING #"%" (toString sm.cs_next_var))
      (mload b s) s) = SOME (n2w b)` by
    (irule eval_operand_update_other_local >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[not_fresh_at_def]) >>
  conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  drule step_ADD >> disch_then (qspec_then `Lit 32w` mp_tac) >>
  simp[eval_operand_def] >>
  disch_then (qspecl_then [`sm.cs_next_id + 1`,
    `STRING #"%" (toString (sm.cs_next_var + 1))`] assume_tac) >>
  simp[run_inst_seq_mem_ok_last] >>
  `LENGTH ops < dimword (:256)` by simp[dimword_def] >>
  mp_tac (Q.SPECL [`sm.cs_next_id + 2`, `LENGTH (ops:operand list)`, `REVERSE ops`]
    below_frontier_LOG) >>
  simp[LENGTH_REVERSE] >> disch_then (fn th => rewrite_tac[th]) >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, toString_inj, GSYM word_add_n2w] >>
  Cases_on `n = 0` >> simp[] >>
  `n2w b + 32w = (n2w (b + 32):256 word)` by simp[word_add_n2w] >>
  simp[] >> decide_tac
QED

Theorem raw_log_fixed_suffix_mem_ok:
  emit_void MSTORE [pop; x] sm = (u,s1) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;pop]) [] s1 = (u',sb) /\
  eval_operand pop s = SOME p /\ eval_operand x s = SOME w /\
  LENGTH (ops:operand list) <= 4 /\ w2n p + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sm sb) s
Proof
  simp[emit_void_def, emit_inst_def, comp_bind_def, comp_return_def,
       fresh_id_def, emit_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> gnvs[] >>
  `!k. LENGTH sm.cs_current_insts - (LENGTH sm.cs_current_insts + k) = 0`
    by decide_tac >>
  simp[emitted_insts_def, DROP_APPEND] >>
  rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- simp[below_frontier_MSTORE] >>
  `step_inst_base (mk_inst sm.cs_next_id MSTORE [pop;x] []) s =
     OK (mstore (w2n p) w s)` by (irule step_MSTORE >> simp[]) >>
  simp[run_inst_seq_mem_ok_last] >>
  `LENGTH ops < dimword (:256)` by simp[dimword_def] >>
  mp_tac (Q.SPECL [`sm.cs_next_id + 1`, `LENGTH (ops:operand list)`, `REVERSE ops`]
    below_frontier_LOG) >>
  simp[LENGTH_REVERSE] >> disch_then (fn th => rewrite_tac[th]) >>
  `eval_operand pop (mstore (w2n p) w s) = SOME p` by
    (Cases_on `pop` >> gvs[eval_operand_def, mstore_def,
                            lookup_var_def]) >>
  simp[eval_operand_def, mstore_def, dimword_def]
QED
