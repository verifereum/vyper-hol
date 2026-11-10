(* Counted preparation and final read, composed without losing exemptions. *)
Theory exprSimExtract32Assembly
Ancestors
  exprSimHashBoundary
  exprSimExtract32Post exprSimExtract32Run exprSimExtract32Counted
  gasSummary gasOutcome exprSimHash fragGasMode exprSimExtract32Read
  builtinBytes fragExec list rich_list exprLoweringProps vyperState
  exprSimExtract32Value valueEncoding vyperTypeSystem vyperValue words compileEnv

Theorem extract32_prepare_run_path:
  compile_bytestring_src op sa = ((len,dp),sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  gas_marked_path F ctx func s 0
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >>
  drule_at (Pos (el 2)) extract32_read_code_shape >>
  simp[extract32_read_prepare] >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by gvs[EVERY_MEM] >>
  drule_all hash_run_path >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (gvs[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  simp[]
QED

Theorem extract32_prepare_marked:
  compile_bytestring_src op sa = ((len,dp),sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  gas_marked_exec F (ctx,func) (return v) (es,s) [] (INL v) es
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >> drule_all extract32_prepare_run_path >>
  simp[gas_marked_exec_def, return_def]
QED

Theorem extract32_tail_success_marked:
  extract32_result_base_ok bt /\
  (case bt of UintT k => k <= 256 | IntT k => 0 < k /\ k <= 256 |
              BytesT (Fixed k) => k <= 32 | _ => T) /\
  val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p s.vs_memory /\
  LENGTH bs < dimword (:256) /\ n < dimword (:256) /\
  p + 32 + LENGTH bs < dimword (:256) /\
  eval_operand len s = SOME (n2w (LENGTH bs)) /\
  eval_operand dp s = SOME (n2w (p + 32)) /\
  eval_operand off s = SOME (n2w n) /\ fresh_vars_wrt sa s /\
  compile_extract32_load len dp off sa = (raw,sm) /\
  compile_clamp_basetype raw (BaseT bt) sm = (op,sb) /\
  evaluate_extract32 bs n bt = INL v /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_exec F (ctx,func) (lift_sum (evaluate_extract32 bs n bt))
        (es,s) [] (INL v) es
        (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
      eval_operand op u = SOME (typed_val_to_w256 (BaseTV bt) v) /\
      fresh_vars_wrt sb u /\ (u with vs_vars := s.vs_vars) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >> drule_all extract32_tail_success >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  drule_all extract32_tail_run_path >> strip_tac >>
  qexists_tac `u` >> simp[gas_marked_exec_def, lift_sum_def, return_def]
QED

Theorem extract32_tail_error_marked:
  extract32_result_base_ok bt /\
  (case bt of UintT k => k <= 256 | IntT k => 0 < k /\ k <= 256 |
              BytesT (Fixed k) => k <= 32 | _ => T) /\
  val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p s.vs_memory /\
  LENGTH bs < dimword (:256) /\ n < dimword (:256) /\
  p + 32 + LENGTH bs < dimword (:256) /\
  eval_operand len s = SOME (n2w (LENGTH bs)) /\
  eval_operand dp s = SOME (n2w (p + 32)) /\
  eval_operand off s = SOME (n2w n) /\ fresh_vars_wrt sa s /\
  compile_extract32_load len dp off sa = (raw,sm) /\
  compile_clamp_basetype raw (BaseT bt) sm = (op,sb) /\
  evaluate_extract32 bs n bt = INR (RuntimeError msg) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u count j. gas_marked_exec F (ctx,func)
    (lift_sum (evaluate_extract32 bs n bt)) (es,s) (REPLICATE count F)
    (INR (Error (RuntimeError msg))) es (Abort Revert_abort (u with vs_inst_idx := j))
Proof
  strip_tac >> drule_all extract32_tail_error >> strip_tac >>
  drule_all extract32_tail_abort_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`u`, `n'`, `j`] >>
  simp[gas_marked_exec_def, lift_sum_def, raise_def]
QED
