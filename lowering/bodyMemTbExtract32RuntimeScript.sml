(* Ordinary typed execution of the extract32 suffix. *)
Theory bodyMemTbExtract32Runtime
Ancestors
  bodyMemTbExtract32Clamp bodyMemTbExtract32Readonly bodyMemTbExtract32Slice
  bodyMemTbExtract32Encoding builtinProps exprLoweringProps compileEnv
  emitHelperProps venomState valueEncoding exprLowering varsExt freshWrites

Theorem extract32_load_fresh[local]:
  compile_extract32_load l d off sa = (raw,sc) /\
  run_inst_seq (emitted_insts sa sc) s = OK t /\ fresh_vars_wrt sa s ==>
  fresh_vars_wrt sc t
Proof
  strip_tac >> irule extract32_suffix_fresh >>
  qexistsl_tac [`d`, `l`, `off`, `raw`, `raw`, `s`, `sa`, `sc`, `BaseT BoolT`] >>
  gvs[compile_clamp_basetype_def, comp_return_def, emitted_insts_def]
QED

Theorem extract32_suffix_success_run:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw (BaseT bt) sc = (op,sb) /\
  eval_operand l s = SOME (n2w (LENGTH bs)) /\
  eval_operand d s = SOME (n2w (p + 32)) /\
  eval_operand off s = SOME (n2w n) /\ fresh_vars_wrt sa s /\
  LENGTH bs < dimword (:256) /\ n < dimword (:256) /\
  n + 32 <= LENGTH bs /\ p + 32 + n < dimword (:256) /\
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) p s.vs_memory /\
  extract32_result_base_ok bt /\ well_formed_type tenv (BaseT bt) /\
  evaluate_extract32 bs n bt = INL v ==>
  ?t. run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb) s = OK t /\
      eval_operand op t = SOME (typed_val_to_w256 (BaseTV bt) v)
Proof
  strip_tac >> drule_all compile_extract32_correct >>
  simp[wordsTheory.w2n_n2w] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sc) s = OK u` >>
  `fresh_vars_wrt sc u` by (irule extract32_load_fresh >> metis_tac[]) >>
  drule_all extract32_payload_mload >> strip_tac >> gvs[] >>
  drule extract32_inbounds_slice >> disch_then (qspec_then `bt` strip_assume_tac) >>
  gvs[] >>
  `LENGTH (TAKE 32 (DROP n bs)) = 32` by simp[listTheory.LENGTH_TAKE_EQ] >>
  drule_all extract32_clamp_success >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  qpat_x_assum `run_inst_seq (emitted_insts sa sc) s = OK u`
    (mp_tac o MATCH_MP run_inst_seq_append) >> simp[]
QED

Theorem extract32_suffix_revert_run:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw (BaseT bt) sc = (op,sb) /\
  eval_operand l s = SOME (n2w (LENGTH bs)) /\
  eval_operand d s = SOME (n2w (p + 32)) /\
  eval_operand off s = SOME (n2w n) /\ fresh_vars_wrt sa s /\
  LENGTH bs < dimword (:256) /\ n < dimword (:256) /\
  (n + 32 <= LENGTH bs ==> p + 32 + n < dimword (:256)) /\
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) p s.vs_memory /\
  extract32_result_base_ok bt /\ well_formed_type tenv (BaseT bt) /\
  evaluate_extract32 bs n bt = INR (RuntimeError msg) ==>
  ?t. run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb) s = Abort Revert_abort t
Proof
  strip_tac >> drule_all compile_extract32_correct >>
  simp[wordsTheory.w2n_n2w] >>
  Cases_on `n + 32 <= LENGTH bs`
  >- (simp[] >> strip_tac >>
      rename1 `run_inst_seq (emitted_insts sa sc) s = OK u` >>
      `fresh_vars_wrt sc u` by (irule extract32_load_fresh >> metis_tac[]) >>
      `p + 32 + n < dimword (:256)` by simp[] >>
      drule_all extract32_payload_mload >> strip_tac >> gvs[] >>
      drule extract32_inbounds_slice >> disch_then (qspec_then `bt` strip_assume_tac) >>
      gvs[] >>
      `LENGTH (TAKE 32 (DROP n bs)) = 32` by simp[listTheory.LENGTH_TAKE_EQ] >>
      drule_all extract32_clamp_revert >> strip_tac >> qexists_tac `t` >>
      qpat_x_assum `run_inst_seq (emitted_insts sa sc) s = OK u`
        (mp_tac o MATCH_MP run_inst_seq_append) >> simp[]) >>
  simp[] >> strip_tac >> qexists_tac `ss'` >>
  `!t. run_inst_seq (emitted_insts sa sc) s <> OK t` by simp[] >>
  drule run_inst_seq_append_err >> simp[]
QED

Theorem extract32_suffix_vars_ext[local]:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw (BaseT bt) sc = (op,sb) /\
  vars_ext s t ==>
  vars_ext_result
    (run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb) s)
    (run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb) t)
Proof
  strip_tac >> irule run_inst_seq_vars_ext >> reverse conj_tac >- simp[] >>
  drule_all extract32_suffix_output_range >> strip_tac >>
  irule listTheory.EVERY_MONOTONIC >> goal_assum (drule_at Any) >>
  simp[listTheory.MEM] >> rpt strip_tac >>
  gvs[venomInstTheory.is_terminator_def, venomInstTheory.is_ext_call_op_def]
QED

Theorem extract32_suffix_success_separated_run:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw (BaseT bt) sc = (op,sb) /\
  eval_operand l s = SOME (n2w (LENGTH bs)) /\
  eval_operand d s = SOME (n2w (p + 32)) /\
  eval_operand off s = SOME (n2w n) /\
  (!x. l = Var x \/ d = Var x \/ off = Var x ==> not_fresh_at sa x) /\
  LENGTH bs < dimword (:256) /\ n < dimword (:256) /\
  n + 32 <= LENGTH bs /\ p + 32 + n < dimword (:256) /\
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) p s.vs_memory /\
  extract32_result_base_ok bt /\ well_formed_type tenv (BaseT bt) /\
  evaluate_extract32 bs n bt = INL v ==>
  ?t. run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb) s = OK t /\
      eval_operand op t = SOME (typed_val_to_w256 (BaseTV bt) v) /\
      (?u. run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb)
        (drop_fresh sa s) = OK u)
Proof
  strip_tac >>
  `eval_operand l (drop_fresh sa s) = SOME (n2w (LENGTH bs)) /\
   eval_operand d (drop_fresh sa s) = SOME (n2w (p + 32)) /\
   eval_operand off (drop_fresh sa s) = SOME (n2w n)` by
    (simp[eval_operand_drop_fresh]) >>
  `val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) p
     (drop_fresh sa s).vs_memory` by simp[drop_fresh_def] >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  drule_all extract32_suffix_success_run >> strip_tac >>
  `vars_ext_result (OK t)
     (run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb) s)` by
    (`vars_ext (drop_fresh sa s) s` by simp[vars_ext_drop_fresh] >>
     drule_all extract32_suffix_vars_ext >> simp[]) >>
  gvs[vars_ext_result_def] >>
  qpat_x_assum `vars_ext t t'` (strip_assume_tac o REWRITE_RULE [vars_ext_def]) >>
  qpat_x_assum `t' = t with vs_vars := _` SUBST1_TAC >>
  simp[eval_operand_vars_ext]
QED

Theorem extract32_suffix_revert_separated_run:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw (BaseT bt) sc = (op,sb) /\
  eval_operand l s = SOME (n2w (LENGTH bs)) /\
  eval_operand d s = SOME (n2w (p + 32)) /\
  eval_operand off s = SOME (n2w n) /\
  (!x. l = Var x \/ d = Var x \/ off = Var x ==> not_fresh_at sa x) /\
  LENGTH bs < dimword (:256) /\ n < dimword (:256) /\
  (n + 32 <= LENGTH bs ==> p + 32 + n < dimword (:256)) /\
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) p s.vs_memory /\
  extract32_result_base_ok bt /\ well_formed_type tenv (BaseT bt) /\
  evaluate_extract32 bs n bt = INR (RuntimeError msg) ==>
  ?t. run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb) s = Abort Revert_abort t /\
      (?u. run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb)
        (drop_fresh sa s) = Abort Revert_abort u)
Proof
  strip_tac >>
  `eval_operand l (drop_fresh sa s) = SOME (n2w (LENGTH bs)) /\
   eval_operand d (drop_fresh sa s) = SOME (n2w (p + 32)) /\
   eval_operand off (drop_fresh sa s) = SOME (n2w n)` by
    (simp[eval_operand_drop_fresh]) >>
  `val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) p
     (drop_fresh sa s).vs_memory` by simp[drop_fresh_def] >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  drule_all extract32_suffix_revert_run >> strip_tac >>
  `vars_ext (drop_fresh sa s) s` by simp[vars_ext_drop_fresh] >>
  drule_all extract32_suffix_vars_ext >> simp[vars_ext_result_def] >>
  metis_tac[]
QED
