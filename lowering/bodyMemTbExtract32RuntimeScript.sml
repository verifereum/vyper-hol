(* Ordinary typed execution of the extract32 suffix. *)
Theory bodyMemTbExtract32Runtime
Ancestors
  bodyMemTbExtract32Clamp bodyMemTbExtract32Readonly bodyMemTbExtract32Slice
  bodyMemTbExtract32Encoding builtinProps exprLoweringProps compileEnv
  emitHelperProps venomState valueEncoding exprLowering

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
