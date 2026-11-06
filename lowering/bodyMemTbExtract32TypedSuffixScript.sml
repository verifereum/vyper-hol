(* Typed source representation at the extract32 suffix entry. *)
Theory bodyMemTbExtract32TypedSuffix
Ancestors
  bodyMemTbExtract32Runtime bodyMemTbExtract32Clamp bodyMemTbExtract32AddressClamp bodyMemTbExtract32FixedClamp bodyMemTbExtract32IntClamp bodyMemTbExtract32Readonly bodyMemTbExtract32Load bodyMemTbExtract32Cuts bodyMemTbExtract32Slice bodyMemTbExtract32Encoding stmtSimLogArgs
  exprSimHash exprSimProps exprSimWordArgs loweringPosts exprSimDefs
  valueEncoding vyperTypeSystem compileEnv

Theorem extract32_source_bytes_kept:
  expr_sim_inv cenv cx env es /\
  expr_val_at cenv cx (BaseT (BytesT (Dynamic cap))) sa sm es (BytesV bs) src s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  eval_operand src s = SOME w /\
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) (w2n w) s.vs_memory /\
  expr_post ctx func cenv cx off es sm sb s es' v op t ==>
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) (w2n w) t.vs_memory
Proof
  strip_tac >>
  `log_arg_clear cenv cx (BaseT (BytesT (Dynamic cap))) (BytesV bs)` by
    (irule log_arg_clear_base >> goal_assum (drule_at Any)) >>
  `wb_frame cenv es sm s t` by metis_tac[expr_post_frame] >>
  `~is_word_type (BaseT (BytesT (Dynamic cap)))` by simp[is_word_type_def] >>
  drule_all log_argument_footprint_kept >> strip_tac >>
  drule_all expr_val_at_footprint >> strip_tac >>
  irule val_in_memory_footprint_agree >> metis_tac[]
QED

Theorem extract32_suffix_success_path:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw (BaseT bt) sc = (op,sb) /\
  code = emitted_insts sa sc ++ emitted_insts sc sb /\
  eval_operand l s = SOME (n2w (LENGTH bs)) /\
  eval_operand d s = SOME (n2w (p + 32)) /\
  eval_operand off s = SOME (n2w n) /\ fresh_vars_wrt sa s /\
  LENGTH bs < dimword (:256) /\ n < dimword (:256) /\
  n + 32 <= LENGTH bs /\ p + 32 + n < dimword (:256) /\
  p + 32 < dimword (:256) /\ p + 32 + LENGTH bs <= s.vs_alloca_next /\
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) p s.vs_memory /\
  extract32_result_base_ok bt /\ well_formed_type tenv (BaseT bt) /\
  evaluate_extract32 bs n bt = INL v /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_path_mem ctx func s (LENGTH (FILTER (\i. i.inst_opcode = GAS) code))
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)) /\
      eval_operand op t = SOME (typed_val_to_w256 (BaseTV bt) v) /\
      t = s with vs_vars := t.vs_vars /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      fresh_vars_wrt sb t /\
      run_inst_seq code s = OK t
Proof
  strip_tac >> drule_all extract32_suffix_success_run >> strip_tac >>
  `w2n (n2w (p + 32):bytes32) + w2n (n2w (LENGTH bs):bytes32) <= s.vs_alloca_next` by
    simp[wordsTheory.w2n_n2w] >>
  drule_all extract32_suffix_gas_paths >> strip_tac >>
  drule_all extract32_suffix_readonly_frame >> strip_tac >>
  drule_all extract32_suffix_fresh >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  rpt strip_tac >> irule extract32_suffix_lookup_kept >> metis_tac[]
QED

Theorem extract32_suffix_revert_path:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw (BaseT bt) sc = (op,sb) /\
  code = emitted_insts sa sc ++ emitted_insts sc sb /\
  eval_operand l s = SOME (n2w (LENGTH bs)) /\
  eval_operand d s = SOME (n2w (p + 32)) /\
  eval_operand off s = SOME (n2w n) /\ fresh_vars_wrt sa s /\
  LENGTH bs < dimword (:256) /\ n < dimword (:256) /\
  (n + 32 <= LENGTH bs ==> p + 32 + n < dimword (:256)) /\
  p + 32 < dimword (:256) /\ p + 32 + LENGTH bs <= s.vs_alloca_next /\
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) p s.vs_memory /\
  extract32_result_base_ok bt /\ well_formed_type tenv (BaseT bt) /\
  evaluate_extract32 bs n bt = INR (RuntimeError msg) /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t k j. gas_path_mem ctx func s k (Abort Revert_abort (t with vs_inst_idx := j))
Proof
  strip_tac >> drule_all extract32_suffix_revert_run >> strip_tac >>
  `w2n (n2w (p + 32):bytes32) + w2n (n2w (LENGTH bs):bytes32) <= s.vs_alloca_next` by
    simp[wordsTheory.w2n_n2w] >>
  drule_all extract32_suffix_gas_paths >> strip_tac >>
  first_x_assum (qspec_then `ctx` strip_assume_tac) >>
  gvs[] >> metis_tac[]
QED
