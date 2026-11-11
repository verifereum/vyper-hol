(* Resource composition for the Log suffix, by actual allocation sites. *)
Theory bodyIntCallFamStmtLogSuffixMemory
Ancestors
  bodyIntCallFamStmtLogSuffixStore bodyIntCallFamStmtLogSuffixFootprint
  bodyIntCallFamStmtLogSuffixResources stmtSimLogSuffixCode
  stmtSimLogSuffixActual stmtSimLogSourceAllocate stmtSimLogTopics
  stmtSimLogTrace stmtSimLogEmit stmtSimLogDataRun
  localPtrsProps exprLoweringProps emitHelperProps
  abiDecoderFrame abiDecoderReentry venomState finite_map words list arithmetic

Theorem intcall_log_suffix_resources:
  ce.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  compile_log_eval_all ce args sa = (xs,sm) /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  compile_stmt ce lctx ty (Log id args) sa = ((),sb) /\
  EVERY (supported_scalar_type o SND) xs /\ LENGTH flags = LENGTH xs /\
  run_inst_seq (emitted_insts sm sb) s = OK t /\ allocas_above lo s ==>
  allocas_above lo t /\ s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> drule_all log_success_suffix_code >> strip_tac >>
  irule intcall_noninvoke_run_resources >> simp[] >>
  qexists_tac `emitted_insts sm sb` >> simp[EVERY_MEM] >>
  gvs[EVERY_MEM]
QED

Theorem intcall_log_topics_memory:
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  LENGTH flags = LENGTH xs /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\ (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. log_arg_rel ce cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  encode_indexed_event_topics flags (MAP SND xs) vs = SOME topics /\
  run_inst_seq (emitted_insts sm st) s = OK u ==>
  u.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `LENGTH vs = LENGTH xs` by metis_tac[LIST_REL_LENGTH] >>
  drule_all log_indexed_encoding_select >> strip_tac >>
  drule_all log_indexed_selection_rel >> strip_tac >>
  drule_all log_indexed_selection_every >> strip_tac >>
  `compile_log_topic_ops
    (MAP (\p. (FST p,is_bytestring_type (SND p)))
      (MAP FST (FILTER SND (ZIP (xs,flags))))) sm = (ops,st)` by
    (drule_all split_log_ops_select >> strip_tac >>
     gvs[MAP_MAP_o, combinTheory.o_DEF]) >>
  `encode_indexed_event_topics
    (REPLICATE (LENGTH (MAP FST (FILTER SND (ZIP (xs,flags))))) T)
    (MAP SND (MAP FST (FILTER SND (ZIP (xs,flags)))))
    (MAP FST (FILTER SND (ZIP (vs,flags)))) = SOME topics` by metis_tac[] >>
  drule_all compile_log_topic_ops_run >> strip_tac >>
  gvs[] >> fs[venom_state_component_equality]
QED
