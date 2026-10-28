(* TOP-LEVEL: the actual indexed-only Log suffix preserves source state
   and encodes the event resolved by the checker, from saved arguments. *)
Theory checkedLogEmpty
Ancestors
  checkedLogMetadata logArgumentLogSafety logArgumentListContract abiLogTopicsEmpty
  eventLogSourceLookup sourceLogFrames abiTypeShape typedCopyProducer sourceMemoryFrames
  typedLogArgs abiFieldOperands compileEnv compileVyper vyperTypeContract
  vyperTypeInvariants vyperTypeExprSoundness vyperTypeSystem vyperContext vyperEvent
  fragExec fragBlockPath venomState list pair words

Theorem checked_compile_saved_log_empty:
  !tops dep layouts addr art env cx es cenv ctx func ret event_id exprs env' lctx
    cs cs' sig_hash fts flags args eval_cut raw_topics topic_ops topic_cut atvs values ss
    ids reserved requests final_cut credit.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\
    env.event_fields = art.cta_event_fields /\ env.type_defs = type_env tops /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    cenv.ce_event_info = build_event_info (type_env tops) tops (K NONE) /\
    ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
    type_stmt env ret (Log event_id exprs) = SOME env' /\
    cenv.ce_event_info (nsid_to_string event_id) = SOME (sig_hash,fts,flags) /\
    compile_log_eval_all cenv exprs cs = (args,eval_cut) /\
    split_log_ops args flags = (raw_topics,[]) /\
    compile_log_topic_ops raw_topics eval_cut = (topic_ops,topic_cut) /\
    compile_stmt cenv lctx ret (Log event_id exprs) cs = ((),cs') /\
    fn_has_code eval_cut topic_cut func /\ fn_has_code topic_cut cs' func /\
    LIST_REL (\arg tv. evaluate_type (type_env tops) (SND arg) = SOME tv) args atvs /\
    log_prefix_ready env cx cenv func ids reserved requests final_cut [] eval_cut es ss credit args atvs values /\
    LENGTH (Lit (n2w sig_hash)::topic_ops) < dimword(:256) /\ ~ss.vs_halted ==>
    ?out ev.
      encode_source_event (get_tenv cx) cx.sources cx.txn.target event_id values = SOME ev /\
      fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      out.vs_logs = ss.vs_logs ++ [ev] /\
      state_rel_simple cenv cx (es with logs := es.logs ++ [ev]) out /\
      local_ptrs_rel func cenv es.scopes out
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `log_args_safe args atvs ss 0 0` by (drule_all log_ready_arguments_empty_safe >> simp[]) >>
  qpat_x_assum `log_prefix_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [log_prefix_ready_def]) >>
  `env_consistent env cx es` by fs[runtime_consistent_def] >>
  `abi_struct_env_rel env.type_defs cenv.ce_struct_fields` by
    (drule checked_contract_struct_args_unique >> DISCH_TAC >> fs[abi_struct_env_rel_tops]) >>
  drule_all checked_log_compiler_metadata >> strip_tac >>
  qspecl_then [`ctx`, `func`, `type_env tops`, `cenv`, `lctx`, `ret`, `event_id`, `exprs`, `cs`, `cs'`,
    `sig_hash`, `fts`, `flags`, `args`, `eval_cut`, `raw_topics`, `topic_ops`, `topic_cut`,
    `atvs`, `values`, `ss`, `0`, `0`] mp_tac compile_saved_log_empty_path >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` (qx_choose_then `topics` strip_assume_tac)) >>
  qabbrev_tac `ev = <|logger := w2w ss.vs_call_ctx.cc_address; topics := n2w sig_hash::topics; data := []|>` >>
  qspecl_then [`func`, `cenv`, `cx`, `es`, `ss`, `out`, `[ev]`, `eval_cut.cs_next_var`]
    mp_tac source_relations_log_memory_frame >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[Abbr`ev`]]) >> strip_tac >>
  `env.type_defs = get_tenv cx /\ ss.vs_call_ctx.cc_address = cx.txn.target` by
    (drule_all source_log_context >> simp[]) >>
  qspecl_then [`tops`, `dep`, `layouts`, `addr`, `art`, `env`, `ret`, `event_id`, `exprs`, `env'`,
    `cx.sources`, `cx.txn.target`, `cenv`, `(sig_hash,fts,flags)`, `values`]
    mp_tac checked_log_metadata_source_encoding >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qexistsl_tac [`out`, `ev`] >> fs[Abbr`ev`]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed checked indexed-only Log suffix: " ^ name)
  end) (DB.thms "checkedLogEmpty")
