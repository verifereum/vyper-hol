(* TOP-LEVEL: execute the entire compiled indexed-only Log, including all
   argument evaluation. Per-expression lowering is the statement induction
   hypothesis; the saved-argument list and Log suffix are proved here. *)
Theory checkedLogEmptyExecution
Ancestors
  checkedLogEmpty logArgumentCodeExecution logArgumentCharges logArgumentListContract
  sourceLogFrames compileAllocationRequests compileAllocaProvenance compileAppendProps
  compileIdFlow stmtLowering exprLowering compileEnv compileVyper vyperTypeContract
  vyperTypeSystem vyperContext vyperState vyperInterpreter fragExec fragBlockPath
  venomState list pair words

Theorem checked_compile_log_empty_execution:
  !layout_tvs tops dep layouts addr art env cx cenv ctx func ret event_id exprs env' lctx
    cs cs' sig_hash fts flags args eval_cut raw_topics topic_ops topic_cut charge
    es values es' total_charge before credit ids reserved requests.
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
    fn_has_code cs cs' func /\ fn_has_code eval_cut topic_cut func /\ fn_has_code topic_cut cs' func /\
    fn_inst_ids_distinct func /\ cs_extends eval_cut cs' /\
    ids = compiler_alloca_ids cs cs' /\ requests = compiler_alloca_requests cs cs' /\
    EVERY (\e. cs_appends (lower_value compile_expr cenv (expr_type e) e)) exprs /\
    EVERY (\e. compiler_id_flow (lower_value compile_expr cenv (expr_type e) e)) exprs /\
    LIST_REL (\e tv. evaluate_type (type_env tops) (lowered_value_type cenv e) = SOME tv /\
      type_memory_size tv < dimword(:256)) exprs layout_tvs /\
    EVERY (log_argument_lowering tops env ctx func cenv cx ids reserved requests cs' charge) exprs /\
    log_argument_charges charge cx exprs es values es' total_charge /\ total_charge <= credit /\
    log_prefix_ready env cx cenv func ids reserved requests cs' exprs cs es before credit [] [] [] /\
    LENGTH (Lit (n2w sig_hash)::topic_ops) < dimword(:256) /\ ~before.vs_halted ==>
    ?out ev.
      eval_stmt cx (Log event_id exprs) es = (INL (),es' with logs := es'.logs ++ [ev]) /\
      fragment_path ctx func before out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      state_rel cenv cx (es' with logs := es'.logs ++ [ev]) out /\
      local_ptrs_rel func cenv es'.scopes out
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qspecl_then [`exprs`, `layout_tvs`, `tops`, `dep`, `layouts`, `addr`, `art`, `env`, `ctx`, `func`,
    `cenv`, `cx`, `ids`, `reserved`, `requests`, `cs'`, `charge`, `cs`, `eval_cut`, `args`,
    `es`, `values`, `es'`, `total_charge`, `before`, `credit`]
    mp_tac checked_compile_log_arguments_from_code >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `middle` (qx_choose_then `atvs` strip_assume_tac)) >>
  `~middle.vs_halted` by fs[] >>
  qspecl_then [`tops`, `dep`, `layouts`, `addr`, `art`, `env`, `cx`, `es'`, `cenv`, `ctx`, `func`,
    `ret`, `event_id`, `exprs`, `env'`, `lctx`, `cs`, `cs'`, `sig_hash`, `fts`, `flags`, `args`,
    `eval_cut`, `raw_topics`, `topic_ops`, `topic_cut`, `atvs`, `values`, `middle`, `ids`,
    `reserved`, `requests`, `cs'`, `credit - total_charge`] mp_tac checked_compile_saved_log_empty >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` (qx_choose_then `ev` strip_assume_tac)) >>
  `eval_exprs cx exprs es = (INL values,es')` by (drule_all log_argument_charges_source >> simp[]) >>
  `eval_stmt cx (Log event_id exprs) es = (INL (),es' with logs := es'.logs ++ [ev])` by
    (drule_all eval_log_arguments >> simp[]) >>
  `fragment_path ctx func before out` by
    (irule fragment_path_trans >> qexists_tac `middle` >> simp[]) >>
  qexistsl_tac [`out`, `ev`] >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete indexed-only Log execution: " ^ name)
  end) (DB.thms "checkedLogEmptyExecution")
