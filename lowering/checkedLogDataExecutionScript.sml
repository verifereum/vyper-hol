(* TOP-LEVEL: execute an entire checked Log with nonempty event data.
   Expression lowering is the ordinary induction hypothesis. Source typing,
   argument snapshots, recursive ABI packing, encoding and LOG are composed
   here, with the concrete compiler allocation profile. *)
Theory checkedLogDataExecution
Ancestors
  checkedLogData checkedLogValues logArgumentCodeExecution logArgumentCharges logArgumentListContract
  sourceLogFrames compileAllocationRequests compileAllocaProvenance compileAppendProps compileIdFlow
  stmtLowering exprLowering compileEnv compileVyper vyperTypeContract vyperTypeSystem
  vyperTypeExprSoundness vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperContext vyperState vyperInterpreter fragExec fragBlockPath venomState list pair words

Theorem checked_compile_log_data_execution:
  !layout_tvs tops dep layouts addr art ctx func cenv cx env env' lctx ret event_id exprs cs cs'
    sig_hash fts flags args eval_cut raw_topics data_ops topic_ops topic_cut data_types data_capacity
    data_buf store_cut packed_cut abi_buf encode_cut capacity charge
    es values es' total_charge before credit ids reserved requests.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\
    env.event_fields = art.cta_event_fields /\ env.type_defs = type_env tops /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    cenv.ce_event_info = build_event_info (type_env tops) tops (K NONE) /\
    ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
    type_stmt env ret (Log event_id exprs) = SOME env' /\
    functions_well_typed cx /\ call_evaluation_safe cx (int_calls_exprs exprs) /\
    cenv.ce_event_info (nsid_to_string event_id) = SOME (sig_hash,fts,flags) /\
    compile_log_eval_all cenv exprs cs = (args,eval_cut) /\
    split_log_ops args flags = (raw_topics,data_ops) /\ ~NULL data_ops /\
    compile_log_topic_ops raw_topics eval_cut = (topic_ops,topic_cut) /\
    data_types = log_non_indexed_types flags fts /\
    data_capacity = MAX 32 (SUM (MAP (type_memory_bytes cenv) data_types)) /\
    compile_alloc_buffer data_capacity topic_cut = (data_buf,store_cut) /\
    compile_log_store_data cenv data_ops data_types data_buf.buf_operand 0 store_cut = ((),packed_cut) /\
    capacity = MAX 32 (abi_size_bound cenv.ce_struct_fields (TupleT data_types)) /\
    compile_alloc_buffer capacity packed_cut = (abi_buf,encode_cut) /\
    compile_stmt cenv lctx ret (Log event_id exprs) cs = ((),cs') /\
    fn_has_code cs cs' func /\ fn_has_code eval_cut topic_cut func /\ fn_has_code topic_cut store_cut func /\
    fn_has_code store_cut packed_cut func /\ fn_has_code packed_cut encode_cut func /\ fn_has_code encode_cut cs' func /\
    fn_inst_ids_distinct func /\ compiler_id_history packed_cut /\ cs_extends eval_cut cs' /\
    eval_cut.cs_next_var <= topic_cut.cs_next_var /\
    ids = compiler_alloca_ids cs cs' /\ requests = compiler_alloca_requests cs cs' /\
    EVERY (\e. cs_appends (lower_value compile_expr cenv (expr_type e) e)) exprs /\
    EVERY (\e. compiler_id_flow (lower_value compile_expr cenv (expr_type e) e)) exprs /\
    LIST_REL (\e tv. evaluate_type (type_env tops) (lowered_value_type cenv e) = SOME tv /\
      type_memory_size tv < dimword(:256)) exprs layout_tvs /\
    EVERY (log_argument_lowering tops env ctx func cenv cx ids reserved requests cs' charge) exprs /\
    log_argument_charges charge cx exprs es values es' total_charge /\ total_charge <= credit /\
    log_prefix_ready env cx cenv func ids reserved requests cs' exprs cs es before credit [] [] [] /\
    (!id. MEM id (topic_cut.cs_next_id::packed_cut.cs_next_id::compiler_alloca_ids encode_cut cs') ==> MEM id ids) /\
    MEM topic_cut.cs_next_id (compiler_alloca_ids eval_cut cs') /\
    MEM (topic_cut.cs_next_id,data_capacity) requests /\ MEM (packed_cut.cs_next_id,capacity) requests /\
    (!id. MEM id (compiler_alloca_ids encode_cut cs') ==> MEM (id,32) requests) /\
    32 <= reserved /\ data_capacity + capacity <= reserved /\
    LENGTH (Lit (n2w sig_hash)::topic_ops) < dimword(:256) /\ ~before.vs_halted ==>
    ?out ev.
      eval_stmt cx (Log event_id exprs) es = (INL (),es' with logs := es'.logs ++ [ev]) /\
      fragment_path ctx func before out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      state_rel cenv cx (es' with logs := es'.logs ++ [ev]) out /\
      local_ptrs_rel func cenv es'.scopes out
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `eval_exprs cx exprs es = (INL values,es')` by (drule_all log_argument_charges_source >> simp[]) >>
  `runtime_consistent env cx es` by fs[log_prefix_ready_def] >>
  qspecl_then [`env`, `cx`, `es`, `ret`, `event_id`, `exprs`, `env'`, `values`, `es'`]
    mp_tac checked_log_evaluated_argument_types >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  `LIST_REL (\e v. ?tv. evaluate_type (type_env tops) (expr_type e) = SOME tv /\
    value_has_type tv v) exprs values` by
    (qpat_assum `env.type_defs = type_env tops` (fn env_types =>
       qpat_assum `LIST_REL _ exprs values` (ACCEPT_TAC o REWRITE_RULE [env_types]))) >>
  qspecl_then [`tops`, `dep`, `layouts`, `addr`, `art`, `env`, `ret`, `event_id`, `exprs`, `env'`,
    `cenv`, `sig_hash`, `fts`, `flags`, `values`] mp_tac checked_log_declared_values >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `ftvs` strip_assume_tac) >>
  qspecl_then [`exprs`, `layout_tvs`, `tops`, `dep`, `layouts`, `addr`, `art`, `env`, `ctx`, `func`,
    `cenv`, `cx`, `ids`, `reserved`, `requests`, `cs'`, `charge`, `cs`, `eval_cut`, `args`,
    `es`, `values`, `es'`, `total_charge`, `before`, `credit`]
    mp_tac checked_compile_log_arguments_from_code >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `middle` (qx_choose_then `atvs` strip_assume_tac)) >>
  `~middle.vs_halted` by fs[] >>
  qspecl_then [`tops`, `dep`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `cx`, `es'`, `env`, `env'`,
    `lctx`, `ret`, `event_id`, `exprs`, `cs`, `cs'`, `sig_hash`, `fts`, `flags`, `args`, `eval_cut`,
    `raw_topics`, `data_ops`, `topic_ops`, `topic_cut`, `data_types`, `data_capacity`, `data_buf`, `store_cut`,
    `packed_cut`, `abi_buf`, `encode_cut`, `capacity`, `ftvs`, `atvs`, `values`, `middle`,
    `ids`, `reserved`, `requests`, `cs'`, `credit - total_charge`] mp_tac checked_compile_saved_log_data >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` (qx_choose_then `ev` strip_assume_tac)) >>
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
    then () else raise Fail ("unclosed complete nonempty Log execution: " ^ name)
  end) (DB.thms "checkedLogDataExecution")
