(* TOP-LEVEL: checked nonempty Log emission from saved arguments. Actual
   compiler requests establish allocator room and argument non-overlap;
   source typing establishes ABI conversion success and buffer capacity. *)
Theory checkedLogData
Ancestors
  checkedLogMetadata checkedLogDataEncoding logArgumentLogSafety logArgumentLogResources
  logArgumentListContract abiNativeLogTopicsState abiLogPackingReady
  sourceLogFrames sourceAllocationPrivacy abiTypeShape typedCopyProducer eventLogSourceLookup
  typedLogArgs abiAllocationBudget abiAllocationFrame abiFieldOperands
  compileAllocaProvenance compileIdFlow stmtLowering compileEnv compileVyper
  vyperTypeContract vyperTypeSystem vyperTypeInvariants vyperTypeExprSoundness
  vyperContext vyperEvent vyperState vyperABI contractABI fragExec fragBlockPath
  memoryValueSnapshot venomState list pair words arithmetic

Theorem checked_compile_saved_log_data:
  !tops dep layouts addr art ctx func cenv cx es env env' lctx ret event_id exprs cs cs'
    sig_hash fts flags args eval_cut raw_topics data_ops topic_ops topic_cut data_types data_capacity
    data_buf store_cut packed_cut abi_buf encode_cut capacity ftvs atvs values ss
    ids reserved requests final_cut credit.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\
    env.event_fields = art.cta_event_fields /\ env.type_defs = type_env tops /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    cenv.ce_event_info = build_event_info (type_env tops) tops (K NONE) /\
    ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
    type_stmt env ret (Log event_id exprs) = SOME env' /\
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
    fn_has_code eval_cut topic_cut func /\ fn_has_code topic_cut store_cut func /\
    fn_has_code store_cut packed_cut func /\ fn_has_code packed_cut encode_cut func /\ fn_has_code encode_cut cs' func /\
    fn_inst_ids_distinct func /\ compiler_id_history packed_cut /\
    eval_cut.cs_next_var <= topic_cut.cs_next_var /\
    LIST_REL (\fty tv. evaluate_type (type_env tops) fty = SOME tv) fts ftvs /\
    LIST_REL (\arg tv. evaluate_type (type_env tops) (SND arg) = SOME tv) args atvs /\
    values_have_types ftvs values /\
    log_prefix_ready env cx cenv func ids reserved requests final_cut [] eval_cut es ss credit args atvs values /\
    (!id. MEM id (topic_cut.cs_next_id::packed_cut.cs_next_id::compiler_alloca_ids encode_cut cs') ==> MEM id ids) /\
    MEM topic_cut.cs_next_id (compiler_alloca_ids eval_cut final_cut) /\
    MEM (topic_cut.cs_next_id,data_capacity) requests /\ MEM (packed_cut.cs_next_id,capacity) requests /\
    (!id. MEM id (compiler_alloca_ids encode_cut cs') ==> MEM (id,32) requests) /\
    32 <= reserved /\ data_capacity + capacity <= reserved /\
    LENGTH (Lit (n2w sig_hash)::topic_ops) < dimword(:256) /\ ~ss.vs_halted ==>
    ?out ev.
      encode_source_event (get_tenv cx) cx.sources cx.txn.target event_id values = SOME ev /\
      fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      out.vs_logs = ss.vs_logs ++ [ev] /\
      state_rel cenv cx (es with logs := es.logs ++ [ev]) out /\
      local_ptrs_rel func cenv es.scopes out
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qspecl_then [`env`, `cx`, `cenv`, `func`, `ids`, `reserved`, `requests`, `final_cut`, `eval_cut`, `es`,
    `ss`, `credit`, `args`, `atvs`, `values`, `topic_cut.cs_next_id`, `data_capacity`, `packed_cut.cs_next_id`,
    `capacity`, `compiler_alloca_ids encode_cut cs'`] mp_tac log_ready_suffix_resources >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qpat_assum `log_prefix_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [log_prefix_ready_def]) >>
  `env_consistent env cx es` by fs[runtime_consistent_def] >>
  `abi_struct_env_rel env.type_defs cenv.ce_struct_fields` by
    (drule checked_contract_struct_args_unique >> DISCH_TAC >> fs[abi_struct_env_rel_tops]) >>
  qpat_assum `env.type_defs = type_env tops` (fn env_types =>
    qpat_assum `abi_struct_env_rel env.type_defs cenv.ce_struct_fields`
      (ASSUME_TAC o REWRITE_RULE [env_types])) >>
  drule_all checked_log_compiler_metadata >> strip_tac >>
  `LENGTH flags = LENGTH fts` by (imp_res_tac LIST_REL_LENGTH >> fs[]) >>
  `type_memory_size (TupleTV (select_log_args F flags ftvs)) <= data_capacity` by
    (drule_all checked_log_data_memory_size >> DISCH_TAC >> fs[]) >>
  `log_args_safe args atvs ss (w2n (memory_snapshot_addr topic_cut.cs_next_id ss))
    (type_memory_size (TupleTV (select_log_args F flags ftvs)))` by
    (qspecl_then [`env`, `cx`, `cenv`, `func`, `ids`, `reserved`, `requests`, `final_cut`, `eval_cut`, `topic_cut`,
       `es`, `ss`, `credit`, `args`, `atvs`, `values`, `data_capacity`, `data_buf`, `store_cut`,
       `type_memory_size (TupleTV (select_log_args F flags ftvs))`] mp_tac log_ready_arguments_buffer_safe >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  `source_alloca_floor cenv es.scopes (topic_cut.cs_next_id::packed_cut.cs_next_id::compiler_alloca_ids encode_cut cs') ss` by
    (qspecl_then [`cenv`, `es.scopes`, `topic_cut.cs_next_id::packed_cut.cs_next_id::compiler_alloca_ids encode_cut cs'`, `ids`, `ss`]
       mp_tac source_alloca_floor_subprofile >> simp[]) >>
  qspecl_then [`type_env tops`, `cenv.ce_struct_fields`, `flags`, `fts`, `ftvs`, `values`]
    mp_tac checked_log_data_encoding_bound >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, fs[]]) >>
  disch_then (qx_choose_then `avs` strip_assume_tac) >>
  `vyper_to_abi_list (type_env tops) data_types (select_log_args F flags values) = SOME avs /\
    LENGTH (enc (Tuple (MAP (vyper_to_abi_type (type_env tops)) data_types)) (ListV avs)) <= capacity` by gvs[] >>
  qspecl_then [`tops`, `dep`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `cx`, `es`, `lctx`, `ret`, `event_id`, `exprs`, `cs`, `cs'`,
    `sig_hash`, `fts`, `flags`, `args`, `eval_cut`, `raw_topics`, `data_ops`, `topic_ops`, `topic_cut`, `data_types`, `data_capacity`,
    `data_buf`, `store_cut`, `packed_cut`, `abi_buf`, `encode_cut`, `capacity`, `ftvs`, `atvs`, `values`, `avs`, `ss`]
    mp_tac checked_compile_native_log_stmt_topics_state >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` (qx_choose_then `topics` strip_assume_tac)) >>
  `env.type_defs = get_tenv cx /\ ss.vs_call_ctx.cc_address = cx.txn.target` by
    (drule_all source_log_context >> simp[]) >>
  qspecl_then [`tops`, `dep`, `layouts`, `addr`, `art`, `env`, `ret`, `event_id`, `exprs`, `env'`,
    `cx.sources`, `cx.txn.target`, `cenv`, `(sig_hash,fts,flags)`, `values`]
    mp_tac checked_log_metadata_source_encoding >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qexistsl_tac [`out`, `<|logger := w2w ss.vs_call_ctx.cc_address; topics := n2w sig_hash::topics;
    data := enc (Tuple (MAP (vyper_to_abi_type (type_env tops)) data_types)) (ListV avs)|>`] >> gvs[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed checked nonempty Log suffix: " ^ name)
  end) (DB.thms "checkedLogData")
