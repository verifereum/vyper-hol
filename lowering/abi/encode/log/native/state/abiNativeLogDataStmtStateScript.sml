(* TOP-LEVEL: the actual nonempty Log statement data suffix preserves the
   complete source state. Real compiler buffer capacities and checked field
   layouts establish the arena footprint; every runtime cut is executed. *)
Theory abiNativeLogDataStmtState
Ancestors
  abiNativeLogDataState abiLogStmtCode abiLogPackingReady sourceAllocationPrivacy sourceMemoryFrames allocationGrowth
  typedLogArgs abiAllocationBudget abiAllocationFrame abiStateFrame abiFieldOperands memoryValueSnapshot memoryValueDefs valueEncoding
  compileAllocaProvenance compileIdFlow stmtLowering compileEnv compileVyper
  vyperTypeContract vyperContext vyperTypeSystem vyperTypeInvariants vyperState
  fragExec fragBlockPath vyperABI contractABI venomState list pair words arithmetic

Theorem checked_compile_native_log_stmt_data_state:
  !tops dep layouts addr art ctx func cenv cx es lctx ty event_id exprs cs cs'
    sig_hash fts flags args eval_cut raw_topics data_ops topic_ops topic_cut
    data_types data_capacity data_buf store_cut packed_cut abi_buf encode_cut capacity ftvs atvs values avs topics ss.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\ cenv.ce_struct_fields = make_struct_fields_map tops /\
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
    compile_stmt cenv lctx ty (Log event_id exprs) cs = ((),cs') /\
    fn_has_code topic_cut store_cut func /\ fn_has_code store_cut packed_cut func /\
    fn_has_code packed_cut encode_cut func /\ fn_has_code encode_cut cs' func /\
    fn_inst_ids_distinct func /\ compiler_id_history packed_cut /\
    LENGTH flags = LENGTH args /\ LIST_REL event_arg_compatible fts (MAP SND args) /\
    LIST_REL (\fty tv. evaluate_type (type_env tops) fty = SOME tv) fts ftvs /\
    LIST_REL (\arg tv. evaluate_type (type_env tops) (SND arg) = SOME tv) args atvs /\
    state_well_typed es /\ state_rel cenv cx es ss /\ local_ptrs_rel func cenv es.scopes ss /\
    vyper_to_abi_list (type_env tops) data_types (select_log_args F flags values) = SOME avs /\
    source_alloca_floor cenv es.scopes (topic_cut.cs_next_id::packed_cut.cs_next_id::compiler_alloca_ids encode_cut cs') ss /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before topic_cut.cs_next_var (Var p)) /\
    ss.vs_current_bb = topic_cut.cs_current_bb /\ ss.vs_inst_idx = LENGTH topic_cut.cs_current_insts /\ ~ss.vs_halted /\
    log_args_rel args atvs values ss /\
    log_args_safe args atvs ss (w2n (memory_snapshot_addr topic_cut.cs_next_id ss))
      (type_memory_size (TupleTV (select_log_args F flags ftvs))) /\
    EVERY (\arg. abi_operand_before topic_cut.cs_next_var (FST arg)) args /\
    EVERY (abi_operand_before topic_cut.cs_next_var) (Lit (n2w sig_hash)::topic_ops) /\
    eval_operands (Lit (n2w sig_hash)::topic_ops) ss = SOME topics /\ LENGTH (Lit (n2w sig_hash)::topic_ops) < dimword(:256) /\
    alloca_inv ss /\ abi_alloca_request_ok topic_cut.cs_next_id data_capacity ss /\
    abi_alloca_request_ok packed_cut.cs_next_id capacity ss /\
    abi_alloca_budget 32 (compiler_alloca_ids encode_cut cs') ss + data_capacity + capacity < dimword(:256) /\
    (!id. MEM id (compiler_alloca_ids encode_cut cs') ==> abi_alloca_request_ok id 32 ss) /\
    LENGTH (enc (Tuple (MAP (vyper_to_abi_type (type_env tops)) data_types)) (ListV avs)) <= capacity ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      out.vs_logs = ss.vs_logs ++ [<|logger := w2w ss.vs_call_ctx.cc_address; topics := topics;
        data := enc (Tuple (MAP (vyper_to_abi_type (type_env tops)) data_types)) (ListV avs)|>] /\
      state_rel cenv cx (es with logs := es.logs ++ [<|logger := w2w ss.vs_call_ctx.cc_address; topics := topics;
        data := enc (Tuple (MAP (vyper_to_abi_type (type_env tops)) data_types)) (ListV avs)|>]) out /\
      local_ptrs_rel func cenv es.scopes out /\ allocation_growth ss out /\
      read_memory (w2n (memory_snapshot_addr packed_cut.cs_next_id
        (memory_snapshot_allocated topic_cut.cs_next_id topic_cut.cs_next_var data_capacity ss)))
        (LENGTH (enc (Tuple (MAP (vyper_to_abi_type (type_env tops)) data_types)) (ListV avs))) out =
        enc (Tuple (MAP (vyper_to_abi_type (type_env tops)) data_types)) (ListV avs) /\
      (!arg_op. abi_operand_before topic_cut.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      abi_state_frame ss (out with vs_logs := ss.vs_logs)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `data_capacity = _` SUBST_ALL_TAC >> qpat_x_assum `capacity = _` SUBST_ALL_TAC >>
  qspecl_then [`cenv`, `lctx`, `ty`, `event_id`, `exprs`, `cs`, `sig_hash`, `fts`, `flags`, `args`, `eval_cut`,
    `raw_topics`, `data_ops`, `topic_ops`, `topic_cut`, `data_types`, `data_buf`, `store_cut`, `packed_cut`, `abi_buf`, `encode_cut`]
    mp_tac compile_log_stmt_nonempty_suffix >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  `compile_log_abi_emit abi_buf.buf_operand data_buf.buf_operand
    (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT data_types)) (Lit (n2w sig_hash)::topic_ops) encode_cut = ((),cs')` by fs[] >>
  `compile_log_store_data cenv (SND (split_log_ops args flags)) data_types data_buf.buf_operand 0 store_cut = ((),packed_cut)` by
    (qpat_x_assum `compile_log_store_data cenv data_ops _ _ _ _ = _` mp_tac >> asm_simp_tac bool_ss [SND]) >>
  drule_all checked_log_data_memory_size >> DISCH_TAC >>
  `32 <= MAX 32 (SUM (MAP (type_memory_bytes cenv) data_types)) /\
    type_memory_size (TupleTV (select_log_args F flags ftvs)) <= MAX 32 (SUM (MAP (type_memory_bytes cenv) data_types)) /\
    32 <= MAX 32 (abi_size_bound cenv.ce_struct_fields (TupleT data_types))` by
    (qpat_x_assum `data_types = _` (fn th => fs[th])) >>
  qspecl_then [`tops`, `dep`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `cx`, `es`, `flags`, `fts`, `args`, `ftvs`, `atvs`, `values`,
    `MAX 32 (SUM (MAP (type_memory_bytes cenv) data_types))`, `topic_cut`, `data_buf`, `store_cut`, `()`, `packed_cut`,
    `MAX 32 (abi_size_bound cenv.ce_struct_fields (TupleT data_types))`, `abi_buf`, `encode_cut`, `cs'`, `avs`,
    `Lit (n2w sig_hash)::topic_ops`, `topics`, `ss`] mp_tac checked_compile_native_log_data_state >>
  qpat_x_assum `data_types = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual Log data suffix source state: " ^ name)
  end) (DB.thms "abiNativeLogDataStmtState")
