(* TOP-LEVEL: both actual Log allocations, checked compatible packing,
   arbitrary recursive ABI encoding and LOG preserve complete source state
   from saved arguments before data allocation. All runtime cuts are produced.
   Helper: the data allocation transports native encoder resources. *)
Theory abiNativeLogDataState
Ancestors
  abiNativeLogPackedState abiNativeLogAllocationReady abiNativeLogBufferProfile abiLogArenaState
  abiLogPackingReady abiLogTopicsReady abiLogAllocationFrame sourceAllocationPrivacy sourceMemoryFrames allocationGrowth
  typedLogArgs abiAllocationBudget abiAllocationFrame abiAllocatedWindows abiStateFrame abiFieldOperands abiFlatRun
  memoryValueSnapshot memoryValueDefs valueEncoding compileAllocaProvenance compileIdFlow
  stmtLowering compileEnv compileVyper vyperTypeContract vyperContext vyperTypeSystem vyperTypeInvariants vyperState
  fragExec fragBlockPath vyperABI contractABI venomState list words arithmetic

Theorem native_log_arena_resources:
  !ids id var_base capacity index before after output_id output_capacity cenv scopes.
    after = (memory_snapshot_allocated id var_base capacity before with vs_inst_idx := index) /\
    after.vs_alloca_next <= before.vs_alloca_next + capacity /\ allocation_growth before after /\
    source_alloca_floor cenv scopes (id::output_id::ids) before /\ id <> output_id /\ 32 <= capacity /\
    abi_alloca_request_ok output_id output_capacity before /\
    abi_alloca_budget 32 ids before + capacity + output_capacity < dimword(:256) /\
    (!request_id. MEM request_id ids ==> abi_alloca_request_ok request_id 32 before) ==>
    abi_alloca_request_ok output_id output_capacity after /\
    abi_alloca_budget 32 ids after + output_capacity < dimword(:256) /\
    (!request_id. MEM request_id ids ==> abi_alloca_request_ok request_id 32 after) /\
    source_alloca_floor cenv scopes (output_id::ids) after
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`ids`, `id`, `var_base`, `capacity`, `index`, `before`, `after`, `output_id`, `output_capacity`]
    mp_tac abi_native_log_data_allocation_resources >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qspecl_then [`cenv`, `scopes`, `id::output_id::ids`, `before`, `after`] mp_tac source_alloca_floor_growth >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qspecl_then [`cenv`, `scopes`, `output_id::ids`, `id::output_id::ids`, `after`] mp_tac source_alloca_floor_subprofile >>
  impl_tac >- (conj_tac >- first_assum MATCH_ACCEPT_TAC >> simp[]) >> DISCH_TAC >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem checked_compile_native_log_data_state:
  !tops dep layouts addr art ctx func cenv cx es flags fts args ftvs atvs values data_capacity cs data_buf store_cut
    ret packed_cut capacity abi_buf encode_cut cs' avs topic_ops topics ss.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\ cenv.ce_struct_fields = make_struct_fields_map tops /\
    LENGTH flags = LENGTH args /\ LIST_REL event_arg_compatible fts (MAP SND args) /\
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) fts ftvs /\
    LIST_REL (\arg tv. evaluate_type (type_env tops) (SND arg) = SOME tv) args atvs /\
    compile_alloc_buffer data_capacity cs = (data_buf,store_cut) /\
    compile_log_store_data cenv (SND (split_log_ops args flags)) (log_non_indexed_types flags fts)
      data_buf.buf_operand 0 store_cut = (ret,packed_cut) /\
    compile_alloc_buffer capacity packed_cut = (abi_buf,encode_cut) /\
    compile_log_abi_emit abi_buf.buf_operand data_buf.buf_operand
      (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT (log_non_indexed_types flags fts))) topic_ops encode_cut = ((),cs') /\
    fn_has_code cs store_cut func /\ fn_has_code store_cut packed_cut func /\
    fn_has_code packed_cut encode_cut func /\ fn_has_code encode_cut cs' func /\
    fn_inst_ids_distinct func /\ compiler_id_history packed_cut /\
    state_well_typed es /\ state_rel cenv cx es ss /\ local_ptrs_rel func cenv es.scopes ss /\
    vyper_to_abi_list (type_env tops) (log_non_indexed_types flags fts) (select_log_args F flags values) = SOME avs /\
    source_alloca_floor cenv es.scopes (cs.cs_next_id::packed_cut.cs_next_id::compiler_alloca_ids encode_cut cs') ss /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before cs.cs_next_var (Var p)) /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    log_args_rel args atvs values ss /\
    log_args_safe args atvs ss (w2n (memory_snapshot_addr cs.cs_next_id ss))
      (type_memory_size (TupleTV (select_log_args F flags ftvs))) /\
    EVERY (\arg. abi_operand_before cs.cs_next_var (FST arg)) args /\
    EVERY (abi_operand_before cs.cs_next_var) topic_ops /\
    eval_operands topic_ops ss = SOME topics /\ LENGTH topic_ops < dimword(:256) /\
    32 <= data_capacity /\ type_memory_size (TupleTV (select_log_args F flags ftvs)) <= data_capacity /\ 32 <= capacity /\
    alloca_inv ss /\ abi_alloca_request_ok cs.cs_next_id data_capacity ss /\
    abi_alloca_request_ok packed_cut.cs_next_id capacity ss /\
    abi_alloca_budget 32 (compiler_alloca_ids encode_cut cs') ss + data_capacity + capacity < dimword(:256) /\
    (!id. MEM id (compiler_alloca_ids encode_cut cs') ==> abi_alloca_request_ok id 32 ss) /\
    LENGTH (enc (Tuple (MAP (vyper_to_abi_type (type_env tops)) (log_non_indexed_types flags fts))) (ListV avs)) <= capacity ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      out.vs_logs = ss.vs_logs ++ [<|logger := w2w ss.vs_call_ctx.cc_address; topics := topics;
        data := enc (Tuple (MAP (vyper_to_abi_type (type_env tops)) (log_non_indexed_types flags fts))) (ListV avs)|>] /\
      state_rel cenv cx (es with logs := es.logs ++ [<|logger := w2w ss.vs_call_ctx.cc_address; topics := topics;
        data := enc (Tuple (MAP (vyper_to_abi_type (type_env tops)) (log_non_indexed_types flags fts))) (ListV avs)|>]) out /\
      local_ptrs_rel func cenv es.scopes out /\ allocation_growth ss out /\
      read_memory (w2n (memory_snapshot_addr packed_cut.cs_next_id
        (memory_snapshot_allocated cs.cs_next_id cs.cs_next_var data_capacity ss)))
        (LENGTH (enc (Tuple (MAP (vyper_to_abi_type (type_env tops)) (log_non_indexed_types flags fts))) (ListV avs))) out =
        enc (Tuple (MAP (vyper_to_abi_type (type_env tops)) (log_non_indexed_types flags fts))) (ListV avs) /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      abi_state_frame ss (out with vs_logs := ss.vs_logs)
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_log_buffer_ids_distinct >> DISCH_TAC >>
  drule_all compile_log_buffers_outside_encoder_profile >> strip_tac >>
  `ss.vs_alloca_next + data_capacity < dimword (:256)` by
    (qspecl_then [`32`, `compiler_alloca_ids encode_cut cs'`, `ss`] mp_tac abi_alloca_budget_frontier >> decide_tac) >>
  `ss.vs_alloca_next < dimword (:256)` by decide_tac >>
  qspecl_then [`cenv`, `es.scopes`, `cs.cs_next_id::packed_cut.cs_next_id::compiler_alloca_ids encode_cut cs'`, `ss`, `cs.cs_next_id`]
    mp_tac source_alloca_floor_snapshot >> impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]) >> DISCH_TAC >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `ss`, `data_capacity`, `cs`, `data_buf`, `store_cut`, `args`, `atvs`, `values`,
    `TupleTV (select_log_args F flags ftvs)`, `topic_ops`, `topics`] mp_tac compile_log_arena_source_state >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> disch_then (qx_choose_then `arena` strip_assume_tac) >>
  qspecl_then [`compiler_alloca_ids encode_cut cs'`, `cs.cs_next_id`, `cs.cs_next_var`, `data_capacity`,
    `LENGTH store_cut.cs_current_insts`, `ss`, `arena`, `packed_cut.cs_next_id`, `capacity`, `cenv`, `es.scopes`]
    mp_tac native_log_arena_resources >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  `abi_allocated_window arena cs.cs_next_id (w2n (memory_snapshot_addr cs.cs_next_id ss))
    (type_memory_size_list (select_log_args F flags ftvs))` by
    (qpat_x_assum `abi_allocated_window arena _ _ (type_memory_size _)` mp_tac >> simp_tac bool_ss [Once type_memory_size_def]) >>
  `log_args_avoid args (compiler_var_names store_cut.cs_next_var (packed_cut.cs_next_var - store_cut.cs_next_var))` by
    (qspecl_then [`args`, `cs.cs_next_var`, `store_cut.cs_next_var`, `packed_cut.cs_next_var - store_cut.cs_next_var`]
       mp_tac log_args_before_names >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >> first_assum MATCH_ACCEPT_TAC) >>
  qspecl_then [`tops`, `dep`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `cx`, `es`, `flags`, `fts`, `args`, `ftvs`, `atvs`, `values`,
    `data_buf.buf_operand`, `store_cut`, `ret`, `packed_cut`, `capacity`, `abi_buf`, `encode_cut`, `cs'`, `avs`, `topic_ops`, `topics`,
    `arena`, `memory_snapshot_addr cs.cs_next_id ss`, `cs.cs_next_id`] mp_tac checked_compile_native_packed_log_state >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> disch_then (qx_choose_then `out` strip_assume_tac) >>
  qspecl_then [`ss`, `arena`] mp_tac abi_state_frame_observables >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
  qpat_x_assum `state_rel cenv cx (es with logs := _) out` mp_tac >> asm_simp_tac bool_ss [] >> DISCH_TAC >>
  `fragment_path ctx func ss out` by (irule fragment_path_trans >> qexists_tac `arena` >> simp[]) >>
  `allocation_growth ss out` by (irule allocation_growth_trans >> qexists_tac `arena` >> simp[]) >>
  `!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss` by
    (qspecl_then [`cs.cs_next_var`, `store_cut.cs_next_var`, `ss`, `arena`, `out`]
       mp_tac abi_operand_before_frame_trans >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  `abi_state_frame ss (out with vs_logs := ss.vs_logs)` by
    (qspecl_then [`ss`, `arena`, `out`] mp_tac abi_log_allocation_state_frame >> simp[]) >>
  qexists_tac `out` >> asm_simp_tac bool_ss [] >>
  qpat_x_assum `read_memory _ _ out = _` mp_tac >> asm_simp_tac (srw_ss()) [memory_snapshot_addr_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual native Log allocations and source state: " ^ name)
  end) (DB.thms "abiNativeLogDataState")
