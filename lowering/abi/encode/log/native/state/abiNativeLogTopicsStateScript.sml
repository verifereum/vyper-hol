(* TOP-LEVEL: actual topic production, both real allocations, compatible
   packing and arbitrary recursive ABI encoding preserve complete source
   state and emit the source event metadata from saved arguments.
   Helper: topic hashing preserves source values and allocator backing. *)
Theory abiNativeLogTopicsState
Ancestors
  abiNativeLogDataStmtState abiNativeLogSource eventLogTopicsPath abiLogTopicsReady abiLogPackingReady abiLogAllocationFrame
  sourceAllocationPrivacy sourceMemoryFrames allocationGrowth typedLogArgs typedCopyStateFrame
  abiAllocationBudget abiAllocationFrame abiStateFrame abiFieldOperands abiFlatRun
  memoryValueSnapshot memoryValueDefs valueEncoding compileAllocaProvenance compileIdFlow
  stmtLowering compileEnv compileVyper vyperTypeContract vyperContext vyperTypeSystem vyperTypeInvariants vyperState
  fragExec fragBlockPath vyperEvent vyperABI contractABI venomState list pair words arithmetic

Theorem compile_saved_log_topics_source_state:
  !ctx func tenv flags args values fts atvs cs ops cs' ss dst byte_count cenv cx es.
    LENGTH flags = LENGTH args /\ LIST_REL event_arg_compatible fts (MAP SND args) /\
    LIST_REL (\flag ty. flag ==> event_indexable_type ty) flags fts /\
    LIST_REL (\arg tv. evaluate_type tenv (SND arg) = SOME tv) args atvs /\
    log_args_rel args atvs values ss /\ log_args_safe args atvs ss dst byte_count /\
    state_rel cenv cx es ss /\ local_ptrs_rel func cenv es.scopes ss /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before cs.cs_next_var (Var p)) /\
    compile_log_topic_ops (FST (split_log_ops args flags)) cs = (ops,cs') /\
    EVERY (\arg. abi_operand_before cs.cs_next_var (FST arg)) args /\ fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    ?out topics. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      eval_operands ops out = SOME topics /\ encode_indexed_event_topics flags fts values = SOME topics /\
      EVERY (abi_operand_before cs'.cs_next_var) ops /\ cs.cs_next_var <= cs'.cs_next_var /\
      copy_state_frame ss out /\ out.vs_memory = ss.vs_memory /\ allocation_growth ss out /\
      state_rel cenv cx es out /\ local_ptrs_rel func cenv es.scopes out /\
      (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
        FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before cs'.cs_next_var (Var p)) /\
      log_args_rel args atvs values out /\ log_args_safe args atvs out dst byte_count /\
      EVERY (\arg. abi_operand_before cs'.cs_next_var (FST arg)) args /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`ctx`, `func`, `tenv`, `flags`, `args`, `values`, `fts`, `atvs`, `cs`, `ops`, `cs'`, `ss`, `dst`, `byte_count`]
    mp_tac compile_saved_log_topics_path >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` (qx_choose_then `topics` strip_assume_tac)) >>
  drule copy_state_frame_external >> DISCH_TAC >> drule allocation_growth_copy_frame >> DISCH_TAC >>
  qspecl_then [`func`, `cenv`, `cx`, `es`, `ss`, `out`, `cs.cs_next_var`] mp_tac source_relations_memory_frame >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qspecl_then [`cenv`, `es.scopes`, `cs.cs_next_var`, `cs'.cs_next_var`] mp_tac source_pointer_lifetimes_mono >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qexistsl_tac [`out`, `topics`] >> asm_simp_tac bool_ss [] >> first_assum MATCH_ACCEPT_TAC
QED

Theorem checked_compile_native_log_stmt_topics_state:
  !tops dep layouts addr art ctx func cenv cx es lctx ty event_id exprs cs cs'
    sig_hash fts flags args eval_cut raw_topics data_ops topic_ops topic_cut
    data_types data_capacity data_buf store_cut packed_cut abi_buf encode_cut capacity ftvs atvs values avs ss.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\ cenv.ce_struct_fields = make_struct_fields_map tops /\
    cenv.ce_event_info (nsid_to_string event_id) = SOME (sig_hash,fts,flags) /\
    compile_log_eval_all cenv exprs cs = (args,eval_cut) /\ split_log_ops args flags = (raw_topics,data_ops) /\ ~NULL data_ops /\
    compile_log_topic_ops raw_topics eval_cut = (topic_ops,topic_cut) /\ data_types = log_non_indexed_types flags fts /\
    data_capacity = MAX 32 (SUM (MAP (type_memory_bytes cenv) data_types)) /\
    compile_alloc_buffer data_capacity topic_cut = (data_buf,store_cut) /\
    compile_log_store_data cenv data_ops data_types data_buf.buf_operand 0 store_cut = ((),packed_cut) /\
    capacity = MAX 32 (abi_size_bound cenv.ce_struct_fields (TupleT data_types)) /\
    compile_alloc_buffer capacity packed_cut = (abi_buf,encode_cut) /\ compile_stmt cenv lctx ty (Log event_id exprs) cs = ((),cs') /\
    fn_has_code eval_cut topic_cut func /\ fn_has_code topic_cut store_cut func /\ fn_has_code store_cut packed_cut func /\
    fn_has_code packed_cut encode_cut func /\ fn_has_code encode_cut cs' func /\
    fn_inst_ids_distinct func /\ compiler_id_history packed_cut /\
    LENGTH flags = LENGTH args /\ LIST_REL event_arg_compatible fts (MAP SND args) /\
    LIST_REL (\flag fty. flag ==> event_indexable_type fty) flags fts /\
    LIST_REL (\fty tv. evaluate_type (type_env tops) fty = SOME tv) fts ftvs /\
    LIST_REL (\arg tv. evaluate_type (type_env tops) (SND arg) = SOME tv) args atvs /\
    state_well_typed es /\ state_rel cenv cx es ss /\ local_ptrs_rel func cenv es.scopes ss /\
    vyper_to_abi_list (type_env tops) data_types (select_log_args F flags values) = SOME avs /\
    source_alloca_floor cenv es.scopes (topic_cut.cs_next_id::packed_cut.cs_next_id::compiler_alloca_ids encode_cut cs') ss /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before eval_cut.cs_next_var (Var p)) /\
    ss.vs_current_bb = eval_cut.cs_current_bb /\ ss.vs_inst_idx = LENGTH eval_cut.cs_current_insts /\ ~ss.vs_halted /\
    log_args_rel args atvs values ss /\
    log_args_safe args atvs ss (w2n (memory_snapshot_addr topic_cut.cs_next_id ss))
      (type_memory_size (TupleTV (select_log_args F flags ftvs))) /\
    EVERY (\arg. abi_operand_before eval_cut.cs_next_var (FST arg)) args /\
    LENGTH (Lit (n2w sig_hash)::topic_ops) < dimword(:256) /\ alloca_inv ss /\
    abi_alloca_request_ok topic_cut.cs_next_id data_capacity ss /\ abi_alloca_request_ok packed_cut.cs_next_id capacity ss /\
    abi_alloca_budget 32 (compiler_alloca_ids encode_cut cs') ss + data_capacity + capacity < dimword(:256) /\
    (!id. MEM id (compiler_alloca_ids encode_cut cs') ==> abi_alloca_request_ok id 32 ss) /\
    LENGTH (enc (Tuple (MAP (vyper_to_abi_type (type_env tops)) data_types)) (ListV avs)) <= capacity ==>
    ?out topics. encode_indexed_event_topics flags fts values = SOME topics /\
      encode_vyper_event_metadata (type_env tops) (w2w ss.vs_call_ctx.cc_address) (sig_hash,fts,flags) values =
        SOME <|logger := w2w ss.vs_call_ctx.cc_address; topics := n2w sig_hash::topics;
          data := enc (Tuple (MAP (vyper_to_abi_type (type_env tops)) data_types)) (ListV avs)|> /\
      fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      out.vs_logs = ss.vs_logs ++ [<|logger := w2w ss.vs_call_ctx.cc_address; topics := n2w sig_hash::topics;
        data := enc (Tuple (MAP (vyper_to_abi_type (type_env tops)) data_types)) (ListV avs)|>] /\
      state_rel cenv cx (es with logs := es.logs ++ [<|logger := w2w ss.vs_call_ctx.cc_address; topics := n2w sig_hash::topics;
        data := enc (Tuple (MAP (vyper_to_abi_type (type_env tops)) data_types)) (ListV avs)|>]) out /\
      local_ptrs_rel func cenv es.scopes out /\ allocation_growth ss out /\
      read_memory (w2n (memory_snapshot_addr packed_cut.cs_next_id
        (memory_snapshot_allocated topic_cut.cs_next_id topic_cut.cs_next_var data_capacity ss)))
        (LENGTH (enc (Tuple (MAP (vyper_to_abi_type (type_env tops)) data_types)) (ListV avs))) out =
        enc (Tuple (MAP (vyper_to_abi_type (type_env tops)) data_types)) (ListV avs) /\
      (!arg_op. abi_operand_before eval_cut.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      abi_state_frame ss (out with vs_logs := ss.vs_logs)
Proof
  rpt gen_tac >> strip_tac >>
  `compile_log_topic_ops (FST (split_log_ops args flags)) eval_cut = (topic_ops,topic_cut)` by asm_simp_tac bool_ss [FST] >>
  qspecl_then [`ctx`, `func`, `type_env tops`, `flags`, `args`, `values`, `fts`, `atvs`, `eval_cut`, `topic_ops`, `topic_cut`, `ss`,
    `w2n (memory_snapshot_addr topic_cut.cs_next_id ss)`, `type_memory_size (TupleTV (select_log_args F flags ftvs))`, `cenv`, `cx`, `es`]
    mp_tac compile_saved_log_topics_source_state >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `middle` (qx_choose_then `topics` strip_assume_tac)) >>
  drule_all abi_log_packing_allocator_frame >> strip_tac >> drule copy_state_frame_allocator >> strip_tac >>
  qspecl_then [`ss`, `middle`, `32`, `compiler_alloca_ids encode_cut cs'`] mp_tac abi_alloca_budget_fields >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qspecl_then [`cenv`, `es.scopes`, `topic_cut.cs_next_id::packed_cut.cs_next_id::compiler_alloca_ids encode_cut cs'`, `ss`, `middle`]
    mp_tac source_alloca_floor_growth >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qspecl_then [`topic_cut.cs_next_var`, `topic_ops`, `middle`, `topics`, `sig_hash`] mp_tac log_topic_header >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  `abi_alloca_budget 32 (compiler_alloca_ids encode_cut cs') middle + data_capacity + capacity < dimword(:256)` by
    (qpat_x_assum `abi_alloca_budget _ _ ss + _ + _ < _` mp_tac >> asm_simp_tac bool_ss []) >>
  qspecl_then [`tops`, `dep`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `cx`, `es`, `lctx`, `ty`, `event_id`, `exprs`, `cs`, `cs'`,
    `sig_hash`, `fts`, `flags`, `args`, `eval_cut`, `raw_topics`, `data_ops`, `topic_ops`, `topic_cut`, `data_types`, `data_capacity`,
    `data_buf`, `store_cut`, `packed_cut`, `abi_buf`, `encode_cut`, `capacity`, `ftvs`, `atvs`, `values`, `avs`, `n2w sig_hash::topics`, `middle`]
    mp_tac checked_compile_native_log_stmt_data_state >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, asm_simp_tac bool_ss [] >> first_assum MATCH_ACCEPT_TAC]) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  `vyper_to_abi_list (type_env tops) (log_non_indexed_types flags fts) (select_log_args F flags values) = SOME avs` by
    (qpat_x_assum `vyper_to_abi_list _ data_types _ = _` mp_tac >>
     qpat_x_assum `data_types = _` (fn th => PURE_REWRITE_TAC [th]) >> simp[]) >>
  qspecl_then [`type_env tops`, `flags`, `fts`, `values`, `avs`, `w2w ss.vs_call_ctx.cc_address`, `sig_hash`, `topics`]
    mp_tac event_metadata_encoding >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  drule copy_state_frame_external >> DISCH_TAC >>
  qspecl_then [`ss`, `middle`] mp_tac abi_state_frame_observables >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
  qpat_x_assum `state_rel cenv cx (es with logs := _) out` mp_tac >> asm_simp_tac bool_ss [] >> DISCH_TAC >>
  `fragment_path ctx func ss out` by (irule fragment_path_trans >> qexists_tac `middle` >> simp[]) >>
  `allocation_growth ss out` by (irule allocation_growth_trans >> qexists_tac `middle` >> simp[]) >>
  `!arg_op. abi_operand_before eval_cut.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss` by
    (qspecl_then [`eval_cut.cs_next_var`, `topic_cut.cs_next_var`, `ss`, `middle`, `out`]
       mp_tac abi_operand_before_frame_trans >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  `abi_state_frame ss (out with vs_logs := ss.vs_logs)` by
    (qspecl_then [`ss`, `middle`, `out`] mp_tac abi_log_allocation_state_frame >> simp[]) >>
  drule_all copy_frame_allocation_address >> DISCH_TAC >>
  qexistsl_tac [`out`, `topics`] >> asm_simp_tac bool_ss [] >>
  qpat_x_assum `read_memory _ _ out = _` mp_tac >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual recursive Log topics and source state: " ^ name)
  end) (DB.thms "abiNativeLogTopicsState")
