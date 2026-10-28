(* TOP-LEVEL: checked compatible data packing, the actual output allocation,
   arbitrary recursive encoding and LOG preserve the complete source state.
   The packed runtime state is produced by execution.
   Helper: saved operands retain their values and precede the next cut. *)
Theory abiNativeLogPackedState
Ancestors
  abiNativeLogAllocatedState abiLogPackingState abiLogPackingReady abiLogTopicsReady abiLogAllocationFrame abiLogReady
  abiMemoryTypedMetadata abiTypeShape typedCopyStateFrame typedLogArgs typedCopyContract typedSArrayDynInvariant typedCopyProducer
  sourceAllocationPrivacy sourceMemoryFrames allocationGrowth
  abiAllocationBudget abiAllocationTrace abiAllocationFrame abiAllocatedWindows abiAllocatorState
  abiStateFrame abiFieldOperands abiFlatRun memoryValueDefs valueEncoding
  compileAllocaProvenance compileIdFlow stmtLowering compileEnv compileVyper
  vyperTypeContract vyperContext vyperTypeSystem vyperTypeInvariants vyperState
  fragExec fragBlockPath vyperABI vyperValue vyperTyping contractABI venomState venomMemDefs list words arithmetic

Theorem saved_log_operand_context:
  !bound next_var before after buf root_addr topic_ops topics.
    bound <= next_var /\ abi_operand_before bound buf /\ EVERY (abi_operand_before bound) topic_ops /\
    eval_operand buf before = SOME root_addr /\ eval_operands topic_ops before = SOME topics /\
    (!arg. abi_operand_before bound arg ==> eval_operand arg after = eval_operand arg before) ==>
    abi_operand_before next_var buf /\ EVERY (abi_operand_before next_var) topic_ops /\
    eval_operand buf after = SOME root_addr /\ eval_operands topic_ops after = SOME topics
Proof
  rpt gen_tac >> strip_tac >>
  `abi_operand_before next_var buf` by (irule abi_operand_before_mono >> qexists_tac `bound` >> simp[]) >>
  `EVERY (abi_operand_before next_var) topic_ops` by
    (simp_tac bool_ss [EVERY_MEM] >> rpt strip_tac >>
     irule abi_operand_before_mono >> qexists_tac `bound` >> fs[EVERY_MEM]) >>
  `eval_operand buf after = SOME root_addr` by
    (qpat_x_assum `!arg. abi_operand_before bound arg ==> _` (qspec_then `buf` mp_tac) >> simp[]) >>
  `eval_operands topic_ops after = SOME topics` by
    (qspecl_then [`topic_ops`, `bound`, `before`, `after`] mp_tac eval_operands_before_frame >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem checked_compile_native_packed_log_state:
  !tops dep layouts addr art ctx func cenv cx es flags fts args ftvs atvs values buf cs ret packed_cut
    capacity abi_buf encode_cut cs' avs topic_ops topics ss root_addr source_id.
    check_contract dep layouts addr [(NONE,tops)] = SOME art /\ cenv.ce_struct_fields = make_struct_fields_map tops /\
    LENGTH flags = LENGTH args /\ LIST_REL event_arg_compatible fts (MAP SND args) /\
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) fts ftvs /\
    LIST_REL (\arg tv. evaluate_type (type_env tops) (SND arg) = SOME tv) args atvs /\
    compile_log_store_data cenv (SND (split_log_ops args flags)) (log_non_indexed_types flags fts) buf 0 cs = (ret,packed_cut) /\
    compile_alloc_buffer capacity packed_cut = (abi_buf,encode_cut) /\
    compile_log_abi_emit abi_buf.buf_operand buf
      (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT (log_non_indexed_types flags fts))) topic_ops encode_cut = ((),cs') /\
    fn_has_code cs packed_cut func /\ fn_has_code packed_cut encode_cut func /\ fn_has_code encode_cut cs' func /\
    fn_inst_ids_distinct func /\ compiler_id_history packed_cut /\
    state_well_typed es /\ state_rel cenv cx es ss /\ local_ptrs_rel func cenv es.scopes ss /\
    vyper_to_abi_list (type_env tops) (log_non_indexed_types flags fts) (select_log_args F flags values) = SOME avs /\
    source_memory_separated cenv es.scopes ss (w2n root_addr) (type_memory_size (TupleTV (select_log_args F flags ftvs))) /\
    source_alloca_floor cenv es.scopes (packed_cut.cs_next_id::compiler_alloca_ids encode_cut cs') ss /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before cs.cs_next_var (Var p)) /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    log_args_rel args atvs values ss /\
    log_args_safe args atvs ss (w2n root_addr) (type_memory_size (TupleTV (select_log_args F flags ftvs))) /\
    log_args_avoid args (compiler_var_names cs.cs_next_var (packed_cut.cs_next_var - cs.cs_next_var)) /\
    abi_operand_before cs.cs_next_var buf /\ EVERY (abi_operand_before cs.cs_next_var) topic_ops /\
    eval_operand buf ss = SOME root_addr /\ eval_operands topic_ops ss = SOME topics /\ LENGTH topic_ops < dimword(:256) /\
    abi_allocated_window ss source_id (w2n root_addr) (type_memory_size_list (select_log_args F flags ftvs)) /\
    source_id <> packed_cut.cs_next_id /\ ~MEM source_id (compiler_alloca_ids encode_cut cs') /\
    ~MEM packed_cut.cs_next_id (compiler_alloca_ids encode_cut cs') /\
    32 <= capacity /\ alloca_inv ss /\ abi_alloca_request_ok packed_cut.cs_next_id capacity ss /\
    abi_alloca_budget 32 (compiler_alloca_ids encode_cut cs') ss + capacity < dimword (:256) /\
    (!id. MEM id (compiler_alloca_ids encode_cut cs') ==> abi_alloca_request_ok id 32 ss) /\
    LENGTH (enc (Tuple (MAP (vyper_to_abi_type (type_env tops)) (log_non_indexed_types flags fts))) (ListV avs)) <= capacity ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      out.vs_logs = ss.vs_logs ++ [<|logger := w2w ss.vs_call_ctx.cc_address; topics := topics;
        data := enc (Tuple (MAP (vyper_to_abi_type (type_env tops)) (log_non_indexed_types flags fts))) (ListV avs)|>] /\
      state_rel cenv cx (es with logs := es.logs ++ [<|logger := w2w ss.vs_call_ctx.cc_address; topics := topics;
        data := enc (Tuple (MAP (vyper_to_abi_type (type_env tops)) (log_non_indexed_types flags fts))) (ListV avs)|>]) out /\
      local_ptrs_rel func cenv es.scopes out /\ allocation_growth ss out /\
      read_memory (w2n (memory_snapshot_addr packed_cut.cs_next_id ss))
        (LENGTH (enc (Tuple (MAP (vyper_to_abi_type (type_env tops)) (log_non_indexed_types flags fts))) (ListV avs))) out =
        enc (Tuple (MAP (vyper_to_abi_type (type_env tops)) (log_non_indexed_types flags fts))) (ListV avs) /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      abi_state_frame ss (out with vs_logs := ss.vs_logs)
Proof
  rpt gen_tac >> strip_tac >>
  `ss.vs_alloca_next < dimword (:256)` by
    (qspecl_then [`32`, `compiler_alloca_ids encode_cut cs'`, `ss`] mp_tac abi_alloca_budget_frontier >> decide_tac) >>
  `w2n root_addr + type_memory_size (TupleTV (select_log_args F flags ftvs)) < dimword (:256)` by
    (qspecl_then [`ss`, `source_id`, `w2n root_addr`, `type_memory_size_list (select_log_args F flags ftvs)`]
       mp_tac abi_allocated_window_frontier >> impl_tac >- fs[alloca_inv_def] >> simp_tac bool_ss [type_memory_size_def] >> decide_tac) >>
  qspecl_then [`tops`, `dep`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `cx`, `es`, `flags`, `fts`, `args`, `ftvs`, `atvs`,
    `values`, `buf`, `cs`, `ret`, `packed_cut`, `capacity`, `abi_buf`, `encode_cut`, `ss`, `root_addr`]
    mp_tac checked_log_packing_source_state >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `packed` strip_assume_tac) >> drule_all abi_log_packing_allocator_frame >> strip_tac >>
  `abi_alloca_budget 32 (compiler_alloca_ids encode_cut cs') packed = abi_alloca_budget 32 (compiler_alloca_ids encode_cut cs') ss` by
    (irule abi_alloca_budget_allocator_state >> fs[copy_state_frame_def, abi_allocator_state_eq]) >>
  qspecl_then [`cenv`, `es.scopes`, `packed_cut.cs_next_id::compiler_alloca_ids encode_cut cs'`, `ss`, `packed`]
    mp_tac source_alloca_floor_growth >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qspecl_then [`cs.cs_next_var`, `packed_cut.cs_next_var`, `ss`, `packed`, `buf`, `root_addr`, `topic_ops`, `topics`]
    mp_tac saved_log_operand_context >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qspecl_then [`cenv`, `es.scopes`, `cs.cs_next_var`, `packed_cut.cs_next_var`] mp_tac source_pointer_lifetimes_mono >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  drule_all log_non_indexed_evaluate_types >> DISCH_TAC >> drule checked_contract_struct_args_unique >> DISCH_TAC >>
  `abi_memory_env_rel (type_env tops) cenv` by (irule abi_memory_env_rel_tops >> simp[]) >>
  `abi_struct_env_rel (type_env tops) cenv.ce_struct_fields` by (drule abi_struct_env_rel_tops >> simp[]) >>
  qspecl_then [`type_env tops`, `cenv.ce_struct_fields`, `cenv`, `log_non_indexed_types flags fts`, `select_log_args F flags ftvs`,
    `select_log_args F flags values`, `avs`, `ctx`, `func`, `cx`, `es`, `capacity`, `packed_cut`, `abi_buf`, `encode_cut`, `cs'`,
    `buf`, `topic_ops`, `topics`, `packed`, `root_addr`, `type_memory_size_list (select_log_args F flags ftvs)`, `source_id`]
    mp_tac compile_abi_native_allocated_log_state >> impl_tac >- (fs[] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >> drule copy_state_frame_external >> DISCH_TAC >>
  qspecl_then [`ss`, `packed`] mp_tac abi_state_frame_observables >> impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum `state_rel cenv cx (es with logs := _) out` mp_tac >> asm_simp_tac bool_ss [] >> DISCH_TAC >>
  `fragment_path ctx func ss out` by (irule fragment_path_trans >> qexists_tac `packed` >> simp[]) >>
  `allocation_growth ss out` by (irule allocation_growth_trans >> qexists_tac `packed` >> simp[]) >>
  `!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss` by
    (qspecl_then [`cs.cs_next_var`, `packed_cut.cs_next_var`, `ss`, `packed`, `out`]
       mp_tac abi_operand_before_frame_trans >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  `abi_state_frame ss (out with vs_logs := ss.vs_logs)` by
    (qspecl_then [`ss`, `packed`, `out`] mp_tac abi_log_allocation_state_frame >> simp[]) >>
  qexists_tac `out` >> asm_simp_tac bool_ss [] >>
  qpat_x_assum `read_memory _ _ out = _` mp_tac >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed checked packed recursive Log source state: " ^ name)
  end) (DB.thms "abiNativeLogPackedState")
