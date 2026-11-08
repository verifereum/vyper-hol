(* Public API redesign: START OF PACKING, with evaluated saved arguments
   and topics. Canonical #551 scratch/output resources replace the old actual
   ALLOCA ledger. The conclusion is a continuation simulation, NOT the retired
   native fragment_path/exact-allocation endpoint. Encoding and packing are
   proved by logDataPacking; source events are the interpreter's real events. *)
Theory checkedLogData
Ancestors
  checkedLogMetadata checkedLogDataEncoding logDataPacking logSourceFrame
  eventLogSourceLookup eventLogSplitProps e2eDefs abiLogSourceEncoding abiLogStmtCode
  sourceAbiTypingLists sourceLogFrames sourceMemoryFrames sourceValueFrames
  typedCopyProducer abiTypeShape abiLogPackingReady abiBufferAllocationPath abiBufferAllocationCode
  typedCopyStateFrame typedLogStoreCode abiFieldOperands abiStaticLoopCode allocationGrowth abiStateFrame
  memoryValueSnapshot memoryValueDefs valueEncoding compileVyper compileEnv
  stmtLowering vyperTypeContract vyperTypeSystem vyperTypeInvariants
  vyperContext vyperEvent vyperState vyperABI contractABI fragExec fragBlockPath
  venomState venomMemDefs list pair words arithmetic

Theorem log_packing_resources_shrink:
  log_packing_resources cut start endcs capacity lo top tv src capacity ss /\
  n <= capacity ==>
  log_packing_resources cut start endcs capacity lo top tv src n ss
Proof
  simp[log_packing_resources_def, venomMemDefsTheory.regions_disjoint_def] >>
  rpt strip_tac >> decide_tac
QED

Theorem checked_event_metadata_encoding:
  encode_indexed_event_topics flags tys values = SOME topics /\
  vyper_to_abi_list tenv (log_non_indexed_types flags tys)
    (select_log_args F flags values) = SOME avs ==>
  encode_vyper_event_metadata tenv logger (sig_hash,tys,flags) values =
    SOME <|logger := logger; topics := n2w sig_hash::topics;
      data := enc (Tuple (MAP (vyper_to_abi_type tenv)
        (log_non_indexed_types flags tys))) (ListV avs)|>
Proof
  strip_tac >>
  `LENGTH flags = LENGTH tys /\ LENGTH flags = LENGTH values` by
    fs[encode_indexed_event_topics_characterization] >>
  drule_all non_indexed_event_args_exists >> strip_tac >>
  asm_simp_tac (srw_ss()) [encode_vyper_event_metadata_def,
    log_non_indexed_values_select, source_abi_types_map]
QED

(* Frame the actual packed state and the actual following output ALLOCA.
   Source geometry is transported, not a premise about encoder execution. *)
Theorem log_packed_source_regions:
  copy_state_frame ss packed /\
  (!op. abi_operand_before cs.cs_next_var op ==>
    eval_operand op packed = eval_operand op ss) /\
  cs.cs_next_var <= cut.cs_next_var /\ cut.cs_next_var < start.cs_next_var /\
  log_source_regions cs lo outs cenv scopes ss ==>
  log_source_regions start lo outs cenv scopes
    (memory_snapshot_allocated cut.cs_next_id cut.cs_next_var capacity packed)
Proof
  strip_tac >>
  `!name entry p sz. lookup_scopes name scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    abi_operand_before cs.cs_next_var (Var p)` by
    (fs[log_source_regions_def, abi_operand_before_def, not_fresh_at_def,
      compiler_var_name_def] >> metis_tac[]) >>
  `!name entry p sz. lookup_scopes name scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p (memory_snapshot_allocated cut.cs_next_id cut.cs_next_var capacity packed) = lookup_var p ss` by
    (rpt strip_tac >>
     `abi_operand_before cut.cs_next_var (Var p)` by
       (irule abi_operand_before_mono >> qexists_tac `cs.cs_next_var` >> simp[] >>
        first_x_assum irule >> goal_assum (drule_at Any) >> simp[]) >>
     drule buffer_allocation_old_operand >>
     simp[eval_operand_def] >> metis_tac[eval_operand_def]) >>
  drule copy_state_frame_allocator >> strip_tac >>
  irule log_source_regions_transport >> qexistsl_tac [`ss`,`cs`] >>
  simp[] >> first_assum MATCH_ACCEPT_TAC
QED

Theorem checked_compile_saved_log_data:
  check_contract dep layouts addr [(NONE,tops)] = SOME art /\
  env.event_fields = art.cta_event_fields /\ env.type_defs = type_env tops /\
  cenv.ce_struct_fields = make_struct_fields_map tops /\
  cenv.ce_event_info = build_event_info (type_env tops) tops (K NONE) /\
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  type_stmt env ret (Log event_id exprs) = SOME env' /\
  cenv.ce_event_info (nsid_to_string event_id) = SOME (sig_hash,fts,flags) /\
  compile_log_eval_all cenv exprs initial = (args,eval_cut) /\
  compile_log_store_data cenv (SND (split_log_ops args flags))
    (log_non_indexed_types flags fts) src 0 cs = ((),packed_cut) /\
  compile_alloc_buffer capacity packed_cut = (buf,encoder_start) /\
  compile_abi_encode_to_buf buf.buf_operand src ei encoder_start = (size_op,encoder_end) /\
  compile_log_abi_emit buf.buf_operand src ei (Lit (n2w sig_hash)::ops) encoder_start = ((),final) /\
  abi_enc_plan (type_env tops) (TupleT (log_non_indexed_types flags fts)) ei /\
  capacity = MAX 32 (abi_size_bound cenv.ce_struct_fields
    (TupleT (log_non_indexed_types flags fts))) /\
  LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) fts ftvs /\
  LIST_REL (\arg tv. evaluate_type (type_env tops) (SND arg) = SOME tv) args atvs /\
  values_have_types ftvs values /\ env_consistent env cx es /\ state_well_typed es /\
  state_rel_simple cenv cx es ss /\ local_ptrs_rel func cenv es.scopes ss /\
  fn_has_code cs packed_cut func /\ fn_has_code packed_cut encoder_start func /\
  fn_has_code packed_cut final func /\
  source_memory_separated cenv es.scopes ss (w2n root_addr)
    (type_memory_size (TupleTV (select_log_args F flags ftvs))) /\
  (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    abi_operand_before cs.cs_next_var (Var p)) /\
  log_args_rel args atvs values ss /\
  log_args_safe args atvs ss (w2n root_addr)
    (type_memory_size (TupleTV (select_log_args F flags ftvs))) /\
  log_args_avoid args (compiler_var_names cs.cs_next_var (packed_cut.cs_next_var - cs.cs_next_var)) /\
  w2n root_addr + type_memory_size (TupleTV (select_log_args F flags ftvs)) < dimword(:256) /\
  EVERY (log_abi_old_operand cs) (src::Lit (n2w sig_hash)::ops) /\
  eval_operand src ss = SOME root_addr /\ eval_operands ops ss = SOME topics /\
  encode_indexed_event_topics flags fts values = SOME topics /\
  LENGTH (Lit (n2w sig_hash)::ops) < dimword(:256) /\
  log_packing_resources packed_cut encoder_start encoder_end capacity lo top
    (TupleTV (select_log_args F flags ftvs)) (w2n root_addr) capacity ss /\
  log_source_regions cs lo [(w2n (memory_snapshot_addr packed_cut.cs_next_id ss),capacity)]
    cenv es.scopes ss /\
  ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted/\
  ~ss.vs_call_ctx.cc_static ==>
  ?out ev.
    encode_source_event (get_tenv cx) cx.sources cx.txn.target event_id values = SOME ev /\
    out.vs_logs = ss.vs_logs ++ [ev] /\
    frag_exec ctx cs final (\s. s = ss) (\s. s.vs_logs = ss.vs_logs ++ [ev]) (\r. F) /\
    state_rel_simple cenv cx (es with logs := es.logs ++ [ev]) out /\
    local_ptrs_rel func cenv es.scopes out /\
    out.vs_current_bb = final.cs_current_bb /\
    out.vs_inst_idx = LENGTH final.cs_current_insts /\ ~out.vs_halted /\
    (!fuel r. run_from fuel ctx func out = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx func ss = r)
Proof
  rpt strip_tac >>
  drule checked_contract_struct_args_unique >> strip_tac >>
  `abi_struct_env_rel env.type_defs cenv.ce_struct_fields` by
    fs[abi_struct_env_rel_tops] >>
  drule_all checked_log_compiler_metadata >> strip_tac >>
  `LENGTH flags = LENGTH fts` by (imp_res_tac LIST_REL_LENGTH >> fs[]) >>
  `abi_struct_env_rel (type_env tops) cenv.ce_struct_fields` by metis_tac[] >>
  drule_all checked_log_data_encoding_bound >>
  disch_then (qx_choose_then `avs` strip_assume_tac) >>
  qabbrev_tac `bytes = enc (Tuple (MAP (vyper_to_abi_type (type_env tops))
    (log_non_indexed_types flags fts))) (ListV avs)` >>
  `LENGTH bytes <= capacity` by
    (qpat_x_assum `LENGTH bytes <= _` mp_tac >> simp[]) >>
  `vyper_to_abi (type_env tops) (TupleT (log_non_indexed_types flags fts))
    (ArrayV (TupleV (select_log_args F flags values))) = SOME (ListV avs)` by
    simp[Once vyper_to_abi_def] >>
  `eval_operands (Lit (n2w sig_hash)::ops) ss = SOME (n2w sig_hash::topics)` by
    simp[eval_operands_def, eval_operand_def] >>
  `log_packing_resources packed_cut encoder_start encoder_end capacity lo top
    (TupleTV (select_log_args F flags ftvs)) (w2n root_addr) (LENGTH bytes) ss` by
    (drule_all log_packing_resources_shrink >> simp[]) >>
  `log_packing_resources packed_cut encoder_start encoder_end capacity lo top
    (TupleTV (select_log_args F flags ftvs)) (w2n root_addr)
    (LENGTH (enc (vyper_to_abi_type (type_env tops)
      (TupleT (log_non_indexed_types flags fts))) (ListV avs))) ss` by
    (qpat_x_assum `log_packing_resources _ _ _ _ _ _ _ _ (LENGTH bytes) _` mp_tac >>
     simp[Abbr`bytes`, Once vyper_to_abi_type_def, source_abi_types_map]) >>
  suspend "packing"
QED

Resume checked_compile_saved_log_data[packing]:
  drule_all checked_log_packing_canonical >>
  disch_then (qspec_then `ctx` (qx_choose_then `packed` strip_assume_tac)) >>
  drule_all log_packing_path_frag >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  `log_data_result packed_cut encoder_start encoder_end capacity lo top
    bytes (n2w sig_hash::topics) packed out` by
    (qpat_x_assum `log_data_result _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Abbr`bytes`, Once vyper_to_abi_type_def, source_abi_types_map]) >>
  qabbrev_tac `allocated = memory_snapshot_allocated packed_cut.cs_next_id packed_cut.cs_next_var capacity packed` >>
  drule compile_log_store_data_next_var >> strip_tac >>
  `state_rel_simple cenv cx es allocated /\ local_ptrs_rel func cenv es.scopes allocated` by
    (simp[Abbr`allocated`] >>
     irule (Q.INST [`st` |-> `packed_cut`] log_buffer_source_relations) >> simp[] >>
     rpt strip_tac >> irule abi_operand_before_mono >>
     qexists_tac `cs.cs_next_var` >> simp[] >>
     first_x_assum irule >> goal_assum (drule_at Any) >> simp[]) >>
  drule compile_alloc_buffer_code >> strip_tac >>
  `log_source_regions encoder_start lo
    [(w2n (memory_snapshot_addr packed_cut.cs_next_id ss),capacity)] cenv es.scopes allocated` by
    (simp[Abbr`allocated`] >>
     irule log_packed_source_regions >> simp[] >> qexistsl_tac [`cs`,`ss`] >>
     simp[] >> qpat_x_assum `log_source_regions cs _ _ _ _ _` mp_tac >> simp[]) >>
  `memory_snapshot_addr packed_cut.cs_next_id packed = memory_snapshot_addr packed_cut.cs_next_id ss` by
    (drule abi_log_packing_allocator_frame >> simp[]) >>
  `log_source_regions encoder_start lo
    [(w2n (memory_snapshot_addr packed_cut.cs_next_id packed),LENGTH bytes)] cenv es.scopes allocated` by
    (irule log_source_regions_shrink >> qexists_tac `capacity` >>
     simp[] >> qpat_x_assum `log_source_regions encoder_start _ _ _ _ _` mp_tac >> simp[]) >>
  suspend "source_result"
QED

Resume checked_compile_saved_log_data[source_result]:
  `env.type_defs = get_tenv cx /\ ss.vs_call_ctx.cc_address = cx.txn.target` by
    (qspecl_then [`env`,`cenv`,`cx`,`es`,`ss`] mp_tac source_log_context >>
     impl_tac >- (conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  drule_all checked_log_metadata_source_encoding >>
  disch_then (qspec_then `values` assume_tac) >>
  drule_all checked_event_metadata_encoding >>
  disch_then (qspecl_then [`sig_hash`,`cx.txn.target`] assume_tac) >>
  qabbrev_tac `ev = <|logger := w2w ss.vs_call_ctx.cc_address;
    topics := n2w sig_hash::topics; data := bytes|>` >>
  `encode_source_event (get_tenv cx) cx.sources cx.txn.target event_id values = SOME ev` by
    fs[Abbr`ev`, Abbr`bytes`] >>
  `out.vs_logs = ss.vs_logs ++ [ev]` by
    (drule_all log_data_result_logs >> simp[Abbr`ev`, Abbr`bytes`]) >>
  `abi_state_frame packed allocated` by
    simp[Abbr`allocated`, buffer_allocation_context] >>
  `allocated.vs_logs = packed.vs_logs /\
   allocated.vs_tx_ctx = packed.vs_tx_ctx /\
   allocated.vs_block_ctx = packed.vs_block_ctx /\
   allocated.vs_immutables = packed.vs_immutables /\
   allocated.vs_outcomes = packed.vs_outcomes` by
    (qpat_x_assum `abi_state_frame packed allocated` mp_tac >>
     simp_tac (srw_ss()) [abi_state_frame_def, abi_state_context_def,
       venom_state_component_equality] >> strip_tac >> simp[]) >>
  `state_rel_simple cenv cx (es with logs := es.logs ++ [ev]) out /\
   local_ptrs_rel func cenv es.scopes out` by
    (irule log_public_source_relations >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     qexistsl_tac [`allocated`,`lo`,
       `[(w2n (memory_snapshot_addr packed_cut.cs_next_id packed),LENGTH bytes)]`,`encoder_start`] >>
     rpt conj_tac >> TRY (first_assum MATCH_ACCEPT_TAC) >>
     qpat_x_assum `log_data_result _ _ _ _ _ _ bytes _ _ _` mp_tac >>
     simp[log_data_result_def, Abbr`allocated`]) >>
  `frag_exec ctx cs final (\s. s = ss) (\s. s.vs_logs = ss.vs_logs ++ [ev]) (\r. F)` by
    (drule_all checked_log_data_frag >> disch_then (qspec_then `ctx` assume_tac) >>
     irule frag_exec_conseq >> goal_assum (drule_at Any) >> simp[] >>
     rpt strip_tac >> drule_all log_data_result_logs >>
     simp[Abbr`ev`, Abbr`bytes`, Once vyper_to_abi_type_def, source_abi_types_map]) >>
  qexistsl_tac [`out`,`ev`] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Finalise checked_compile_saved_log_data
