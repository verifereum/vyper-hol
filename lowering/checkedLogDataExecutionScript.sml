(* Full nonempty Log composition.  The prefix executes saved arguments,
   topics and the data ALLOCA; only the shared encoder uses continuation
   semantics.  Reservations at the packing cut are allocator metadata, not
   assumptions about execution of the packing prefix. *)
Theory checkedLogDataExecution
Ancestors
  vyperEventArgCompat
  checkedLogData checkedLogMetadata checkedLogValues logDataPacking logSourceFrame logAbiEncoder
  sourceLogFrames logArgumentLogSafety compileAllocationRequests compileAppendProps
  exprLowering context emitHelper emitHelperProps abiEncoderProps abiStaticLoopCode
  venomMemDefs
  eventLogTopicsPath eventLogSplitProps eventTopicCode abiLogTopicsReady
  abiLogDataAllocation abiLogStmtCode abiLogPackingReady
  logArgumentCodeExecution logArgumentListContract logArgumentCharges
  sourceAllocationPrivacy sourceMemoryFrames allocationGrowth typedLogArgs typedCopyStateFrame typedCopyProducer
  abiAllocationBudget abiAllocationFrame abiStateFrame abiFieldOperands abiFlatRun abiTypeShape
  abiBufferAllocationPath abiBufferAllocationCode abiAllocatorState
  memoryValueSnapshot memoryValueDefs valueEncoding compileAllocaProvenance compileIdFlow
  stmtLowering compileEnv compileVyper vyperTypeContract vyperContext vyperTypeSystem vyperTypeInvariants vyperState
  vyperTypeExprSoundness vyperTypeCallGraph vyperTypeCallStackSoundness
  fragExec fragBlockPath vyperEvent vyperABI contractABI venomState list pair words arithmetic
Libs pairLib

(* Minimal canonical replacement for the former native topic-state helper. *)
Theorem saved_log_topics_source_state:
  !ctx func tenv flags args values fts atvs cs ops cs' ss dst byte_count cenv cx es.
    LENGTH flags = LENGTH args /\ LIST_REL event_arg_compatible fts (MAP SND args) /\
    LIST_REL (\flag ty. flag ==> event_indexable_type ty) flags fts /\
    LIST_REL (\arg tv. evaluate_type tenv (SND arg) = SOME tv) args atvs /\
    log_args_rel args atvs values ss /\ log_args_safe args atvs ss dst byte_count /\
    state_rel_simple cenv cx es ss /\ local_ptrs_rel func cenv es.scopes ss /\
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
      state_rel_simple cenv cx es out /\ local_ptrs_rel func cenv es.scopes out /\
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

(* Topic lowering cannot introduce a label operand.  The non-hashing branch
   returns its input; the hashing branch returns an emitted SSA result. *)
Theorem log_topic_code_no_labels:
  !inputs cs ops cut.
    compile_log_topic_ops inputs cs = (ops,cut) /\
    EVERY (\arg. !l. FST arg <> Label l) inputs ==>
    EVERY (\op. !l. op <> Label l) ops
Proof
  Induct_on `inputs` >- simp[compile_log_topic_ops_def, comp_return_def] >>
  rpt gen_tac >> simp[Once compile_log_topic_ops_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_encode_log_topic (FST input) (SND input) cs = (op,mid)` >>
  `!l. op <> Label l` by
    (Cases_on `SND input` >>
     gvs[compile_encode_log_topic_def, comp_bind_def, comp_return_def,
       emit_op_def, fresh_id_def, fresh_var_def, emit_def, comp_ignore_bind_def]) >>
  simp[] >> first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED

Theorem log_split_topics_no_labels:
  !flags args.
    LENGTH flags = LENGTH args /\ EVERY (\arg. !l. FST arg <> Label l) args ==>
    EVERY (\arg. !l. FST arg <> Label l) (FST (split_log_ops args flags))
Proof
  Induct_on `flags`
  >- (Cases_on `args` >> simp[split_log_ops_def]) >>
  rpt gen_tac >> Cases_on `args` >> simp[] >> strip_tac >>
  rename1 `split_log_ops (arg::rest) (flag::flags)` >>
  PairCases_on `arg` >> Cases_on `flag` >>
  simp[split_log_ops_def, LET_THM] >> pairarg_tac >> gvs[] >>
  first_x_assum (qspec_then `rest` mp_tac) >> simp[]
QED

Theorem log_before_no_labels_old:
  abi_operand_before st.cs_next_var op /\ (!l. op <> Label l) ==>
  log_abi_old_operand st op
Proof
  Cases_on `op` >> simp[abi_operand_before_def, log_abi_old_operand_def,
    not_fresh_at_def, compiler_var_name_def]
QED

(* Allocator-only reservations survive topic evaluation and the virtual
   first buffer allocation, irrespective of the new SSA bindings/position. *)
Theorem log_virtual_allocation_copy_frame:
  copy_state_frame before after ==>
  copy_state_frame
    (memory_snapshot_allocated id var capacity before)
    (memory_snapshot_allocated id var capacity after)
Proof
  strip_tac >> fs[copy_state_frame_def, memory_snapshot_allocated_def,
    memory_snapshot_alloc_frame_def, memory_snapshot_addr_def, update_var_def,
    abi_state_frame_def, abi_state_context_def, venom_state_component_equality] >>
  IF_CASES_TAC >> fs[]
QED

Theorem log_packing_resources_inst_idx[simp]:
  log_packing_resources cut start end_cut capacity lo top tv src n
    (s with vs_inst_idx := index) <=>
  log_packing_resources cut start end_cut capacity lo top tv src n s
Proof
  Cases_on `FLOOKUP s.vs_allocas cut.cs_next_id = NONE` >>
  simp[log_packing_resources_def, memory_snapshot_allocated_def,
    memory_snapshot_alloc_frame_def, memory_snapshot_addr_def, update_var_def,
    abi_alloca_request_ok_def, enc_scratch_def, alloca_inv_def,
    allocas_non_overlapping_def, alloca_next_valid_def]
QED

(* Nonexecuting entry geometry. The first allocation is computed virtually
   only to state the canonical reservation for the later packing cut. *)
Definition log_statement_resources_def:
  log_statement_resources cenv scopes eval_cut topic_cut packed_cut encoder_start encoder_end
    data_capacity capacity lo top tv ss <=>
    alloca_inv ss /\ abi_alloca_request_ok topic_cut.cs_next_id data_capacity ss /\
    ss.vs_alloca_next + data_capacity < dimword(:256) /\
    type_memory_size tv <= data_capacity /\
    w2n (memory_snapshot_addr topic_cut.cs_next_id ss) + type_memory_size tv < dimword(:256) /\
    source_memory_separated cenv scopes ss
      (w2n (memory_snapshot_addr topic_cut.cs_next_id ss)) (type_memory_size tv) /\
    (let virtual = memory_snapshot_allocated topic_cut.cs_next_id topic_cut.cs_next_var data_capacity ss in
      log_packing_resources packed_cut encoder_start encoder_end capacity lo top tv
        (w2n (memory_snapshot_addr topic_cut.cs_next_id ss)) capacity virtual /\
      log_source_regions eval_cut lo
        [(w2n (memory_snapshot_addr packed_cut.cs_next_id virtual),capacity)] cenv scopes ss)
End

Theorem checked_compile_saved_log_statement:
  check_contract dep layouts addr [(NONE,tops)] = SOME art /\
  env.event_fields = art.cta_event_fields /\ env.type_defs = type_env tops /\
  cenv.ce_struct_fields = make_struct_fields_map tops /\
  cenv.ce_event_info = build_event_info (type_env tops) tops (K NONE) /\
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  type_stmt env ret (Log event_id exprs) = SOME env' /\
  cenv.ce_event_info (nsid_to_string event_id) = SOME (sig_hash,fts,flags) /\
  compile_log_eval_all cenv exprs begin = (args,eval_cut) /\
  compile_log_topic_ops (FST (split_log_ops args flags)) eval_cut = (ops,topic_cut) /\
  compile_alloc_buffer data_capacity topic_cut = (data_buf,store_cut) /\
  compile_log_store_data cenv (SND (split_log_ops args flags))
    (log_non_indexed_types flags fts) data_buf.buf_operand 0 store_cut = ((),packed_cut) /\
  compile_alloc_buffer capacity packed_cut = (buf,encoder_start) /\
  compile_abi_encode_to_buf buf.buf_operand data_buf.buf_operand ei encoder_start = (size_op,encoder_end) /\
  compile_log_abi_emit buf.buf_operand data_buf.buf_operand ei
    (Lit (n2w sig_hash)::ops) encoder_start = ((),final) /\
  abi_enc_plan (type_env tops) (TupleT (log_non_indexed_types flags fts)) ei /\
  capacity = MAX 32 (abi_size_bound cenv.ce_struct_fields (TupleT (log_non_indexed_types flags fts))) /\
  LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) fts ftvs /\
  LIST_REL (\arg tv. evaluate_type (type_env tops) (SND arg) = SOME tv) args atvs /\
  values_have_types ftvs values /\ env_consistent env cx es /\ state_well_typed es /\
  state_rel_simple cenv cx es ss /\ local_ptrs_rel func cenv es.scopes ss /\
  fn_has_code eval_cut topic_cut func /\ fn_has_code topic_cut store_cut func /\
  fn_has_code store_cut packed_cut func /\ fn_has_code packed_cut encoder_start func /\
  fn_has_code packed_cut final func /\
  (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    abi_operand_before eval_cut.cs_next_var (Var p)) /\
  log_args_rel args atvs values ss /\
  log_args_safe args atvs ss (w2n (memory_snapshot_addr topic_cut.cs_next_id ss))
    (type_memory_size (TupleTV (select_log_args F flags ftvs))) /\
  EVERY (\arg. abi_operand_before eval_cut.cs_next_var (FST arg)) args /\
  EVERY (\arg. !l. FST arg <> Label l) args /\
  LENGTH (Lit (n2w sig_hash)::ops) < dimword(:256) /\
  log_statement_resources cenv es.scopes eval_cut topic_cut packed_cut encoder_start encoder_end
    data_capacity capacity lo top (TupleTV (select_log_args F flags ftvs)) ss /\
  ss.vs_current_bb = eval_cut.cs_current_bb /\ ss.vs_inst_idx = LENGTH eval_cut.cs_current_insts /\ ~ss.vs_halted/\
  (!fid sig. FLOOKUP env.fn_sigs fid = SOME sig ==> cenv.ce_func_return_type (nsid_to_string fid) = sig.ret_ty) /\
  ~ss.vs_call_ctx.cc_static ==>
  ?out ev.
    encode_source_event (get_tenv cx) cx.sources cx.txn.target event_id values = SOME ev /\
    out.vs_logs = ss.vs_logs ++ [ev] /\
    state_rel_simple cenv cx (es with logs := es.logs ++ [ev]) out /\
    local_ptrs_rel func cenv es.scopes out /\
    out.vs_current_bb = final.cs_current_bb /\ out.vs_inst_idx = LENGTH final.cs_current_insts /\ ~out.vs_halted /\
    (!fuel r. run_from fuel ctx func out = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx func ss = r)
Proof
  rpt strip_tac >>
  drule checked_contract_struct_args_unique >> strip_tac >>
  `abi_struct_env_rel env.type_defs cenv.ce_struct_fields` by fs[abi_struct_env_rel_tops] >>
  drule_all checked_log_compiler_metadata >> strip_tac >>
  qpat_x_assum `log_statement_resources _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [log_statement_resources_def, LET_THM]) >>
  drule_all saved_log_topics_source_state >>
  disch_then (qspec_then `ctx` (qx_choose_then `middle` (qx_choose_then `topics` strip_assume_tac))) >>
  suspend "allocation"
QED

Resume checked_compile_saved_log_statement[allocation]:
  drule_all abi_log_packing_allocator_frame >> strip_tac >>
  `alloca_inv middle /\ abi_alloca_request_ok topic_cut.cs_next_id data_capacity middle /\
    middle.vs_alloca_next + data_capacity < dimword(:256)` by fs[] >>
  `log_args_safe args atvs middle (w2n (memory_snapshot_addr topic_cut.cs_next_id middle))
    (type_memory_size (TupleTV (select_log_args F flags ftvs)))` by fs[] >>
  drule_all compile_log_data_allocation_path >>
  disch_then (qspec_then `ctx` (qx_choose_then `allocated` strip_assume_tac)) >>
  `state_rel_simple cenv cx es allocated /\ local_ptrs_rel func cenv es.scopes allocated` by
    (qpat_x_assum `allocated = _` SUBST1_TAC >>
     simp_tac (srw_ss()) [] >>
     drule_all log_buffer_source_relations >> simp[]) >>
  qpat_assum `compile_alloc_buffer data_capacity topic_cut = _`
    (strip_assume_tac o MATCH_MP compile_alloc_buffer_code) >>
  `!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    abi_operand_before store_cut.cs_next_var (Var p)` by
    (qspecl_then [`cenv`,`es.scopes`,`topic_cut.cs_next_var`,`store_cut.cs_next_var`]
       mp_tac source_pointer_lifetimes_mono >>
     impl_tac >- (conj_tac >- first_assum MATCH_ACCEPT_TAC >> simp[]) >> simp[]) >>
  `!op. abi_operand_before eval_cut.cs_next_var op ==>
    eval_operand op allocated = eval_operand op ss` by
    (qspecl_then [`eval_cut.cs_next_var`,`topic_cut.cs_next_var`,`ss`,`middle`,`allocated`]
       mp_tac abi_operand_before_frame_trans >> simp[]) >>
  `!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p allocated = lookup_var p ss` by
    (rpt strip_tac >>
     `abi_operand_before eval_cut.cs_next_var (Var p)` by
       (qpat_assum `!name entry p sz. _ ==> abi_operand_before eval_cut.cs_next_var _`
         (qspecl_then [`name`,`entry`,`p`,`sz`] mp_tac) >> simp[]) >>
     qpat_x_assum `!op. abi_operand_before eval_cut.cs_next_var op ==>
       eval_operand op allocated = eval_operand op ss`
       (qspec_then `Var p` mp_tac) >> simp[eval_operand_def]) >>
  `source_memory_separated cenv es.scopes allocated
    (w2n (memory_snapshot_addr topic_cut.cs_next_id ss))
    (type_memory_size (TupleTV (select_log_args F flags ftvs)))` by
    (irule source_memory_separated_frame >> qexists_tac `ss` >>
     conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `log_args_avoid args (compiler_var_names store_cut.cs_next_var
    (packed_cut.cs_next_var - store_cut.cs_next_var))` by
    (irule log_args_before_names >> qexists_tac `topic_cut.cs_next_var` >> simp[]) >>
  suspend "resources"
QED

Resume checked_compile_saved_log_statement[resources]:
  `copy_state_frame
    (memory_snapshot_allocated topic_cut.cs_next_id topic_cut.cs_next_var data_capacity ss) allocated` by
    (qpat_x_assum `allocated = _` SUBST1_TAC >> simp[] >>
     irule log_virtual_allocation_copy_frame >> simp[]) >>
  `log_packing_resources packed_cut encoder_start encoder_end capacity lo top
    (TupleTV (select_log_args F flags ftvs))
    (w2n (memory_snapshot_addr topic_cut.cs_next_id ss)) capacity allocated` by
    (qpat_assum `copy_state_frame (memory_snapshot_allocated _ _ _ ss) allocated`
       (fn th => PURE_ONCE_REWRITE_TAC [MATCH_MP log_packing_resources_copy_frame th]) >>
     first_assum MATCH_ACCEPT_TAC) >>
  `memory_snapshot_addr packed_cut.cs_next_id allocated =
    memory_snapshot_addr packed_cut.cs_next_id
      (memory_snapshot_allocated topic_cut.cs_next_id topic_cut.cs_next_var data_capacity ss)` by
    (qpat_assum `copy_state_frame (memory_snapshot_allocated _ _ _ ss) allocated`
       (strip_assume_tac o MATCH_MP abi_log_packing_allocator_frame) >> simp[]) >>
  `log_source_regions store_cut lo
    [(w2n (memory_snapshot_addr packed_cut.cs_next_id allocated),capacity)] cenv es.scopes allocated` by
    (irule log_source_regions_transport >> qexistsl_tac [`ss`,`eval_cut`] >>
     rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
       (qpat_x_assum `log_source_regions eval_cut _ _ _ _ ss` mp_tac >> simp[] >> NO_TAC),
       fs[] >> decide_tac]) >>
  suspend "endpoint"
QED

Resume checked_compile_saved_log_statement[endpoint]:
  `EVERY (\op. !l. op <> Label l) ops` by
    (irule log_topic_code_no_labels >> goal_assum (drule_at Any) >>
     irule log_split_topics_no_labels >> simp[]) >>
  `EVERY (log_abi_old_operand store_cut) (data_buf.buf_operand::Lit (n2w sig_hash)::ops)` by
    (simp_tac bool_ss [EVERY_DEF] >> conj_tac
     >- (irule log_before_no_labels_old >> simp[] >> drule compile_alloc_buffer_code >> simp[]) >>
     conj_tac >- simp[log_abi_old_operand_def] >>
     fs[EVERY_MEM] >> rpt strip_tac >> irule log_before_no_labels_old >> simp[]) >>
  `fragment_path ctx func ss allocated` by
    (irule fragment_path_trans >> qexists_tac `middle` >> simp[]) >>
  `~allocated.vs_call_ctx.cc_static` by
    (qpat_assum `fragment_path ctx func ss allocated` (mp_tac o MATCH_MP fragment_path_call_ctx) >> fs[]) >>
  `eval_operand data_buf.buf_operand allocated = SOME (memory_snapshot_addr topic_cut.cs_next_id ss)` by
    (qpat_assum `eval_operand data_buf.buf_operand allocated = _` mp_tac >> simp[]) >>
  `log_args_safe args atvs allocated (w2n (memory_snapshot_addr topic_cut.cs_next_id ss))
    (type_memory_size (TupleTV (select_log_args F flags ftvs)))` by
    (qpat_x_assum `log_args_safe args atvs allocated _ _` mp_tac >> simp[]) >>
  drule_all checked_compile_saved_log_data >>
  disch_then (qspec_then `ctx` (qx_choose_then `out` (qx_choose_then `ev` strip_assume_tac))) >>
  `allocated.vs_logs = ss.vs_logs` by
    (qpat_assum `abi_state_frame middle allocated`
       (strip_assume_tac o MATCH_MP abi_state_frame_observables) >>
     qpat_assum `copy_state_frame ss middle`
       (strip_assume_tac o MATCH_MP abi_state_frame_observables o MATCH_MP copy_state_frame_external) >>
     simp[]) >>
  qexistsl_tac [`out`,`ev`] >> rpt conj_tac >> TRY (first_assum MATCH_ACCEPT_TAC)
  >- simp[] >>
  rpt gen_tac >> strip_tac >>
  `?fuel'. run_from fuel' ctx func allocated = r` by
    (qpat_x_assum `!fuel r. _ ==> ?fuel'. run_from fuel' ctx func allocated = r`
       (qspecl_then [`fuel`,`r`] mp_tac) >> simp[]) >>
  qpat_assum `fragment_path ctx func ss allocated`
    (fn th => drule_all (MATCH_MP fragment_path_continue th)) >> simp[]
QED

Finalise checked_compile_saved_log_statement

(* The resource interface quantifies over the expression-IH endpoint, but
   contains only reservations and source-region geometry. In particular it
   neither assumes topic correctness nor a packing-prefix execution. *)
Theorem log_save_arg_no_labels:
  compile_log_save_arg cenv ty src suffix cs = (saved,cut) /\ (!l. src <> Label l) ==>
  !l. saved <> Label l
Proof
  simp[compile_log_save_arg_def] >> IF_CASES_TAC
  >- (simp[comp_return_def] >> rpt strip_tac >> gvs[]) >>
  simp[compile_materialize_vv_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, unwrap_value_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule compile_alloc_buffer_code >> simp[]
QED

Theorem log_eval_code_no_labels:
  !exprs cenv cs args cut.
    compile_log_eval_all cenv exprs cs = (args,cut) /\
    EVERY (\e. !st op finish. lower_value compile_expr cenv (expr_type e) e st = (op,finish) ==>
      !l. op <> Label l) exprs ==>
    EVERY (\arg. !l. FST arg <> Label l) args
Proof
  Induct_on `exprs` >- simp[compile_log_eval_all_def, comp_return_def] >>
  rpt gen_tac >> simp[Once compile_log_eval_all_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  qpat_assum `!st op finish. lower_value _ _ _ _ _ = _ ==> _` drule_all >> DISCH_TAC >>
  conj_tac >- (drule_all log_save_arg_no_labels >> simp[]) >>
  qpat_x_assum `!cenv cs args cut. _` drule_all >> simp[]
QED

(* Field layouts in the resource geometry are uniquely determined by type
   evaluation; source type soundness supplies their value typing below. *)
Theorem log_evaluated_field_types_unique[local]:
  !tys tenv tvs tvs'.
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs /\
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs' ==>
    tvs = tvs'
Proof
  Induct_on `tys` >> rpt gen_tac >> Cases_on `tvs` >> Cases_on `tvs'` >> simp[] >>
  rpt strip_tac >> gvs[] >> first_x_assum irule >>
  qexists_tac `tenv` >> conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

(* Canonical resources are required only at reached, ready expression-prefix
   endpoints; their addresses may depend on that state's allocator geometry,
   including cached scratch. The expression IH proves both path and readiness. *)
Theorem checked_compile_log_data_execution:
  check_contract dep layouts addr [(NONE,tops)] = SOME art /\
  env.event_fields = art.cta_event_fields /\ env.type_defs = type_env tops /\
  cenv.ce_struct_fields = make_struct_fields_map tops /\
  cenv.ce_event_info = build_event_info (type_env tops) tops (K NONE) /\
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  ~cx.txn.is_static /\ ~before.vs_call_ctx.cc_static /\
  (!fid sig. FLOOKUP env.fn_sigs fid = SOME sig ==> cenv.ce_func_return_type (nsid_to_string fid) = sig.ret_ty) /\
  type_stmt env ret (Log event_id exprs) = SOME env' /\
  cenv.ce_event_info (nsid_to_string event_id) = SOME (sig_hash,fts,flags) /\
  compile_log_eval_all cenv exprs begin = (args,eval_cut) /\
  compile_log_topic_ops (FST (split_log_ops args flags)) eval_cut = (ops,topic_cut) /\
  compile_alloc_buffer data_capacity topic_cut = (data_buf,store_cut) /\
  compile_log_store_data cenv (SND (split_log_ops args flags))
    (log_non_indexed_types flags fts) data_buf.buf_operand 0 store_cut = ((),packed_cut) /\
  compile_alloc_buffer capacity packed_cut = (buf,encoder_start) /\
  compile_abi_encode_to_buf buf.buf_operand data_buf.buf_operand ei encoder_start = (size_op,encoder_end) /\
  compile_log_abi_emit buf.buf_operand data_buf.buf_operand ei
    (Lit (n2w sig_hash)::ops) encoder_start = ((),final) /\
  abi_enc_plan (type_env tops) (TupleT (log_non_indexed_types flags fts)) ei /\
  capacity = MAX 32 (abi_size_bound cenv.ce_struct_fields (TupleT (log_non_indexed_types flags fts))) /\
  LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) fts ftvs /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_exprs exprs) /\
  data_capacity = MAX 32 (SUM (MAP (type_memory_bytes cenv) (log_non_indexed_types flags fts))) /\
  ei = type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT (log_non_indexed_types flags fts)) /\
  ~NULL (SND (split_log_ops args flags)) /\
  compile_stmt cenv lctx ret (Log event_id exprs) begin = ((),final) /\
  fn_has_code begin final func /\ cs_extends eval_cut final /\ fn_inst_ids_distinct func /\
  fn_has_code eval_cut topic_cut func /\ fn_has_code topic_cut store_cut func /\
  fn_has_code store_cut packed_cut func /\ fn_has_code packed_cut encoder_start func /\
  fn_has_code packed_cut final func /\
  ids = compiler_alloca_ids begin final /\ requests = compiler_alloca_requests begin final /\
  EVERY (\e. cs_appends (lower_value compile_expr cenv (expr_type e) e)) exprs /\
  EVERY (\e. compiler_id_flow (lower_value compile_expr cenv (expr_type e) e)) exprs /\
  LIST_REL (\e tv. evaluate_type (type_env tops) (lowered_value_type cenv e) = SOME tv /\
    type_memory_size tv < dimword(:256)) exprs layout_tvs /\
  EVERY (log_argument_lowering tops env ctx func cenv cx ids reserved requests final charge) exprs /\
  log_argument_charges charge cx exprs es values es' total_charge /\ total_charge <= credit /\
  log_prefix_ready env cx cenv func ids reserved requests final exprs begin es before credit [] [] [] /\
  EVERY (\e. !st op finish. lower_value compile_expr cenv (expr_type e) e st = (op,finish) ==>
    !l. op <> Label l) exprs /\
  eval_cut.cs_next_var <= topic_cut.cs_next_var /\
  MEM topic_cut.cs_next_id (compiler_alloca_ids eval_cut final) /\
  MEM (topic_cut.cs_next_id,data_capacity) requests /\
  LENGTH (Lit (n2w sig_hash)::ops) < dimword(:256) /\ ~before.vs_halted /\
  (!saved tvs. fragment_path ctx func before saved /\
    log_prefix_ready env cx cenv func ids reserved requests final [] eval_cut es' saved
      (credit - total_charge) args tvs values ==>
    ?lo top. log_statement_resources cenv es'.scopes eval_cut topic_cut packed_cut encoder_start encoder_end
      data_capacity capacity lo top (TupleTV (select_log_args F flags ftvs)) saved) ==>
  ?out ev.
    eval_stmt cx (Log event_id exprs) es = (INL (),es' with logs := es'.logs ++ [ev]) /\
    encode_source_event (get_tenv cx) cx.sources cx.txn.target event_id values = SOME ev /\
    state_rel_simple cenv cx (es' with logs := es'.logs ++ [ev]) out /\
    local_ptrs_rel func cenv es'.scopes out /\
    out.vs_current_bb = final.cs_current_bb /\ out.vs_inst_idx = LENGTH final.cs_current_insts /\ ~out.vs_halted /\
    (!fuel r. run_from fuel ctx func out = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx func before = r)
Proof
  rpt strip_tac >>
  `eval_exprs cx exprs es = (INL values,es')` by (drule_all log_argument_charges_source >> simp[]) >>
  `runtime_consistent env cx es` by fs[log_prefix_ready_def] >>
  drule_all checked_log_evaluated_argument_types >>
  qpat_assum `env.type_defs = type_env tops`
    (fn th => disch_then (assume_tac o REWRITE_RULE [th])) >>
  drule_all checked_log_declared_values >>
  disch_then (qx_choose_then `declared_tvs` strip_assume_tac) >>
  `ftvs = declared_tvs` by
    (irule log_evaluated_field_types_unique >> qexistsl_tac [`type_env tops`, `fts`] >>
     conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `values_have_types ftvs values` by simp[] >>
  `EVERY (\arg. !l. FST arg <> Label l) args` by
    (drule_all log_eval_code_no_labels >> simp[]) >>
  qspecl_then [`exprs`, `layout_tvs`, `tops`, `dep`, `layouts`, `addr`, `art`, `env`, `ctx`, `func`,
    `cenv`, `cx`, `ids`, `reserved`, `requests`, `final`, `charge`, `begin`, `eval_cut`, `args`,
    `es`, `values`, `es'`, `total_charge`, `before`, `credit`]
    mp_tac checked_compile_log_arguments_from_code >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `saved` (qx_choose_then `atvs` strip_assume_tac)) >>
  qpat_x_assum `!saved tvs. fragment_path _ _ _ _ /\ _ ==> _`
    (qspecl_then [`saved`, `atvs`] mp_tac) >>
  impl_tac >- (conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `lo` (qx_choose_then `top` assume_tac)) >>
  `type_memory_size (TupleTV (select_log_args F flags ftvs)) <= data_capacity` by
    fs[log_statement_resources_def] >>
  `log_args_safe args atvs saved (w2n (memory_snapshot_addr topic_cut.cs_next_id saved))
    (type_memory_size (TupleTV (select_log_args F flags ftvs)))` by
    (drule_all log_ready_arguments_buffer_safe >> simp[]) >>
  qpat_x_assum `log_prefix_ready _ _ _ _ _ _ _ _ [] _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [log_prefix_ready_def]) >>
  `env_consistent env cx es'` by fs[runtime_consistent_def] >>
  `~saved.vs_halted` by fs[] >>
  `~saved.vs_call_ctx.cc_static` by (qpat_assum `fragment_path ctx func before saved` (mp_tac o MATCH_MP fragment_path_call_ctx) >> fs[]) >>
  drule_all checked_compile_saved_log_statement >>
  disch_then (qspec_then `ctx` (qx_choose_then `out` (qx_choose_then `ev` strip_assume_tac))) >>
  `eval_stmt cx (Log event_id exprs) es = (INL (),es' with logs := es'.logs ++ [ev])` by
    (drule_all eval_log_arguments >> simp[]) >>
  qexistsl_tac [`out`,`ev`] >> rpt conj_tac >> TRY (first_assum MATCH_ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  `?fuel'. run_from fuel' ctx func saved = r` by
    (qpat_x_assum `!fuel r. _ ==> ?fuel'. run_from fuel' ctx func saved = r`
       (qspecl_then [`fuel`,`r`] mp_tac) >> simp[]) >>
  qpat_assum `fragment_path ctx func before saved`
    (fn th => drule_all (MATCH_MP fragment_path_continue th)) >> simp[]
QED
