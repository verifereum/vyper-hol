(* Canonical #551 Log packing seam.  The output ALLOCA is executed, while
   encoder scratch is governed by enc_scratch, not a native per-id trace.
   TOP-LEVEL: checked_log_data_frag (whole canonical execution),
     checked_log_packing_canonical (checked source-state cut),
     log_data_result_logs (initial-state logger and exact data).
   Helpers expose allocation, typed RAM and the public preservation frame. *)
Theory logDataPacking
Ancestors
  typeValueInduction
  logAbiEncoder abiLogPackingState abiBufferAllocationPath abiBufferAllocationCode abiLogReady
  abiLogPackingReady typedCopyStateFrame abiFieldOperands abiStaticLoopCode
  abiAllocatedState abiAllocatorState abiAllocatedWindows abiAllocationFrame
  memoryValueSnapshot memoryValueDefs memoryValueFrame valueEncoding valueEncodingProps
  abiEncoderProps abiEncoderStructure abiLogCode
  context compileEnv stmtLowering exprLoweringProps emitHelperProps fragExec fragBlockPath instIdxIndep
  venomState venomExecSemantics venomMemDefs venomInst vyperTyping vyperValue vyperABI vyperMisc
  contractABI list rich_list words finite_map arithmetic valueEncodingProofs
  memoryValueEncoding vyperTypeABI vyperTypeContract vyperContext
  vyperTypeSystem vyperTypeInvariants sourceMemoryFrames abiStateFrame typedLogArgs
  typedSArrayDynInvariant abiLogPackingBoundary typedLogSplitComplete typedLogStoreCode
  logStoreComposition

(* This is the non-memory part of enc_pre after the actual output ALLOCA.
   In particular it reserves finitely many 32-byte encoder cells below the
   word limit, accepts cached allocations, and says nothing about encoding
   execution or the bytes of its result. *)
Definition log_packing_resources_def:
  log_packing_resources packed_cut encoder_start encoder_end capacity lo top
      tv src output_size s <=>
    alloca_inv s /\ abi_alloca_request_ok packed_cut.cs_next_id capacity s /\
    s.vs_alloca_next + capacity < dimword(:256) /\
    src + type_memory_size tv <= lo /\
    w2n (memory_snapshot_addr packed_cut.cs_next_id s) + output_size <= lo /\
    regions_disjoint (src,type_memory_size tv)
      (w2n (memory_snapshot_addr packed_cut.cs_next_id s),output_size) /\
    enc_scratch (frag_ids encoder_start encoder_end) lo top
      (memory_snapshot_allocated packed_cut.cs_next_id packed_cut.cs_next_var capacity s)
End

Theorem log_packing_resources_copy_frame:
  copy_state_frame before after ==>
  (log_packing_resources packed_cut encoder_start encoder_end capacity lo top
     tv src output_size after <=>
   log_packing_resources packed_cut encoder_start encoder_end capacity lo top
     tv src output_size before)
Proof
  strip_tac >>
  `abi_allocator_state after = abi_allocator_state before` by
    fs[copy_state_frame_def, abi_allocator_state_eq] >>
  drule abi_alloca_inv_state >> strip_tac >>
  drule abi_alloca_request_ok_state >> strip_tac >>
  fs[log_packing_resources_def, copy_state_frame_def,
    memory_snapshot_addr_def, memory_snapshot_allocated_def,
    memory_snapshot_alloc_frame_def, update_var_def, enc_scratch_def,
    alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  IF_CASES_TAC >> fs[]
QED

Theorem log_old_operand_before[simp]:
  log_abi_old_operand st op ==> abi_operand_before st.cs_next_var op
Proof
  Cases_on `op` >>
  simp[log_abi_old_operand_def, abi_operand_before_def,
    not_fresh_at_def, compiler_var_name_def]
QED

Theorem log_old_operand_mono:
  log_abi_old_operand st op /\ st.cs_next_var <= st'.cs_next_var ==>
  log_abi_old_operand st' op
Proof
  Cases_on `op` >> simp[log_abi_old_operand_def, not_fresh_at_def] >>
  metis_tac[LESS_EQ_TRANS]
QED

(* The encoder consumes the plain tuple constructor, not ListV (the latter
   belongs to the ABI value language). *)
Theorem log_packed_tuple_typed:
  values_have_types tvs vs ==>
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs))
Proof
  simp[value_has_type_def]
QED

Theorem compile_alloc_buffer_frag:
  compile_alloc_buffer capacity st = (buf,st') /\
  capacity < dimword(:256) ==>
  frag_exec ctx st st' (\s. s = s0)
    (\s. s = (memory_snapshot_allocated st.cs_next_id st.cs_next_var capacity s0
      with vs_inst_idx := LENGTH st'.cs_current_insts)) (\r. F)
Proof
  strip_tac >> drule_all compile_alloc_buffer_code >> strip_tac >>
  irule frag_exec_run_inst_seq >>
  fs[same_blocks_def] >>
  simp[IS_PREFIX_APPEND, mk_inst_def, is_terminator_def] >>
  qexists_tac `memory_snapshot_allocated st.cs_next_id st.cs_next_var capacity s0` >>
  simp[] >> drule_all compile_alloc_buffer_execution >> simp[mk_inst_def]
QED

(* The canonical frame protects every readable low region outside the
   output, not just the tuple used by this particular caller. *)
Theorem log_enc_frame_low_memory:
  enc_frame st st' lo top outs before after /\ b + n <= lo /\
  EVERY (\(base,len). regions_disjoint (b,n) (base,len)) outs ==>
  mem_bytes_at b n after.vs_memory = mem_bytes_at b n before.vs_memory
Proof
  strip_tac >> irule LIST_EQ >> simp[] >> qx_gen_tac `i` >> strip_tac >>
  `mem_bytes_at (b+i) 1 after.vs_memory =
     mem_bytes_at (b+i) 1 before.vs_memory` by
    (qpat_x_assum `enc_frame _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [enc_frame_def]) >>
     qpat_x_assum `!a. EVERY _ outs /\ _ ==> _`
       (qspec_then `b+i` mp_tac) >>
     impl_tac >- (conj_tac
       >- (fs[EVERY_MEM] >> Cases >> simp[] >> rpt strip_tac >>
           res_tac >> fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
       fs[enc_scratch_def] >> rpt strip_tac >> res_tac >> decide_tac) >> simp[]) >>
  pop_assum (mp_tac o AP_TERM ``EL 0 : word8 list -> word8``) >>
  simp[EL_mem_bytes_at, ADD_ASSOC]
QED

Definition log_packing_public_frame_def:
  log_packing_public_frame st lo outs before after <=>
    (!x w. not_fresh_at st x /\ lookup_var x before = SOME w ==>
      lookup_var x after = SOME w) /\
    (!id r. FLOOKUP before.vs_allocas id = SOME r ==>
      FLOOKUP after.vs_allocas id = SOME r) /\
    alloca_inv after /\ lo <= after.vs_alloca_next /\
    (!id b n. FLOOKUP after.vs_allocas id = SOME (b,n) /\
      FLOOKUP before.vs_allocas id = NONE ==> lo <= b) /\
    (!b n. b+n <= lo /\
      EVERY (\(base,len). regions_disjoint (b,n) (base,len)) outs ==>
      mem_bytes_at b n after.vs_memory = mem_bytes_at b n before.vs_memory) /\
    after.vs_accounts = before.vs_accounts /\
    after.vs_transient = before.vs_transient /\
    after.vs_requests = before.vs_requests /\
    after.vs_call_ctx = before.vs_call_ctx /\
    after.vs_data_section = before.vs_data_section /\
    after.vs_tx_ctx = before.vs_tx_ctx /\ after.vs_block_ctx = before.vs_block_ctx /\
    after.vs_immutables = before.vs_immutables /\ after.vs_outcomes = before.vs_outcomes
End

Theorem log_enc_frame_public:
  enc_frame st st' lo top outs before (after with vs_logs := before.vs_logs) /\
  after.vs_call_ctx = before.vs_call_ctx /\
  after.vs_data_section = before.vs_data_section /\
  after.vs_tx_ctx = before.vs_tx_ctx /\ after.vs_block_ctx = before.vs_block_ctx /\
  after.vs_immutables = before.vs_immutables /\ after.vs_outcomes = before.vs_outcomes ==>
  log_packing_public_frame st lo outs before after
Proof
  strip_tac >>
  `!b n. b+n <= lo /\
     EVERY (\(base,len). regions_disjoint (b,n) (base,len)) outs ==>
     mem_bytes_at b n after.vs_memory = mem_bytes_at b n before.vs_memory` by
    (rpt strip_tac >> drule_all log_enc_frame_low_memory >> simp[]) >>
  `!id b n. FLOOKUP after.vs_allocas id = SOME (b,n) /\
     FLOOKUP before.vs_allocas id = NONE ==> lo <= b` by
    (rpt strip_tac >> Cases_on `id IN frag_ids st st'`
     >- (fs[enc_frame_def, enc_scratch_def] >>
         qpat_x_assum `!i b sz. i IN frag_ids st st' /\ _ ==> _`
           (qspecl_then [`id`,`b`,`n`] mp_tac) >> simp[]) >>
     fs[enc_frame_def] >> qpat_x_assum `!i. i NOTIN frag_ids st st' ==> _`
       (qspec_then `id` mp_tac) >> simp[]) >>
  fs[log_packing_public_frame_def, enc_frame_def, enc_scratch_def,
     lookup_var_def, alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

(* Source owning pointers retain both their binding and their allocation
   record.  Their complete registered region is unchanged when below lo
   and separate from the output; no per-id encoder execution is assumed. *)
Theorem log_packing_owned_pointer:
  log_packing_public_frame st lo outs before after /\ not_fresh_at st p /\
  lookup_var p before = SOME w /\
  FLOOKUP before.vs_allocas id = SOME (b,n) /\
  b+n <= lo /\ EVERY (\(base,len). regions_disjoint (b,n) (base,len)) outs ==>
  lookup_var p after = SOME w /\
  FLOOKUP after.vs_allocas id = SOME (b,n) /\ alloca_inv after /\
  mem_bytes_at b n after.vs_memory = mem_bytes_at b n before.vs_memory
Proof
  simp[log_packing_public_frame_def] >> metis_tac[]
QED

Theorem log_packing_owned_value:
  log_packing_public_frame st lo outs before after /\ not_fresh_at st p /\
  lookup_var p before = SOME w /\ w2n w = b /\
  FLOOKUP before.vs_allocas id = SOME (b,n) /\ b+n <= lo /\
  EVERY (\(base,len). regions_disjoint (b,n) (base,len)) outs /\
  memory_value_rel tv v b before.vs_memory /\ val_wf tv v /\
  type_memory_size tv <= n ==>
  lookup_var p after = SOME w /\
  FLOOKUP after.vs_allocas id = SOME (b,n) /\ alloca_inv after /\
  memory_value_rel tv v (w2n w) after.vs_memory
Proof
  strip_tac >> drule_all log_packing_owned_pointer >> strip_tac >>
  simp[] >> irule memory_value_rel_mem_agree_region >> simp[] >>
  qexistsl_tac [`n`,`before.vs_memory`] >> simp[]
QED

Definition log_data_result_def:
  log_data_result packed_cut encoder_start encoder_end capacity lo top bytes ws packed s <=>
    ?allocated.
      allocated = (memory_snapshot_allocated packed_cut.cs_next_id packed_cut.cs_next_var capacity packed
        with vs_inst_idx := LENGTH encoder_start.cs_current_insts) /\
      mem_bytes_at (w2n (memory_snapshot_addr packed_cut.cs_next_id packed))
        (LENGTH bytes) s.vs_memory = bytes /\
      s.vs_logs = packed.vs_logs ++
        [<|logger := w2w packed.vs_call_ctx.cc_address; topics := ws; data := bytes|>] /\
      s.vs_call_ctx = packed.vs_call_ctx /\ s.vs_data_section = packed.vs_data_section /\
      s.vs_tx_ctx = packed.vs_tx_ctx /\ s.vs_block_ctx = packed.vs_block_ctx /\
      s.vs_immutables = packed.vs_immutables /\ s.vs_outcomes = packed.vs_outcomes /\
      enc_frame encoder_start encoder_end lo top
        [(w2n (memory_snapshot_addr packed_cut.cs_next_id packed),LENGTH bytes)] allocated
        (s with vs_logs := packed.vs_logs) /\
      log_packing_public_frame encoder_start lo
        [(w2n (memory_snapshot_addr packed_cut.cs_next_id packed),LENGTH bytes)] allocated s
End

Theorem log_enc_scratch_inst_idx[simp]:
  enc_scratch ids lo top (s with vs_inst_idx := index) <=> enc_scratch ids lo top s
Proof
  simp[enc_scratch_def, alloca_inv_def,
    allocas_non_overlapping_def, alloca_next_valid_def]
QED

Theorem log_enc_frame_before_inst_idx[simp]:
  enc_frame st st' lo top outs (before with vs_inst_idx := index) after <=>
  enc_frame st st' lo top outs before after
Proof
  simp[enc_frame_def, lookup_var_def]
QED

Theorem log_public_frame_before_inst_idx[simp]:
  log_packing_public_frame st lo outs (before with vs_inst_idx := index) after <=>
  log_packing_public_frame st lo outs before after
Proof
  simp[log_packing_public_frame_def, lookup_var_def]
QED

(* The checked store supplies val_in_memory; the only other execution proof
   used here is compile_log_abi_emit_frag, hence compile_abi_encode_to_buf_frag.
   The canonical frame is exposed rather than inventing a native trace. *)
Theorem log_data_allocate_emit_frag:
  compile_alloc_buffer capacity packed_cut = (buf,encoder_start) /\
  compile_abi_encode_to_buf buf.buf_operand src ei encoder_start = (size_op,encoder_end) /\
  compile_log_abi_emit buf.buf_operand src ei ops encoder_start = ((),final) /\
  abi_enc_plan env ty ei /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  eval_operand src packed = SOME sw /\ eval_operands ops packed = SOME ws /\
  EVERY (log_abi_old_operand packed_cut) (src::ops) /\
  LENGTH ops < dimword(:256) /\
  val_in_memory tv v (w2n sw) packed.vs_memory /\
  log_packing_resources packed_cut encoder_start encoder_end capacity lo top tv (w2n sw)
    (LENGTH (enc (vyper_to_abi_type env ty) av)) packed ==>
  frag_exec ctx packed_cut final (\s. s = packed)
    (log_data_result packed_cut encoder_start encoder_end capacity lo top
      (enc (vyper_to_abi_type env ty) av) ws packed) (\r. F)
Proof
  rpt strip_tac >>
  `capacity < dimword(:256)` by
    (fs[log_packing_resources_def] >> decide_tac) >>
  drule_all compile_alloc_buffer_code >> strip_tac >>
  qabbrev_tac `allocated = memory_snapshot_allocated packed_cut.cs_next_id
    packed_cut.cs_next_var capacity packed with
      vs_inst_idx := LENGTH encoder_start.cs_current_insts` >>
  `!op. log_abi_old_operand packed_cut op ==>
     eval_operand op allocated = eval_operand op packed` by
    (rpt strip_tac >> simp[Abbr`allocated`, eval_op_inst_idx] >>
     irule buffer_allocation_old_operand >> drule_all log_old_operand_before >> simp[]) >>
  `eval_operand src allocated = SOME sw` by fs[] >>
  `eval_operands ops allocated = eval_operands ops packed` by
    (irule eval_operands_before_frame >>
     qexists_tac `packed_cut.cs_next_var` >>
     simp[Abbr`allocated`, eval_op_inst_idx, buffer_allocation_old_operand] >>
     fs[EVERY_MEM] >> rpt strip_tac >> irule log_old_operand_before >> fs[]) >>
  `eval_operands ops allocated = SOME ws` by simp[] >>
  `EVERY (log_abi_old_operand encoder_start) (buf.buf_operand::ops)` by
    (simp_tac bool_ss [EVERY_DEF] >> conj_tac
     >- (simp[log_abi_old_operand_def, not_fresh_at_def] >>
         rpt strip_tac >> decide_tac) >>
     fs[EVERY_MEM] >> rpt strip_tac >> irule log_old_operand_mono >>
     qexists_tac `packed_cut` >> simp[]) >>
  `log_abi_old_operand encoder_start src` by
    (irule log_old_operand_mono >> qexists_tac `packed_cut` >> fs[]) >>
  `enc_pre encoder_start encoder_end [buf.buf_operand;src] lo top tv v (w2n sw)
     [(w2n (memory_snapshot_addr packed_cut.cs_next_id packed),
       LENGTH (enc (vyper_to_abi_type env ty) av))] allocated` by
    (qpat_x_assum `log_packing_resources _ _ _ _ _ _ _ _ _ packed`
       (strip_assume_tac o REWRITE_RULE [log_packing_resources_def]) >>
     simp[enc_pre_def, Abbr`allocated`] >>
     rpt strip_tac >> gvs[] >> fs[log_abi_old_operand_def]) >>
  `eval_operand buf.buf_operand allocated =
      SOME (memory_snapshot_addr packed_cut.cs_next_id packed)` by
    simp[Abbr`allocated`, eval_op_inst_idx] >>
  suspend "shared_fragment"
QED

Resume log_data_allocate_emit_frag[shared_fragment]:
  drule_all compile_log_abi_emit_frag >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `cs_extends packed_cut encoder_start` by
    (irule cs_extends_same_block >> fs[same_blocks_def, IS_PREFIX_APPEND]) >>
  `cs_extends encoder_start final` by
    (qpat_x_assum `compile_log_abi_emit _ _ _ _ _ = _` mp_tac >>
     simp[compile_log_abi_emit_def, comp_bind_def] >> fs[] >> strip_tac >>
     irule cs_extends_trans >> qexists_tac `encoder_end` >> conj_tac
     >- (drule compile_abi_encode_extends >> simp[]) >>
     irule cs_extends_same_block >> drule emit_inst_extends >>
     simp[IS_PREFIX_APPEND]) >>
  irule frag_exec_seq >>
  qexistsl_tac [`\s. s = allocated`,`encoder_start`] >> simp[] >>
  conj_tac
  >- (simp[Abbr`allocated`] >> drule_all compile_alloc_buffer_frag >> simp[]) >>
  irule frag_exec_conseq >> goal_assum (drule_at Any) >>
  simp_tac bool_ss [log_data_result_def] >> qx_gen_tac `s` >> strip_tac >>
  `log_packing_public_frame encoder_start lo
    [(w2n (memory_snapshot_addr packed_cut.cs_next_id packed),
      LENGTH (enc (vyper_to_abi_type env ty) av))] allocated s` by
    (irule log_enc_frame_public >> simp[] >>
     qexistsl_tac [`encoder_end`,`top`] >> simp[]) >>
  fs[Abbr`allocated`] >>
  fs[memory_snapshot_allocated_def, update_var_def,
    memory_snapshot_alloc_frame_def] >> rw[] >> fs[]
QED

Finalise log_data_allocate_emit_frag

Theorem log_evaluate_types:
  !tys tvs tenv.
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs ==>
    OPT_MMAP (evaluate_type tenv) tys = SOME tvs
Proof
  Induct >> Cases_on `tvs` >> simp[OPT_MMAP_def]
QED

Theorem log_base_memory_slots:
  !bt. type_memory_size (BaseTV bt) = 32 * type_slot_size (BaseTV bt)
Proof
  gen_tac >> Cases_on `bt` >>
  TRY (rename1 `BytesT bound` >> Cases_on `bound`) >>
  simp[type_memory_size_def, type_slot_size_def, LEFT_ADD_DISTRIB]
QED

Theorem log_array_memory_slots:
  !tv bound. type_memory_size tv = 32 * type_slot_size tv ==>
    type_memory_size (ArrayTV tv bound) = 32 * type_slot_size (ArrayTV tv bound)
Proof
  rpt gen_tac >> Cases_on `bound` >>
  simp[type_memory_size_def, type_slot_size_def, LEFT_ADD_DISTRIB] >>
  strip_tac >> asm_rewrite_tac[] >>
  TRY AP_TERM_TAC >> CONV_TAC (AC_CONV (MULT_ASSOC,MULT_COMM))
QED

Theorem log_memory_slot_sizes:
  (!tv. type_memory_size tv = 32 * type_slot_size tv) /\
  (!tvs. type_memory_size_fields tvs = 32 * type_slot_size_fields tvs) /\
  (!p:string # type_value. type_memory_size (SND p) = 32 * type_slot_size (SND p)) /\
  (!tvs. type_memory_size_list tvs = 32 * type_slot_size_list tvs)
Proof
  ho_match_mp_tac type_value_mutual_induction >>
  simp[log_array_memory_slots, log_base_memory_slots, type_memory_size_def, type_slot_size_def,
    LEFT_ADD_DISTRIB, MULT_ASSOC] >>
  rpt gen_tac >> strip_tac >> rename1 `type_memory_size (SND entry)` >>
  PairCases_on `entry` >> fs[type_memory_size_def, type_slot_size_def]
QED

Theorem log_selected_tuple_type:
  LENGTH flags = LENGTH args /\ LIST_REL event_arg_compatible fts (MAP SND args) /\
  LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) fts ftvs /\
  type_memory_size (TupleTV (select_log_args F flags ftvs)) < dimword(:256) ==>
  evaluate_type tenv (TupleT (log_non_indexed_types flags fts)) =
    SOME (TupleTV (select_log_args F flags ftvs))
Proof
  strip_tac >> drule_all log_non_indexed_evaluate_types >> strip_tac >>
  drule log_evaluate_types >> strip_tac >>
  simp[evaluate_type_def, evaluate_types_OPT_MMAP] >>
  mp_tac (Q.SPEC `TupleTV (select_log_args F flags ftvs)`
    (CONJUNCT1 log_memory_slot_sizes)) >> decide_tac
QED

(* TOP-LEVEL: the real checked recursive packing path is retained, and its
   endpoint is immediately consumed by the canonical allocating encoder/LOG
   fragment.  No packed-memory or encoder-execution fact is a premise.
   The prefix is an actual path; the suffix deliberately uses #551's more
   reusable continuation semantics rather than a native per-instruction path. *)
Theorem checked_log_packing_canonical:
  check_contract dep layouts addr [(NONE,tops)] = SOME art /\
  cenv.ce_struct_fields = make_struct_fields_map tops /\
  LENGTH flags = LENGTH args /\ LIST_REL event_arg_compatible fts (MAP SND args) /\
  LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) fts ftvs /\
  LIST_REL (\arg tv. evaluate_type (type_env tops) (SND arg) = SOME tv) args atvs /\
  compile_log_store_data cenv (SND (split_log_ops args flags))
    (log_non_indexed_types flags fts) src 0 cs = (ret,packed_cut) /\
  compile_alloc_buffer capacity packed_cut = (buf,encoder_start) /\
  compile_abi_encode_to_buf buf.buf_operand src ei encoder_start = (size_op,encoder_end) /\
  compile_log_abi_emit buf.buf_operand src ei ops encoder_start = ((),final) /\
  abi_enc_plan (type_env tops) (TupleT (log_non_indexed_types flags fts)) ei /\
  vyper_to_abi (type_env tops) (TupleT (log_non_indexed_types flags fts))
    (ArrayV (TupleV (select_log_args F flags values))) = SOME av /\
  fn_has_code cs packed_cut func /\ fn_has_code packed_cut encoder_start func /\
  state_well_typed es /\ state_rel_simple cenv cx es ss /\
  local_ptrs_rel func cenv es.scopes ss /\
  source_memory_separated cenv es.scopes ss (w2n root_addr)
    (type_memory_size (TupleTV (select_log_args F flags ftvs))) /\
  (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==>
    abi_operand_before cs.cs_next_var (Var p)) /\
  log_args_rel args atvs values ss /\
  log_args_safe args atvs ss (w2n root_addr)
    (type_memory_size (TupleTV (select_log_args F flags ftvs))) /\
  log_args_avoid args (compiler_var_names cs.cs_next_var (packed_cut.cs_next_var - cs.cs_next_var)) /\
  w2n root_addr + type_memory_size (TupleTV (select_log_args F flags ftvs)) < dimword(:256) /\
  EVERY (log_abi_old_operand cs) (src::ops) /\
  eval_operand src ss = SOME root_addr /\ eval_operands ops ss = SOME ws /\
  LENGTH ops < dimword(:256) /\
  log_packing_resources packed_cut encoder_start encoder_end capacity lo top
    (TupleTV (select_log_args F flags ftvs)) (w2n root_addr)
    (LENGTH (enc (vyper_to_abi_type (type_env tops)
      (TupleT (log_non_indexed_types flags fts))) av)) ss /\
  ss.vs_current_bb = cs.cs_current_bb /\
  ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
  ?packed.
    fragment_path ctx func ss packed /\ copy_state_frame ss packed /\
    (!op. abi_operand_before cs.cs_next_var op ==>
      eval_operand op packed = eval_operand op ss) /\
    state_rel_simple cenv cx es packed /\ local_ptrs_rel func cenv es.scopes packed /\
    packed.vs_current_bb = packed_cut.cs_current_bb /\
    packed.vs_inst_idx = LENGTH packed_cut.cs_current_insts /\ ~packed.vs_halted /\
    frag_exec ctx packed_cut final (\s. s = packed)
      (log_data_result packed_cut encoder_start encoder_end capacity lo top
        (enc (vyper_to_abi_type (type_env tops)
          (TupleT (log_non_indexed_types flags fts))) av) ws packed) (\r. F)
Proof
  rpt strip_tac >>
  `abi_operand_before cs.cs_next_var src` by
    (fs[] >> drule_all log_old_operand_before >> simp[]) >>
  drule_all checked_log_packing_source_state >>
  disch_then (qspec_then `ctx` (qx_choose_then `packed` strip_assume_tac)) >>
  `val_in_memory (TupleTV (select_log_args F flags ftvs))
     (ArrayV (TupleV (select_log_args F flags values)))
     (w2n root_addr) packed.vs_memory` by
    (drule_all memory_tuple_rel_val_in_memory >> simp[]) >>
  `value_has_type (TupleTV (select_log_args F flags ftvs))
     (ArrayV (TupleV (select_log_args F flags values)))` by
    (irule log_packed_tuple_typed >> simp[]) >>
  `eval_operand src packed = SOME root_addr` by simp[] >>
  `EVERY (abi_operand_before cs.cs_next_var) ops` by
    (fs[EVERY_MEM] >> rpt strip_tac >> drule_all log_old_operand_before >> simp[]) >>
  `eval_operands ops packed = SOME ws` by
    (drule_all eval_operands_before_frame >> simp[]) >>
  `EVERY (log_abi_old_operand packed_cut) (src::ops)` by
    (fs[EVERY_MEM] >> rpt strip_tac >> irule log_old_operand_mono >>
     qexists_tac `cs` >> simp[]) >>
  `log_packing_resources packed_cut encoder_start encoder_end capacity lo top
     (TupleTV (select_log_args F flags ftvs)) (w2n root_addr)
     (LENGTH (enc (vyper_to_abi_type (type_env tops)
       (TupleT (log_non_indexed_types flags fts))) av)) packed` by
    (drule_all log_packing_resources_copy_frame >> simp[]) >>
  `type_memory_size (TupleTV (select_log_args F flags ftvs)) < dimword(:256)` by decide_tac >>
  drule_all log_selected_tuple_type >> strip_tac >>
  qexists_tac `packed` >> simp[] >>
  drule_all log_data_allocate_emit_frag >> simp[]
QED

(* Consume a retained actual packing prefix and a canonical suffix.  This
   is exactly frag_exec's successful continuation conclusion, at the caller's
   containing function.  It intentionally does not assert a native trace. *)
Theorem log_packing_path_frag:
  fragment_path ctx func before packed /\
  packed.vs_current_bb = cut.cs_current_bb /\
  packed.vs_inst_idx = LENGTH cut.cs_current_insts /\ ~packed.vs_halted /\
  fn_has_code cut final func /\
  frag_exec ctx cut final (\s. s = packed) Q (\r. F) ==>
  ?out. Q out /\ out.vs_current_bb = final.cs_current_bb /\
    out.vs_inst_idx = LENGTH final.cs_current_insts /\ ~out.vs_halted /\
    !fuel r. run_from fuel ctx func out = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx func before = r
Proof
  strip_tac >> qpat_x_assum `frag_exec _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [frag_exec_def]) >>
  disch_then (qspecl_then [`func`,`packed`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  qexists_tac `out` >> rpt conj_tac >> TRY (first_assum MATCH_ACCEPT_TAC) >>
  qx_gen_tac `fuel` >> strip_tac >>
  `?fuel'. run_from fuel' ctx func packed = run_from fuel ctx func out` by metis_tac[] >>
  drule_all fragment_path_continue >> metis_tac[]
QED

Theorem log_data_compile_extends:
  compile_alloc_buffer capacity packed_cut = (buf,encoder_start) /\
  compile_abi_encode_to_buf buf.buf_operand src ei encoder_start = (size_op,encoder_end) /\
  compile_log_abi_emit buf.buf_operand src ei ops encoder_start = ((),final) ==>
  cs_extends packed_cut encoder_start /\ cs_extends encoder_start final /\
  cs_extends packed_cut final
Proof
  strip_tac >> drule compile_alloc_buffer_code >> strip_tac >>
  `cs_extends packed_cut encoder_start` by
    (irule cs_extends_same_block >> fs[same_blocks_def, IS_PREFIX_APPEND]) >>
  `cs_extends encoder_start encoder_end` by
    (drule compile_abi_encode_extends >> simp[]) >>
  `cs_extends encoder_end final` by
    (qpat_x_assum `compile_log_abi_emit _ _ _ _ _ = _` mp_tac >>
     simp[compile_log_abi_emit_def, comp_bind_def] >> fs[] >> strip_tac >>
     irule cs_extends_same_block >> drule emit_inst_extends >>
     simp[IS_PREFIX_APPEND]) >>
  metis_tac[cs_extends_trans]
QED

(* The entire store -> ALLOCA -> shared encoder -> LOG, in canonical
   fragment semantics.  The actual following ALLOCA supplies the no-PHI
   packing continuation in every containing function.  Source relations
   for a particular containing function are supplied by the source-state
   theorem above; this global judgment does not invent backing code for
   arbitrary functions. *)
Theorem checked_log_data_frag:
  check_contract dep layouts addr [(NONE,tops)] = SOME art /\
  cenv.ce_struct_fields = make_struct_fields_map tops /\
  LENGTH flags = LENGTH args /\ LIST_REL event_arg_compatible fts (MAP SND args) /\
  LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) fts ftvs /\
  LIST_REL (\arg tv. evaluate_type (type_env tops) (SND arg) = SOME tv) args atvs /\
  compile_log_store_data cenv (SND (split_log_ops args flags))
    (log_non_indexed_types flags fts) src 0 cs = (ret,packed_cut) /\
  compile_alloc_buffer capacity packed_cut = (buf,encoder_start) /\
  compile_abi_encode_to_buf buf.buf_operand src ei encoder_start = (size_op,encoder_end) /\
  compile_log_abi_emit buf.buf_operand src ei ops encoder_start = ((),final) /\
  abi_enc_plan (type_env tops) (TupleT (log_non_indexed_types flags fts)) ei /\
  vyper_to_abi (type_env tops) (TupleT (log_non_indexed_types flags fts))
    (ArrayV (TupleV (select_log_args F flags values))) = SOME av /\
  log_args_rel args atvs values ss /\
  log_args_safe args atvs ss (w2n root_addr)
    (type_memory_size (TupleTV (select_log_args F flags ftvs))) /\
  log_args_avoid args (compiler_var_names cs.cs_next_var (packed_cut.cs_next_var - cs.cs_next_var)) /\
  w2n root_addr + type_memory_size (TupleTV (select_log_args F flags ftvs)) < dimword(:256) /\
  EVERY (log_abi_old_operand cs) (src::ops) /\
  eval_operand src ss = SOME root_addr /\ eval_operands ops ss = SOME ws /\
  LENGTH ops < dimword(:256) /\
  log_packing_resources packed_cut encoder_start encoder_end capacity lo top
    (TupleTV (select_log_args F flags ftvs)) (w2n root_addr)
    (LENGTH (enc (vyper_to_abi_type (type_env tops)
      (TupleT (log_non_indexed_types flags fts))) av)) ss ==>
  frag_exec ctx cs final (\s. s = ss)
    (\s. ?packed. copy_state_frame ss packed /\
      (!op. abi_operand_before cs.cs_next_var op ==>
        eval_operand op packed = eval_operand op ss) /\
      log_data_result packed_cut encoder_start encoder_end capacity lo top
        (enc (vyper_to_abi_type (type_env tops)
          (TupleT (log_non_indexed_types flags fts))) av) ws packed s) (\r. F)
Proof
  rpt strip_tac >>
  `abi_operand_before cs.cs_next_var src` by
    (fs[] >> drule_all log_old_operand_before >> simp[]) >>
  `EVERY (\name. src <> Var name)
     (compiler_var_names cs.cs_next_var (packed_cut.cs_next_var - cs.cs_next_var))` by
    (irule abi_operand_before_names >> qexists_tac `cs.cs_next_var` >> simp[]) >>
  drule_all log_data_compile_extends >> strip_tac >>
  `cs_extends cs packed_cut` by
    (drule compile_log_store_data_extends >> simp[]) >>
  simp_tac bool_ss [frag_exec_def] >> qx_gen_tac `func` >> strip_tac >>
  `fn_has_code cs packed_cut func /\ fn_has_code packed_cut final func` by
    (irule fn_has_code_split >> goal_assum (drule_at Any) >> simp[]) >>
  `fn_has_code packed_cut encoder_start func` by
    (mp_tac (Q.SPECL [`packed_cut`,`encoder_start`,`final`,`func`] fn_has_code_split) >>
     simp[]) >>
  mp_tac (Q.SPECL [`tops`,`dep`,`layouts`,`addr`,`art`,`ctx`,`func`,`cenv`,
    `flags`,`fts`,`args`,`ftvs`,`atvs`,`src`,`0`,`cs`,`ret`,`packed_cut`,
    `capacity`,`buf`,`encoder_start`] checked_compile_split_log_data_allocation_boundary) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qspecl_then [`ss`,`values`,`root_addr`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `packed` strip_assume_tac) >>
  RULE_ASSUM_TAC (REWRITE_RULE [ADD_CLAUSES]) >>
  `val_in_memory (TupleTV (select_log_args F flags ftvs))
     (ArrayV (TupleV (select_log_args F flags values)))
     (w2n root_addr) packed.vs_memory` by
    (drule_all memory_tuple_rel_val_in_memory >> simp[]) >>
  `value_has_type (TupleTV (select_log_args F flags ftvs))
     (ArrayV (TupleV (select_log_args F flags values)))` by
    (irule log_packed_tuple_typed >> simp[]) >>
  drule compile_log_store_data_next_var >> strip_tac >>
  `!op. abi_operand_before cs.cs_next_var op ==>
     eval_operand op packed = eval_operand op ss` by
    (mp_tac (Q.SPECL [`cs.cs_next_var`,`cs.cs_next_var`,
       `packed_cut.cs_next_var - cs.cs_next_var`,`ss`,`packed`] abi_operand_before_frame) >>
     simp[]) >>
  suspend "canonical_suffix"
QED

Resume checked_log_data_frag[canonical_suffix]:
  `eval_operand src packed = SOME root_addr` by simp[] >>
  `EVERY (abi_operand_before cs.cs_next_var) ops` by
    (fs[EVERY_MEM] >> rpt strip_tac >> drule_all log_old_operand_before >> simp[]) >>
  `eval_operands ops packed = SOME ws` by
    (drule_all eval_operands_before_frame >> simp[]) >>
  `EVERY (log_abi_old_operand packed_cut) (src::ops)` by
    (fs[EVERY_MEM] >> rpt strip_tac >> irule log_old_operand_mono >>
     qexists_tac `cs` >> simp[]) >>
  `log_packing_resources packed_cut encoder_start encoder_end capacity lo top
     (TupleTV (select_log_args F flags ftvs)) (w2n root_addr)
     (LENGTH (enc (vyper_to_abi_type (type_env tops)
       (TupleT (log_non_indexed_types flags fts))) av)) packed` by
    (drule_all log_packing_resources_copy_frame >> simp[]) >>
  `type_memory_size (TupleTV (select_log_args F flags ftvs)) < dimword(:256)` by decide_tac >>
  drule_all log_selected_tuple_type >> strip_tac >>
  drule_all log_data_allocate_emit_frag >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule_all log_packing_path_frag >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  qexists_tac `out` >> simp[] >> conj_tac
  >- (qexists_tac `packed` >> fs[]) >>
  qx_gen_tac `fuel` >> strip_tac >>
  qpat_x_assum `!fuel r. run_from fuel ctx func out = r /\ _ ==> _`
    (qspecl_then [`fuel`,`run_from fuel ctx func out`] mp_tac) >> simp[]
QED

Finalise checked_log_data_frag

(* Public observations of the whole seam are expressed at the original
   source state, not an encoder-internal or native path state. *)
Theorem log_data_result_logs:
  copy_state_frame before packed /\
  log_data_result packed_cut encoder_start encoder_end capacity lo top bytes ws packed out ==>
  out.vs_logs = before.vs_logs ++
    [<|logger := w2w before.vs_call_ctx.cc_address; topics := ws; data := bytes|>] /\
  out.vs_call_ctx = before.vs_call_ctx /\
  out.vs_data_section = before.vs_data_section /\ alloca_inv out
Proof
  strip_tac >> drule copy_state_frame_external >> strip_tac >>
  drule abi_state_frame_observables >> strip_tac >>
  drule abi_state_frame_source_fields >> strip_tac >>
  fs[log_data_result_def, log_packing_public_frame_def] >> metis_tac[]
QED
