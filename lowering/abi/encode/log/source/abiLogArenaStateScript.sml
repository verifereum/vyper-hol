(* TOP-LEVEL: the real Log data-arena allocation preserves source state,
   live locals and evaluated arguments, and establishes private packing
   storage using the emitted allocation's identity, including cached slots. *)
Theory abiLogArenaState
Ancestors
  sourceBufferFrames sourceMemoryFrames sourceValueFrames
  localPtrsProps typedLogStoreCode abiStaticLoopCode
  abiLogDataAllocation abiBufferAllocationCode abiBufferAllocationPath
  allocationPathGrowth allocationGrowth abiAllocatedWindows abiAllocationFrame
  typedLogArgs abiStateFrame abiFieldOperands memoryValueSnapshot
  memoryValueDefs valueEncoding context compileEnv fragExec fragBlockPath
  venomMemDefs venomState venomInst list words arithmetic

Theorem compile_log_arena_source_state:
  !ctx func cenv cx es ss capacity cs buf cut args atvs values ftv topic_ops topics.
    state_rel cenv cx es ss /\ local_ptrs_rel func cenv es.scopes ss /\
    alloca_inv ss /\ fn_inst_ids_distinct func /\
    compile_alloc_buffer capacity cs = (buf,cut) /\ fn_has_code cs cut func /\
    abi_alloca_request_ok cs.cs_next_id capacity ss /\ ss.vs_alloca_next + capacity < dimword(:256) /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before cs.cs_next_var (Var p)) /\
    (!name entry offset region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (MemLoc offset region_size) ==>
      offset + type_memory_size entry.type <= w2n (memory_snapshot_addr cs.cs_next_id ss)) /\
    log_args_rel args atvs values ss /\
    log_args_safe args atvs ss (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size ftv) /\
    EVERY (\arg. abi_operand_before cs.cs_next_var (FST arg)) args /\
    EVERY (abi_operand_before cs.cs_next_var) topic_ops /\ eval_operands topic_ops ss = SOME topics /\
    type_memory_size ftv <= capacity /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    ?out. fragment_path ctx func ss out /\
      out = (memory_snapshot_allocated cs.cs_next_id cs.cs_next_var capacity ss
        with vs_inst_idx := LENGTH cut.cs_current_insts) /\
      out.vs_current_bb = cut.cs_current_bb /\ out.vs_inst_idx = LENGTH cut.cs_current_insts /\ ~out.vs_halted /\
      state_rel cenv cx es out /\ local_ptrs_rel func cenv es.scopes out /\
      eval_operand buf.buf_operand out = SOME (memory_snapshot_addr cs.cs_next_id ss) /\
      abi_operand_before cut.cs_next_var buf.buf_operand /\
      abi_allocated_window out cs.cs_next_id (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size ftv) /\
      alloca_inv out /\ out.vs_memory = ss.vs_memory /\
      ss.vs_alloca_next <= out.vs_alloca_next /\ out.vs_alloca_next <= ss.vs_alloca_next + capacity /\
      log_args_rel args atvs values out /\
      log_args_safe args atvs out (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size ftv) /\
      EVERY (abi_operand_before cut.cs_next_var) topic_ops /\ eval_operands topic_ops out = SOME topics /\
      abi_state_frame ss out /\ allocation_growth ss out /\
      source_memory_separated cenv es.scopes out (w2n (memory_snapshot_addr cs.cs_next_id ss)) capacity /\
      source_memory_separated cenv es.scopes out (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size ftv) /\
      cs.cs_next_var <= cut.cs_next_var /\
      (!arg. abi_operand_before cs.cs_next_var arg ==> eval_operand arg out = eval_operand arg ss) /\
      (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
        FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before cut.cs_next_var (Var p))
Proof
  rpt gen_tac >> strip_tac >> `ss.vs_alloca_next < dimword(:256)` by decide_tac >>
  drule compile_alloc_buffer_code >> strip_tac >> `cs.cs_next_var <= cut.cs_next_var` by simp[] >>
  drule_all compile_buffer_source_separated >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `capacity`, `cs`, `buf`, `cut`, `args`, `atvs`, `values`,
    `ftv`, `topic_ops`, `topics`, `ss`] compile_log_data_allocation_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  drule_all fragment_path_allocation_growth >> DISCH_TAC >>
  mp_tac (Q.SPECL [`func`, `cenv`, `cx`, `es`, `ss`, `out`, `cs.cs_next_var`] source_relations_memory_frame) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.SPECL [`cs.cs_next_var`, `cenv`, `es.scopes`, `ss`, `out`] local_pointer_operands_frame) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`cenv`, `es.scopes`, `ss`, `out`, `w2n (memory_snapshot_addr cs.cs_next_id ss)`, `capacity`]
    source_memory_separated_frame) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`cenv`, `es.scopes`, `out`, `w2n (memory_snapshot_addr cs.cs_next_id ss)`, `capacity`,
    `w2n (memory_snapshot_addr cs.cs_next_id ss)`, `type_memory_size ftv`] source_memory_separated_subrange) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`cenv`, `es.scopes`, `cs.cs_next_var`, `cut.cs_next_var`] source_pointer_lifetimes_mono) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qexists_tac `out` >> asm_simp_tac bool_ss [] >>
  qpat_x_assum `!name entry p region_size. _ ==> abi_operand_before cut.cs_next_var (Var p)` mp_tac >>
  asm_simp_tac bool_ss []
QED

Theorem compile_log_buffer_ids_distinct:
  !data_capacity cs data_buf store_cut cenv ops tys field_offset ret packed_cut
    capacity abi_buf encode_cut func.
    compile_alloc_buffer data_capacity cs = (data_buf,store_cut) /\ fn_has_code cs store_cut func /\
    compile_log_store_data cenv ops tys data_buf.buf_operand field_offset store_cut = (ret,packed_cut) /\
    compile_alloc_buffer capacity packed_cut = (abi_buf,encode_cut) /\ fn_has_code packed_cut encode_cut func /\
    fn_inst_ids_distinct func ==> cs.cs_next_id <> packed_cut.cs_next_id
Proof
  rpt gen_tac >> strip_tac >> drule compile_log_store_data_next_var >> DISCH_TAC >>
  mp_tac (Q.SPECL [`data_capacity`, `cs`, `data_buf`, `store_cut`] compile_alloc_buffer_code) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
  `cs.cs_next_var <> packed_cut.cs_next_var` by decide_tac >>
  mp_tac (Q.SPECL [`data_capacity`, `cs`, `data_buf`, `store_cut`, `func`] compile_buffer_allocation_member) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`capacity`, `packed_cut`, `abi_buf`, `encode_cut`, `func`] compile_buffer_allocation_member) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >> CCONTR_TAC >>
  mp_tac (Q.SPECL [`func`,
    `mk_inst cs.cs_next_id ALLOCA [Lit (n2w data_capacity)] [compiler_var_name cs.cs_next_var 0]`,
    `mk_inst packed_cut.cs_next_id ALLOCA [Lit (n2w capacity)] [compiler_var_name packed_cut.cs_next_var 0]`]
    fn_inst_ids_distinct_inj) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[mk_inst_def]]) >>
  disch_then (mp_tac o AP_TERM ``\inst:instruction. inst.inst_outputs``) >>
  simp[mk_inst_def, compiler_var_name_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual Log arena source state: " ^ name)
  end) (DB.thms "abiLogArenaState")
