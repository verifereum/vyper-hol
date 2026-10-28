(* TOP-LEVEL: the real output allocation, arbitrary typed recursive ABI
   encoding and LOG preserve complete source state from before allocation.
   Output and scratch privacy follow from actual compiler provenance and
   the physical bounds of static source locations, including cached slots. *)
Theory abiNativeLogAllocatedState
Ancestors
  abiNativeLogAllocatedPath abiNativeLogState sourceAllocationPrivacy sourceMemoryFrames
  abiBufferAllocationCode abiAllocationBudget abiAllocationTrace abiAllocatedWindows abiMemoryFrame
  allocationGrowth abiStateFrame abiFieldOperands memoryValueSnapshot memoryValueDefs valueEncoding
  compileAllocaProvenance compileIdFlow compileEnv fragExec fragBlockPath
  vyperTypeInvariants vyperState vyperABI vyperValue vyperTyping contractABI venomState list words arithmetic

Theorem compile_abi_native_allocated_log_state:
  !tenv sfields cenv tys tvs values avs ctx func cx es capacity cs buf cut cs' src topic_ops topics ss src_addr span source_id.
    state_well_typed es /\ state_rel_simple cenv cx es ss /\ local_ptrs_rel func cenv es.scopes ss /\
    compile_alloc_buffer capacity cs = (buf,cut) /\
    compile_log_abi_emit buf.buf_operand src (type_to_abi_enc_info sfields cenv (TupleT tys)) topic_ops cut = ((),cs') /\
    fn_has_code cs cut func /\ fn_has_code cut cs' func /\ fn_inst_ids_distinct func /\ compiler_id_history cs /\
    abi_memory_env_rel tenv cenv /\ abi_struct_env_rel tenv sfields /\
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs /\
    values_have_types tvs values /\ vyper_to_abi_list tenv tys values = SOME avs /\
    memory_tuple_rel tvs values (w2n src_addr) ss.vs_memory /\ type_memory_size_list tvs <= span /\
    abi_allocated_window ss source_id (w2n src_addr) span /\
    source_id <> cs.cs_next_id /\ ~MEM source_id (compiler_alloca_ids cut cs') /\
    ~MEM cs.cs_next_id (compiler_alloca_ids cut cs') /\
    32 <= capacity /\ alloca_inv ss /\ abi_alloca_request_ok cs.cs_next_id capacity ss /\
    abi_alloca_budget 32 (compiler_alloca_ids cut cs') ss + capacity < dimword (:256) /\
    (!id. MEM id (compiler_alloca_ids cut cs') ==> abi_alloca_request_ok id 32 ss) /\
    LENGTH (enc (Tuple (MAP (vyper_to_abi_type tenv) tys)) (ListV avs)) <= capacity /\
    source_alloca_floor cenv es.scopes (cs.cs_next_id::compiler_alloca_ids cut cs') ss /\
    (!name entry p region_size. lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) region_size) ==> abi_operand_before cs.cs_next_var (Var p)) /\
    EVERY (abi_operand_before cs.cs_next_var) topic_ops /\ abi_operand_before cs.cs_next_var src /\
    LENGTH topic_ops < dimword (:256) /\ eval_operands topic_ops ss = SOME topics /\ eval_operand src ss = SOME src_addr /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      out.vs_logs = ss.vs_logs ++ [<|logger := w2w ss.vs_call_ctx.cc_address;
        topics := topics; data := enc (Tuple (MAP (vyper_to_abi_type tenv) tys)) (ListV avs)|>] /\
      state_rel_simple cenv cx (es with logs := es.logs ++ [<|logger := w2w ss.vs_call_ctx.cc_address;
        topics := topics; data := enc (Tuple (MAP (vyper_to_abi_type tenv) tys)) (ListV avs)|>]) out /\
      local_ptrs_rel func cenv es.scopes out /\ allocation_growth ss out /\
      read_memory (w2n (memory_snapshot_addr cs.cs_next_id ss))
        (LENGTH (enc (Tuple (MAP (vyper_to_abi_type tenv) tys)) (ListV avs))) out =
        enc (Tuple (MAP (vyper_to_abi_type tenv) tys)) (ListV avs) /\
      abi_allocated_window out cs.cs_next_id (w2n (memory_snapshot_addr cs.cs_next_id ss)) capacity /\
      abi_memory_frame ((w2n (memory_snapshot_addr cs.cs_next_id ss),
        LENGTH (enc (Tuple (MAP (vyper_to_abi_type tenv) tys)) (ListV avs)))::
        abi_allocation_windows (compiler_alloca_ids cut cs') out) ss out /\
      abi_allocation_trace 32 (compiler_alloca_ids cut cs')
        (memory_snapshot_allocated cs.cs_next_id cs.cs_next_var capacity ss) out /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      abi_state_frame ss (out with vs_logs := ss.vs_logs)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`tenv`, `sfields`, `cenv`, `tys`, `tvs`, `values`, `avs`, `ctx`, `func`, `capacity`, `cs`, `buf`, `cut`, `cs'`,
    `src`, `topic_ops`, `topics`, `ss`, `src_addr`, `span`, `source_id`] mp_tac compile_abi_native_allocated_log_path >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> disch_then (qx_choose_then `out` strip_assume_tac) >>
  `ss.vs_alloca_next < dimword (:256)` by
    (qspecl_then [`32`, `compiler_alloca_ids cut cs'`, `ss`] mp_tac abi_alloca_budget_frontier >> decide_tac) >>
  `source_alloca_floor cenv es.scopes (compiler_alloca_ids cut cs') ss` by
    (qspecl_then [`cenv`, `es.scopes`, `compiler_alloca_ids cut cs'`, `cs.cs_next_id::compiler_alloca_ids cut cs'`, `ss`]
       mp_tac source_alloca_floor_subprofile >>
     impl_tac >- (conj_tac >- first_assum MATCH_ACCEPT_TAC >> simp[]) >> DISCH_TAC >> first_assum MATCH_ACCEPT_TAC) >>
  qspecl_then [`func`, `cenv`, `es.scopes`, `ss`, `capacity`, `cs`, `buf`, `cut`,
    `LENGTH (enc (Tuple (MAP (vyper_to_abi_type tenv) tys)) (ListV avs))`, `cs.cs_next_id::compiler_alloca_ids cut cs'`]
    mp_tac compile_buffer_payload_private >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]) >> DISCH_TAC >>
  qspecl_then [`capacity`, `cs`, `buf`, `cut`] mp_tac compile_alloc_buffer_code >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >> `cs.cs_next_var <= cut.cs_next_var` by decide_tac >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `buf.buf_operand`, `src`, `type_to_abi_enc_info sfields cenv (TupleT tys)`,
    `topic_ops`, `topics`, `cut`, `cs'`, `cs.cs_next_var`, `ss`, `out`, `memory_snapshot_addr cs.cs_next_id ss`,
    `enc (Tuple (MAP (vyper_to_abi_type tenv) tys)) (ListV avs)`] mp_tac native_log_source_state_frame >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qexists_tac `out` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual allocated recursive Log source state: " ^ name)
  end) (DB.thms "abiNativeLogAllocatedState")
