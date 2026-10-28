(* TOP-LEVEL: execute the real output allocation, arbitrary recursive tuple
   encoding and LOG from complete packed source memory. Encoder readiness
   and its runtime cut state are derived from the allocation execution. *)
Theory abiNativeLogAllocatedPath
Ancestors
  abiNativeLogAllocationReady abiNativeLogPath abiNativeEncodingDefs abiMemoryTypedMetadata
  abiBufferAllocationPath abiBufferAllocationCode abiLogAllocationReady abiLogAllocationFrame
  abiAllocationBudget abiAllocationTrace abiAllocationTraceOwned abiAllocatedWindows abiAllocatorState abiMemoryFrame
  abiStateFrame abiFieldOperands abiFlatRun memoryValueSnapshot memoryValueDefs valueEncoding
  compileAllocaProvenance compileIdFlow context compileEnv fragExec fragBlockPath
  vyperABI vyperValue vyperTyping contractABI venomState list words arithmetic

Theorem compile_abi_native_allocated_log_path:
  !tenv sfields cenv tys tvs vs avs ctx func capacity cs buf cut cs' src topic_ops topics ss src_addr span source_id.
    compile_alloc_buffer capacity cs = (buf,cut) /\
    compile_log_abi_emit buf.buf_operand src (type_to_abi_enc_info sfields cenv (TupleT tys)) topic_ops cut = ((),cs') /\
    fn_has_code cs cut func /\ fn_has_code cut cs' func /\ fn_inst_ids_distinct func /\ compiler_id_history cs /\
    abi_memory_env_rel tenv cenv /\ abi_struct_env_rel tenv sfields /\
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs /\
    values_have_types tvs vs /\ vyper_to_abi_list tenv tys vs = SOME avs /\
    memory_tuple_rel tvs vs (w2n src_addr) ss.vs_memory /\ type_memory_size_list tvs <= span /\
    abi_allocated_window ss source_id (w2n src_addr) span /\
    source_id <> cs.cs_next_id /\ ~MEM source_id (compiler_alloca_ids cut cs') /\
    ~MEM cs.cs_next_id (compiler_alloca_ids cut cs') /\
    32 <= capacity /\ alloca_inv ss /\ abi_alloca_request_ok cs.cs_next_id capacity ss /\
    abi_alloca_budget 32 (compiler_alloca_ids cut cs') ss + capacity < dimword (:256) /\
    (!id. MEM id (compiler_alloca_ids cut cs') ==> abi_alloca_request_ok id 32 ss) /\
    LENGTH (enc (Tuple (MAP (vyper_to_abi_type tenv) tys)) (ListV avs)) <= capacity /\
    EVERY (abi_operand_before cs.cs_next_var) topic_ops /\ abi_operand_before cs.cs_next_var src /\
    LENGTH topic_ops < dimword (:256) /\ eval_operands topic_ops ss = SOME topics /\ eval_operand src ss = SOME src_addr /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      out.vs_logs = ss.vs_logs ++ [<|logger := w2w ss.vs_call_ctx.cc_address;
        topics := topics; data := enc (Tuple (MAP (vyper_to_abi_type tenv) tys)) (ListV avs)|>] /\
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
  `ss.vs_alloca_next + capacity < dimword (:256)` by
    (qspecl_then [`32`, `compiler_alloca_ids cut cs'`, `ss`] mp_tac abi_alloca_budget_frontier >> decide_tac) >>
  qspecl_then [`ctx`, `func`, `capacity`, `cs`, `buf`, `cut`, `ss`] mp_tac compile_alloc_buffer_path >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `middle` strip_assume_tac) >>
  `abi_allocated_window middle source_id (w2n src_addr) span` by
    (qpat_x_assum `!id offset count. abi_allocated_window ss _ _ _ ==> _` irule >> simp[]) >>
  `abi_native_memory_ready func cut cs' source_id cs.cs_next_id src_addr span
     (memory_snapshot_addr cs.cs_next_id ss) (enc (Tuple (MAP (vyper_to_abi_type tenv) tys)) (ListV avs)) middle` by
    (qspecl_then [`func`, `cs`, `cut`, `cs'`, `buf`, `capacity`, `ss`, `middle`, `source_id`, `src_addr`, `span`,
       `enc (Tuple (MAP (vyper_to_abi_type tenv) tys)) (ListV avs)`]
       mp_tac abi_native_log_output_allocation_ready >> simp[]) >>
  qspecl_then [`capacity`, `cs`, `cut`, `buf`, `ss`, `middle`, `src`, `topic_ops`, `topics`, `src_addr`, `tvs`, `vs`]
    mp_tac abi_log_allocation_args >> impl_tac >- simp[] >> strip_tac >>
  `abi_allocator_state middle = abi_allocator_state (memory_snapshot_allocated cs.cs_next_id cs.cs_next_var capacity ss)` by
    simp[abi_allocator_state_def] >>
  qpat_x_assum `middle = _` (K ALL_TAC) >>
  qspecl_then [`ss`, `middle`] mp_tac abi_state_frame_observables >> impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`tenv`, `sfields`, `cenv`, `tys`, `tvs`, `vs`, `avs`, `ctx`, `func`, `buf.buf_operand`, `src`,
    `topic_ops`, `topics`, `cut`, `cs'`, `middle`, `memory_snapshot_addr cs.cs_next_id ss`, `src_addr`, `span`,
    `source_id`, `cs.cs_next_id`] mp_tac compile_abi_typed_tuple_log_path >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `out` strip_assume_tac) >>
  drule compile_alloc_buffer_code >> strip_tac >>
  `!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss` by
    (qspecl_then [`cs.cs_next_var`, `cut.cs_next_var`, `ss`, `middle`, `out`]
       mp_tac abi_operand_before_frame_trans >> impl_tac >- (simp[] >> decide_tac) >> simp[]) >>
  `abi_state_frame ss (out with vs_logs := ss.vs_logs)` by
    (qspecl_then [`ss`, `middle`, `out`] mp_tac abi_log_allocation_state_frame >> simp[]) >>
  `abi_allocation_trace 32 (compiler_alloca_ids cut cs')
     (memory_snapshot_allocated cs.cs_next_id cs.cs_next_var capacity ss) out` by
    (qspecl_then [`32`, `compiler_alloca_ids cut cs'`, `middle`, `out`,
       `memory_snapshot_allocated cs.cs_next_id cs.cs_next_var capacity ss`, `out`]
       mp_tac abi_allocation_trace_fields >> simp[]) >>
  `fragment_path ctx func ss out` by (irule fragment_path_trans >> qexists_tac `middle` >> simp[]) >>
  `abi_allocated_window out cs.cs_next_id (w2n (memory_snapshot_addr cs.cs_next_id ss)) capacity` by
    (qspecl_then [`32`, `compiler_alloca_ids cut cs'`, `middle`, `out`, `cs.cs_next_id`,
       `w2n (memory_snapshot_addr cs.cs_next_id ss)`, `capacity`] mp_tac abi_allocation_trace_owned >> simp[]) >>
  qexists_tac `out` >> fs[abi_memory_frame_def, read_memory_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed allocated general native Log path: " ^ name)
  end) (DB.thms "abiNativeLogAllocatedPath")
