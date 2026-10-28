(* TOP-LEVEL: an actual final LOG consumes a completed native encoding and
   preserves its scratch profile, allocation trace and caller memory frame. *)
Theory abiNativeLogEmit
Ancestors
  abiNativeEncodingDefs abiMemoryLeafRun abiNativeArrayFrames abiLogEmit abiLogReady
  abiAllocationTrace abiAllocationWindows abiAllocatorState abiMemoryFrame abiStateFrame
  abiFieldOperands compileAllocaProvenance compileEnv fragExec fragBlockPath
  venomState list words

Theorem abi_native_encoding_LOG_path:
  !ctx func cs mid cs' size_op dst dst_addr payload topic_ops topics before encoded.
    abi_native_encoding_result ctx func cs mid size_op dst_addr payload before encoded /\
    emit_inst LOG (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [size_op;dst]) [] mid = ((),cs') /\
    fn_has_code mid cs' func /\ LENGTH topic_ops < dimword (:256) /\ LENGTH payload < dimword (:256) /\
    EVERY (abi_operand_before cs.cs_next_var) topic_ops /\ eval_operands topic_ops before = SOME topics /\
    abi_operand_before cs.cs_next_var dst /\ eval_operand dst before = SOME dst_addr /\ ~before.vs_halted ==>
    ?out. fragment_path ctx func before out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      out.vs_logs = before.vs_logs ++ [<|logger := w2w before.vs_call_ctx.cc_address;
        topics := topics; data := payload|>] /\
      read_memory (w2n dst_addr) (LENGTH payload) out = payload /\
      abi_memory_frame ((w2n dst_addr,LENGTH payload)::
        abi_allocation_windows (compiler_alloca_ids cs mid) out) before out /\
      abi_allocation_trace 32 (compiler_alloca_ids cs mid) before out /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op before) /\
      abi_state_frame before (out with vs_logs := before.vs_logs)
Proof
  rpt gen_tac >> strip_tac >>
  `~encoded.vs_halted` by (drule_all abi_native_encoding_not_halted >> simp[]) >>
  qpat_x_assum `abi_native_encoding_result _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_encoding_result_def, abi_encoding_result_def]) >>
  `eval_operands topic_ops encoded = SOME topics` by
    (qspecl_then [`topic_ops`, `cs.cs_next_var`, `before`, `encoded`]
       mp_tac eval_operands_before_frame >> simp[]) >>
  `eval_operand dst encoded = SOME dst_addr` by fs[] >>
  qspecl_then [`ctx`, `func`, `mid`, `cs'`, `topic_ops`, `topics`, `dst`, `size_op`,
    `dst_addr`, `n2w (LENGTH payload):bytes32`, `encoded`] mp_tac emit_inst_LOG_path >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  `abi_allocator_state out = abi_allocator_state encoded` by
    (qpat_assum `out with vs_logs := encoded.vs_logs = _`
       (mp_tac o AP_TERM ``abi_allocator_state``) >> simp[abi_allocator_state_def]) >>
  `abi_allocation_windows (compiler_alloca_ids cs mid) out =
   abi_allocation_windows (compiler_alloca_ids cs mid) encoded` by
    (qspecl_then [`compiler_alloca_ids cs mid`, `encoded`, `out`]
       mp_tac abi_allocation_windows_allocator_state >> simp[]) >>
  `abi_allocation_trace 32 (compiler_alloca_ids cs mid) before out` by
    (qspecl_then [`32`, `compiler_alloca_ids cs mid`, `before`, `encoded`, `before`, `out`]
       mp_tac abi_allocation_trace_fields >> simp[]) >>
  `abi_memory_frame ((w2n dst_addr,LENGTH payload)::
     abi_allocation_windows (compiler_alloca_ids cs mid) out) before out` by
    (qpat_assum `abi_allocation_windows _ out = _` (fn th => PURE_REWRITE_TAC [th]) >>
     qspecl_then [`(w2n dst_addr,LENGTH payload)::abi_allocation_windows (compiler_alloca_ids cs mid) encoded`,
       `before`, `out`, `encoded`] mp_tac abi_memory_frame_memory_eq >> simp[]) >>
  `abi_state_frame before (out with vs_logs := before.vs_logs)` by
    (irule abi_state_frame_log_image >> qexistsl_tac [`encoded`, `LENGTH cs'.cs_current_insts`] >> simp[]) >>
  `read_memory (w2n dst_addr) (LENGTH payload) out = payload` by
    (qpat_x_assum `read_memory _ _ encoded = _` mp_tac >> simp[read_memory_def]) >>
  `fragment_path ctx func before out` by
    (irule fragment_path_trans >> qexists_tac `encoded` >> simp[]) >>
  qspecl_then [`before`, `encoded`] mp_tac abi_state_frame_observables >>
  impl_tac >- simp[] >> strip_tac >> qexists_tac `out` >> fs[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native encoded LOG execution: " ^ name)
  end) (DB.thms "abiNativeLogEmit")
