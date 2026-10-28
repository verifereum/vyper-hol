(* TOP-LEVEL: invoke an arbitrary recursive encoder after the real dynamic
   child prefix. This consumes the native induction assertion and derives
   the actual child result, rather than accepting an execution contract. *)
Theory abiNativeDynamicInner
Ancestors
  abiNativeEncodingDefs abiNativeDynamicEntry abiNativeResources abiMemoryChildEntry
  abiChildCode compileEnv venomState valueEncoding list words arithmetic

Theorem abi_native_dynamic_inner:
  !info span reference payload ctx func dst src dyn_ptr head_offset cs ret mid after ss
      dst_addr src_addr dyn_addr source_id target_id.
    abi_native_encoder info (w2n src_addr) span reference payload /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 2)) src info
      (abi_child_prefix_cut dst dyn_ptr head_offset cs) = (ret,mid) /\
    fn_has_code (abi_child_prefix_cut dst dyn_ptr head_offset cs) mid func /\
    cs_extends mid after /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand src ss = SOME src_addr /\ abi_operand_before cs.cs_next_var src /\
    abi_native_memory_ready func cs after source_id target_id src_addr span
      (dst_addr + mload (w2n dyn_addr) ss) payload ss /\
    mem_bytes_at (w2n src_addr) span reference = mem_bytes_at (w2n src_addr) span ss.vs_memory ==>
    ?out. abi_native_encoding_result ctx func (abi_child_prefix_cut dst dyn_ptr head_offset cs) mid ret
      (dst_addr + mload (w2n dyn_addr) ss) payload
      (abi_child_entry_state cs head_offset dst_addr dyn_addr ss) out
Proof
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  qspecl_then [`cs`, `head_offset`, `dst_addr`, `dyn_addr`, `ss`, `src`, `src_addr`]
    mp_tac abi_native_dynamic_entry_inputs >> impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`func`, `cs`, `after`, `source_id`, `target_id`, `src_addr`, `span`,
    `dst_addr + mload (w2n dyn_addr) ss`, `payload`, `ss`, `mid`, `dst`, `dyn_ptr`,
    `head_offset`, `dst_addr`, `dyn_addr`] mp_tac abi_native_dynamic_entry_ready >>
  impl_tac >- simp[] >> DISCH_TAC >>
  `(abi_child_entry_state cs head_offset dst_addr dyn_addr ss).vs_inst_idx =
    LENGTH (abi_child_prefix_cut dst dyn_ptr head_offset cs).cs_current_insts` by
    simp[abi_child_entry_state_def, abi_child_prefix_cut_def, abi_child_prefix_insts_def] >>
  qpat_x_assum `abi_native_encoder _ _ _ _ _`
    (mp_tac o PURE_REWRITE_RULE [abi_native_encoder_def]) >>
  disch_then (qspecl_then [`ctx`, `func`, `Var (compiler_var_name cs.cs_next_var 2)`, `src`,
    `abi_child_prefix_cut dst dyn_ptr head_offset cs`, `ret`, `mid`,
    `abi_child_entry_state cs head_offset dst_addr dyn_addr ss`, `src_addr`,
    `dst_addr + mload (w2n dyn_addr) ss`, `source_id`, `target_id`] mp_tac) >>
  impl_tac >- simp[abi_child_prefix_cut_def, abi_child_entry_frame] >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native dynamic recursive invocation: " ^ name)
  end) (DB.thms "abiNativeDynamicInner")
