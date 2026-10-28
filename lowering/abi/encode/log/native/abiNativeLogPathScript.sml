(* TOP-LEVEL: actual ABI encoding followed by LOG, for arbitrary recursive
   source encodings and actual compiler scratch profiles. The typed tuple
   corollary supplies the complete non-indexed event payload. *)
Theory abiNativeLogPath
Ancestors
  abiNativeLogCode abiNativeLogEmit abiNativeEncodingDefs abiMemoryTypedTuple abiMemoryTypedMetadata
  abiLogCode abiAllocationTrace abiAllocationWindows abiMemoryFrame abiStateFrame abiFieldOperands
  compileAllocaProvenance compileEnv fragExec fragBlockPath venomState
  valueEncoding vyperABI vyperValue vyperTyping contractABI list words arithmetic

Theorem compile_abi_native_log_path:
  !ctx func dst src info topic_ops topics cs cs' ss dst_addr src_addr span source_id target_id payload.
    abi_native_encoder info (w2n src_addr) span ss.vs_memory payload /\
    compile_log_abi_emit dst src info topic_ops cs = ((),cs') /\ fn_has_code cs cs' func /\
    abi_native_memory_ready func cs cs' source_id target_id src_addr span dst_addr payload ss /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var src /\
    EVERY (abi_operand_before cs.cs_next_var) topic_ops /\
    eval_operands topic_ops ss = SOME topics /\ LENGTH topic_ops < dimword (:256) ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      out.vs_logs = ss.vs_logs ++ [<|logger := w2w ss.vs_call_ctx.cc_address;
        topics := topics; data := payload|>] /\
      read_memory (w2n dst_addr) (LENGTH payload) out = payload /\
      abi_memory_frame ((w2n dst_addr,LENGTH payload)::
        abi_allocation_windows (compiler_alloca_ids cs cs') out) ss out /\
      abi_allocation_trace 32 (compiler_alloca_ids cs cs') ss out /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      abi_state_frame ss (out with vs_logs := ss.vs_logs)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_log_abi_emit _ _ _ _ _ = _`
    (mp_tac o ONCE_REWRITE_RULE [compile_log_abi_emit_split]) >>
  disch_then (qx_choose_then `size_op` (qx_choose_then `mid` strip_assume_tac)) >>
  drule_all compile_log_abi_emit_code >> strip_tac >>
  `compiler_alloca_ids cs cs' = compiler_alloca_ids cs mid` by
    (qspecl_then [`cs`, `mid`, `cs'`,
       `Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [size_op;dst]`, `[]`]
       mp_tac compiler_alloca_ids_emit_LOG >> simp[]) >>
  `abi_native_memory_ready func cs mid source_id target_id src_addr span dst_addr payload ss` by
    fs[abi_native_memory_ready_def] >>
  qspecl_then [`func`, `cs`, `mid`, `source_id`, `target_id`, `src_addr`, `span`, `dst_addr`, `payload`, `ss`]
    mp_tac abi_native_memory_bounds >> impl_tac >- simp[] >> strip_tac >>
  `LENGTH payload < dimword (:256)` by decide_tac >>
  qpat_x_assum `abi_native_encoder _ _ _ _ _` (mp_tac o REWRITE_RULE [abi_native_encoder_def]) >>
  disch_then (qspecl_then [`ctx`, `func`, `dst`, `src`, `cs`, `size_op`, `mid`, `ss`,
    `src_addr`, `dst_addr`, `source_id`, `target_id`] mp_tac) >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `encoded` ASSUME_TAC) >>
  qspecl_then [`ctx`, `func`, `cs`, `mid`, `cs'`, `size_op`, `dst`, `dst_addr`, `payload`,
    `topic_ops`, `topics`, `ss`, `encoded`] mp_tac abi_native_encoding_LOG_path >>
  impl_tac >- simp[] >> asm_simp_tac bool_ss []
QED

Theorem compile_abi_typed_tuple_log_path:
  !env sfields cenv tys tvs vs avs ctx func dst src topic_ops topics cs cs' ss dst_addr src_addr span source_id target_id.
    abi_memory_env_rel env cenv /\ abi_struct_env_rel env sfields /\
    LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs /\
    memory_tuple_rel tvs vs (w2n src_addr) ss.vs_memory /\ values_have_types tvs vs /\
    vyper_to_abi_list env tys vs = SOME avs /\ type_memory_size_list tvs <= span /\
    compile_log_abi_emit dst src (type_to_abi_enc_info sfields cenv (TupleT tys)) topic_ops cs = ((),cs') /\
    fn_has_code cs cs' func /\
    abi_native_memory_ready func cs cs' source_id target_id src_addr span dst_addr
      (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)) ss /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var src /\
    EVERY (abi_operand_before cs.cs_next_var) topic_ops /\
    eval_operands topic_ops ss = SOME topics /\ LENGTH topic_ops < dimword (:256) ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      out.vs_logs = ss.vs_logs ++ [<|logger := w2w ss.vs_call_ctx.cc_address;
        topics := topics; data := enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)|>] /\
      read_memory (w2n dst_addr) (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs))) out =
        enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs) /\
      abi_memory_frame ((w2n dst_addr,LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)))::
        abi_allocation_windows (compiler_alloca_ids cs cs') out) ss out /\
      abi_allocation_trace 32 (compiler_alloca_ids cs cs') ss out /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      abi_state_frame ss (out with vs_logs := ss.vs_logs)
Proof
  rpt gen_tac >> strip_tac >>
  `abi_native_encoder (type_to_abi_enc_info sfields cenv (TupleT tys)) (w2n src_addr) span ss.vs_memory
     (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs))` by
    (qspecl_then [`env`, `sfields`, `cenv`, `tys`, `tvs`, `vs`, `avs`, `w2n src_addr`, `span`, `ss.vs_memory`]
       mp_tac abi_native_typed_tuple >> simp[]) >>
  qspecl_then [`ctx`, `func`, `dst`, `src`, `type_to_abi_enc_info sfields cenv (TupleT tys)`,
    `topic_ops`, `topics`, `cs`, `cs'`, `ss`, `dst_addr`, `src_addr`, `span`, `source_id`, `target_id`,
    `enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)`] mp_tac compile_abi_native_log_path >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed general native ABI tuple LOG path: " ^ name)
  end) (DB.thms "abiNativeLogPath")
