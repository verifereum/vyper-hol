(* TOP-LEVEL: actual static ABI encoder paths write the checked source bytes
   and return their exact encoded size. Word encoding permits repeated SSA
   outputs; only the destination must avoid the overwritten temporary. *)
Theory memoryValueAbiExec
Ancestors
  memoryValueAbiStatic memoryValueDefs valueEncoding valueEncodingProps valueEncodingProofs
  memoryReadProps abiEncoderPathProps ssaOperandFrame fragBlockPath fragExec
  abiEncoder compileEnv exprLoweringProps emitHelperProps instIdxIndep
  vyperABI vyperTyping contractABI venomState venomExecSemantics venomMemProps
  list words arithmetic

Theorem read_memory_inst_idx:
  !offset byte_count ss index.
    read_memory offset byte_count (ss with vs_inst_idx := index) =
      read_memory offset byte_count ss
Proof
  simp[read_memory_def]
QED

Theorem abi_memory_write_control[simp]:
  (!dst src byte_count ss.
    (mcopy dst src byte_count ss).vs_current_bb = ss.vs_current_bb /\
    (mcopy dst src byte_count ss).vs_halted = ss.vs_halted) /\
  (!dst value ss.
    (mstore dst value ss).vs_current_bb = ss.vs_current_bb /\
    (mstore dst value ss).vs_halted = ss.vs_halted) /\
  (!name value ss.
    (update_var name value ss).vs_current_bb = ss.vs_current_bb /\
    (update_var name value ss).vs_halted = ss.vs_halted)
Proof
  simp[mcopy_def, mstore_def, write_memory_with_expansion_def, update_var_def]
QED

Theorem read_memory_static_abi:
  !env ty tv v av offset ss.
    evaluate_type env ty = SOME tv /\
    memory_value_rel tv v offset ss.vs_memory /\ value_has_type tv v /\
    vyper_to_abi env ty v = SOME av /\ ~is_dynamic (vyper_to_abi_type env ty) ==>
    read_memory offset (type_memory_size tv) ss = enc (vyper_to_abi_type env ty) av /\
    LENGTH (enc (vyper_to_abi_type env ty) av) = type_memory_size tv
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`env`, `ty`, `tv`, `v`, `av`, `offset`, `ss.vs_memory`]
    memory_value_rel_static_abi) >> impl_tac >- fs[] >> DISCH_TAC >> conj_tac
  >- fs[read_memory_eq_mem_bytes_at] >>
  qpat_x_assum `mem_bytes_at _ _ _ = enc _ _`
    (mp_tac o AP_TERM ``LENGTH : byte list -> num``) >> simp[LENGTH_mem_bytes_at]
QED

Theorem compile_abi_copy_source_path:
  !ctx func env ty tv v av dst src cs op cs' ss dst_addr src_addr.
    evaluate_type env ty = SOME tv /\
    memory_value_rel tv v (w2n src_addr) ss.vs_memory /\ value_has_type tv v /\
    vyper_to_abi env ty v = SOME av /\ ~is_dynamic (vyper_to_abi_type env ty) /\
    compile_abi_encode_to_buf dst src (AbiCopy (type_memory_size tv)) cs = (op,cs') /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    type_memory_size tv < dimword(:256) /\ fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\
      out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ out.vs_halted = ss.vs_halted /\
      eval_operand op out = SOME (n2w (LENGTH (enc (vyper_to_abi_type env ty) av))) /\
      read_memory (w2n dst_addr) (LENGTH (enc (vyper_to_abi_type env ty) av)) out =
        enc (vyper_to_abi_type env ty) av /\
      (fresh_vars_wrt cs' out = fresh_vars_wrt cs ss) /\
      (!arg_op. eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt strip_tac >> drule_all read_memory_static_abi >> strip_tac >>
  drule_all compile_abi_copy_path >> strip_tac >>
  drule_all compile_abi_copy_execution >> strip_tac >>
  qexists_tac `(mcopy (w2n (dst_addr:bytes32)) (w2n (src_addr:bytes32)) (type_memory_size tv) ss)
    with vs_inst_idx := LENGTH cs'.cs_current_insts` >>
  fs[same_blocks_def, read_memory_inst_idx, read_memory_mcopy_self,
    eval_op_inst_idx, eval_operand_mcopy_eq] >> gvs[]
QED

Theorem compile_abi_word_source_path:
  !ctx func env ty tv v av dst src cs op cs' ss dst_addr src_addr.
    evaluate_type env ty = SOME tv /\
    memory_value_rel tv v (w2n src_addr) ss.vs_memory /\ value_has_type tv v /\
    vyper_to_abi env ty v = SOME av /\ ~is_dynamic (vyper_to_abi_type env ty) /\
    type_memory_size tv = 32 /\ compile_abi_encode_static dst src cs = (op,cs') /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    dst <> Var (STRING #"%" (toString cs.cs_next_var)) /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\
      out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ out.vs_halted = ss.vs_halted /\
      eval_operand op out = SOME (n2w (LENGTH (enc (vyper_to_abi_type env ty) av))) /\
      read_memory (w2n dst_addr) (LENGTH (enc (vyper_to_abi_type env ty) av)) out =
        enc (vyper_to_abi_type env ty) av /\
      (!arg_op. arg_op <> Var (STRING #"%" (toString cs.cs_next_var)) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt strip_tac >> drule_all read_memory_static_abi >> strip_tac >>
  drule_all compile_abi_encode_static_path >> DISCH_TAC >>
  drule compile_abi_encode_static_code >> strip_tac >>
  qexists_tac `(mstore (w2n (dst_addr:bytes32)) (mload (w2n (src_addr:bytes32)) ss)
    (update_var (STRING #"%" (toString cs.cs_next_var)) (mload (w2n (src_addr:bytes32)) ss) ss))
      with vs_inst_idx := LENGTH cs'.cs_current_insts` >>
  fs[same_blocks_def, read_memory_inst_idx, read_memory_word,
    mload_mstore_same, eval_op_inst_idx, eval_operand_mstore_eq,
    eval_operand_update_var_avoids, eval_operand_lit] >> gvs[] >>
  qpat_x_assum `read_memory _ 32 ss = enc _ _` mp_tac >> simp[read_memory_word]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed source ABI execution theorem: " ^ name)
  end) (DB.thms "memoryValueAbiExec")
