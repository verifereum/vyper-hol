(* TOP-LEVEL: a concrete static field prepares the following bytestring
   field from original source observations and pure output geometry. *)
Theory abiStaticBytesReady
Ancestors
  abiStaticFieldStep abiBytesFieldReady abiFieldOperands abiFieldLayoutDefs
  abiBytesFieldPre abiFieldMemory abiMemoryFrame abiStaticLoopCode
  abiBytestringCorrect contractABI compileEnv fragExec fragBlockPath venomState list pair words arithmetic

Definition abi_static_bytes_pre_def:
  abi_static_bytes_pre fields tail_offset dst_addr dyn_addr root_addr source_offset mem_size payload bs ss <=>
    abi_static_field_pre fields tail_offset dst_addr dyn_addr (root_addr + n2w source_offset) payload ss /\
    mload (w2n dyn_addr) ss = n2w (tail_offset + abi_field_tail_size fields) /\
    bytestring_abi_pre (dst_addr + n2w (tail_offset + abi_field_tail_size fields))
      (root_addr + n2w (source_offset + mem_size)) bs ss /\
    abi_bytes_field_geometry (fields ++ [(F,payload)]) tail_offset dst_addr dyn_addr bs /\
    abi_window_separated (w2n (root_addr + n2w (source_offset + mem_size))) (32 + LENGTH bs)
      (w2n (dst_addr + n2w (abi_field_head_size fields))) (LENGTH payload)
End

Theorem compile_abi_static_before_bytes:
  !ctx func dst src info payload dyn_ptr mem_size cap byte_mem_size rest source_offset cs ret cs'
      ss dst_addr dyn_addr root_addr fields tail_offset bs.
    ((info = AbiPrimWord /\ LENGTH payload = 32) \/ info = AbiCopy (LENGTH payload) \/
      (info = AbiComplex [] /\ LENGTH payload = 0)) /\
    compile_abi_encode_complex_elems dst src
      ((info,LENGTH payload,mem_size,F)::(AbiBytestring cap,32,byte_mem_size,T)::rest)
      source_offset (abi_field_head_size fields) dyn_ptr cs = (ret,cs') /\ fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME root_addr /\
    eval_operand dyn_ptr ss = SOME dyn_addr /\
    abi_operand_before cs.cs_next_var src /\ abi_operand_before cs.cs_next_var dst /\
    abi_operand_before cs.cs_next_var dyn_ptr /\
    abi_static_bytes_pre fields tail_offset dst_addr dyn_addr root_addr source_offset mem_size payload bs ss ==>
    ?mid out.
      compile_abi_encode_complex_elems dst src ((AbiBytestring cap,32,byte_mem_size,T)::rest)
        (source_offset + mem_size) (abi_field_head_size fields + LENGTH payload) dyn_ptr mid = (ret,cs') /\
      fn_has_code mid cs' func /\ cs.cs_next_var <= mid.cs_next_var /\
      fragment_path ctx func ss out /\
      out.vs_current_bb = mid.cs_current_bb /\ out.vs_inst_idx = LENGTH mid.cs_current_insts /\ ~out.vs_halted /\
      eval_operand dst out = SOME dst_addr /\ eval_operand src out = SOME root_addr /\
      eval_operand dyn_ptr out = SOME dyn_addr /\
      abi_bytes_field_pre (fields ++ [(F,payload)]) tail_offset dst_addr dyn_addr
        (root_addr + n2w (source_offset + mem_size)) bs out /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      abi_memory_frame [(w2n (dst_addr + n2w (abi_field_head_size fields)),LENGTH payload)] ss out
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qpat_x_assum `abi_static_bytes_pre _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_static_bytes_pre_def]) >>
  mp_tac (Q.SPECL [`cs.cs_next_var`, `cs.cs_next_var`, `src`, `dst`, `dyn_ptr`,
    `(if info = AbiPrimWord then 2 else 1) + 1`] abi_field_operands_names) >>
  impl_tac >- simp[] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `info`, `payload`, `dyn_ptr`, `mem_size`,
    `(AbiBytestring cap,32,byte_mem_size,T)::rest`, `source_offset`, `cs`, `ret`, `cs'`,
    `ss`, `dst_addr`, `dyn_addr`, `root_addr`, `fields`, `tail_offset`] compile_abi_static_field_step) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `mid` (qx_choose_then `out` strip_assume_tac)) >>
  mp_tac (Q.SPECL [`cs.cs_next_var`, `cs.cs_next_var`,
    `(if info = AbiPrimWord then 2 else 1) + 1`, `ss`, `out`] abi_operand_before_frame) >>
  impl_tac >- simp[] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`fields ++ [(F,payload)]`, `tail_offset`, `dst_addr`, `dyn_addr`,
    `root_addr + n2w (source_offset + mem_size)`, `bs`,
    `[(w2n (dst_addr + n2w (abi_field_head_size fields):bytes32),LENGTH (payload:word8 list))]`,
    `ss`, `out`] abi_bytes_field_ready_frame) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_field_tail_size_append, abi_field_tail_def] >> DISCH_TAC >>
  `cs.cs_next_var <= mid.cs_next_var` by decide_tac >>
  qexistsl_tac [`mid`, `out`] >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual static-to-bytes ABI field preparation: " ^ name)
  end) (DB.thms "abiStaticBytesReady")
