(* TOP-LEVEL: actual ABI word and fixed-size copy emitters produce paths in
   their containing function, with memory and operand effects preserved.
   These are base cases for encoding aggregates across generated blocks. *)
Theory abiEncoderPathProps
Ancestors
  fragBlockPath fragExec abiEncoder abiEncoderProps context compileEnv
  exprLoweringProps emitHelper emitHelperProps instIdxIndep
  venomExecSemantics venomState venomInst list rich_list words abiEncoderLeafRaw
Libs pairLib wordsLib

Theorem fresh_vars_wrt_inst_idx:
  !cs ss n.
    fresh_vars_wrt cs (ss with vs_inst_idx := n) = fresh_vars_wrt cs ss
Proof
  simp[fresh_vars_wrt_def]
QED

Theorem mload_inst_idx:
  !offset ss n. mload offset (ss with vs_inst_idx := n) = mload offset ss
Proof
  simp[mload_def]
QED

(* Preserve the path API while sharing the dependency-light execution proofs. *)
Theorem compile_abi_encode_static_code =
  abiEncoderLeafRawTheory.compile_abi_encode_static_code;

Theorem compile_abi_encode_static_straight:
  !dst src cs op cs'.
    compile_abi_encode_static dst src cs = (op,cs') ==>
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts cs cs')
Proof
  rpt gen_tac >> strip_tac >> drule compile_abi_encode_static_code >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem compile_abi_encode_static_execution =
  abiEncoderLeafRawTheory.compile_abi_encode_static_execution;

Theorem compile_abi_encode_static_path:
  !ctx func dst src cs op cs' ss src_addr dst_addr.
    compile_abi_encode_static dst src cs = (op,cs') /\
    eval_operand src ss = SOME src_addr /\ eval_operand dst ss = SOME dst_addr /\
    dst <> Var (STRING #"%" (toString cs.cs_next_var)) /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    fragment_path ctx func ss
      ((mstore (w2n dst_addr) (mload (w2n src_addr) ss)
        (update_var (STRING #"%" (toString cs.cs_next_var))
          (mload (w2n src_addr) ss) ss))
        with vs_inst_idx := LENGTH cs'.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_abi_encode_static_execution >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ _ = OK raw_out` >>
  drule compile_abi_encode_static_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts cs cs')` by
    (drule_all compile_abi_encode_static_straight >> simp[]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `cs'`, `ss`, `raw_out`]
    fragment_path_emitted) >> simp[Abbr`raw_out`]
QED

Theorem compile_abi_encode_static_path_fresh:
  !ctx func dst src cs op cs' ss src_addr dst_addr.
    compile_abi_encode_static dst src cs = (op,cs') /\
    eval_operand src ss = SOME src_addr /\ eval_operand dst ss = SOME dst_addr /\
    fresh_vars_wrt cs ss /\ fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\
      out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      eval_operand op out = SOME 32w /\
      mload (w2n dst_addr) out = mload (w2n src_addr) ss /\
      fresh_vars_wrt cs' out /\
      (!old w. eval_operand old ss = SOME w ==> eval_operand old out = SOME w) /\
      (!a. a < LENGTH ss.vs_memory /\
        (a < w2n dst_addr \/ w2n dst_addr + 32 <= a) ==>
        EL a out.vs_memory = EL a ss.vs_memory) /\
      LENGTH ss.vs_memory <= LENGTH out.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_abi_encode_static_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs cs') ss = OK raw_out` >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts cs cs')` by
    (drule_all compile_abi_encode_static_straight >> simp[]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `cs'`, `ss`, `raw_out`]
    fragment_path_emitted) >> impl_tac >- simp[] >> strip_tac >>
  qexists_tac `raw_out with vs_inst_idx := LENGTH cs'.cs_current_insts` >>
  simp[eval_op_inst_idx, eval_operand_def, mload_inst_idx, fresh_vars_wrt_inst_idx] >>
  rpt gen_tac >> strip_tac >> qpat_x_assum `!a. _` irule >>
  simp[arithmeticTheory.GREATER_EQ]
QED

Theorem compile_abi_copy_execution =
  abiEncoderLeafRawTheory.compile_abi_copy_execution;

Theorem compile_abi_copy_path:
  !ctx func dst src copy_size cs op cs' ss dst_addr src_addr.
    compile_abi_encode_to_buf dst src (AbiCopy copy_size) cs = (op,cs') /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    copy_size < dimword(:256) /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    fragment_path ctx func ss
      ((mcopy (w2n dst_addr) (w2n src_addr) copy_size ss)
        with vs_inst_idx := LENGTH cs'.cs_current_insts) /\
    eval_operand op
      ((mcopy (w2n dst_addr) (w2n src_addr) copy_size ss)
        with vs_inst_idx := LENGTH cs'.cs_current_insts) = SOME (n2w copy_size) /\
    (fresh_vars_wrt cs'
      ((mcopy (w2n dst_addr) (w2n src_addr) copy_size ss)
        with vs_inst_idx := LENGTH cs'.cs_current_insts) = fresh_vars_wrt cs ss)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`dst`, `src`, `copy_size`, `cs`, `op`, `cs'`, `ss`,
    `dst_addr`, `src_addr`] compile_abi_copy_execution) >>
  impl_tac >- simp[] >> strip_tac >>
  `emit_void MCOPY [dst; src; Lit (n2w copy_size)] cs = ((),cs')` by
    (fs[Once compile_abi_encode_child_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> pairarg_tac >> gvs[]) >>
  drule emitted_insts_emit_void >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts cs cs')` by simp[mk_inst_def, is_terminator_def] >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `cs'`, `ss`,
    `mcopy (w2n (dst_addr:bytes32)) (w2n (src_addr:bytes32)) copy_size ss`]
      fragment_path_emitted) >>
  simp[eval_op_inst_idx, eval_operand_def, fresh_vars_wrt_inst_idx]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed ABI path theorem: " ^ name)
  end)
  (DB.thms "abiEncoderPathProps")
