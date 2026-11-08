(* Raw leaf execution shared by the path API and enclosing-loop endpoints.
   No dependency on recursive encoder correctness. *)
Theory abiEncoderLeafRaw
Ancestors
  abiEncoder context compileEnv exprLoweringProps emitHelper emitHelperProps
  venomExecSemantics venomState venomInst list rich_list words
Libs pairLib wordsLib

Theorem compile_abi_encode_static_code:
  !dst src cs op cs'.
    compile_abi_encode_static dst src cs = (op,cs') ==>
    emitted_insts cs cs' =
      [mk_inst cs.cs_next_id MLOAD [src]
         [STRING #"%" (toString cs.cs_next_var)];
       mk_inst (cs.cs_next_id + 1) MSTORE
         [dst; Var (STRING #"%" (toString cs.cs_next_var))] []] /\
    op = Lit 32w /\ same_blocks cs cs' /\
    cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs' /\
    cs'.cs_next_var = cs.cs_next_var + 1 /\
    cs'.cs_next_id = cs.cs_next_id + 2
Proof
  rw[compile_abi_encode_static_def, emit_op_def, emit_void_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >>
  simp[emitted_insts_def, DROP_APPEND1, DROP_LENGTH_NIL,
    same_blocks_def]
QED

(* Loop iterations may overwrite the same generated SSA name repeatedly.
   Only the destination operand must avoid the name written by MLOAD. *)
Theorem compile_abi_encode_static_execution:
  !dst src cs op cs' ss src_addr dst_addr.
    compile_abi_encode_static dst src cs = (op,cs') /\
    eval_operand src ss = SOME src_addr /\ eval_operand dst ss = SOME dst_addr /\
    dst <> Var (STRING #"%" (toString cs.cs_next_var)) ==>
    run_inst_seq (emitted_insts cs cs') ss =
      OK (mstore (w2n dst_addr) (mload (w2n src_addr) ss)
        (update_var (STRING #"%" (toString cs.cs_next_var))
          (mload (w2n src_addr) ss) ss))
Proof
  rpt gen_tac >> strip_tac >> drule compile_abi_encode_static_code >> strip_tac >>
  `eval_operand dst (update_var (STRING #"%" (toString cs.cs_next_var))
      (mload (w2n (src_addr:bytes32)) ss) ss) = SOME dst_addr` by
    (irule eval_operand_update_var_mstore >> simp[] >>
     rpt gen_tac >> strip_tac >> gvs[]) >>
  mp_tac (Q.SPECL [`src`, `src_addr`, `cs.cs_next_id`,
    `STRING #"%" (toString cs.cs_next_var)`, `ss`] step_MLOAD) >>
  asm_rewrite_tac[] >> strip_tac >>
  mp_tac (Q.SPECL [`dst`, `Var (STRING #"%" (toString cs.cs_next_var))`,
    `dst_addr`, `mload (w2n (src_addr:bytes32)) ss`, `cs.cs_next_id + 1`,
    `update_var (STRING #"%" (toString cs.cs_next_var)) (mload (w2n (src_addr:bytes32)) ss) ss`]
    step_MSTORE) >> asm_simp_tac (srw_ss()) [eval_operand_update_var] >> strip_tac >>
  simp[run_inst_seq_def]
QED

Theorem compile_abi_copy_execution:
  !dst src copy_size cs op cs' ss dst_addr src_addr.
    compile_abi_encode_to_buf dst src (AbiCopy copy_size) cs = (op,cs') /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    copy_size < dimword(:256) ==>
    run_inst_seq (emitted_insts cs cs') ss =
      OK (mcopy (w2n dst_addr) (w2n src_addr) copy_size ss) /\
    op = Lit (n2w copy_size) /\ same_blocks cs cs' /\
    cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs' /\
    (fresh_vars_wrt cs' (mcopy (w2n dst_addr) (w2n src_addr) copy_size ss) =
       fresh_vars_wrt cs ss) /\
    (!old w. eval_operand old ss = SOME w ==>
      eval_operand old (mcopy (w2n dst_addr) (w2n src_addr) copy_size ss) = SOME w)
Proof
  rpt gen_tac >>
  simp[Once compile_abi_encode_child_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  simp[run_inst_seq_def, venomExecSemanticsTheory.step_inst_base_opcode_eqs, mk_inst_def,
    eval_operand_def, fresh_vars_wrt_def, mcopy_def, write_memory_with_expansion_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `old` >> gvs[eval_operand_def, lookup_var_def]
QED
