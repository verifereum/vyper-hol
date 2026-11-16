(* Rejected primitive calldata decoders: one runtime and ghost endpoint. *)
Theory calldataExactScalarRejected
Ancestors
  calldataExactScalarJoint calldataWordLive calldataOverwritePtr
  fragGasOriginPtrExec fragGasOriginPtrLoop stmtReasonLitFragMemory
  calldataClampPtr entryDecodeProps abiDecoderContract abiDecoderReentry
  abiEncoder compileEnv exprLowering emitHelperProps exprLoweringProps
  fragExec fragExecMem ptrDiscipline passSharedFrame
  venomExecSemantics venomState venomInst words finite_map list rich_list
  pred_set arithmetic

Theorem calldata_word_rejected_joint:
  !st last limit ctx fn site src child initial p d oid base_addr cap G tn lower PG cl.
  compile_abi_decode_to_buf (Var child) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecPrimWord cl) st = ((),last) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  last.cs_next_var <= limit.cs_next_var /\
  unit_alloca_budget ctx < dimword (:256) /\
  (last.cs_current_insts = [] ==> !bb.
    lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  eval_operand src initial = SOME p /\
  eval_operand (Var child) initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var child) /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  (!id q k. st.cs_next_id <= id /\ id < last.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ last.cs_next_id <= oid) /\
  base_addr <= d /\ d+32 <= base_addr+cap /\
  d+32 < dimword (:256) /\ ptr_covers G tn child initial 32 /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  fresh_vars_wrt limit initial /\ allocas_from lower initial /\
  lower <= initial.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  ~abi_clamp_ok cl (abi_decode_load CALLDATALOAD p initial) ==>
  ?z H u. z.vs_returndata = [] /\
    (?fuel. run_from fuel ctx fn initial = Abort Revert_abort z /\
      mem_safe_run fuel ctx fn initial) /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (initial,G,tn) [] (Abort Revert_abort z,H,u))
Proof
  rpt gen_tac >>
  simp_tac bool_ss [compile_abi_decode_to_buf_def, compile_abi_dec_addr_def,
    compile_abi_decode_range_check_def, comp_return_def, pairTheory.UNCURRY_DEF,
    compile_abi_decode_static_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] st = (value,c1)` >>
  rename1 `compile_abi_clamp_basetype value cl c1 = ((),c2)` >>
  FAIL_TAC "split"
QED
