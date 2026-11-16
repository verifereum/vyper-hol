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
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [compile_abi_decode_to_buf_def, compile_abi_dec_addr_def,
    compile_abi_decode_range_check_def, comp_return_def, pairTheory.UNCURRY_DEF,
    compile_abi_decode_static_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >>
  rename1 `emit_op CALLDATALOAD [src] st = (value,c1)` >>
  qpat_assum `emit_op _ _ _ = _` (fn th => simp_tac (srw_ss()) [th]) >>
  pairarg_tac >>
  rename1 `compile_abi_clamp_basetype value cl c1 = (u,c2)` >>
  qpat_assum `compile_abi_clamp_basetype _ _ _ = _`
    (fn th => simp_tac (srw_ss()) [th]) >> disch_tac >>
  Cases_on `u` >>
  drule compile_abi_clamp_structure >> strip_tac >>
  `same_blocks st c1 /\ same_blocks c2 last` by
    metis_tac[emit_op_same_blocks, emit_void_same_blocks] >>
  `inst_extends st c1 /\ inst_extends c2 last` by
    metis_tac[inst_extends_emit_op, inst_extends_emit_void] >>
  `cs_extends st c1 /\ cs_extends c1 c2 /\ cs_extends c2 last` by
    (simp_tac (srw_ss()) [cs_extends_def] >>
     rpt conj_tac >> qexists_tac `[]` >>
     simp_tac (srw_ss()) [] >>
     metis_tac[same_blocks_def, inst_extends_def, IS_PREFIX_APPEND]) >>
  `cs_extends c1 last` by metis_tac[cs_extends_trans] >>
  `fn_has_code st c1 fn /\ fn_has_code c1 last fn` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code c1 c2 fn` by metis_tac[fn_has_code_split] >>
  `!x. src = Var x ==> not_fresh_at st x` by
    (qpat_assum `abi_decoder_operand_live _ src` mp_tac >>
     Cases_on `src` >> simp_tac (srw_ss()) [abi_decoder_operand_live_def,
      abi_decoder_older_vars_def, loweringStateRelDefsTheory.not_fresh_at_def]) >>
  drule_all calldata_load_overwrite_prefix_uniform_origin_joint >>
  disch_then (qspecl_then [`PG`, `G`] strip_assume_tac) >>
  rename1 `eval_operand value loaded = SOME _` >>
  `abi_decoder_operand_live c1.cs_next_var value` by
    metis_tac[abi_decoder_operand_live_emit] >>
  drule_all calldata_clamp_repeat >>
  disch_then (qx_choose_then `stopped` strip_assume_tac) >>
  `run_inst_seq (emitted_insts c1 c2) loaded = Abort Revert_abort stopped` by
    metis_tac[] >>
  `allocas_from lower loaded` by
    metis_tac[allocas_from_def] >>
  `?bb. lookup_block loaded.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts c1 c2)
      (DROP loaded.vs_inst_idx bb.bb_instructions)` by
    (qspecl_then [`c1`, `c2`, `fn`, `emitted_insts c1 c2`] mp_tac
       fn_has_code_code >>
     (impl_tac >- metis_tac[inst_extends_def]) >>
     strip_tac >> qexists_tac `bb` >> asm_rewrite_tac[]) >>
  `?j HG th.
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (loaded,H,u) [] (Abort Revert_abort (stopped with vs_inst_idx := j),HG,th)) /\
    th.t_mem = u.t_mem /\ th.t_stor = u.t_stor /\
    th.t_trans = u.t_trans /\ th.t_imm = u.t_imm /\
    (!x. x IN ({}:string set) ==> FLOOKUP HG x = FLOOKUP H x /\
      FLOOKUP th.t_var x = FLOOKUP u.t_var x)` by
    (irule exact_scalar_clamp_abort_joint >>
     asm_rewrite_tac[NOT_IN_EMPTY] >> metis_tac[]) >>
  `!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
    (initial,G,tn) [] (Abort Revert_abort (stopped with vs_inst_idx := j),HG,th)` by
    (rpt gen_tac >>
     metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND]) >>
  `?fuel. run_from fuel ctx fn initial =
      Abort Revert_abort (stopped with vs_inst_idx := j) /\
      mem_safe_run fuel ctx fn initial` by
    (qpat_x_assum `!D explicit. gas_origin_ptr_path _ (initial,_,_) _ _`
      (qspecl_then [`ARB`, `ARB`] mp_tac) >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_exec) >>
     simp_tac (srw_ss()) [] >> metis_tac[]) >>
  `!xs s a t. EVERY (\i. ~is_terminator i.inst_opcode) xs /\
    run_inst_seq xs s = Abort a t ==> t.vs_returndata = []` by
    (POP_ASSUM_LIST (K ALL_TAC) >> Induct >> simp[run_inst_seq_def] >>
     rpt strip_tac >> Cases_on `step_inst_base h s` >> gvs[] >>
     metis_tac[step_inst_base_abort_returndata]) >>
  `stopped.vs_returndata = []` by
    (first_x_assum irule >> qexistsl_tac [`Revert_abort`, `loaded`, `emitted_insts c1 c2`] >>
     asm_rewrite_tac[] >>
     qpat_x_assum `EVERY _ (emitted_insts c1 c2)` mp_tac >>
     simp_tac (srw_ss()) [EVERY_MEM] >> metis_tac[]) >>
  qexistsl_tac [`stopped with vs_inst_idx := j`, `HG`, `th`] >>
  asm_simp_tac (srw_ss()) [] >> metis_tac[]
QED
