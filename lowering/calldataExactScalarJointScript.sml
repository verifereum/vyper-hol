(* Exact scalar calldata decoding: shared runtime and pointer witnesses. *)
Theory calldataExactScalarJoint
Ancestors
  calldataScalarSourceExact calldataWordPtr calldataClampPtr
  entryHaltMem fragGasCopyLoop fragGasCopySeqLiftProps fragGasSeqPtr fragGasOriginPtr
  emitHelperProps exprLoweringProps ptrDiscipline fragExec fragExecMem
  venomExecSemantics venomState venomInst finite_map list pred_set arithmetic

Theorem exact_scalar_clamp_opcodes[local]:
  compile_abi_clamp_basetype value clamp sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS /\
    i.inst_opcode <> DALLOCA) (emitted_insts sa sb)
Proof
  strip_tac >> drule calldata_clamp_instructions >> strip_tac >>
  gvs[mk_inst_def, MEM, is_terminator_def] >>
  Cases_on `signed` >> simp[mk_inst_def, is_terminator_def]
QED

Theorem exact_scalar_clamp_abort_joint:
  compile_abi_clamp_basetype value clamp sa = ((),sb) /\
  op_prov G value = NONE /\ op_taint tn value = {} /\
  (!x. x IN R ==> not_fresh_at sa x) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (emitted_insts sa sb) s = Abort a t ==>
  ?j H u.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (Abort a (t with vs_inst_idx := j),H,u)) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP H x = FLOOKUP G x /\
      FLOOKUP u.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS /\
    i.inst_opcode <> DALLOCA) (emitted_insts sa sb)` by
    metis_tac[exact_scalar_clamp_opcodes] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[compile_abi_clamp_basetype_mem_ok] >>
  `?H u. inst_seq_ptr (ARB : dead) 0 ctx fn PG G tn (emitted_insts sa sb) s H u /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. x IN R ==> FLOOKUP H x = FLOOKUP G x /\
      FLOOKUP u.t_var x = FLOOKUP tn.t_var x)` by
    (irule abi_decode_clamp_abort_ptr >> metis_tac[]) >>
  `(ctx_has_dalloca ctx ==> !pre i post u.
    emitted_insts sa sb = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
    unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     qpat_x_assum `EVERY _ _` mp_tac >> simp[EVERY_APPEND]) >>
  `?j. !D lo explicit PG G tn HG th.
    inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s HG th ==>
    gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (Abort a (t with vs_inst_idx := j),HG,th)` by
    (irule run_inst_seq_abort_origin_ptr_uniform >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  qexistsl_tac [`j`, `H`, `u`] >> simp[] >> rpt gen_tac >>
  `?H' u'. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H' u'` by
    metis_tac[abi_decode_clamp_abort_ptr] >>
  `H' = H /\ u' = u` by metis_tac[inst_seq_ptr_ghost_unique] >> gvs[] >>
  first_x_assum irule >>
  irule inst_seq_ptr_lower_bound_transport >>
  conj_tac >- (fs[EVERY_MEM] >> metis_tac[]) >>
  simp[] >> qexists_tac `0` >> simp[]
QED
