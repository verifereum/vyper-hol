Theory bodyFullConvertCastOrigin
Ancestors
  exprSimConvertBytes bodyMemTbConvertCastMemory
  bodyPtrTypeBuiltinsCheckedArithmetic bodyPtrSignedConvertHeaderLoad
  bodyFullConvertScalarCertificate fragGasCopyLoop fragGasOriginPtr
  fragGasSeqPtr ptrSafetyTransport ptrSafeRun instIdxIndep stateFrame
  assignBasePtrBytesPrefix instSeqComposePtr fragExec
  exprLowering exprLoweringProps compileEnv ptrDiscipline emitHelper freshWrites
  venomExecSemantics venomState venomInst finite_map list

Theorem cast_fixed_certificate[local]:
  ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ mload (w2n a) s = n2w L /\
  L < dimword(:256) /\ n < dimword(:256) /\
  (!j. w2n a <= j /\ j < w2n a+32 ==> j NOTIN tn.t_mem) ==>
  ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MLOAD [Var src] [len];
       mk_inst (id+1) GT [Var len;Lit (n2w n)] [gt];
       mk_inst (id+2) ISZERO [Var gt] [ok];
       mk_inst (id+3) ASSERT [Var ok] []] s H th /\
    (!p. p <> len /\ p <> gt /\ p <> ok ==>
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >> drule_all assign_base_bytes_mload_seq >>
  disch_then (qspecl_then [`D`,`fn`,`PG`,`id`,`len`] strip_assume_tac) >>
  `eval_operand (Var len) u = SOME (n2w L)` by
    simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `?t err. run_inst_seq
      [mk_inst (id+1) GT [Var len;Lit (n2w n)] [gt];
       mk_inst (id+2) ISZERO [Var gt] [ok];
       mk_inst (id+3) ASSERT [Var ok] []] u = OK t \/
    run_inst_seq
      [mk_inst (id+1) GT [Var len;Lit (n2w n)] [gt];
       mk_inst (id+2) ISZERO [Var gt] [ok];
       mk_inst (id+3) ASSERT [Var ok] []] u = Abort err t` by
    (drule_all convert_cast_check_insts >>
     disch_then (qspecl_then [`id+1`,`id+2`,`id+3`,`gt`,`ok`] mp_tac) >>
     simp[] >> Cases_on `L <= n` >> simp[] >> metis_tac[]) >>
  `MEM GT [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
   op_prov G' (Lit (n2w n)) = NONE /\ op_taint tn' (Lit (n2w n)) = {}` by
    simp[op_prov_def, op_taint_def] >>
  FIRST [
    drule_all (cj 1 (SRULE [LEFT_AND_OVER_OR, DISJ_IMP_THM, GSYM arithmeticTheory.ADD_ASSOC]
      (Q.INST [`opc` |-> `GT`, `id` |-> `id+1`] scalar_checked_pair_uniform_certificate))),
    drule_all (cj 2 (SRULE [LEFT_AND_OVER_OR, DISJ_IMP_THM, GSYM arithmeticTheory.ADD_ASSOC]
      (Q.INST [`opc` |-> `GT`, `id` |-> `id+1`] scalar_checked_pair_uniform_certificate)))] >>
  disch_then (qspecl_then [`fn`,`PG`,`D`,`s.vs_inst_idx+1`] strip_assume_tac) >>
  qexistsl [`H`,`th`] >> reverse conj_tac >- (simp[] >> metis_tac[]) >>
  `step_inst_base (mk_inst id MLOAD [Var src] [len]) s = OK u` by
    (qpat_x_assum `run_inst_seq [_] s = OK u` mp_tac >>
     simp[run_inst_seq_def, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `s.vs_inst_idx`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [inst_seq_ptr_def])) >>
  gvs[] >> simp[Once inst_seq_ptr_def, arithmeticTheory.ADD1]
QED

Theorem cast_compiled_certificate[local]:
  compile_type_convert (Var src) (ConvBytestringCast n i) sa = (out,sb) /\
  ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ mload (w2n a) s = n2w L /\
  L < dimword(:256) /\ n < dimword(:256) /\
  (!j. w2n a <= j /\ j < w2n a+32 ==> j NOTIN tn.t_mem) ==>
  ?H th. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >> Cases_on `n < i`
  >- (qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
      simp[compile_type_convert_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
        fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
      `!j. LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts+j) = 0`
        by decide_tac >>
      simp[emitted_insts_def, DROP_APPEND] >>
      drule_all cast_fixed_certificate >>
      disch_then (qspecl_then [`STRING #"%" (toString (sa.cs_next_var+2))`,
        `STRING #"%" (toString sa.cs_next_var)`,`sa.cs_next_id`,
        `STRING #"%" (toString (sa.cs_next_var+1))`,`fn`,`PG`,`D`] strip_assume_tac) >>
      qexistsl [`H`,`th`] >> simp[] >> rpt strip_tac >>
      fs[loweringStateRelDefsTheory.not_fresh_at_def] >>
      qpat_x_assum `!p. _ /\ _ /\ _ ==> _` (qspec_then `p` mp_tac) >>
      simp[]) >>
  gvs[compile_type_convert_def, comp_return_def, emitted_insts_refl] >>
  qexistsl [`G`,`tn`] >> simp[inst_seq_ptr_def]
QED

Theorem cast_uniform_certificate[local]:
  compile_type_convert (Var src) (ConvBytestringCast n i) sa = (out,sb) /\
  ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ mload (w2n a) s = n2w L /\
  L < dimword(:256) /\ n < dimword(:256) /\
  (!j. w2n a <= j /\ j < w2n a+32 ==> j NOTIN tn.t_mem) ==>
  ?H th. (!D. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th) /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >> drule_all cast_compiled_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`ARB`] strip_assume_tac) >>
  qexistsl [`H`,`th`] >> simp[] >> gen_tac >>
  drule_all cast_compiled_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  metis_tac[inst_seq_ptr_ghost_unique]
QED

Theorem convert_cast_origin_path:
  compile_type_convert (Var src) (ConvBytestringCast n i) sa = (out,sb) /\
  not_fresh_at sa src /\ lookup_var src s = SOME a /\
  mload (w2n a) s = n2w L /\ L <= i /\
  i < dimword(:256) /\ n < dimword(:256) /\
  ptr_covers G tn src s capacity /\ 32 <= capacity /\
  (!j. w2n a <= j /\ j < w2n a+32 ==> j NOTIN tn.t_mem) /\
  w2n a+32 <= s.vs_alloca_next /\ fn_has_code sa sb fn /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  out = Var src /\
  (L <= n ==> ?t H th.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,H,th)) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm) /\
  (n < L ==> ?t H th.
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (Abort Revert_abort t,H,th))
Proof
  strip_tac >> drule convert_cast_static_frame >> strip_tac >> simp[] >>
  `L < dimword(:256)` by decide_tac >>
  `eval_operand (Var src) s = SOME a` by simp[eval_operand_def] >>
  `ptr_covers G tn src s 32` by fs[bodyPtrDefsTheory.ptr_covers_def] >>
  drule_all cast_uniform_certificate >>
  disch_then (qspecl_then [`fn`,`PG`] strip_assume_tac) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule convert_bytestring_cast_mem_ok >> metis_tac[]) >>
  `EVERY (\ins. ins.inst_opcode <> INVOKE /\ ~is_terminator ins.inst_opcode /\
      ins.inst_opcode <> GAS) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `!D. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s H th` by
    (gen_tac >> irule scalar_seq_lower_bound >> simp[] >>
     conj_tac >- (fs[EVERY_MEM] >> metis_tac[]) >>
     qexists `0` >> simp[]) >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, same_blocks_def, rich_listTheory.IS_PREFIX_APPEND,
        emitted_insts_def] >> simp[DROP_APPEND] >> metis_tac[]) >>
  conj_tac >- suspend "success" >> suspend "abort"
QED

Resume convert_cast_origin_path[success]:
  strip_tac >> drule_all convert_cast_run_frame >> strip_tac >>
  `FILTER (\ins. ins.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (tt with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)),H,th)` by
    (gen_tac >>
     `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s H th` by metis_tac[] >>
     `EVERY (\ins. ins.inst_opcode <> INVOKE /\ ~is_terminator ins.inst_opcode)
       (emitted_insts sa sb)` by (fs[EVERY_MEM] >> metis_tac[]) >>
     drule_all run_inst_seq_gas_origin_ptr_path >> simp[]) >>
  qexistsl [`tt with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)`,`H`,`th`] >>
  simp[] >>
  qpat_x_assum `tt = s with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >>
  simp[same_blocks_def, lookup_var_def] >>
  fs[emitted_insts_def, rich_listTheory.IS_PREFIX_APPEND,
     same_blocks_def, lookup_var_def]
QED

Resume convert_cast_origin_path[abort]:
  strip_tac >> drule_all convert_cast_abort_run >> strip_tac >>
  drule_all run_inst_seq_abort_origin_ptr_uniform >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl [`tt with vs_inst_idx := j`,`H`,`th`] >> metis_tac[]
QED

Finalise convert_cast_origin_path
