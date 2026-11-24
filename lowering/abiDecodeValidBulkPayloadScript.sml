(* The allocated dynamic-array payload, starting after the count store. *)
Theory abiDecodeValidBulkPayload
Ancestors calldataDecodePtr[qualified,ignore_grammar] abiDecodePtrMemberFrame[qualified] arithmetic[qualified,ignore_grammar]
  abiDecoderBulk decoderNavigationPtr decoderArraySetupPtr
  decoderGhostFramePtr fragGasCopyLoop fragGasCopySeqLiftProps fragGasOriginPtr logInstSeqPtr
  stmtReasonMemory allocaFootprint exprSimBufferStore exprSimAccounts
  emitHelperProps exprLoweringProps fragExec instIdxIndep words rich_list pred_set
  venomState ptrDiscipline fragGasSeqPtr venomInst abiEncoder abiDecoderComposition compileEnv
  venomExecSemantics freshWrites ghostPcTransportPtr fragGasOriginPtrLoop

Theorem bulk_payload_copy_endpoint[local]:
  emit_void MCOPY [Var dst;Var src;lenop] sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\
  lookup_var dst s = SOME (n2w d) /\ lookup_var src s = SOME (n2w b) /\
  eval_operand lenop s = SOME (n2w k) /\ op_taint tn lenop = {} /\
  ptr_covers G tn dst s k /\ ptr_covers G tn src s k /\
  d < dimword (:256) /\ b < dimword (:256) /\ k < dimword (:256) /\
  d+k <= s.vs_alloca_next /\ b+k <= s.vs_alloca_next /\
  (!i. b <= i /\ i < b+k ==> i NOTIN tn.t_mem) ==>
  ?tf.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G,tf)) /\
    t = mcopy d b k s /\ tf.t_var = tn.t_var /\
    tf.t_mem = tn.t_mem DIFF {i | d <= i /\ i < d+k} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm
Proof
  strip_tac >>
  `eval_operand (Var dst) s = SOME (n2w d) /\
   eval_operand (Var src) s = SOME (n2w b)` by simp[eval_operand_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule emit_mcopy_mem_ok >>
     goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >> simp[w2n_n2w]) >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
     simp[listTheory.DROP_APPEND]) >>
  `step_inst_base (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;lenop] []) s =
   OK (mcopy d b k s)` by simp[step_mcopy_eq, w2n_n2w] >>
  `t = mcopy d b k s` by fs[run_inst_seq_def] >>
  qabbrev_tac `tf = step_taint (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;lenop] [])
    s (mcopy d b k s) tn` >>
  `step_prov PG G (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;lenop] [])
       (mcopy d b k s) = G /\ tf.t_var = tn.t_var /\
   tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
   tf.t_mem = (tn.t_mem DIFF {i | d <= i /\ i < d+k}) UNION
     {d+i | i < k /\ b+i IN tn.t_mem}` by
    (mp_tac (Q.SPECL [`PG`,`G`,`tn`,`s`,`sa.cs_next_id`,`Var dst`,`Var src`,
        `lenop`,`n2w b`,`n2w d`,`n2w k`] fragExecPtrTheory.mcopy_operand_ghost_frame) >>
     simp[Abbr `tf`, w2n_n2w]) >>
  `{d+i | i < k /\ b+i IN tn.t_mem} = {}` by
    (simp[EXTENSION, GSYM IMP_DISJ_THM] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `!D. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G tf` by
    (simp[inst_seq_ptr_def, Abbr `tf`] >>
     irule fragExecPtrTheory.ptr_inst_ok_mcopy_operand >>
     simp[SF SFY_ss, w2n_n2w]) >>
  `tf.t_imm = tn.t_imm` by
    simp[Abbr `tf`, step_taint_def, imm_taint_def, mk_inst_def] >>
  qexists_tac `tf` >> simp[] >>
  rpt gen_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
           i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  `(ctx_has_dalloca ctx ==>
     !pre i post u. emitted_insts sa sb = pre ++ i::post /\
       run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
     irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     `MEM i [mk_inst sa.cs_next_id MCOPY [Var dst;Var src;lenop] []]` by
       (qpat_assum `emitted_insts sa sb = [mk_inst _ _ _ _]` (SUBST1_TAC o SYM) >>
        qpat_assum `emitted_insts sa sb = pre ++ i::post` SUBST1_TAC >> simp[]) >>
     fs[mk_inst_def]) >>
  `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s G tf` by simp[] >>
  drule_all (cj 1 run_inst_seq_origin_ptr_lift) >> simp[]
QED

Theorem bulk_payload_actual_cuts[local]:
  abi_decode_bulk_payload (Var dst) pos cnt mem_sz MLOAD (Var base_v) sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?sz c1 off c2 src c3 data c4 s1 s2 s3 s4.
    emit_op MUL [cnt;Lit (n2w mem_sz)] sa = (sz,c1) /\
    emit_op ADD [pos;Lit 32w] c1 = (off,c2) /\
    emit_op ADD [Var base_v;off] c2 = (src,c3) /\
    emit_op ADD [Var dst;Lit 32w] c3 = (data,c4) /\
    emit_void MCOPY [data;src;sz] c4 = ((),sb) /\
    run_inst_seq (emitted_insts sa c1) s = OK s1 /\
    run_inst_seq (emitted_insts c1 c2) s1 = OK s2 /\
    run_inst_seq (emitted_insts c2 c3) s2 = OK s3 /\
    run_inst_seq (emitted_insts c3 c4) s3 = OK s4 /\
    run_inst_seq (emitted_insts c4 sb) s4 = OK t
Proof
  simp[abi_decode_bulk_payload_def, compile_abi_dec_addr_def, comp_bind_def,
    abi_decode_copy_opcode_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MUL [cnt;Lit (n2w mem_sz)] sa = (sz,c1)` >>
  rename1 `emit_op ADD [pos;Lit 32w] c1 = (off,c2)` >>
  rename1 `emit_op ADD [Var base_v;off] c2 = (src,c3)` >>
  rename1 `emit_op ADD [Var dst;Lit 32w] c3 = (data,c4)` >>
  `emitted_insts sa sb = emitted_insts sa c1 ++ emitted_insts c1 c2 ++
    emitted_insts c2 c3 ++ emitted_insts c3 c4 ++ emitted_insts c4 sb` by
    (imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
     imp_res_tac inst_extends_trans >> metis_tac[emitted_insts_append, inst_extends_def]) >>
  qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = OK t` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  ntac 4 (dxrule run_inst_seq_append_ok >> strip_tac) >>
  rename1 `run_inst_seq (emitted_insts sa c1) s = OK s1` >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  rename1 `run_inst_seq (emitted_insts c3 c4) s3 = OK s4` >>
  qexistsl [`s1`,`s2`,`s3`,`s4`] >> simp[]
QED

(* The two scalar instructions leave the source and destination roots live. *)
Theorem bulk_payload_scalar_cuts[local]:
  emit_op MUL [cnt;Lit (n2w mem_sz)] sa = (sz,c1) /\
  emit_op ADD [pos;Lit 32w] c1 = (off,c2) /\
  run_inst_seq (emitted_insts sa c1) s = OK s1 /\
  run_inst_seq (emitted_insts c1 c2) s1 = OK s2 /\
  fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand cnt s = SOME (n2w n) /\ eval_operand pos s = SOME (n2w p) /\
  op_taint tn cnt = {} /\ op_prov G cnt = NONE /\
  op_taint tn pos = {} /\ op_prov G pos = NONE /\
  (!x. pos = Var x ==> not_fresh_at sa x) ==>
  ?G2 tn2.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK (s2 with vs_inst_idx := LENGTH c2.cs_current_insts),G2,tn2)) /\
    eval_operand sz s2 = SOME (n2w (n*mem_sz)) /\ op_taint tn2 sz = {} /\
    eval_operand off s2 = SOME (n2w (p+32)) /\ op_taint tn2 off = {} /\
    op_prov G2 off = NONE /\
    (!x. not_fresh_at sa x ==> lookup_var x s2 = lookup_var x s /\
      FLOOKUP G2 x = FLOOKUP G x /\ op_taint tn2 (Var x) = op_taint tn (Var x)) /\
    (s2 with vs_vars := s.vs_vars) = s /\ s2.vs_current_bb = c2.cs_current_bb /\
    tn2.t_mem = tn.t_mem /\ tn2.t_stor = tn.t_stor /\
    tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm
Proof
  strip_tac >>
  `eval_operand (Lit (n2w mem_sz)) s = SOME (n2w mem_sz) /\
   op_taint tn (Lit (n2w mem_sz)) = {} /\ op_prov G (Lit (n2w mem_sz)) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all (SRULE [] (Q.INST [`H` |-> `ARB`, `opc` |-> `MUL`]
    (SPEC_ALL emit_scalar_binop_endpoint_ptr_origin_core))) >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`] strip_assume_tac) >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!D lower ctx' func. _ ==> !fuel. _` kall_tac >>
  rename1 `op_taint tn1 sz = {}` >> rename1 `op_prov G1 sz = NONE` >>
  `eval_operand sz s1 = SOME (n2w (n*mem_sz)) /\
   (s1 with vs_vars := s.vs_vars) = s /\
   (!x. sz = Var x ==> not_fresh_at c1 x)` by
    (qpat_assum `emit_op MUL _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       word_mul_n2w, loweringStateRelDefsTheory.not_fresh_at_def]) >>
  `eval_operand pos s1 = SOME (n2w p) /\
   op_taint tn1 pos = {} /\ op_prov G1 pos = NONE` by
    (qpat_assum `!q. not_fresh_at sa q ==> _`
       (mp_then Any (qspec_then `pos` mp_tac) old_operand_ghost_frame) >>
     `s1.vs_labels = s.vs_labels` by
       (qpat_assum `s1 with vs_vars := s.vs_vars = s`
          (mp_tac o AP_TERM ``(\v:venom_state. v.vs_labels)``) >> simp[]) >> simp[]) >>
  `run_inst_seq (emitted_insts c1 c2)
    (s1 with vs_inst_idx := LENGTH c1.cs_current_insts) =
    OK (s2 with vs_inst_idx := LENGTH c1.cs_current_insts)` by
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac emit_op_run_pc) >>
     disch_then (qspecl_then [`s1`,`LENGTH c1.cs_current_insts`] mp_tac) >>
     simp[is_terminator_def, exec_result_map_def]) >>
  `eval_operand (Lit 32w) s1 = SOME 32w /\
   op_taint tn1 (Lit 32w) = {} /\ op_prov G1 (Lit 32w) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s1` by
    (qpat_assum `s1 with vs_vars := s.vs_vars = s`
       (mp_tac o AP_TERM ``allocas_below_fmp``) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[allocas_below_fmp_def] >> metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (s1 with vs_inst_idx := LENGTH c1.cs_current_insts)` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s1` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[allocas_below_fmp_def] >> metis_tac[]) >>
  drule_all (SRULE [] (Q.INST [`H` |-> `ARB`, `opc` |-> `ADD`,
    `s` |-> `s1 with vs_inst_idx := LENGTH c1.cs_current_insts`,
    `t` |-> `s2 with vs_inst_idx := LENGTH c1.cs_current_insts`]
    (SPEC_ALL emit_scalar_binop_endpoint_ptr_origin_core))) >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`] strip_assume_tac) >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!D lower ctx' func. _ ==> !fuel. _` kall_tac >>
  rename1 `op_taint tn2 off = {}` >> rename1 `op_prov G2 off = NONE` >>
  `eval_operand off s2 = SOME (n2w (p+32)) /\
   (s2 with vs_vars := s1.vs_vars) = s1` by
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       GSYM word_add_n2w]) >>
  `s2.vs_labels = s1.vs_labels /\ s2.vs_current_bb = s1.vs_current_bb /\
   s1.vs_current_bb = s.vs_current_bb` by
    (imp_res_tac emit_op_run_control_frame >> simp[]) >>
  `c2.cs_current_bb = c1.cs_current_bb /\ c1.cs_current_bb = sa.cs_current_bb` by
    (imp_res_tac emit_op_same_blocks >> fs[same_blocks_def]) >>
  `sa.cs_next_var <= c1.cs_next_var` by
    (qpat_assum `emit_op MUL _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at c1 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!q. not_fresh_at c1 q ==> lookup_var q s2 = lookup_var q s1 /\
    FLOOKUP G2 q = FLOOKUP G1 q /\ op_taint tn2 (Var q) = op_taint tn1 (Var q)` by
    (qpat_assum `!q. not_fresh_at c1 q ==> _`
      (mp_tac o SRULE [lookup_var_def]) >> simp[lookup_var_def]) >>
  `eval_operand sz s2 = SOME (n2w (n*mem_sz)) /\ op_taint tn2 sz = {}` by
    (qpat_assum `!q. not_fresh_at c1 q ==> lookup_var q s2 = lookup_var q s1 /\ _`
       (mp_then Any (qspec_then `sz` mp_tac) old_operand_ghost_frame) >> simp[]) >>
  `s2 with vs_vars := s.vs_vars = s` by
    (qpat_assum `s2 with vs_vars := s1.vs_vars = s1`
      (mp_tac o AP_TERM ``(\v:venom_state. v with vs_vars := s.vs_vars)``) >> simp[]) >>
  `~s1.vs_halted` by
    (qpat_assum `s1 with vs_vars := s.vs_vars = s`
      (mp_tac o AP_TERM ``(\v:venom_state. v.vs_halted)``) >> simp[]) >>
  `allocas_from lo s1 /\
   allocas_from lo (s1 with vs_inst_idx := LENGTH c1.cs_current_insts)` by
    (simp[allocas_from_def] >> qpat_assum `allocas_from lo s`
       (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  qexistsl [`G2`,`tn2`] >> simp[] >> rpt gen_tac >>
  irule gas_origin_ptr_path_trans >>
  qexistsl [`G1`,`s1 with vs_inst_idx := LENGTH c1.cs_current_insts`,`tn1`] >> simp[]
QED

(* Both computed copy addresses belong to the same actual payload run. *)
Theorem bulk_payload_address_cuts[local]:
  emit_op ADD [Var base_v;off] c2 = (src,c3) /\
  emit_op ADD [Var dst;Lit 32w] c3 = (data,c4) /\
  run_inst_seq (emitted_insts c2 c3) s2 = OK s3 /\
  run_inst_seq (emitted_insts c3 c4) s3 = OK s4 /\
  fn_has_code c2 c3 func /\ fn_has_code c3 c4 func /\
  allocas_from lo s2 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s2) /\ ~s2.vs_halted /\
  s2.vs_current_bb = c2.cs_current_bb /\
  lookup_var base_v s2 = SOME (n2w B) /\ ptr_covers G2 tn2 base_v s2 L /\
  lookup_var dst s2 = SOME (n2w d) /\ ptr_covers G2 tn2 dst s2 cap /\
  not_fresh_at c2 dst /\
  eval_operand off s2 = SOME (n2w (p+32)) /\ op_taint tn2 off = {} /\
  op_prov G2 off = NONE /\ p+32+k <= L /\ 32+k <= cap /\
  B+p+32 < dimword (:256) /\ d+32 < dimword (:256) ==>
  ?G4 tn4 x y.
    src = Var x /\ data = Var y /\
    lookup_var x s4 = SOME (n2w (B+p+32)) /\ ptr_covers G4 tn4 x s4 k /\
    lookup_var y s4 = SOME (n2w (d+32)) /\ ptr_covers G4 tn4 y s4 k /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s2 with vs_inst_idx := LENGTH c2.cs_current_insts,G2,tn2) []
       (OK (s4 with vs_inst_idx := LENGTH c4.cs_current_insts),G4,tn4)) /\
    (!x. not_fresh_at c2 x ==> lookup_var x s4 = lookup_var x s2 /\
      FLOOKUP G4 x = FLOOKUP G2 x /\ op_taint tn4 (Var x) = op_taint tn2 (Var x)) /\
    (s4 with vs_vars := s2.vs_vars) = s2 /\ s4.vs_current_bb = c4.cs_current_bb /\
    tn4.t_mem = tn2.t_mem /\ tn4.t_stor = tn2.t_stor /\
    tn4.t_trans = tn2.t_trans /\ tn4.t_imm = tn2.t_imm
Proof
  strip_tac >>
  `run_inst_seq (emitted_insts c2 c3) (s2 with vs_inst_idx := LENGTH c2.cs_current_insts) =
     OK (s3 with vs_inst_idx := LENGTH c2.cs_current_insts)` by
    (qpat_assum `emit_op ADD [Var base_v;off] _ = _` (mp_then Any mp_tac emit_op_run_pc) >>
     disch_then (qspecl_then [`s2`,`LENGTH c2.cs_current_insts`] mp_tac) >>
     simp[is_terminator_def, exec_result_map_def]) >>
  `lookup_var base_v (s2 with vs_inst_idx := LENGTH c2.cs_current_insts) = SOME (n2w B) /\
   ptr_covers G2 tn2 base_v (s2 with vs_inst_idx := LENGTH c2.cs_current_insts) L /\
   eval_operand off (s2 with vs_inst_idx := LENGTH c2.cs_current_insts) = SOME (n2w (p+32))` by
    gvs[lookup_var_def] >>
  `w2n ((n2w B):256 word) + (p+32) < dimword (:256)` by
    (`B < dimword (:256)` by decide_tac >> simp[w2n_n2w] >> decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (s2 with vs_inst_idx := LENGTH c2.cs_current_insts)` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s2` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[allocas_below_fmp_def] >> metis_tac[]) >>
  drule_all (Q.INST [`H` |-> `ARB`, `sa` |-> `c2`, `off` |-> `p+32`,
    `n` |-> `k`, `total` |-> `L`, `s` |-> `s2 with vs_inst_idx := LENGTH c2.cs_current_insts`,
    `t` |-> `s3 with vs_inst_idx := LENGTH c2.cs_current_insts`]
    (SPEC_ALL emit_ptr_offset_endpoint_ptr_origin_core)) >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`] (strip_assume_tac o SRULE [])) >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!D lower ctx' func. _ ==> !fuel. _` kall_tac >>
  rename1 `src = Var x` >> rename1 `ptr_covers G3 tn3 x s3 k` >>
  `B < dimword (:256) /\ d < dimword (:256)` by decide_tac >>
  `lookup_var x s3 = SOME (n2w (B+p+32))` by
    ((qpat_assum `lookup_var x (s3 with vs_inst_idx := _) = _` mp_tac >>
     simp[lookup_var_def, GSYM arithmeticTheory.ADD_ASSOC] >> (gvs[lookup_var_def, GSYM arithmeticTheory.ADD_ASSOC]))) >>
  `!z. not_fresh_at c2 z ==> lookup_var z s3 = lookup_var z s2 /\
    FLOOKUP G3 z = FLOOKUP G2 z /\ op_taint tn3 (Var z) = op_taint tn2 (Var z)` by
    (qpat_assum `!z. not_fresh_at c2 z ==> _`
       (mp_tac o SRULE [lookup_var_def]) >> simp[lookup_var_def]) >>
  `lookup_var dst s3 = SOME (n2w d) /\ ptr_covers G3 tn3 dst s3 cap` by
    (qpat_assum `!z. not_fresh_at c2 z ==> lookup_var z s3 = lookup_var z s2 /\ _`
       (qspec_then `dst` strip_assume_tac) >> gvs[bodyPtrDefsTheory.ptr_covers_def]) >>
  `run_inst_seq (emitted_insts c3 c4) (s3 with vs_inst_idx := LENGTH c3.cs_current_insts) =
     OK (s4 with vs_inst_idx := LENGTH c3.cs_current_insts)` by
    (qpat_assum `emit_op ADD [Var dst;Lit 32w] _ = _` (mp_then Any mp_tac emit_op_run_pc) >>
     disch_then (qspecl_then [`s3`,`LENGTH c3.cs_current_insts`] mp_tac) >>
     simp[is_terminator_def, exec_result_map_def]) >>
  `lookup_var dst (s3 with vs_inst_idx := LENGTH c3.cs_current_insts) = SOME (n2w d) /\
   ptr_covers G3 tn3 dst (s3 with vs_inst_idx := LENGTH c3.cs_current_insts) cap /\
   eval_operand (Lit 32w) (s3 with vs_inst_idx := LENGTH c3.cs_current_insts) = SOME (n2w 32) /\
   op_taint tn3 (Lit 32w) = {} /\ op_prov G3 (Lit 32w) = NONE /\
   w2n ((n2w d):256 word) + 32 < dimword (:256)` by
    gvs[lookup_var_def, eval_operand_def, op_taint_def, op_prov_def] >>
  `s3 with vs_vars := s2.vs_vars = s2` by
    (qpat_assum `emit_op ADD [Var base_v;off] _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s3` by
    (qpat_assum `s3 with vs_vars := s2.vs_vars = s2`
       (mp_tac o AP_TERM ``allocas_below_fmp``) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s2` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[allocas_below_fmp_def] >> metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (s3 with vs_inst_idx := LENGTH c3.cs_current_insts)` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s3` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[allocas_below_fmp_def] >> metis_tac[]) >>
  drule_all (Q.INST [`H` |-> `ARB`, `sa` |-> `c3`, `off` |-> `32`,
    `n` |-> `k`, `total` |-> `cap`, `s` |-> `s3 with vs_inst_idx := LENGTH c3.cs_current_insts`,
    `t` |-> `s4 with vs_inst_idx := LENGTH c3.cs_current_insts`]
    (SPEC_ALL emit_ptr_offset_endpoint_ptr_origin_core)) >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`] (strip_assume_tac o SRULE [])) >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!D lower ctx' func. _ ==> !fuel. _` kall_tac >>
  rename1 `data = Var y` >> rename1 `ptr_covers G4 tn4 y s4 k` >>
  `lookup_var y s4 = SOME (n2w (d+32))` by
    gvs[blockPrefixEquivTheory.lookup_var_set_inst_idx] >>
  `!z. not_fresh_at c3 z ==> lookup_var z s4 = lookup_var z s3 /\
    FLOOKUP G4 z = FLOOKUP G3 z /\ op_taint tn4 (Var z) = op_taint tn3 (Var z)` by
    (qpat_assum `!z. not_fresh_at c3 z ==> _`
       (mp_tac o SRULE [blockPrefixEquivTheory.lookup_var_set_inst_idx]) >> simp[]) >>
  `c2.cs_next_var <= c3.cs_next_var /\ not_fresh_at c3 x` by
    (qpat_assum `emit_op ADD [Var base_v;off] _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  `lookup_var x s4 = SOME (n2w (B+p+32)) /\ ptr_covers G4 tn4 x s4 k` by
    (qpat_assum `!z. not_fresh_at c3 z ==> lookup_var z s4 = lookup_var z s3 /\ _`
       (qspec_then `x` strip_assume_tac) >> gvs[bodyPtrDefsTheory.ptr_covers_def]) >>
  `s4 with vs_vars := s3.vs_vars = s3` by
    (qpat_assum `emit_op ADD [Var dst;Lit 32w] _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def]) >>
  `s4 with vs_vars := s2.vs_vars = s2` by
    (qpat_assum `s4 with vs_vars := s3.vs_vars = s3`
      (mp_tac o AP_TERM ``(\v:venom_state. v with vs_vars := s2.vs_vars)``) >> simp[]) >>
  `~s3.vs_halted /\ s3.vs_current_bb = s2.vs_current_bb /\
   s4.vs_current_bb = s2.vs_current_bb` by
    (imp_res_tac emit_op_run_control_frame >>
     qpat_assum `s3 with vs_vars := s2.vs_vars = s2`
       (mp_tac o AP_TERM ``(\v:venom_state. v.vs_halted)``) >> simp[]) >>
  `c4.cs_current_bb = c3.cs_current_bb /\ c3.cs_current_bb = c2.cs_current_bb` by
    (imp_res_tac emit_op_same_blocks >> fs[same_blocks_def]) >>
  `allocas_from lo s3 /\
   allocas_from lo (s2 with vs_inst_idx := LENGTH c2.cs_current_insts) /\
   allocas_from lo (s3 with vs_inst_idx := LENGTH c3.cs_current_insts)` by
    (simp[allocas_from_def] >> qpat_assum `allocas_from lo s2`
       (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `!z. not_fresh_at c2 z ==> not_fresh_at c3 z` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `c2` >> simp[]) >>
  qexistsl [`G4`,`tn4`,`x`,`y`] >> simp[] >> rpt gen_tac >>
  irule gas_origin_ptr_path_trans >>
  qexistsl [`G3`,`s3 with vs_inst_idx := LENGTH c3.cs_current_insts`,`tn3`] >> simp[]
QED

(* Join the two arithmetic pairs and the copy on the supplied physical run. *)
Theorem abi_decode_bulk_payload_success_joint:
  abi_decode_bulk_payload (Var dst) pos cnt mem_sz MLOAD (Var base_v) sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  abi_decode_ptr_window G tn s base_v (n2w B) L /\
  lookup_var dst s = SOME (n2w d) /\ ptr_covers G tn dst s cap /\
  not_fresh_at sa base_v /\ not_fresh_at sa dst /\
  eval_operand cnt s = SOME (n2w n) /\ eval_operand pos s = SOME (n2w p) /\
  op_taint tn cnt = {} /\ op_prov G cnt = NONE /\
  op_taint tn pos = {} /\ op_prov G pos = NONE /\
  (!x. pos = Var x ==> not_fresh_at sa x) /\
  B+p+32 < dimword (:256) /\ d+32 < dimword (:256) /\ n*mem_sz < dimword (:256) /\
  B+L <= s.vs_alloca_next /\ d+cap <= s.vs_alloca_next /\
  p+32+n*mem_sz <= L /\ 32+n*mem_sz <= cap /\
  (B+L <= d \/ d+cap <= B) ==>
  ?Gf tf.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tf)) /\
    abi_decode_ptr_window Gf tf t base_v (n2w B) L /\ ptr_covers Gf tf dst t cap /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    (t with vs_vars := s.vs_vars) = mcopy (d+32) (B+p+32) (n*mem_sz) s /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\ allocas_from lo t /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    tf.t_mem = tn.t_mem DIFF {i | d+32 <= i /\ i < d+32+n*mem_sz}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bulk_payload_actual_cuts >> strip_tac >>
  imp_res_tac emit_op_extends_next_var >>
  `cs_extends c4 sb` by
    (qpat_assum `emit_void MCOPY _ _ = _` (mp_then Any strip_assume_tac emit_void_extends) >>
     gvs[same_blocks_def, cs_extends_def]) >>
  `cs_extends c1 sb /\ cs_extends c2 sb /\ cs_extends c3 sb` by
    metis_tac[cs_extends_trans] >>
  mp_tac (Q.SPECL [`sa`,`c1`,`sb`,`func`] fn_has_code_split) >> simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`c1`,`c2`,`sb`,`func`] fn_has_code_split) >> simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`c2`,`c3`,`sb`,`func`] fn_has_code_split) >> simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`c3`,`c4`,`sb`,`func`] fn_has_code_split) >> simp[] >> strip_tac >>
  drule_all bulk_payload_scalar_cuts >> disch_then (qspec_then `PG` strip_assume_tac) >>
  `allocas_from lo s2 /\ ~s2.vs_halted` by
    (qpat_assum `s2 with vs_vars := s.vs_vars = s` (fn th =>
       assume_tac (SRULE [] (AP_TERM ``(\v:venom_state. v.vs_allocas)`` th)) >>
       assume_tac (SRULE [] (AP_TERM ``(\v:venom_state. v.vs_halted)`` th))) >>
     simp[allocas_from_def] >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `!x. not_fresh_at sa x ==> not_fresh_at c2 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[] >> decide_tac) >>
  `lookup_var base_v s2 = SOME (n2w B) /\ ptr_covers G2 tn2 base_v s2 L /\
   lookup_var dst s2 = SOME (n2w d) /\ ptr_covers G2 tn2 dst s2 cap` by
    (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x s2 = _ /\ _`
       (qspecl_then [`base_v`] strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x s2 = _ /\ _`
       (qspecl_then [`dst`] strip_assume_tac) >>
     gvs[abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def, bodyPtrDefsTheory.ptr_covers_def]) >>
  `not_fresh_at c2 dst` by simp[] >>
  `p+32+(n*mem_sz) <= L /\ 32+(n*mem_sz) <= cap` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s2` by
    (qpat_assum `s2 with vs_vars := s.vs_vars = s`
       (mp_tac o AP_TERM ``allocas_below_fmp``) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[allocas_below_fmp_def] >> metis_tac[]) >>
  drule_all (Q.INST [`k` |-> `n*mem_sz`] (SPEC_ALL bulk_payload_address_cuts)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `src = Var src_v` >> rename1 `data = Var data_v` >>
  `!v. sz = Var v ==> not_fresh_at c2 v` by
    (qpat_assum `emit_op MUL _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
  `s4.vs_labels = s2.vs_labels /\ s4.vs_allocas = s2.vs_allocas /\
   s4.vs_alloca_next = s.vs_alloca_next /\ ~s4.vs_halted` by
    (qpat_assum `s4 with vs_vars := s2.vs_vars = s2` (fn th =>
       map_every (fn p => mp_tac (SRULE [] (AP_TERM p th)))
         [``(\v:venom_state. v.vs_labels)``, ``(\v:venom_state. v.vs_allocas)``,
          ``(\v:venom_state. v.vs_alloca_next)``, ``(\v:venom_state. v.vs_halted)``]) >>
     qpat_assum `s2 with vs_vars := s.vs_vars = s`
       (mp_tac o SRULE [] o AP_TERM ``(\v:venom_state. v.vs_alloca_next)``) >> simp[]) >>
  `eval_operand sz s4 = SOME (n2w (n*mem_sz)) /\ op_taint tn4 sz = {}` by
    (qpat_assum `!v. not_fresh_at c2 v ==> lookup_var v s4 = _ /\ _`
       (mp_then Any (qspec_then `sz` mp_tac) old_operand_ghost_frame) >> simp[]) >>
  `!i. B+p+32 <= i /\ i < B+p+32+n*mem_sz ==> i NOTIN tn4.t_mem` by
    (gen_tac >> strip_tac >>
     `B MOD dimword (:256) = B` by (irule arithmeticTheory.LESS_MOD >> decide_tac) >>
     qpat_assum `B MOD dimword (:256) = B` (fn mod_eq =>
       qpat_assum `abi_decode_ptr_window G tn s base_v (n2w B) L`
         (strip_assume_tac o REWRITE_RULE [abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def,
           w2n_n2w, mod_eq])) >>
     `B <= i /\ i < B+L` by decide_tac >>
     qpat_assum `!j. B <= j /\ j < B+L ==> j NOTIN tn.t_mem` (qspec_then `i` mp_tac) >> simp[]) >>
  `B+p+32+n*mem_sz <= s4.vs_alloca_next /\ d+32+n*mem_sz <= s4.vs_alloca_next` by
    decide_tac >>
  `emit_void MCOPY [Var data_v;Var src_v;sz] c4 = ((),sb)` by fs[] >>
  `run_inst_seq (emitted_insts c4 sb) (s4 with vs_inst_idx := LENGTH c4.cs_current_insts) =
    OK (t with vs_inst_idx := LENGTH c4.cs_current_insts)` by
    (qpat_assum `emit_void MCOPY [Var data_v;Var src_v;sz] c4 = _`
       (mp_then Any assume_tac emitted_insts_emit_void) >>
     irule EQ_TRANS >> qexists_tac `exec_result_map
       (\v. v with vs_inst_idx := LENGTH c4.cs_current_insts)
       (run_inst_seq (emitted_insts c4 sb) s4)` >>
     simp[run_inst_seq_inst_idx, mk_inst_def, is_terminator_def, exec_result_map_def]) >>
  `allocas_from lo (s4 with vs_inst_idx := LENGTH c4.cs_current_insts)` by
    (simp[allocas_from_def] >> qpat_assum `allocas_from lo s2`
       (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `lookup_var data_v (s4 with vs_inst_idx := LENGTH c4.cs_current_insts) = SOME (n2w (d+32)) /\
   lookup_var src_v (s4 with vs_inst_idx := LENGTH c4.cs_current_insts) = SOME (n2w (B+p+32))` by
    fs[lookup_var_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s4` by
    (qpat_assum `s4 with vs_vars := s2.vs_vars = s2`
       (mp_tac o AP_TERM ``allocas_below_fmp``) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s2` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[allocas_below_fmp_def] >> metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (s4 with vs_inst_idx := LENGTH c4.cs_current_insts)` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s4` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[allocas_below_fmp_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`dst` |-> `data_v`, `src` |-> `src_v`, `lenop` |-> `sz`,
    `sa` |-> `c4`, `sb` |-> `sb`, `s` |-> `s4 with vs_inst_idx := LENGTH c4.cs_current_insts`,
    `t` |-> `t with vs_inst_idx := LENGTH c4.cs_current_insts`,
    `ctx` |-> `ctx`, `func` |-> `func`, `lo` |-> `lo`,
    `G` |-> `G4`, `tn` |-> `tn4`, `PG` |-> `PG`,
    `d` |-> `d+32`, `b` |-> `B+p+32`, `k` |-> `n*mem_sz`]
    (SPEC_ALL bulk_payload_copy_endpoint)) >>
  impl_tac >- simp[] >>
  disch_then (strip_assume_tac o SRULE []) >>
  `t = mcopy (d+32) (B+p+32) (n*mem_sz) s4` by
    (qpat_assum `emit_void MCOPY [Var data_v;Var src_v;sz] c4 = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
     qpat_x_assum `run_inst_seq (emitted_insts c4 sb) s4 = OK t` mp_tac >>
     simp[run_inst_seq_def, step_mcopy_eq, eval_operand_def, w2n_n2w,
       arithmeticTheory.LESS_MOD]) >>
  `s4 with vs_vars := s.vs_vars = s` by
    (qpat_assum `s4 with vs_vars := s2.vs_vars = s2`
       (mp_tac o AP_TERM ``(\v:venom_state. v with vs_vars := s.vs_vars)``) >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
     FLOOKUP G4 x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >>
     `not_fresh_at c2 x` by simp[] >>
     `lookup_var x t = lookup_var x s4 /\ op_taint tf (Var x) = op_taint tn4 (Var x)` by
       (qpat_assum `t = mcopy _ _ _ _` (fn mc =>
          qpat_assum `tf.t_var = tn4.t_var` (fn tv =>
            simp[NoAsms, mc, tv, lookup_var_def, ssaOperandFrameTheory.mcopy_vars,
              op_taint_def]))) >>
     qpat_assum `!v. not_fresh_at c2 v ==> lookup_var v s4 = _ /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >>
     qpat_assum `!v. not_fresh_at sa v ==> lookup_var v s2 = _ /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >> simp[]) >>
  qexistsl [`G4`,`tf`] >>
  rpt conj_tac
  >- (rpt gen_tac >> irule gas_origin_ptr_path_trans >>
      qexistsl [`G4`,`s4 with vs_inst_idx := LENGTH c4.cs_current_insts`,`tn4`] >>
      simp[] >> irule gas_origin_ptr_path_trans >>
      qexistsl [`G2`,`s2 with vs_inst_idx := LENGTH c2.cs_current_insts`,`tn2`] >> simp[])
  >- (irule abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_frame >>
      goal_assum (drule_at (Pat `abi_decode_ptr_window _ _ _ _ _ _`)) >>
      simp[w2n_n2w, arithmeticTheory.LESS_MOD] >>
      gen_tac >> strip_tac >>
      `~(d+32 <= i /\ i < d+32+n*mem_sz)` by
        (qpat_x_assum `B+L <= d \/ d+cap <= B` strip_assume_tac >> decide_tac) >>
      simp[])
  >- (irule ptr_covers_frame >> goal_assum (drule_at (Pat `ptr_covers _ _ _ _ _`)) >> simp[])
  >- (first_assum ACCEPT_TAC)
  >- (qpat_assum `t = mcopy _ _ _ _` (fn mc =>
        qpat_assum `s4 with vs_vars := s.vs_vars = s` (fn frame =>
          simp[NoAsms, mc, GSYM ssaOperandFrameTheory.mcopy_reset_vars, frame])))
  >> `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
       (qpat_assum `s4 with vs_vars := s.vs_vars = s`
          (mp_tac o AP_TERM ``(\v:venom_state. v.vs_allocas)``) >>
        simp[mcopy_def, write_memory_with_expansion_def])
  >> `allocas_from lo t` by
       (qpat_assum `t.vs_allocas = s.vs_allocas` (fn frame =>
          qpat_assum `allocas_from lo s` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
          simp[NoAsms, allocas_from_def, frame]))
  >> (first_assum ACCEPT_TAC ORELSE simp[])
QED
