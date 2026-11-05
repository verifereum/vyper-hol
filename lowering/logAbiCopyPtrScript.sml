(* Exact bytestring copy: source padding need not be clean. *)
Theory logAbiCopyPtr
Ancestors
  logAbiBytesPtr logInstSeqPtr abiEncoderBytesCode abiEncoderRounding
  typedCopyPtr fragExecPtr fragExec bodyPtrDefs ptrDiscipline ptrSafeRun
  emitHelperProps emitHelper compileEnv context exprLoweringProps
  venomExecSemantics venomState venomInst finite_map words list arithmetic pred_set

Theorem abi_bytes_copy_taint:
  (len:num) <= rounded /\ rounded <= len+32 /\
  (!i:num. (srcpos:num) <= i /\ i < srcpos+32+len ==> i NOTIN old) /\
  mid = old DIFF {i | dest+rounded <= i /\ i < dest+rounded+32} /\
  new = (mid DIFF {i | dest <= i /\ i < dest+32+len}) UNION
    {dest+i | i < 32+len /\ srcpos+i IN mid} ==>
  (!i. dest <= i /\ i < dest+32+rounded ==> i NOTIN new) /\
  (!i. ~(dest <= i /\ i < dest+32+rounded) ==> (i IN new <=> i IN old))
Proof
  strip_tac >>
  `!i. i < 32+len ==> srcpos+i NOTIN mid` by
    (simp[] >> rpt strip_tac >> gvs[] >> metis_tac[LESS_EQ_ADD]) >>
  `new = mid DIFF {i | dest <= i /\ i < dest+32+len}` by
    (qpat_x_assum `new = _` SUBST1_TAC >>
     `{dest+i | i < 32+len /\ srcpos+i IN mid} = {}` by
       (simp_tac bool_ss [EXTENSION, GSPECIFICATION, NOT_IN_EMPTY, pairTheory.PAIR_EQ] >> metis_tac[]) >> simp[]) >>
  gvs[] >> rpt strip_tac >>
  simp[IN_DIFF] >> decide_tac
QED

Theorem abi_encode_bytes_copy_seq_ptr:
  abi_encode_bytes_copy (Var dst) (Var src) (Var len) (Var last) sa = ((),sb) /\
  not_fresh_at sa dst /\ not_fresh_at sa src /\ not_fresh_at sa len /\
  lookup_var dst s = SOME (n2w dest) /\ lookup_var src s = SOME (n2w srcpos) /\
  lookup_var len s = SOME (n2w cnt) /\
  lookup_var last s = SOME (n2w (dest+contractABI$ceil32 cnt)) /\
  ptr_covers G tn dst s (32+contractABI$ceil32 cnt) /\
  ptr_covers G tn src s (32+cnt) /\ ptr_covers G tn last s 32 /\
  op_taint tn (Var len) = {} /\
  (!i. srcpos <= i /\ i < srcpos+32+cnt ==> i NOTIN tn.t_mem) /\
  dest+32+contractABI$ceil32 cnt < dimword(:256) /\
  srcpos+32+cnt < dimword(:256) /\ 32+cnt < dimword(:256) /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf sf.
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    (!i. dest <= i /\ i < dest+32+contractABI$ceil32 cnt ==> i NOTIN tnf.t_mem) /\
    (!i. ~(dest <= i /\ i < dest+32+contractABI$ceil32 cnt) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    sf.vs_memory = (mcopy dest srcpos (32+cnt)
      (mstore (dest+contractABI$ceil32 cnt) 0w s)).vs_memory /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  simp_tac bool_ss [abi_encode_bytes_copy_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  ntac 2 (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `emit_void MSTORE [Var last;Lit 0w] sa = ((),sm)` >>
  rename1 `emit_op ADD [Lit 32w;Var len] sm = (arg,sn)` >>
  `?tmp. arg = Var tmp` by
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac emitted_insts_emit_op) >> metis_tac[]) >>
  gvs[] >>
  `eval_operand (Lit 0w) s = SOME 0w /\ op_taint tn (Lit 0w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all emit_mstore_clean_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `tm` (qx_choose_then `t` strip_assume_tac))) >>
  suspend "after_store"
QED

Resume abi_encode_bytes_copy_seq_ptr[after_store]:
  `dest+contractABI$ceil32 cnt < dimword(:256) /\
   dest < dimword(:256) /\ srcpos < dimword(:256) /\ cnt < dimword(:256)` by decide_tac >>
  `w2n ((n2w (dest+contractABI$ceil32 cnt)):256 word) = dest+contractABI$ceil32 cnt` by
    simp[w2n_n2w] >>
  qabbrev_tac `u = t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sm)` >>
  `eval_operand (Lit 32w) u = SOME 32w /\
   eval_operand (Var len) u = SOME (n2w cnt) /\
   op_taint tm (Lit 32w) = {} /\ op_taint tm (Var len) = {}` by
    gvs[Abbr `u`, eval_operand_def, lookup_var_def, mstore_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`]
    emit_copy_len_binop_seq_ptr)) >>
  disch_then (qspecl_then [`fn`,`PG`,`G`,`D`]
    (qx_choose_then `H` (qx_choose_then `tk` (qx_choose_then `v` strip_assume_tac)))) >>
  suspend "after_add"
QED
Resume abi_encode_bytes_copy_seq_ptr[after_add]:
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    (qpat_x_assum `emit_void MSTORE _ _ = _` mp_tac >>
     simp[emit_void_def, fresh_id_def, emit_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, not_fresh_at_def] >>
     rpt strip_tac >> gvs[]) >>
  qabbrev_tac `w = v with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts sm sn)` >>
  `lookup_var dst w = SOME (n2w dest) /\ lookup_var src w = SOME (n2w srcpos) /\
   eval_operand (Var tmp) w = SOME (n2w (32+cnt)) /\ op_taint tk (Var tmp) = {}` by
    (simp[Abbr `w`, eval_operand_def, GSYM word_add_n2w] >>
     gvs[Abbr `u`, lookup_var_def, mstore_def] >> metis_tac[]) >>
  `ptr_covers H tk dst w (w2n ((n2w (32+cnt)):256 word)) /\
   ptr_covers H tk src w (w2n ((n2w (32+cnt)):256 word))` by suspend "coverage" >>
  drule_all emit_mcopy_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `tf` (qx_choose_then `z` strip_assume_tac))) >>
  `emitted_insts sa sn = emitted_insts sa sm ++ emitted_insts sm sn /\
   emitted_insts sa sb = emitted_insts sa sn ++ emitted_insts sn sb` by
    (imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
     conj_asm1_tac >- (irule emitted_insts_append >> simp[]) >>
     irule emitted_insts_append >> simp[APPEND_ASSOC]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sm) /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sm sn) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sn sb)` by
    (imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
     simp[mk_inst_def, is_terminator_def]) >>
  suspend "compose"
QED
Resume abi_encode_bytes_copy_seq_ptr[compose]:
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sn)` by
    gvs[EVERY_MEM] >>
  qunabbrev_tac `u` >> drule_all successful_seq_ptr_append >> strip_tac >>
  `run_inst_seq (emitted_insts sa sn) s = OK (v with vs_inst_idx := t.vs_inst_idx) /\
   inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sn) s H tk` by
    metis_tac[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sn)` by simp[] >>
  qabbrev_tac `r = v with vs_inst_idx := t.vs_inst_idx` >>
  `w = r with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sn)` by
    (qpat_x_assum `Abbrev (r = _)` mp_tac >>
     qpat_x_assum `Abbrev (w = _)` mp_tac >>
     qpat_x_assum `emitted_insts sa sn = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [markerTheory.Abbrev_def] >> rpt strip_tac >>
     pure_rewrite_tac [venom_state_fupdfupds, combinTheory.K_o_THM,
       venom_state_accfupds, combinTheory.K_THM, LENGTH_APPEND, ADD_ASSOC] >> REFL_TAC) >>
  qpat_x_assum `Abbrev (w = _)` kall_tac >>
  qpat_x_assum `w = _` SUBST_ALL_TAC >>
  qunabbrev_tac `r` >>
  drule_all successful_seq_ptr_append >> strip_tac >>
  qexistsl_tac [`H`,`tf`,`z with vs_inst_idx := t.vs_inst_idx`] >>
  conj_tac >-
    (qpat_x_assum `run_inst_seq (_ ++ _) s = OK (z with vs_inst_idx := _)` mp_tac >>
     pure_rewrite_tac [venom_state_accfupds, combinTheory.K_THM] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  suspend "post"
QED
Resume abi_encode_bytes_copy_seq_ptr[coverage]:
  `cnt <= contractABI$ceil32 cnt` by metis_tac[abi_encoder_ceil32_bounds] >>
  `32+cnt < dimword(:256)` by decide_tac >>
  `!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
    op_taint tk (Var p) = op_taint tn (Var p)` by
    (rpt strip_tac >> gvs[op_taint_def] >> metis_tac[]) >>
  qpat_x_assum `ptr_covers G tn last s _` kall_tac >>
  gvs[ptr_covers_def, w2n_n2w] >>
  mp_tac (Q.INST [`cnt` |-> `cnt`] abi_encoder_ceil32_bounds) >> decide_tac
QED
Resume abi_encode_bytes_copy_seq_ptr[post]:
  rpt (qpat_x_assum `run_inst_seq _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` kall_tac) >>
  `32+cnt < dimword(:256)` by decide_tac >>
  `w2n ((n2w dest):256 word) = dest /\
   w2n ((n2w srcpos):256 word) = srcpos /\
   w2n ((n2w (32+cnt)):256 word) = 32+cnt` by simp[w2n_n2w] >>
  `(!i. dest <= i /\ i < dest+32+contractABI$ceil32 cnt ==> i NOTIN tf.t_mem) /\
   (!i. ~(dest <= i /\ i < dest+32+contractABI$ceil32 cnt) ==>
     (i IN tf.t_mem <=> i IN tn.t_mem))` by suspend "taint" >>
  simp[] >> conj_tac >- suspend "memory" >>
  suspend "vars"
QED
Resume abi_encode_bytes_copy_seq_ptr[taint]:
  qpat_x_assum `tf.t_mem = _` mp_tac >>
  qpat_x_assum `tk.t_mem = _` mp_tac >>
  qpat_x_assum `tm.t_mem = _` mp_tac >>
  qpat_x_assum `!i. srcpos <= i /\ _ ==> _` mp_tac >>
  mp_tac (Q.INST [`cnt` |-> `cnt`] abi_encoder_ceil32_bounds) >>
  rpt (qpat_x_assum `w2n _ = _` mp_tac) >>
  POP_ASSUM_LIST (K all_tac) >> rpt (disch_then strip_assume_tac) >>
  rpt (qpat_x_assum `w2n _ = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]))) >>
  `contractABI$ceil32 cnt <= cnt+32` by decide_tac >>
  `!i. srcpos <= i /\ i < srcpos+32+cnt ==> i NOTIN tn.t_mem` by
    metis_tac[ADD_COMM, ADD_ASSOC] >>
  qpat_x_assum `tm.t_mem = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [ADD_ASSOC]) >>
  drule_all abi_bytes_copy_taint >> simp[]
QED
Resume abi_encode_bytes_copy_seq_ptr[memory]:
  qpat_x_assum `z = _` mp_tac >>
  qpat_x_assum `v.vs_memory = _` mp_tac >>
  qpat_x_assum `t = _` mp_tac >>
  rpt (qpat_x_assum `w2n _ = _` mp_tac) >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  gvs[] >> simp[mcopy_def, write_memory_with_expansion_def]
QED
Resume abi_encode_bytes_copy_seq_ptr[vars]:
  qpat_x_assum `!p. not_fresh_at sm p ==> _` mp_tac >>
  qpat_x_assum `!p. not_fresh_at sa p ==> _` mp_tac >>
  qpat_x_assum `tf.t_var = _` mp_tac >>
  qpat_x_assum `tm.t_var = _` mp_tac >>
  qpat_x_assum `z = _` mp_tac >>
  qpat_x_assum `t = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  gvs[lookup_var_def, mcopy_def, mstore_def,
    write_memory_with_expansion_def, op_taint_def] >> metis_tac[]
QED
Finalise abi_encode_bytes_copy_seq_ptr
