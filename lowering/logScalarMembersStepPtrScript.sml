(* The tuple loop retains its base source pointer and generates one member
   address per iteration.  This boundary keeps its original capacity fixed. *)
Theory logScalarMembersStepPtr
Ancestors
  logScalarChildPtr logAbiPrefixPtr logTopicScalarPtr abiBuiltinPrefix
  abiEncoderCounters appendStorageGhostPtr abiDecoderDynamicLoopSetup ASCIInumbers
  logScalarChildShape logInstSeqPtr stmtSimLogEncodeLayout
  emitHelperProps exprLoweringProps emitHelper compileEnv bodyPtrDefs
  ptrDiscipline venomState venomInst words arithmetic list

Theorem log_member_source_add_seq_ptr:
  emit_op ADD [Var src;Lit (n2w so)] st = (Var elem,next) /\
  lookup_var src s = SOME (n2w sb) /\ ptr_covers G tn src s srcCap /\
  so+mz <= srcCap /\ sb+srcCap < dimword(:256) /\
  next.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~ctx_has_dalloca ctx ==>
  ?H tm t.
    run_inst_seq (emitted_insts st next) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st next) s H tm /\
    abi_builtin_prefix st next limit_st s t /\
    lookup_var elem t = SOME (n2w (sb+so)) /\ ptr_covers H tm elem t mz /\
    t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!v. not_fresh_at st v ==>
      lookup_var v t = lookup_var v s /\ FLOOKUP H v = FLOOKUP G v /\
      op_taint tm (Var v) = op_taint tn (Var v))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ptr_covers G tn src s (so+mz) /\
   eval_operand (Var src) s = SOME (n2w sb) /\
   eval_operand (Lit (n2w so)) s = SOME (n2w so) /\
   op_taint tn (Lit (n2w so)) = {} /\
   w2n ((n2w sb):256 word)+so < dimword(:256)` by
    (gvs[ptr_covers_def, eval_operand_def, op_taint_def, w2n_n2w] >> decide_tac) >>
  drule_all emit_addr_add_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `H` (qx_choose_then `tm` (qx_choose_then `t` strip_assume_tac)))) >>
  `tm.t_imm = tn.t_imm` by
    (irule inst_seq_ptr_immutable_taint_frame >> goal_assum (drule_at Any) >>
     drule emitted_insts_emit_op >> simp[mk_inst_def]) >>
  drule_all abi_builtin_emit_add >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `u = t` by
    (qpat_x_assum `abi_builtin_prefix _ _ _ _ u` mp_tac >>
     simp_tac bool_ss [abi_builtin_prefix_def] >> strip_tac >>
     qpat_x_assum `run_inst_seq _ _ = OK u` mp_tac >>
     qpat_x_assum `run_inst_seq _ _ = OK t` (fn th => rewrite_tac[th]) >> simp[]) >>
  qpat_x_assum `u = t` SUBST_ALL_TAC >>
  qexistsl_tac [`H`,`tm`,`t`] >>
  qpat_x_assum `lookup_var elem t = _` (fn th => assume_tac (PURE_REWRITE_RULE [word_add_n2w] th)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem log_scalar_member_cons_seq_ptr:
  emit_op ADD [Var src;Lit (n2w so)] st = (Var elem,sa) /\
  compile_abi_encode_child (Var dst) (Var elem) ei dyn ho (Var dp) sa = (out,end_st) /\
  log_members_layout ((ei,asz,mz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs sb so ho d hl cap s.vs_memory /\
  (!q. mem_agree_outside tn.t_mem s.vs_memory q ==>
    abi_encoder_input (AbiComplex ((ei,asz,mz,dyn)::infos))
      (Tuple (ty::tys)) (ListV (av::avs)) (sb+so)
      (abi_encoder_member_span ((ei,asz,mz,dyn)::infos)) q) /\
  not_fresh_at st src /\ not_fresh_at st dst /\ not_fresh_at st dp /\
  lookup_var src s = SOME (n2w sb) /\ lookup_var dst s = SOME (n2w d) /\
  lookup_var dp s = SOME (n2w p) /\
  mload p s = n2w (hl+LENGTH (FLAT (abi_tuple_tails pre pvs))) /\
  ptr_covers G tn src s srcCap /\ ptr_covers G tn dst s cap /\ ptr_covers G tn dp s 32 /\
  so+mz+abi_encoder_member_span infos <= srcCap /\ sb+srcCap < dimword(:256) /\
  d+cap < dimword(:256) /\ p+32 < dimword(:256) /\
  (sb+so+mz+abi_encoder_member_span infos <= d \/ d+cap <= sb+so) /\
  (sb+so+mz+abi_encoder_member_span infos <= p \/ p+32 <= sb+so) /\
  (d+cap <= p \/ p+32 <= d) /\
  (!i. d <= i /\ i < d+ho ==> i NOTIN tn.t_mem) /\
  (!i. d+hl <= i /\ i < d+hl+LENGTH (FLAT (abi_tuple_tails pre pvs)) ==>
    i NOTIN tn.t_mem) /\
  (!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s ==>
  ?H tm t.
    run_inst_seq (emitted_insts st end_st) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st end_st) s H tm /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st t /\
    log_members_layout infos tys avs (pre++[ty]) (pvs++[av])
      sb (so+mz) (ho+asz) d hl cap t.vs_memory /\
    mload p t = n2w (hl+LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av])))) /\
    abi_decode_footprint_frame [(d,cap);(p,32)] s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\
    (!q. mem_agree_outside tm.t_mem t.vs_memory q ==>
      abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs)
        (sb+(so+mz)) (abi_encoder_member_span infos) q) /\
    (!i. d <= i /\ i < d+(ho+asz) ==> i NOTIN tm.t_mem) /\
    (!i. d+hl <= i /\
      i < d+hl+LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av]))) ==>
      i NOTIN tm.t_mem) /\
    (!i. p <= i /\ i < p+32 ==> i NOTIN tm.t_mem) /\
    (!i. ~(d <= i /\ i < d+cap) /\ ~(p <= i /\ i < p+32) ==>
      (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!v. not_fresh_at st v ==>
      lookup_var v t = lookup_var v s /\ FLOOKUP H v = FLOOKUP G v /\
      op_taint tm (Var v) = op_taint tn (Var v)) /\
    lookup_var src t = SOME (n2w sb) /\ lookup_var dst t = SOME (n2w d) /\
    lookup_var dp t = SOME (n2w p) /\
    ptr_covers H tm src t srcCap /\ ptr_covers H tm dst t cap /\
    ptr_covers H tm dp t 32
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `sa.cs_next_var <= end_st.cs_next_var` by
    (qpat_assum `compile_abi_encode_child _ _ _ _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[cj 1 abi_encoder_counters_mono_mutual, abi_encoder_counters_mono_def, pairTheory.SND]) >>
  `sa.cs_next_var <= limit_st.cs_next_var /\ so+mz <= srcCap` by decide_tac >>
  drule_all log_member_source_add_seq_ptr >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `G1` (qx_choose_then `tn1` (qx_choose_then `v` strip_assume_tac)))) >>
  suspend "child"
QED

Resume log_scalar_member_cons_seq_ptr[child]:
  markerLib.RESUME_TAC >>
  `!x. not_fresh_at st x ==> not_fresh_at sa x` by
    (drule emitted_insts_emit_op >> simp_tac bool_ss [] >> strip_tac >>
     simp_tac bool_ss [not_fresh_at_def] >> rpt strip_tac >>
     qpat_x_assum `!n. st.cs_next_var <= n ==> _` (qspec_then `n` mp_tac) >>
     impl_tac >- decide_tac >> simp[]) >>
  `not_fresh_at sa elem` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[not_fresh_at_def, toString_inj]) >>
  `ptr_covers G1 tn1 dst v cap /\ ptr_covers G1 tn1 dp v 32` by
    (conj_tac >> irule ptr_covers_old_transport >> goal_assum (drule_at Any) >>
     qexists_tac `st` >> asm_simp_tac bool_ss [] >> metis_tac[]) >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _` (strip_assume_tac o
    PURE_REWRITE_RULE [abi_builtin_prefix_def, abi_decoder_address_frame_def]) >>
  qabbrev_tac `u = v with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st sa)` >>
  mp_tac (Q.INST [`src` |-> `elem`, `s` |-> `u`, `G` |-> `G1`, `tn` |-> `tn1`]
    log_scalar_member_child_seq_ptr) >>
  impl_tac >- suspend "child_pre" >>
  disch_then (qx_choose_then `H` (qx_choose_then `tm` (qx_choose_then `w` strip_assume_tac))) >>
  qexistsl_tac [`H`,`tm`,`w with vs_inst_idx := v.vs_inst_idx`] >>
  suspend "compose"
QED

Resume log_scalar_member_cons_seq_ptr[child_pre]:
  markerLib.RESUME_TAC >>
  `lookup_var dst v = SOME (n2w d) /\ lookup_var dp v = SOME (n2w p)` by
    (qpat_assum `!v'. not_fresh_at st v' ==> _` (qspec_then `dst` mp_tac) >>
     qpat_assum `!v'. not_fresh_at st v' ==> _` (qspec_then `dp` mp_tac) >>
     asm_simp_tac bool_ss []) >>
  `sb+so+mz+abi_encoder_member_span infos < dimword(:256)` by decide_tac >>
  simp_tac (srw_ss()) [Abbr `u`, lookup_var_def, ptr_covers_def,
    fresh_vars_wrt_def, mload_def] >>
  rule_assum_tac (SIMP_RULE (srw_ss())
    [lookup_var_def, ptr_covers_def, fresh_vars_wrt_def, mload_def]) >>
  asm_simp_tac bool_ss []
QED

Resume log_scalar_member_cons_seq_ptr[compose]:
  markerLib.RESUME_TAC >>
  qpat_assum `log_members_layout ((ei,asz,mz,dyn)::infos) _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any strip_assume_tac log_members_layout_cons_input) >>
  drule_all log_scalar_child_straight >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa end_st)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st sa)` by
    (drule emitted_insts_emit_op >> simp[mk_inst_def, is_terminator_def]) >>
  `emitted_insts st end_st = emitted_insts st sa ++ emitted_insts sa end_st` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  conj_tac >-
    (asm_rewrite_tac[] >> qunabbrev_tac `u` >>
     drule_all successful_seq_ptr_append >> simp_tac bool_ss [] >> strip_tac >>
     first_assum ACCEPT_TAC) >>
  conj_tac >-
    (asm_rewrite_tac[] >> irule logInstSeqPtrTheory.inst_seq_ptr_append >>
     asm_simp_tac bool_ss [] >> qexistsl_tac [`G1`,`v`,`tn1`] >>
     asm_simp_tac bool_ss [Abbr `u`]) >>
  conj_tac >- (irule inst_extends_trans >> goal_assum (drule_at Any) >> simp[]) >>
  suspend "post"
QED

Resume log_scalar_member_cons_seq_ptr[post]:
  markerLib.RESUME_TAC >>
  simp_tac (srw_ss()) [fresh_vars_wrt_def, mload_def] >>
  ntac 3 (conj_tac >- first_assum (ACCEPT_TAC o SIMP_RULE (srw_ss())
    [fresh_vars_wrt_def, mload_def])) >>
  conj_tac >- suspend "memory_frame" >>
  ntac 3 (conj_tac >- (asm_simp_tac (srw_ss()) [Abbr `u`])) >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (asm_simp_tac bool_ss []) >>
  ntac 3 (conj_tac >- (asm_simp_tac bool_ss [])) >>
  `!x. not_fresh_at st x ==>
    lookup_var x (w with vs_inst_idx := v.vs_inst_idx) = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)` by suspend "variables" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  suspend "coverage"
QED

Resume log_scalar_member_cons_seq_ptr[memory_frame]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `abi_decode_footprint_frame _ u w` mp_tac >>
  simp_tac (srw_ss()) [abiDecoderFrameTheory.abi_decode_footprint_frame_def, Abbr `u`] >>
  asm_simp_tac bool_ss []
QED
Resume log_scalar_member_cons_seq_ptr[variables]:
  markerLib.RESUME_TAC >>
  qpat_assum `!v. not_fresh_at sa v ==> _` mp_tac >>
  qpat_assum `!v. not_fresh_at st v ==> _ /\ _ /\ _` mp_tac >>
  qpat_assum `!x. not_fresh_at st x ==> not_fresh_at sa x` mp_tac >>
  simp_tac (srw_ss()) [Abbr `u`, lookup_var_def] >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED

Resume log_scalar_member_cons_seq_ptr[coverage]:
  markerLib.RESUME_TAC >>
  conj_tac >-
    (qpat_assum `!x. not_fresh_at st x ==> _ /\ _ /\ _`
       (qspec_then `src` mp_tac) >> asm_simp_tac bool_ss []) >>
  conj_tac >-
    (qpat_assum `!x. not_fresh_at st x ==> _ /\ _ /\ _`
       (qspec_then `dst` mp_tac) >> asm_simp_tac bool_ss []) >>
  conj_tac >-
    (qpat_assum `!x. not_fresh_at st x ==> _ /\ _ /\ _`
       (qspec_then `dp` mp_tac) >> asm_simp_tac bool_ss []) >>
  rpt conj_tac >>
  (irule ptr_covers_old_transport >> qexistsl_tac [`G`,`s`,`st`,`tn`] >>
   reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
   qpat_assum `!x. not_fresh_at st x ==> _ /\ _ /\ _` mp_tac >>
   POP_ASSUM_LIST (K all_tac) >> simp_tac (srw_ss()) [lookup_var_def] >>
   metis_tac[])
QED
Finalise log_scalar_member_cons_seq_ptr
