(* Fixed-capacity source traversal; only the meaningful source bytes must be clean. *)
Theory logScalarMembersPtr
Ancestors
  logScalarMembersStepPtr logScalarChildShape logInstSeqPtr
  stmtSimLogMembersRun stmtSimLogEncodeLayout stmtSimLogScalarMembers abiEncoderMemberCode
  abiEncoderCounters abiDecoderArrayInit abiDecoderFrame
  abiEncoderMembersInput abiEncoder emitHelperProps exprLoweringProps
  bodyPtrDefs ptrDiscipline fragGasSeqPtr abiEncoderInput
  compileEnv emitHelper venomState venomInst words list arithmetic

Theorem log_scalar_members_seq_ptr:
  !infos src dst so ho dp st out final tys avs pre pvs sb d hl cap limit_st p s G tn srcCap.
  compile_abi_encode_complex_elems (Var dst) (Var src) infos so ho (Var dp) st = (out,final) /\
  log_members_layout infos tys avs pre pvs sb so ho d hl cap s.vs_memory /\
  (!q. mem_agree_outside tn.t_mem s.vs_memory q ==>
    abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) (sb+so)
      (abi_encoder_member_span infos) q) /\
  not_fresh_at st src /\ not_fresh_at st dst /\ not_fresh_at st dp /\
  lookup_var src s = SOME (n2w sb) /\ lookup_var dst s = SOME (n2w d) /\
  lookup_var dp s = SOME (n2w p) /\
  mload p s = n2w (hl+LENGTH (FLAT (abi_tuple_tails pre pvs))) /\
  ptr_covers G tn src s srcCap /\ ptr_covers G tn dst s cap /\ ptr_covers G tn dp s 32 /\
  so+abi_encoder_member_span infos <= srcCap /\ sb+srcCap < dimword(:256) /\
  d+cap < dimword(:256) /\ p+32 < dimword(:256) /\
  (sb+so+abi_encoder_member_span infos <= d \/ d+cap <= sb+so) /\
  (sb+so+abi_encoder_member_span infos <= p \/ p+32 <= sb+so) /\
  (d+cap <= p \/ p+32 <= d) /\
  (!i. d <= i /\ i < d+ho ==> i NOTIN tn.t_mem) /\
  (!i. d+hl <= i /\ i < d+hl+LENGTH (FLAT (abi_tuple_tails pre pvs)) ==>
    i NOTIN tn.t_mem) /\
  (!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s ==>
  ?H tm t.
    run_inst_seq (emitted_insts st final) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st final) s H tm /\
    inst_extends st final /\ fresh_vars_wrt limit_st t /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st final) /\
    log_members_layout [] [] [] (pre++tys) (pvs++avs)
      sb (so+abi_encoder_member_span infos)
      (ho+SUM (MAP (\(_,asz,_,_). asz) infos)) d hl cap t.vs_memory /\
    mload p t = n2w (hl+LENGTH (FLAT (abi_tuple_tails (pre++tys) (pvs++avs)))) /\
    abi_decode_footprint_frame [(d,cap);(p,32)] s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\
    (!q. mem_agree_outside tm.t_mem t.vs_memory q ==>
      abi_encoder_input (AbiComplex []) (Tuple []) (ListV [])
        (sb+(so+abi_encoder_member_span infos)) (abi_encoder_member_span []) q) /\
    (!i. d <= i /\ i < d+(ho+SUM (MAP (\(_,asz,_,_). asz) infos)) ==> i NOTIN tm.t_mem) /\
    (!i. d+hl <= i /\ i < d+hl+LENGTH (FLAT (abi_tuple_tails (pre++tys) (pvs++avs))) ==>
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
    ptr_covers H tm src t srcCap /\ ptr_covers H tm dst t cap /\ ptr_covers H tm dp t 32
Proof
  Induct >- suspend "nil" >>
  qx_gen_tac `info` >> PairCases_on `info` >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule log_members_layout_lengths >> strip_tac >>
  Cases_on `tys` >- fs[] >> Cases_on `avs` >- fs[] >>
  rename1 `log_members_layout _ (ty::tys) (av::avs) _ _ _ _ _ _ _ _ _` >>
  drule abi_encoder_member_cons_trace >> strip_tac >>
  drule abi_encoder_members_bounds >> strip_tac >>
  suspend "cons"
QED

Resume log_scalar_members_seq_ptr[nil]:
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ [] _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_encode_child_def, comp_return_def] >> strip_tac >> gvs[] >>
  drule log_members_layout_lengths >> strip_tac >>
  `tys = [] /\ avs = []` by (Cases_on `tys` >> Cases_on `avs` >> fs[]) >>
  gvs[abi_encoder_member_span_def] >> qexistsl_tac [`G`,`tn`,`s`] >>
  simp[emitted_insts_def, run_inst_seq_def, inst_seq_ptr_def, inst_extends_def,
    abi_decode_footprint_frame_refl, abi_encoder_member_span_def]
QED
Resume log_scalar_members_seq_ptr[cons]:
  markerLib.RESUME_TAC >>
  rename1 `compile_abi_encode_complex_elems _ _ ((ei,asz,mz,dyn)::infos) _ _ _ _ = _` >>
  `?elem. elem_src = Var elem` by
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     metis_tac[]) >>
  qpat_x_assum `elem_src = Var elem` SUBST_ALL_TAC >>
  `child_end.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`sa` |-> `prepared`, `end_st` |-> `child_end`, `out` |-> `child_len`]
    log_scalar_member_cons_seq_ptr) >>
  impl_tac >- suspend "cons_pre" >>
  disch_then (qx_choose_then `G1` (qx_choose_then `tn1` (qx_choose_then `v` strip_assume_tac))) >>
  suspend "recurse"
QED

Resume log_scalar_members_seq_ptr[cons_pre]:
  markerLib.RESUME_TAC >>
  asm_simp_tac bool_ss [] >>
  qpat_assum `so+abi_encoder_member_span _ <= srcCap` mp_tac >>
  qpat_assum `sb+so+abi_encoder_member_span _ <= d \/ _` mp_tac >>
  qpat_assum `sb+so+abi_encoder_member_span _ <= p \/ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp_tac (srw_ss()) [abi_encoder_member_span_def, ADD_ASSOC]
QED

Resume log_scalar_members_seq_ptr[recurse]:
  markerLib.RESUME_TAC >>
  drule abi_encoder_child_bounds >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `st.cs_next_var <= child_end.cs_next_var` by decide_tac >>
  `!x. not_fresh_at st x ==> not_fresh_at child_end x` by
    (simp_tac bool_ss [not_fresh_at_def] >> rpt strip_tac >>
     qpat_x_assum `!n. st.cs_next_var <= n ==> _` (qspec_then `n` mp_tac) >>
     impl_tac >- decide_tac >> simp[]) >>
  qabbrev_tac `u = v with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st child_end)` >>
  `ptr_covers G1 tn1 src u srcCap` by
    (simp_tac (srw_ss()) [Abbr `u`, ptr_covers_def, lookup_var_def] >>
     qpat_assum `ptr_covers G1 tn1 src v srcCap` mp_tac >>
     simp_tac (srw_ss()) [ptr_covers_def, lookup_var_def]) >>
  qpat_x_assum `!src dst so ho dp st out final tys avs pre pvs sb d hl cap limit_st p s G tn srcCap. _`
    drule >>
  disch_then (drule_at (Pat `ptr_covers _ _ src _ _`)) >>
  `log_members_layout infos tys avs (pre++[ty]) (pvs++[av]) sb (so+mz) (ho+asz)
    d hl cap u.vs_memory` by
    (simp_tac (srw_ss()) [Abbr `u`] >> first_assum ACCEPT_TAC) >>
  disch_then drule >>
  `lookup_var dp u = SOME (n2w p) /\ fresh_vars_wrt limit_st u` by
    (simp_tac (srw_ss()) [Abbr `u`, lookup_var_def, fresh_vars_wrt_def] >>
     rule_assum_tac (SIMP_RULE (srw_ss()) [lookup_var_def, fresh_vars_wrt_def]) >>
     asm_simp_tac bool_ss []) >>
  disch_then (drule_at (Pat `lookup_var dp _ = _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  impl_tac >- suspend "recursive_pre" >>
  disch_then (qx_choose_then `H` (qx_choose_then `tm` (qx_choose_then `w` strip_assume_tac))) >>
  qexistsl_tac [`H`,`tm`,`w with vs_inst_idx := v.vs_inst_idx`] >>
  suspend "compose"
QED

Resume log_scalar_members_seq_ptr[recursive_pre]:
  markerLib.RESUME_TAC >>
  simp_tac (srw_ss()) [Abbr `u`, ptr_covers_def, lookup_var_def, mload_def] >>
  rule_assum_tac (SIMP_RULE (srw_ss()) [ptr_covers_def, lookup_var_def, mload_def]) >>
  asm_simp_tac bool_ss [] >>
  qpat_assum `so+abi_encoder_member_span _ <= srcCap` mp_tac >>
  qpat_assum `sb+so+abi_encoder_member_span _ <= d \/ _` mp_tac >>
  qpat_assum `sb+so+abi_encoder_member_span _ <= p \/ _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp_tac (srw_ss()) [abi_encoder_member_span_def, ADD_ASSOC] >>
  decide_tac
QED

Resume log_scalar_members_seq_ptr[compose]:
  markerLib.RESUME_TAC >>
  qpat_assum `log_members_layout ((ei,asz,mz,dyn)::infos) _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any strip_assume_tac log_members_layout_cons_input) >>
  drule_all log_scalar_child_straight >> strip_tac >>
  `inst_extends st prepared` by (drule inst_extends_emit_op >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st prepared)` by
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac emitted_insts_emit_op) >>
     simp[mk_inst_def, is_terminator_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st child_end)` by
    (irule abi_decoder_emitted_every_append >> qexists_tac `prepared` >>
     asm_simp_tac bool_ss []) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts child_end final)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `emitted_insts st final = emitted_insts st child_end ++ emitted_insts child_end final` by
    (irule emitted_insts_append >> conj_tac >>
     first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [inst_extends_def])) >>
  conj_tac >-
    (asm_rewrite_tac[] >> qunabbrev_tac `u` >>
     drule_all successful_seq_ptr_append >> simp_tac bool_ss [] >> strip_tac >>
     first_assum ACCEPT_TAC) >>
  conj_tac >-
    (asm_rewrite_tac[] >> irule logInstSeqPtrTheory.inst_seq_ptr_append >>
     asm_simp_tac bool_ss [] >> qexistsl_tac [`G1`,`v`,`tn1`] >>
     asm_simp_tac bool_ss [Abbr `u`]) >>
  conj_tac >- (irule inst_extends_trans >> qexists_tac `child_end` >>
    conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `fresh_vars_wrt limit_st w` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> simp_tac (srw_ss()) [fresh_vars_wrt_def]) >>
  conj_tac >- (asm_simp_tac (srw_ss()) []) >>
  suspend "post"
QED

Resume log_scalar_members_seq_ptr[post]:
  markerLib.RESUME_TAC >>
  simp_tac (srw_ss()) [GSYM APPEND_ASSOC, APPEND, abi_encoder_member_span_def, ADD_ASSOC,
    mload_def] >>
  rule_assum_tac (SIMP_RULE std_ss
    [GSYM APPEND_ASSOC, APPEND, abi_encoder_member_span_def, MAP, SUM, ADD_ASSOC, mload_def]) >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "memory_frame" >>
  ntac 3 (conj_tac >- (asm_simp_tac (srw_ss()) [Abbr `u`])) >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "taint_frame" >>
  ntac 3 (conj_tac >- (asm_simp_tac bool_ss [])) >>
  conj_tac >- suspend "variables" >>
  simp_tac (srw_ss()) [lookup_var_def, ptr_covers_def] >>
  rule_assum_tac (SIMP_RULE (srw_ss()) [lookup_var_def, ptr_covers_def]) >>
  asm_simp_tac bool_ss []
QED

Resume log_scalar_members_seq_ptr[memory_frame]:
  markerLib.RESUME_TAC >>
  qpat_assum `abi_decode_footprint_frame _ s v` mp_tac >>
  qpat_assum `abi_decode_footprint_frame _ u w` mp_tac >>
  simp_tac (srw_ss()) [Abbr `u`, abi_decode_footprint_frame_def] >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED
Resume log_scalar_members_seq_ptr[taint_frame]:
  markerLib.RESUME_TAC >>
  qpat_assum `!i. _ ==> (i IN tm.t_mem <=> i IN tn1.t_mem)` mp_tac >>
  qpat_assum `!i. _ ==> (i IN tn1.t_mem <=> i IN tn.t_mem)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED
Resume log_scalar_members_seq_ptr[variables]:
  markerLib.RESUME_TAC >>
  qpat_assum `!v. not_fresh_at child_end v ==> _` mp_tac >>
  qpat_assum `!v. not_fresh_at st v ==> _ /\ _ /\ _` mp_tac >>
  qpat_assum `!x. not_fresh_at st x ==> not_fresh_at child_end x` mp_tac >>
  simp_tac (srw_ss()) [Abbr `u`, lookup_var_def] >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED
Finalise log_scalar_members_seq_ptr
