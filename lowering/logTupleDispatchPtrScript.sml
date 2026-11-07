(* Scalar log tuples: one sequence interface, retaining cursor ownership only
   for the dynamic branch. *)
Theory logTupleDispatchPtr
Ancestors
  logTupleDynamicPtr logAbiStaticPtr logAbiInputPtr abiEncoderInput abiEncoder
  abiEncoderMembersInput stmtSimLogEncodeLayout abiEncoderBufferFrame abiEncoderComplexDynamic
  abiDecoderFrame bodyPtrDefs emitHelperProps exprLoweringProps compileEnv
  context fragExec fragGasSeqPtr instIdxIndep venomMemProps valueEncodingProps
  venomExecSemantics venomState venomInst words list arithmetic finite_map pred_set

(* Supplement the copy pointer certificate with ordinary operational effects. *)
Theorem log_abi_copy_run_frame:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiCopy n) sa = (out,sb) /\
  lookup_var src s = SOME (n2w a) /\ lookup_var dst s = SOME (n2w b) /\
  a < dimword(:256) /\ b < dimword(:256) /\ n < dimword(:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  inst_extends sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  t.vs_vars = s.vs_vars /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
  abi_decode_footprint_frame [(b,n)] s t
Proof
  strip_tac >>
  `out = Lit (n2w n) /\ emit_void MCOPY [Var dst;Var src;Lit (n2w n)] sa = ((),sb)` by
    (gvs[Once compile_abi_encode_child_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> gvs[] >> metis_tac[pairTheory.PAIR_EQ]) >>
  drule inst_extends_emit_void >> disch_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `t = mcopy b a n s` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
       eval_operand_def, w2n_n2w]) >>
  `abi_decode_footprint_frame [(b,n)] s (mcopy b a n s)` by
    (rewrite_tac[abi_decode_footprint_frame_def] >> conj_tac
     >- (rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >>
         fs[abi_footprint_disjoint_def]) >>
     simp[mcopy_def, write_memory_with_expansion_def]) >>
  asm_simp_tac bool_ss [] >>
  simp[mk_inst_def, is_terminator_def, mcopy_def, write_memory_with_expansion_def]
QED

Theorem compile_log_tuple_seq_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src) ei st = (out,end_st) /\
  fn_has_code st end_st func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce st /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~ctx_has_dalloca ctx /\ srcid <> st.cs_next_id /\ dstid <> st.cs_next_id /\
  FLOOKUP s.vs_allocas srcid = SOME (sb,srcCap) /\
  FLOOKUP s.vs_allocas dstid = SOME (d,cap) /\
  not_fresh_at st src /\ not_fresh_at st dst /\
  lookup_var src s = SOME (n2w sb) /\ lookup_var dst s = SOME (n2w d) /\
  ptr_covers G tn src s srcCap /\ ptr_covers G tn dst s cap /\
  sb+srcCap < dimword(:256) /\ d+cap < dimword(:256) /\
  (sb+srcCap <= d \/ d+cap <= sb) /\
  (!q. mem_agree_outside tn.t_mem s.vs_memory q ==>
    abi_encoder_input ei (Tuple tys) (ListV avs) sb inputCap q) /\
  inputCap <= srcCap /\ LENGTH (enc (Tuple tys) (ListV avs)) <= cap /\
  ((?n. ei = AbiCopy n) \/
   (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
    EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos)) ==>
  ?H tm t.
    run_inst_seq (emitted_insts st end_st) s = OK t /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts st end_st) s H tm /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st t /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st end_st) /\
    eval_operand out t = SOME (n2w (LENGTH (enc (Tuple tys) (ListV avs)))) /\
    op_taint tm out = {} /\ op_prov H out = NONE /\
    mem_bytes_at d (LENGTH (enc (Tuple tys) (ListV avs))) t.vs_memory =
      enc (Tuple tys) (ListV avs) /\
    (!i. d <= i /\ i < d+LENGTH (enc (Tuple tys) (ListV avs)) ==> i NOTIN tm.t_mem) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!v. not_fresh_at st v ==>
      lookup_var v t = lookup_var v s /\ FLOOKUP H v = FLOOKUP G v /\
      op_taint tm (Var v) = op_taint tn (Var v)) /\
    ((H = G /\ abi_decode_footprint_frame [(d,cap)] s t /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_halted = s.vs_halted /\
      (!i. ~(d <= i /\ i < d+cap) ==> (i IN tm.t_mem <=> i IN tn.t_mem))) \/
     (?p. (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
        EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos) /\
      abi_decode_footprint_frame [(d,cap);(p,32)] s t /\
      FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\ p+32 < dimword(:256) /\
      t.vs_allocas = (abi_builtin_allocate_state st.cs_next_id 32 s).vs_allocas /\
      t.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id 32 s).vs_alloca_next /\
      t.vs_halted = s.vs_halted /\
      (sb+srcCap <= p \/ p+32 <= sb) /\ (d+cap <= p \/ p+32 <= d) /\
      (!i. p <= i /\ i < p+32 ==> i NOTIN tm.t_mem) /\
      (!i. ~(d <= i /\ i < d+cap) /\ ~(p <= i /\ i < p+32) ==>
        (i IN tm.t_mem <=> i IN tn.t_mem))))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `(?n. _) \/ _` (DISJ_CASES_THEN strip_assume_tac)
  >- suspend "static" >>
  suspend "dynamic"
QED

Resume compile_log_tuple_seq_ptr[static]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `ei = AbiCopy n` SUBST_ALL_TAC >>
  `abi_encoder_input (AbiCopy n) (Tuple tys) (ListV avs) sb inputCap s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule robust_abi_copy_input_clean >> disch_tac >>
  `n <= inputCap /\ mem_bytes_at sb n s.vs_memory = enc (Tuple tys) (ListV avs)` by
    fs[abi_encoder_input_copy_iff] >>
  `LENGTH (enc (Tuple tys) (ListV avs)) = n` by
    metis_tac[LENGTH_mem_bytes_at] >>
  `n <= srcCap /\ n <= cap /\ sb+n < dimword(:256) /\ d+n < dimword(:256) /\
   sb < dimword(:256) /\ d < dimword(:256) /\ n < dimword(:256)` by
    (qpat_x_assum `n <= inputCap` mp_tac >>
     qpat_x_assum `inputCap <= srcCap` mp_tac >>
     qpat_x_assum `LENGTH _ <= cap` mp_tac >>
     qpat_x_assum `LENGTH _ = n` (fn th => rewrite_tac[th]) >>
     qpat_x_assum `sb+srcCap < _` mp_tac >>
     qpat_x_assum `d+cap < _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `ptr_covers G tn src s n /\ ptr_covers G tn dst s n` by
    (fs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS]) >>
  drule_all compile_abi_copy_seq_ptr >>
  disch_then (qspecl_then [`func`,`PG`,`D`]
    (qx_choose_then `tm` (qx_choose_then `t` (REPEAT_TCL CONJUNCTS_THEN assume_tac)))) >>
  drule_all log_abi_copy_run_frame >> strip_tac >>
  suspend "static_post"
QED

Resume compile_log_tuple_seq_ptr[dynamic]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `ei = AbiComplex infos` SUBST_ALL_TAC >>
  `abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb inputCap s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `abi_encoder_member_span infos <= inputCap` by
    (qpat_x_assum `abi_encoder_input _ _ _ _ _ s.vs_memory` mp_tac >>
     simp[abi_encoder_complex_input_iff] >> metis_tac[]) >>
  `abi_encoder_member_span infos <= srcCap` by decide_tac >>
  `!q. mem_agree_outside tn.t_mem s.vs_memory q ==>
    abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb
      (abi_encoder_member_span infos) q` by
    (rpt strip_tac >> irule abi_encoder_complex_input_span >>
     qexists_tac `inputCap` >> first_x_assum irule >> simp[]) >>
  mp_tac (SPEC_ALL compile_log_dynamic_tuple_seq_ptr) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  disch_then (qx_choose_then `H` (qx_choose_then `tm` (qx_choose_then `t`
    (qx_choose_then `p` (REPEAT_TCL CONJUNCTS_THEN assume_tac))))) >>
  qexistsl_tac [`H`,`tm`,`t`] >> asm_simp_tac bool_ss [] >>
  disj2_tac >> qexists_tac `p` >> asm_simp_tac bool_ss [] >>
  qexists_tac `infos` >> asm_simp_tac bool_ss []
QED

Resume compile_log_tuple_seq_ptr[static_post]:
  markerLib.RESUME_TAC >>
  `fresh_vars_wrt limit_st t` by gns[fresh_vars_wrt_def] >>
  `abi_decode_footprint_frame [(d,cap)] s t` by
    (irule abi_decode_footprint_frame_weaken >>
     qexists_tac `[(d,n)]` >> asm_simp_tac bool_ss [] >>
     simp[] >> decide_tac) >>
  `!i. ~(d <= i /\ i < d+cap) ==> (i IN tm.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >>
     qpat_x_assum `!i. ~(d <= i /\ i < d+n) ==> _` (qspec_then `i` mp_tac) >>
     `~(d <= i /\ i < d+n)` by decide_tac >> simp[]) >>
  qexistsl_tac [`G`,`tm`,`t`] >> asm_simp_tac bool_ss []
QED
Finalise compile_log_tuple_seq_ptr
