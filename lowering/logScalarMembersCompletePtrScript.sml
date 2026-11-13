(* Whole-member endpoint after cursor initialization, before the final length load. *)
Theory logScalarMembersCompletePtr
Ancestors
  logScalarMembersPtr logMembersInvariantPtr stmtSimLogScalarMembers
  stmtSimLogEncodeLayout stmtSimLogDataInput abiCanonicalWindows bodyPtrDefs
  compileEnv venomState venomInst words list arithmetic valueEncoding

Theorem log_scalar_members_complete_seq_ptr:
  compile_abi_encode_complex_elems (Var dst) (Var src) infos 0 0 (Var dp) st = (out,final) /\
  log_members_layout infos tys avs [] [] sb 0 0 d hl cap s.vs_memory /\
  (!q. mem_agree_outside tn.t_mem s.vs_memory q ==>
    abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb
      (abi_encoder_member_span infos) q) /\
  not_fresh_at st src /\ not_fresh_at st dst /\ not_fresh_at st dp /\
  lookup_var src s = SOME (n2w sb) /\ lookup_var dst s = SOME (n2w d) /\
  lookup_var dp s = SOME (n2w p) /\ mload p s = n2w hl /\
  ptr_covers G tn src s srcCap /\ ptr_covers G tn dst s cap /\ ptr_covers G tn dp s 32 /\
  abi_encoder_member_span infos <= srcCap /\ sb+srcCap < dimword(:256) /\
  d+cap < dimword(:256) /\ p+32 < dimword(:256) /\
  (sb+abi_encoder_member_span infos <= d \/ d+cap <= sb) /\
  (sb+abi_encoder_member_span infos <= p \/ p+32 <= sb) /\
  (d+cap <= p \/ p+32 <= d) /\
  (!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s ==>
  ?H tm t.
    run_inst_seq (emitted_insts st final) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st final) s H tm /\
    inst_extends st final /\ fresh_vars_wrt limit_st t /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st final) /\
    log_members_layout [] [] [] tys avs sb (abi_encoder_member_span infos) hl d hl cap t.vs_memory /\
    mload p t = n2w (hl+LENGTH (FLAT (abi_tuple_tails tys avs))) /\
    abi_decode_footprint_frame [(d,cap);(p,32)] s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\
    (!i. d <= i /\ i < d+hl ==> i NOTIN tm.t_mem) /\
    (!i. d+hl <= i /\ i < d+hl+LENGTH (FLAT (abi_tuple_tails tys avs)) ==> i NOTIN tm.t_mem) /\
    (!i. d <= i /\ i < d+LENGTH (enc (Tuple tys) (ListV avs)) ==> i NOTIN tm.t_mem) /\
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
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  mp_tac (Q.INST [`pre` |-> `[]`, `pvs` |-> `[]`, `so` |-> `0`, `ho` |-> `0`]
    (SPEC_ALL log_scalar_members_seq_ptr)) >>
  impl_tac >- suspend "pre" >>
  disch_then (qx_choose_then `H` (qx_choose_then `tm` (qx_choose_then `t` strip_assume_tac))) >>
  suspend "post"
QED

Resume log_scalar_members_complete_seq_ptr[pre]:
  markerLib.RESUME_TAC >>
  simp_tac (srw_ss()) [abi_tuple_tails_def] >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >> decide_tac
QED

Resume log_scalar_members_complete_seq_ptr[post]:
  markerLib.RESUME_TAC >>
  rule_assum_tac (SIMP_RULE bool_ss [APPEND, ADD_CLAUSES]) >>
  drule log_members_layout_empty_head >> disch_then (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
  qexistsl_tac [`H`,`tm`,`t`] >>
  ntac 5 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (asm_rewrite_tac[] >> first_assum ACCEPT_TAC) >>
  ntac 5 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (asm_rewrite_tac[] >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (drule log_members_layout_complete_clean >>
    disch_then (qspec_then `tm.t_mem` mp_tac) >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [] >>
  qpat_x_assum `!i. _ ==> (i IN tm.t_mem <=> i IN tn.t_mem)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED
Finalise log_scalar_members_complete_seq_ptr
