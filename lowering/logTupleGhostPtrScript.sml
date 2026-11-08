(* Footprint-facing adapters for existing exterior ghost transport. No claim
   is made about unused destination capacity being clean. *)
Theory logTupleGhostPtr
Ancestors
  logFieldGhostPtr abiDecoderFrame bodyPtrDefs stmtFragPtr compileEnv
  ptrDiscipline venomState finite_map words list pred_set arithmetic

Theorem ghost_kept_no_new_memory_taint:
  ghost_kept ce es se G0 tn0 s0 G tn /\ se.cs_next_var <= sa.cs_next_var /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
  (!i. i IN tm.t_mem ==> i IN tn.t_mem) ==>
  ghost_kept ce es se G0 tn0 s0 H tm
Proof
  rw[ghost_kept_def] >> metis_tac[not_fresh_at_mono]
QED

(* Integer byte ranges make single-byte exterior tests equivalent to the
   ordinary observational footprint disjointness. *)
Theorem abi_footprint_byte_exterior:
  abi_footprint_disjoint i 1 fp <=>
  i NOTIN {j | EXISTS (\(b,n). b <= j /\ j < b+n) fp}
Proof
  simp[abi_footprint_disjoint_def, EXISTS_MEM, pairTheory.EXISTS_PROD] >>
  eq_tac
  >- (rpt gen_tac >> CCONTR_TAC >> gvs[] >>
      first_x_assum drule >> decide_tac) >>
  rpt strip_tac >> rename1 `MEM (b,n) fp` >>
  first_x_assum (qspecl_then [`b`,`n`] mp_tac) >> simp[] >> decide_tac
QED

Theorem ghost_inv_footprint_transport:
  ghost_inv d ce cx es G tn s /\ local_ptrs_rel func ce es.scopes s /\
  local_ptrs_reserved ce sa /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!n b sz. local_region ce es.scopes s n b sz ==> abi_footprint_disjoint b sz fp) /\
  abi_decode_footprint_frame fp s t /\
  (!i. abi_footprint_disjoint i 1 fp ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  (!p. not_fresh_at sa p ==>
    lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
    op_taint tm (Var p) = op_taint tn (Var p)) ==>
  ghost_inv d ce cx es H tm t
Proof
  strip_tac >> irule ghost_inv_exterior_transport >>
  qexistsl_tac [`G`,`func`,`s`,`sa`,`tn`,
    `{j | EXISTS (\(b,n). b <= j /\ j < b+n) fp}`] >>
  asm_simp_tac bool_ss [] >>
  conj_tac
  >- (rpt strip_tac >>
      `abi_footprint_disjoint b sz fp` by metis_tac[] >>
      fs[abi_footprint_disjoint_def, EXISTS_MEM, pairTheory.EXISTS_PROD] >>
      metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS, NOT_LESS]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >>
      `abi_footprint_disjoint i 1 fp` by metis_tac[abi_footprint_byte_exterior] >>
      fs[abi_decode_footprint_frame_def]) >>
  fs[abi_decode_footprint_frame_def]
QED

(* Protected old allocations and locals need exterior taint equality only.
   This avoids any assumption about the encoder's unused output capacity. *)
Theorem ghost_kept_footprint_transport:
  ghost_kept ce es se G0 tn0 s0 G tn /\ se.cs_next_var <= sa.cs_next_var /\
  (!p. not_fresh_at sa p ==>
    FLOOKUP H p = FLOOKUP G p /\ op_taint tm (Var p) = op_taint tn (Var p)) /\
  (!i. abi_footprint_disjoint i 1 fp ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
  (!aid off sz i.
    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < se.cs_next_id /\
    (!n b sz'. local_region ce es.scopes s0 n b sz' ==>
      off+sz <= b \/ b+sz' <= off) /\ off <= i /\ i < off+sz ==>
    abi_footprint_disjoint i 1 fp) /\
  (!n b sz i. local_region ce es.scopes s0 n b sz /\ b <= i /\ i < b+sz /\
    (!k. dynarray_len_at ce n k ==> i < b+k \/ b+k+32 <= i) ==>
    abi_footprint_disjoint i 1 fp) ==>
  ghost_kept ce es se G0 tn0 s0 H tm
Proof
  strip_tac >> irule ghost_kept_exterior_transport >>
  qexistsl_tac [`G`,`sa`,`tn`, `{i | ~abi_footprint_disjoint i 1 fp}`] >>
  asm_simp_tac bool_ss [] >> simp[] >> metis_tac[ADD_ASSOC]
QED
