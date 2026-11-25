(* Frame the raw ALLOCA endpoint, including a reused allocation site. *)
Theory bodyECAddAllocFrameMods
Ancestors
  bodyFullAllocaFresh bodyFullPostsMods bodyFullHashKeccakFixed
  bodyInvSplit bodyPtrDefs exprSimMemDefs loweringStateRelDefs
  exprLoweringProps abiBuiltinAllocation emitHelperProps fragExec stmtReasonMemory
  venomMemDefs venomInst bodyFullShadowBodyInv ptrDiscipline
  venomExecSemantics vyperStorageFootprint venomState vyperState
  finite_map words exprSimAlloc

Theorem ecadd_alloc_new_rows[local]:
  compile_alloc_buffer n sa = (buf,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK r /\
  n < dimword (:256) /\ FLOOKUP r.vs_allocas aid = SOME (b,sz) ==>
  FLOOKUP s.vs_allocas aid = SOME (b,sz) \/ s.vs_alloca_next <= b
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[run_inst_seq_def, AllCaseEqs()] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_alloca_eq] >> Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >>
  gvs[AllCaseEqs(), update_var_def, FLOOKUP_UPDATE, w2n_n2w] >>
  rpt strip_tac >> Cases_on `aid = sa.cs_next_id` >> gvs[FLOOKUP_UPDATE]
QED

Theorem ecadd_alloc_immutables[local]:
  immutable_frame_mods func ce cx es s /\
  t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
       FLOOKUP s.vs_allocas aid = SOME (b,sz) \/ s.vs_alloca_next <= b) /\
  (!id b sz. local_region ce es.scopes t id b sz <=> local_region ce es.scopes s id b sz) ==>
  immutable_frame_mods func ce cx es t
Proof
  strip_tac >> fs[immutable_frame_mods_def] >> conj_tac
  >- (fs[immutables_rel_mods_def, immutables_rel_def] >> first_assum ACCEPT_TAC) >>
  fs[immutable_alloca_sep_mods_def] >> rpt gen_tac >> strip_tac >>
  irule immutable_alloca_sep_frame >> qexistsl [`s`,`es`] >> simp[] >>
  rpt gen_tac >> disch_tac >> disj1_tac >> qexists `id` >>
  `!u. local_region (ce with ce_module := src) es.scopes u id b sz =
       local_region ce es.scopes u id b sz` by simp[local_region_def] >>
  metis_tac[]
QED

Theorem ecadd_alloc_ghost[local]:
  ghost_inv_at_mods D lo d ce cx es G tn s /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  t with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
           vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
  allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!i. i IN tn'.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < stop)) ==>
  ghost_inv_at_mods D lo d ce cx es G' tn' t
Proof
  strip_tac >>
  `ghost_inv_at D 0 d ce cx es G tn s /\ lo <= s.vs_alloca_next` by
    (fs[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at D 0 d ce cx es G' tn' t` by
    (irule (INST_TYPE [alpha |-> ``:256``] alloc_buffer_ghost_inv_at) >>
     conj_tac >- simp[allocas_from_def] >>
     qexistsl [`G`,`H`,`ctx`,`stop`,`func`,`s`,`sa`,`tn`] >> simp[]) >>
  `t.vs_memory = s.vs_memory` by
    (qpat_assum `t with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `!i. i < lo /\ i IN tn'.t_mem ==> i IN tn.t_mem` by (simp[] >> decide_tac) >>
  fs[ghost_inv_at_mods_def, ghost_inv_at_def] >> rpt conj_tac
  >- metis_tac[]
  >- (rpt strip_tac >> `not_fresh_at sa x` by fs[local_ptrs_reserved_def] >>
      metis_tac[]) >>
  decide_tac
QED

Theorem ecadd_alloc_owner_sep[local]:
  immutable_frame_mods func ce cx es t /\
  MEM (mk_inst aid ALLOCA [Lit (n2w n)] [p]) (fn_insts func) /\
  FLOOKUP t.vs_allocas aid = SOME (b,n) ==>
  !src tops. ALOOKUP ce.ce_modules src = SOME tops /\ ce.ce_is_ctor ==>
    (!name ty tv off.
      FLOOKUP ce.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
      ce.ce_module_var_type (src,name) = SOME ty /\ evaluate_type (get_tenv cx) ty = SOME tv ==>
      regions_disjoint b n off (type_memory_size tv)) /\
    (!name tv iv off.
      FLOOKUP ce.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
             | SOME imms => get_source_immutables src imms) name = SOME (tv,iv) ==>
      regions_disjoint b n off (type_memory_size tv))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  fs[immutable_frame_mods_def, immutable_alloca_sep_mods_def] >>
  first_x_assum (drule_then mp_tac) >>
  simp[immutable_alloca_sep_def, immutable_decl_sep_alt] >> strip_tac >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!name ty tv off. _ ==> _` (drule_all_then strip_assume_tac) >>
      qpat_assum `!aid b sz. _ ==> _` (drule_then mp_tac) >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def, DISJ_COMM]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!name tv iv off. _ ==> _` (drule_all_then strip_assume_tac) >>
  qpat_assum `!inst b sz. _ ==> _`
    (qspecl_then [`mk_inst aid ALLOCA [Lit (n2w n)] [p]`,`b`,`n`] mp_tac) >>
  (impl_tac >- simp[venomInstTheory.mk_inst_def]) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def, DISJ_COMM]
QED

Theorem ecadd_alloc_frame_mods:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  n < dimword (:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK r /\
  t = r with vs_inst_idx := LENGTH sb.cs_current_insts /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,n) /\
  t with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
           vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
  allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!i. i IN tn'.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < b + n)) /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s /\
  immutable_frame_mods func ce cx es s /\
  ghost_inv_at_mods D lo d ce cx es G tn s /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  immutable_frame_mods func ce cx es t /\ ghost_inv_at_mods D lo d ce cx es G' tn' t /\
  (!src tops. ALOOKUP ce.ce_modules src = SOME tops /\ ce.ce_is_ctor ==>
    (!name ty tv off.
      FLOOKUP ce.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
      ce.ce_module_var_type (src,name) = SOME ty /\ evaluate_type (get_tenv cx) ty = SOME tv ==>
      regions_disjoint b n off (type_memory_size tv)) /\
    (!name tv iv off.
      FLOOKUP ce.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
             | SOME imms => get_source_immutables src imms) name = SOME (tv,iv) ==>
      regions_disjoint b n off (type_memory_size tv)))
Proof
  strip_tac >>
  `t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section` by
    (qpat_assum `t with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `!id b sz. local_region ce es.scopes t id b sz <=> local_region ce es.scopes s id b sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     metis_tac[local_ptrs_reserved_def]) >>
  conj_asm1_tac
  >- (irule ecadd_alloc_immutables >> qexists `s` >> simp[] >>
      rpt gen_tac >> disch_tac >> drule_all_then ACCEPT_TAC ecadd_alloc_new_rows) >>
  conj_tac
  >- drule_all_then ACCEPT_TAC ecadd_alloc_ghost >>
  drule_all buffer_alloc_code >> strip_tac >>
  qpat_x_assum `immutable_frame_mods _ _ _ _ s` kall_tac >>
  rpt gen_tac >> strip_tac >> drule_all_then ACCEPT_TAC ecadd_alloc_owner_sep
QED
