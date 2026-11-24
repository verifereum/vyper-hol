(* The allocation prefix of the linked mapping-slot computation. The site
   can already be present; the counted run stays at the original floor. *)
Theory bodyWriteMapScratchAllocMods
Ancestors
  bodyFullAllocaFresh bodyFullHashKeccakFixed bodyFullShadowBodyInv
  bodyFullPostsMods bodyInvSplit exprLoweringProps exprSimAlloc loweringHalt
  abiBuiltinAllocation emitHelperProps stmtReasonMemory fragExec
  venomState venomInst finite_map words ptrDiscipline bodyPtrDefs
  loweringStateRelDefs venomMemDefs ASCIInumbers

Theorem scratch_alloc_site[local]:
  compile_alloc_buffer 64 sa = (buf,sm) /\ buf.buf_operand = Var p /\
  run_inst_seq (emitted_insts sa sm) s = OK raw /\
  t = raw with vs_inst_idx := k /\ FLOOKUP t.vs_allocas aid = SOME (b,n) ==>
  FLOOKUP s.vs_allocas aid = SOME (b,n) \/ s.vs_alloca_next <= b
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[run_inst_seq_def, AllCaseEqs()] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_alloca_eq] >> Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >>
  gvs[AllCaseEqs(), update_var_def, FLOOKUP_UPDATE, w2n_n2w] >>
  rpt strip_tac >> Cases_on `aid = sa.cs_next_id` >> gvs[FLOOKUP_UPDATE]
QED

Theorem scratch_alloc_immutable[local]:
  immutable_frame_mods func cenv cx es s /\
  t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
    FLOOKUP s.vs_allocas aid = SOME (b,sz) \/ s.vs_alloca_next <= b) /\
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  immutable_frame_mods func cenv cx es t
Proof
  strip_tac >>
  `!src name b sz. local_region (cenv with ce_module := src) es.scopes t name b sz <=>
                    local_region (cenv with ce_module := src) es.scopes s name b sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!src tops. _ ==> immutables_rel _ _ _ _ _ _`
        (drule_then assume_tac) >>
      fs[immutables_rel_def] >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> irule immutable_alloca_sep_frame >>
  qexistsl_tac [`s`,`es`] >> simp[] >> metis_tac[]
QED

Theorem scratch_alloc_ghost[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Ga x = FLOOKUP G x /\
    op_taint tna (Var x) = op_taint tn (Var x)) /\
  t with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
            vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
  allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  tna.t_stor = tn.t_stor /\ tna.t_trans = tn.t_trans /\ tna.t_imm = tn.t_imm /\
  (!i. i IN tna.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < stop)) ==>
  ghost_inv_at_mods D lo d cenv cx es Ga tna t
Proof
  strip_tac >>
  `ghost_inv_at D 0 d cenv cx es G tn s /\ lo <= s.vs_alloca_next` by
    (fs[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `allocas_from 0 t` by simp[allocas_from_def] >>
  `ghost_inv_at D 0 d cenv cx es Ga tna t` by
    (irule alloc_buffer_ghost_inv_at >>
     rpt (first_assum (irule_at Any)) >>
     fs[venom_state_component_equality] >> qexists_tac `stop` >> simp[]) >>
  `t.vs_memory = s.vs_memory` by
    (qpat_assum `t with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `!i. i < lo /\ i IN tna.t_mem ==> i IN tn.t_mem` by
    (rpt gen_tac >> simp[] >> decide_tac) >>
  `!i. i < lo /\ i IN tna.t_mem ==>
       imm_section_dead_mods cenv (mem_bytes_at 0 lo t.vs_memory) i` by
    (fs[ghost_inv_at_mods_def] >> rpt strip_tac >>
     `i < lo /\ i IN tn.t_mem` by metis_tac[] >>
     qpat_assum `!i. i < lo /\ i IN tn.t_mem ==> _` (drule_then ACCEPT_TAC)) >>
  `!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==>
       FLOOKUP Ga x = NONE /\ op_taint tna (Var x) = {}` by
    (fs[ghost_inv_at_mods_def, local_ptrs_reserved_def] >> rpt strip_tac >>
     `not_fresh_at sa x` by metis_tac[] >> metis_tac[]) >>
  `lo <= t.vs_alloca_next` by decide_tac >>
  fs[ghost_inv_at_mods_def, ghost_inv_at_def] >> first_assum ACCEPT_TAC
QED

Theorem mapping_scratch_alloc_run_mods:
  compile_alloc_buffer 64 sa = (buf,sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  alloca_history func s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (?H. P H) /\
  (!H. P H ==> stmt_state_rel H ctx func cenv cx es s /\
                immutable_frame_mods func cenv cx es s /\
                ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) ==>
  ?p b t Ga tna raw.
    buf.buf_operand = Var p /\ p = STRING #"%" (toString sa.cs_next_var) /\
    not_fresh_at sm p /\ local_ptrs_reserved cenv sm /\
    (!x. not_fresh_at sa x ==> not_fresh_at sm x) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w] [p]) (fn_insts func) /\
    run_inst_seq (emitted_insts sa sm) s = OK raw /\
    t = raw with vs_inst_idx := LENGTH sm.cs_current_insts /\
    Ga = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit 64w] [p]) raw /\
    tna = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit 64w] [p]) s raw tn /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Ga,tna)) /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    t with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
             vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
    alloca_history func t /\ allocas_from lo t /\
    lo <= b /\ lo <= t.vs_alloca_next /\ s.vs_alloca_next <= t.vs_alloca_next /\
    lookup_var p t = SOME (n2w b) /\ ptr_covers Ga tna p t 64 /\
    op_taint tna (Var p) = {} /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,64) /\ FLOOKUP Ga p = SOME (b,64) /\
    b + 64 < dimword (:256) /\ b + 64 <= t.vs_alloca_next /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP t.vs_allocas aid = SOME e) /\
    (!aid a n. FLOOKUP t.vs_allocas aid = SOME (a,n) ==>
       FLOOKUP s.vs_allocas aid = SOME (a,n) \/ s.vs_alloca_next <= a) /\
    (!aid a n. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,n) ==>
       regions_disjoint b 64 a n) /\
    (!name a n. local_region cenv es.scopes t name a n ==> a+n <= b \/ b+64 <= a) /\
    tna.t_stor = tn.t_stor /\ tna.t_trans = tn.t_trans /\ tna.t_imm = tn.t_imm /\
    (!i. i IN tna.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < b+64)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Ga x = FLOOKUP G x /\
      op_taint tna (Var x) = op_taint tn (Var x)) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!H. P H ==> stmt_state_rel H ctx func cenv cx es t /\
                 immutable_frame_mods func cenv cx es t /\
                 ghost_inv_at_mods (DF H) lo d cenv cx es Ga tna t)
Proof
  strip_tac >> qpat_assum `!H. P H ==> _` (drule_then strip_assume_tac) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `64 < dimword (:256)` by simp[dimword_def] >>
  drule stmt_state_rel_allocas_below_fmp >> strip_tac >>
  drule_all (INST_TYPE [beta |-> alpha] alloc_buffer_origin_ptr_path_with_raw_endpoint) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`p`,`w`,`t`,`Ga`,`tna`,`raw`] strip_assume_tac)) >>
  suspend "endpoint"
QED

Resume mapping_scratch_alloc_run_mods[endpoint]:
  `!aid a n. FLOOKUP t.vs_allocas aid = SOME (a,n) ==>
     FLOOKUP s.vs_allocas aid = SOME (a,n) \/ s.vs_alloca_next <= a` by
    (rpt gen_tac >> disch_tac >> drule_all_then ACCEPT_TAC scratch_alloc_site) >>
  `t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\ ~t.vs_halted` by
    (qpat_assum `t with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality] >> strip_tac >> fs[]) >>
  `lo <= w2n w` by metis_tac[allocas_from_def] >>
  `op_taint tna (Var p) = {}` by fs[ptr_covers_def] >>
  `p = STRING #"%" (toString sa.cs_next_var) /\
   (!x. not_fresh_at sa x ==> not_fresh_at sm x) /\ sa.cs_next_var <= sm.cs_next_var` by
     (drule compile_alloc_buffer_parts >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w] [p]) (fn_insts func)` by
    (drule_all buffer_alloc_code >> simp[]) >>
  `immutable_frame_mods func cenv cx es t` by
    (irule scratch_alloc_immutable >> qexistsl_tac [`s`,`sa`] >> simp[]) >>
  suspend "finish"
QED

Resume mapping_scratch_alloc_run_mods[finish]:
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (`stmt_state_rel H ctx func cenv cx es t` by
       (qpat_assum `!J. stmt_state_rel J ctx func cenv cx es s ==>
                       stmt_state_rel J ctx func cenv cx es t`
           (drule_then ACCEPT_TAC)) >>
     drule_then ACCEPT_TAC stmt_state_rel_allocas_below_fmp) >>
  `lo <= t.vs_alloca_next` by decide_tac >>
  `!H. P H ==> stmt_state_rel H ctx func cenv cx es t /\
               immutable_frame_mods func cenv cx es t /\
               ghost_inv_at_mods (DF H) lo d cenv cx es Ga tna t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. P H ==> _` (drule_then strip_assume_tac) >>
     conj_tac
     >- (qpat_assum `!J. stmt_state_rel J ctx func cenv cx es s ==>
                         stmt_state_rel J ctx func cenv cx es t`
           (drule_then ACCEPT_TAC)) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     drule_all_then ACCEPT_TAC scratch_alloc_ghost) >>
  qexistsl_tac [`p`,`w2n w`,`t`,`Ga`,`tna`,`raw`] >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `!name a n. local_region cenv es.scopes t name a n ==>
                       regions_disjoint _ _ a n` mp_tac >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def, DISJ_COMM]
QED

Finalise mapping_scratch_alloc_run_mods
