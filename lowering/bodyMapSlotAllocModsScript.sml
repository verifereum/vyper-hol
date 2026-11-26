(* The allocation boundary of the mapping-slot fragment. *)
Theory bodyMapSlotAllocMods
Ancestors
  bodyFullAllocaFresh bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit
  bodyFullHashKeccakFixed bodyMemoryDefs exprSimWordArgs exprSimAlloc
  loweringHalt stmtReasonMemory stmtSimProps exprLoweringProps loweringStateRelDefs
  loweringPosts ptrDiscipline bodyPtrDefs venomState venomInst fragExec compileEnv
  finite_map words rich_list stateRelProj venomMemDefs wordArgsPtr

Theorem map_slot_new_alloc[local]:
  compile_alloc_buffer 64 sa = (buf,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK raw /\
  t = raw with vs_inst_idx := k /\ FLOOKUP t.vs_allocas aid = SOME (b,n) ==>
  FLOOKUP s.vs_allocas aid = SOME (b,n) \/ s.vs_alloca_next <= b
Proof
  strip_tac >> drule compile_alloc_buffer_insts >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND, run_inst_seq_def, AllCaseEqs()] >>
  strip_tac >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_alloca_eq] >> Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >>
  gvs[AllCaseEqs(), update_var_def, FLOOKUP_UPDATE] >>
  strip_tac >> Cases_on `aid = sa.cs_next_id` >> gvs[FLOOKUP_UPDATE]
QED

Theorem map_slot_alloc_immutable[local]:
  immutable_frame_mods func cenv cx es s /\
  t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!aid b n. FLOOKUP t.vs_allocas aid = SOME (b,n) ==>
             FLOOKUP s.vs_allocas aid = SOME (b,n) \/ s.vs_alloca_next <= b) /\
  (!id b n. local_region cenv es.scopes t id b n <=>
            local_region cenv es.scopes s id b n) ==>
  immutable_frame_mods func cenv cx es t
Proof
  strip_tac >> fs[immutable_frame_mods_def] >> conj_tac
  >- (fs[immutables_rel_mods_def, immutables_rel_def] >> first_assum ACCEPT_TAC) >>
  fs[immutable_alloca_sep_mods_def] >> rpt gen_tac >> strip_tac >>
  irule immutable_alloca_sep_frame >> qexistsl_tac [`s`,`es`] >> simp[] >>
  rpt gen_tac >> disch_tac >> disj1_tac >> qexists_tac `id` >>
  `!st. local_region (cenv with ce_module := src) es.scopes st id b sz <=>
         local_region cenv es.scopes st id b sz` by simp[local_region_def] >>
  fs[] >>
  qpat_assum `!id b n. local_region _ _ t _ _ _ <=> _`
    (qspecl_then [`id`,`b`,`sz`] (fn th => ONCE_REWRITE_TAC[GSYM th])) >>
  first_assum ACCEPT_TAC
QED

Theorem map_slot_alloc_ghost[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
     lookup_var x t = lookup_var x s /\ FLOOKUP Ga x = FLOOKUP G x /\
     op_taint tna (Var x) = op_taint tn (Var x)) /\
  t with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
           vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
  t.vs_memory = s.vs_memory /\ allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  tna.t_stor = tn.t_stor /\ tna.t_trans = tn.t_trans /\ tna.t_imm = tn.t_imm /\
  (!i. i IN tna.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < stop)) ==>
  ghost_inv_at_mods D lo d cenv cx es Ga tna t
Proof
  strip_tac >>
  `ghost_inv_at D 0 d cenv cx es G tn s /\ lo <= s.vs_alloca_next` by
    (fs[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at D 0 d cenv cx es Ga tna t` by
    (irule alloc_buffer_ghost_inv_at >> simp[allocas_from_def] >>
     qexistsl_tac [`G`,`H`,`ctx`,`stop`,`func`,`s`,`sa`,`tn`] >>
     simp[allocas_from_def] >> rpt conj_tac
     >- (qpat_assum `t with <|vs_vars := _; vs_allocas := _;
                    vs_alloca_next := _; vs_inst_idx := _|> = s` mp_tac >>
         simp[venom_state_component_equality]) >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `!i. i < lo /\ i IN tna.t_mem ==> i IN tn.t_mem` by
    (rpt gen_tac >> simp[] >> decide_tac) >>
  fs[ghost_inv_at_mods_def, ghost_inv_at_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!nm e p z. _ ==> ptr_covers Ga tna p t z /\ _`
        (drule_all_then mp_tac) >> simp[])
  >- (qx_gen_tac `x` >> strip_tac >>
      `not_fresh_at sa x` by metis_tac[local_ptrs_reserved_imm_base] >>
      qpat_assum `!x. not_fresh_at sa x ==> _` (drule_then strip_assume_tac) >>
      qpat_assum `!x. _ ==> FLOOKUP G x = NONE /\ _` (drule_all_then strip_assume_tac) >> simp[]) >>
  decide_tac
QED

Theorem mapping_slot_alloc_mods:
  compile_alloc_buffer 64 sa = (buf,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  alloca_history func s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ P H0 /\
  (!H. P H ==> stmt_state_rel H ctx func cenv cx es s /\
                immutable_frame_mods func cenv cx es s /\
                ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) ==>
  ?p w t Ga tna.
    buf.buf_operand = Var p /\ not_fresh_at sb p /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w] [p]) (fn_insts func) /\
    lookup_var p t = SOME w /\ ptr_covers Ga tna p t 64 /\
    FLOOKUP Ga p = SOME (w2n w,64) /\ op_taint tna (Var p) = {} /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,64) /\
    lo <= w2n w /\ w2n w+64 < dimword (:256) /\ w2n w+64 <= t.vs_alloca_next /\
    (!name b n. local_region cenv es.scopes t name b n ==>
               b+n <= w2n w \/ w2n w+64 <= b) /\
    (!aid b n. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n) ==>
              regions_disjoint (w2n w) 64 b n) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Ga x = FLOOKUP G x /\
      op_taint tna (Var x) = op_taint tn (Var x)) /\
    t.vs_memory = s.vs_memory /\
    (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==>
               FLOOKUP t.vs_allocas aid = SOME ent) /\
    wb_frame cenv es es sa s t /\ pure_frame cenv func es sa s t /\
    ghost_kept_at lo cenv es sa G tn s Ga tna /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t /\
    allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,Ga,tna)) /\
    (!H. P H ==> stmt_state_rel H ctx func cenv cx es t /\
                  immutable_frame_mods func cenv cx es t /\
                  ghost_inv_at_mods (DF H) lo d cenv cx es Ga tna t)
Proof
  strip_tac >>
  qpat_assum `!H. P H ==> _` (qspec_then `H0` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  `64 < dimword (:256)` by simp[dimword_def] >>
  drule_all (INST_TYPE [beta |-> alpha] alloc_buffer_origin_ptr_path_with_raw_endpoint) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`p`,`w`,`t`,`Ga`,`tna`,`raw`] strip_assume_tac)) >>
  `!aid base len. FLOOKUP t.vs_allocas aid = SOME (base,len) ==>
     FLOOKUP s.vs_allocas aid = SOME (base,len) \/ s.vs_alloca_next <= base` by
    (rpt strip_tac >> irule map_slot_new_alloc >>
     qexistsl_tac [`buf`,`LENGTH sb.cs_current_insts`,`raw`,`sa`,`sb`,`t`] >> simp[]) >>
  qpat_x_assum `t = raw with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `Ga = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `tna = step_taint _ _ _ _` kall_tac >>
  suspend "frames"
QED

Resume mapping_slot_alloc_mods[frames]:
  `t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\ ~t.vs_halted` by
    (qpat_assum `~s.vs_halted` mp_tac >>
     qpat_assum `t with <|vs_vars := _; vs_allocas := _;
                        vs_alloca_next := _; vs_inst_idx := _|> = s`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `!id b n. local_region cenv es.scopes t id b n <=>
             local_region cenv es.scopes s id b n` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     rpt strip_tac >> `not_fresh_at sa p'` by metis_tac[local_ptrs_reserved_def] >> metis_tac[]) >>
  `wb_frame cenv es es sa s t` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`sa`,`s`] >> simp[wb_frame_refl] >>
     rpt strip_tac >> qpat_assum `!x. not_fresh_at sa x ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  `!aid b n. FLOOKUP s.vs_allocas aid = SOME (b,n) ==> b+n <= s.vs_alloca_next` by
    (drule stmt_state_rel_local_ptrs_alloca >> simp[alloca_inv_def, alloca_next_valid_def] >>
     strip_tac >> rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  `!name b n. local_region cenv es.scopes s name b n ==> b+n <= s.vs_alloca_next` by
    (rpt strip_tac >> drule_all body_local_region_frontier >> simp[]) >>
  `ghost_kept_at lo cenv es sa G tn s Ga tna` by
    (irule alloc_buffer_ghost_kept_at >> qexistsl_tac [`G`,`w2n w+64`,`s`,`tn`] >>
     simp[ghost_kept_at_refl] >> metis_tac[]) >>
  `immutable_frame_mods func cenv cx es t` by
    (irule map_slot_alloc_immutable >> qexists_tac `s` >> simp[]) >>
  `!H. P H ==> stmt_state_rel H ctx func cenv cx es t /\
               ghost_inv_at_mods (DF H) lo d cenv cx es Ga tna t` by
    (gen_tac >> strip_tac >> qpat_assum `!H. P H ==> _` (drule_then strip_assume_tac) >>
     conj_tac >- (first_x_assum irule >> first_assum ACCEPT_TAC) >>
     irule map_slot_alloc_ghost >> simp[] >>
     qexistsl_tac [`G`,`H`,`ctx`,`func`,`s`,`sa`,`w2n w+64`,`tn`] >> simp[] >>
     qpat_assum `t with <|vs_vars := _; vs_allocas := _;
                        vs_alloca_next := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  suspend "result"
QED

Resume mapping_slot_alloc_mods[result]:
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w] [p]) (fn_insts func)` by
    (drule compile_alloc_buffer_insts >> strip_tac >>
     `p = STRING #"%" (toString sa.cs_next_var)` by metis_tac[operand_11] >>
     drule_all buffer_alloc_code >> simp[]) >>
  `lo <= w2n w` by (fs[allocas_from_def] >> metis_tac[]) >>
  `op_taint tna (Var p) = {}` by fs[ptr_covers_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (`stmt_state_rel H0 ctx func cenv cx es t` by metis_tac[] >>
     drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  qexistsl_tac [`p`,`w`,`t`,`Ga`,`tna`] >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `local_region cenv es.scopes t name b n` by
        (qpat_assum `!id b n. local_region _ _ t _ _ _ <=> _` (fn th => simp[th])) >>
      qpat_assum `!nm b n. local_region _ _ t nm b n ==> regions_disjoint _ _ _ _`
        (drule_then mp_tac) >> simp[loweringStateRelDefsTheory.regions_disjoint_def, DISJ_COMM]) >>
  first_assum ACCEPT_TAC
QED

Finalise mapping_slot_alloc_mods
