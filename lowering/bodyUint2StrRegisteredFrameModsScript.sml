(* The allocation and decimal blocks frame the linked child landing. *)
Theory bodyUint2StrRegisteredFrameMods
Ancestors
  bodyShaRegisteredFrameMods exprSimUint2Str exprSimCopy exprSimWordArgs
  bodyFullAllocaFresh bodyMemoryDefs wordArgsPtr stateRelProj freshWrites
  bodyFullPostsMods loweringPosts loweringStateRelDefs venomMemDefs venomState
  venomInst finite_map list pred_set

Theorem uint2str_byte_frame[local]:
  u2s_frame a b sz ready t /\ ready.vs_memory = s.vs_memory /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id = sm.cs_next_id /\ FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) /\
  (!name off len. local_region ce mid.scopes s name off len ==>
                 b+sz <= off \/ off+len <= b) ==>
  pure_frame ce fn mid sm s t
Proof
  strip_tac >>
  qpat_assum `u2s_frame _ _ _ _ _` (strip_assume_tac o REWRITE_RULE[u2s_frame_def]) >>
  simp[pure_frame_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!name off len. local_region _ _ s _ _ _ ==> _` drule >>
      simp[Once DISJ_COMM] >> strip_tac >>
      qpat_assum `ready.vs_memory = _` (SUBST1_TAC o SYM) >>
      qpat_assum `!x y. _ ==> mem_bytes_at x y t.vs_memory = _` irule >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!j p n. _ ==> loweringStateRelDefs$regions_disjoint _ _ _ _`
    (qspec_then `inst` mp_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> strip_tac >>
  qpat_assum `ready.vs_memory = _` (SUBST1_TAC o SYM) >>
  qpat_assum `!x y. _ ==> mem_bytes_at x y t.vs_memory = _` irule >> simp[]
QED

Theorem uint2str_alloc_kept[local]:
  stmt_state_rel H ctx fn ce cx mid s /\ lo <= s.vs_alloca_next /\
  (!x. not_fresh_at sm x ==> lookup_var x ready = lookup_var x s /\
       FLOOKUP Gr x = FLOOKUP G x /\ op_taint tr (Var x) = op_taint tn (Var x)) /\
  (!i. i IN tr.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < limit)) ==>
  ghost_kept_at lo ce mid sm G tn s Gr tr
Proof
  strip_tac >> drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  irule alloc_buffer_ghost_kept_at >>
  qexistsl_tac [`G`, `limit`, `s`, `tn`] >> simp[ghost_kept_at_refl] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all_then ACCEPT_TAC body_local_region_frontier) >>
  rpt gen_tac >> strip_tac >> fs[alloca_inv_def, alloca_next_valid_def] >>
  qpat_assum `!aid base sz. FLOOKUP s.vs_allocas aid = _ ==> _` drule >> simp[]
QED

Theorem uint2str_registered_frame_mods:
  expr_post_mods H ctx fn ce cx e es sa sm s0 mid v op s /\
  stmt_state_rel H ctx fn ce cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= a.cs_next_var /\ sm.cs_next_id <= a.cs_next_id /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  ghost_inv_at_mods D lo d ce cx mid G tn s /\
  lo <= s.vs_alloca_next /\ s.vs_alloca_next <= ready.vs_alloca_next /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = sm.cs_next_id /\
  ready with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
               vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
  ready.vs_memory = s.vs_memory /\
  (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> FLOOKUP ready.vs_allocas aid = SOME row) /\
  (!aid off len. FLOOKUP ready.vs_allocas aid = SOME (off,len) ==>
                FLOOKUP s.vs_allocas aid = SOME (off,len) \/ s.vs_alloca_next <= off) /\
  (!x. not_fresh_at sm x ==> lookup_var x ready = lookup_var x s /\
       FLOOKUP Gr x = FLOOKUP G x /\ op_taint tr (Var x) = op_taint tn (Var x)) /\
  (!i. i IN tr.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < b+sz)) /\
  (!i. i < lo /\ i IN tf.t_mem ==> i IN tr.t_mem) /\
  u2s_safe H ctx fn ce cx mid a buf b sz inst ready t /\
  ghost_inv_at D 0 d ce cx mid Gf tf t /\
  ghost_kept_at lo ce mid a Gr tr ready Gf tf ==>
  ghost_inv_at_mods D lo d ce cx mid Gf tf t /\
  immutable_frame_mods fn ce cx mid t /\
  ghost_kept_at lo ce es sa G0 tn0 s0 Gf tf
Proof
  simp[expr_post_mods_def] >> strip_tac >>
  drule expr_post_frame >> strip_tac >>
  `stmt_state_rel H ctx fn ce cx mid s` by fs[expr_post_def] >>
  `!name off len. local_region ce mid.scopes ready name off len <=>
                   local_region ce mid.scopes s name off len` by
    (irule copy_buffer_local_region_frame >> qexists_tac `sm` >> simp[] >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at sm x ==> _` drule >> simp[]) >>
  qpat_assum `u2s_safe H _ _ _ _ _ _ _ _ _ _ ready t`
    (strip_assume_tac o REWRITE_RULE[u2s_safe_def]) >>
  qpat_assum `u2s_frame _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[u2s_frame_def]) >>
  `t.vs_allocas = ready.vs_allocas /\ t.vs_alloca_next = ready.vs_alloca_next /\
   t.vs_data_section = s.vs_data_section` by
    (qpat_assum `t with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
                         vs_current_bb := _; vs_inst_idx := _|> = ready` mp_tac >>
     qpat_assum `ready with <|vs_vars := _; vs_inst_idx := _;
                             vs_allocas := _; vs_alloca_next := _|> = s` mp_tac >>
     simp[venom_state_component_equality] >> strip_tac >> simp[]) >>
  `!x. not_fresh_at sm x ==> not_fresh_at a x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at sm x ==> _ /\ _` drule >>
     qpat_assum `!x. not_fresh_at a x ==> lookup_var x t = _` (qspec_then `x` mp_tac) >>
     simp[]) >>
  `!name off len. local_region ce mid.scopes t name off len <=>
                   local_region ce mid.scopes s name off len` by
    (irule copy_buffer_local_region_frame >> qexists_tac `sm` >> simp[]) >>
  `pure_frame ce fn mid sm s t` by
    (irule uint2str_byte_frame >> qexistsl_tac [`a`,`b`,`inst`,`ready`,`sz`] >>
     simp[] >> rpt gen_tac >> strip_tac >>
     qpat_assum `!name off len. local_region _ _ t _ _ _ ==> _`
       (qspecl_then [`name`,`off`,`len`] mp_tac) >> simp[]) >>
  `ghost_inv_at_mods D lo d ce cx mid Gf tf t /\
   immutable_frame_mods fn ce cx mid t` by suspend "linked" >>
  asm_rewrite_tac[] >> suspend "kept"
QED

Resume uint2str_registered_frame_mods[linked]:
  `!x. not_fresh_at sm x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tf (Var x) = op_taint tn (Var x)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at sm x ==> _ /\ _` (qspec_then `x` mp_tac) >>
     qpat_assum `ghost_kept_at _ _ _ a _ _ ready _ _`
       (strip_assume_tac o REWRITE_RULE[bodyPtrDefsTheory.ghost_kept_at_def]) >>
     `not_fresh_at a x` by
       (qpat_assum `!x. not_fresh_at sm x ==> not_fresh_at a x` irule >> simp[]) >>
     qpat_assum `!x. not_fresh_at a x ==> FLOOKUP Gf x = _ /\ _`
       (qspec_then `x` mp_tac) >> simp[] >> strip_tac >> simp[]) >>
  `!i. i < lo /\ i IN tf.t_mem ==> i IN tn.t_mem` by
    (rpt gen_tac >> strip_tac >>
     `i IN tr.t_mem` by
       (qpat_assum `!i. i < lo /\ i IN tf.t_mem ==> _` irule >> simp[]) >>
     `~(s.vs_alloca_next <= i)` by decide_tac >>
     qpat_assum `!i. i IN tr.t_mem <=> _` (qspec_then `i` mp_tac) >> simp[]) >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    (qpat_assum `ready.vs_memory = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  irule sha_registered_frame_mods >> simp[] >>
  qexistsl_tac [`G`,`s`,`sm`,`tn`] >> simp[]
QED

Resume uint2str_registered_frame_mods[kept]:
  `ghost_kept_at lo ce mid sm G tn s Gr tr` by
    (drule_all_then ACCEPT_TAC uint2str_alloc_kept) >>
  `ghost_kept_at lo ce mid sm G tn s Gf tf` by
    (drule_all_then ACCEPT_TAC ghost_kept_at_trans) >>
  drule_all_then ACCEPT_TAC ghost_kept_at_wb_trans
QED

Finalise uint2str_registered_frame_mods
