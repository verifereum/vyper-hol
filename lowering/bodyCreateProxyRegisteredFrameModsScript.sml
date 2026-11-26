Theory bodyCreateProxyRegisteredFrameMods
Ancestors
  bodySliceWindowGhostMods bodyMemoryDefs bodyFullUnwrapSlotPost
  exprSimCopy exprSimStorageCopy exprLoweringProps stmtFragPtr stateRelProj
  loweringStateRelDefs loweringPosts bodyPtrDefs finite_map venomState venomInst

Theorem proxy_registered_snapshot_kept[local]:
  sk.cs_next_var <= sa.cs_next_var /\
  (!aid b n. FLOOKUP s0.vs_allocas aid = SOME (b,n) /\ aid < sk.cs_next_id ==>
             b + n <= front) /\
  (!name b n. local_region cenv es0.scopes s0 name b n ==> b + n <= front) /\
  (!x. not_fresh_at sa x ==>
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!i. i < front /\ i IN tf.t_mem ==> i IN tn.t_mem) /\
  ghost_kept_at lo cenv es0 sk G0 tn0 s0 G tn ==>
  ghost_kept_at lo cenv es0 sk G0 tn0 s0 Gf tf
Proof
  strip_tac >>
  `!x. not_fresh_at sk x ==> not_fresh_at sa x` by
    (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
     qexists_tac `sk` >> simp[]) >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[ghost_kept_at_def]) >>
  rewrite_tac[ghost_kept_at_def] >> conj_tac
  >- (rpt gen_tac >> disch_tac >>
      `not_fresh_at sa x` by simp[] >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `off + sz <= front` by
        (qpat_assum `!aid b n. _ ==> b+n <= front` drule >> simp[]) >>
      `i < front` by decide_tac >>
      `i IN tn.t_mem` by simp[] >>
      qpat_assum `!aid off sz i. FLOOKUP _ aid = _ /\ _ ==> i IN tn0.t_mem`
        (qspecl_then [`aid`,`off`,`sz`,`i`] match_mp_tac) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_assum `!name b n. local_region _ _ _ _ _ _ ==> b+n <= front`
    (drule_then assume_tac) >>
  `i < front` by decide_tac >>
  `i IN tn.t_mem` by simp[] >>
  qpat_assum `!n b sz i. local_region _ _ _ _ _ _ /\ _ ==> i IN tn0.t_mem`
    (drule_all_then ACCEPT_TAC)
QED

Theorem proxy_registered_memory_frames[local]:
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id = sa.cs_next_id /\ FLOOKUP t.vs_allocas inst.inst_id = SOME (b,96) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> FLOOKUP t.vs_allocas aid = SOME row) /\
  (!aid a n. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,n) ==>
             regions_disjoint b 96 a n) /\
  (!name a n. local_region cenv es.scopes s name a n ==> regions_disjoint b 96 a n) /\
  (!a n. a+n <= b \/ b+96 <= a ==>
         mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory) ==>
  wb_frame cenv es es sa s t /\ pure_frame cenv func es sa s t
Proof
  strip_tac >> conj_tac
  >- (irule unwrap_slot_copy_wb_frame >>
      simp[] >> qexistsl_tac [`96:num`,`b`] >>
      asm_rewrite_tac[] >> conj_tac
      >- (rpt strip_tac >>
          qpat_assum `!name a n. local_region _ _ _ _ _ _ ==> _` drule >>
          simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >>
          `aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (off,sz)` by simp[] >>
          qpat_assum `!aid a n. _ ==> regions_disjoint b 96 a n` drule >>
          simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
      rpt strip_tac >>
      qpat_assum `!a n. _ ==> mem_bytes_at a n t.vs_memory = _` irule >> decide_tac) >>
  simp[pure_frame_def] >> conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!a n. _ ==> mem_bytes_at a n t.vs_memory = _` irule >>
      qpat_assum `!name a n. local_region _ _ _ _ _ _ ==> _` drule >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  rpt strip_tac >>
  qpat_assum `!a n. _ ==> mem_bytes_at a n t.vs_memory = _` irule >>
  qpat_x_assum `!inst a sz. _ ==> regions_disjoint _ _ _ _`
    (qspecl_then [`inst`,`b`,`96`] mp_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def]
QED

Theorem create_proxy_registered_frame_mods:
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list)
    ctx func cenv cx es s /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= m1.cs_next_var /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
           vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
  (!H':(bool # bytes32 # type_value) list # num list.
     stmt_state_rel H' ctx func cenv cx es s ==> stmt_state_rel H' ctx func cenv cx es u) /\
  (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> FLOOKUP u.vs_allocas aid = SOME row) /\
  (!aid a n. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,n) ==>
             regions_disjoint b 96 a n) /\
  (!name a n. local_region cenv es.scopes u name a n ==> regions_disjoint b 96 a n) /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  (!aid a n. FLOOKUP u.vs_allocas aid = SOME (a,n) ==>
             FLOOKUP s.vs_allocas aid = SOME (a,n) \/ s.vs_alloca_next <= a) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id = sa.cs_next_id /\ FLOOKUP u.vs_allocas inst.inst_id = SOME (b,96) /\
  t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory; vs_inst_idx := u.vs_inst_idx|> = u /\
  (!x. not_fresh_at m1 x ==> lookup_var x t = lookup_var x u) /\
  LENGTH u.vs_memory <= LENGTH t.vs_memory /\
  (!a n. a+n <= b \/ b+71 <= a ==>
         mem_bytes_at a n t.vs_memory = mem_bytes_at a n u.vs_memory) /\
  (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!i. i < s.vs_alloca_next /\ i IN tf.t_mem ==> i IN tn.t_mem) ==>
  (!H':(bool # bytes32 # type_value) list # num list.
     stmt_state_rel H' ctx func cenv cx es s ==> stmt_state_rel H' ctx func cenv cx es t) /\
  wb_frame cenv es es sa s t /\ pure_frame cenv func es sa s t /\
  (!name a n. local_region cenv es.scopes t name a n ==> regions_disjoint b 96 a n) /\
  (!D d lo. ghost_inv_at_mods D lo d cenv cx es G tn s /\
            immutable_frame_mods func cenv cx es s ==>
            ghost_inv_at_mods D lo d cenv cx es Gf tf t /\
            immutable_frame_mods func cenv cx es t /\
            ghost_kept_at lo cenv es sa G tn s Gf tf) /\
  (!lo sk es0 G0 tn0 s0. sk.cs_next_var <= sa.cs_next_var /\
     (!aid a n. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ aid < sk.cs_next_id ==>
                a + n <= s.vs_alloca_next) /\
     (!name a n. local_region cenv es0.scopes s0 name a n ==> a + n <= s.vs_alloca_next) /\
     ghost_kept_at lo cenv es0 sk G0 tn0 s0 G tn ==>
     ghost_kept_at lo cenv es0 sk G0 tn0 s0 Gf tf)
Proof
  strip_tac >>
  `copy_static t = copy_static u /\ t.vs_immutables = u.vs_immutables` by
    (qpat_assum `t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = u`
       (SUBST1_TAC o SYM) >> simp[copy_static_def]) >>
  drule_then strip_assume_tac copy_static_fields >>
  `u.vs_memory = s.vs_memory /\ u.vs_call_ctx = s.vs_call_ctx /\
   u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
   u.vs_immutables = s.vs_immutables /\ u.vs_data_section = s.vs_data_section` by
    (qpat_assum `u with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _;
                 vs_inst_idx := _|> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `local_ptrs_reserved cenv m1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!a n. a+n <= b \/ b+96 <= a ==>
         mem_bytes_at a n t.vs_memory = mem_bytes_at a n u.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `!a n. _ ==> mem_bytes_at a n t.vs_memory = _` irule >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >> irule copy_buffer_state_rel_frame >>
      qexistsl_tac [`b`,`inst`,`u`,`m1`,`96:num`] >> asm_rewrite_tac[] >>
      conj_tac
      >- (rpt strip_tac >>
          qpat_assum `!name a n. local_region _ _ u _ _ _ ==> _` drule >>
          simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
      qpat_assum `!h. stmt_state_rel h _ _ _ _ _ s ==> stmt_state_rel h _ _ _ _ _ u`
        irule >>
      first_assum ACCEPT_TAC) >>
  `!name a n. local_region cenv es.scopes t name a n <=>
             local_region cenv es.scopes u name a n` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists_tac `m1` >> simp[]) >>
  `!name a n. local_region cenv es.scopes s name a n <=>
             local_region cenv es.scopes t name a n` by
    (rpt gen_tac >> sym_tac >> irule copy_buffer_local_region_frame >>
     qexists_tac `sa` >> simp[]) >>
  `!name a n. local_region cenv es.scopes s name a n ==> regions_disjoint b 96 a n` by
    (simp[] >> first_assum ACCEPT_TAC) >>
  `!a n. a+n <= b \/ b+96 <= a ==>
         mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory` by
    (qpat_assum `u.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `wb_frame cenv es es sa s t /\ pure_frame cenv func es sa s t` by
    (irule proxy_registered_memory_frames >> rpt conj_tac
     >- (rpt strip_tac >> simp[])
     >- (rpt strip_tac >> simp[]) >>
     qexistsl_tac [`b`,`inst`] >> rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     qpat_assum `t.vs_allocas = u.vs_allocas` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  `!name a n. local_region cenv es.scopes t name a n ==> regions_disjoint b 96 a n` by
    (simp[] >> first_assum ACCEPT_TAC) >>
  asm_rewrite_tac[] >> conj_tac >- suspend "linked" >>
  rpt strip_tac >> irule proxy_registered_snapshot_kept >>
  qexistsl_tac [`G`,`s.vs_alloca_next`,`sa`,`tn`] >> simp[] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume create_proxy_registered_frame_mods[linked]:
  rpt gen_tac >> strip_tac >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `!name a n. local_region cenv es.scopes s name a n ==>
       mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory /\
       (!i. a <= i /\ i < a+n /\ i IN tf.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> strip_tac >> conj_tac
     >- (qpat_assum `pure_frame _ _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE[pure_frame_def]) >>
         qpat_assum `!n b sz. local_region _ _ s n b sz ==> mem_bytes_at b sz _ = _`
           (drule_then ACCEPT_TAC)) >>
     rpt strip_tac >> drule_all_then assume_tac body_local_region_frontier >>
     `i < s.vs_alloca_next` by decide_tac >> simp[]) >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    (qpat_assum `u.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `!aid a n. FLOOKUP t.vs_allocas aid = SOME (a,n) ==>
             FLOOKUP s.vs_allocas aid = SOME (a,n) \/ s.vs_alloca_next <= a` by
    (qpat_assum `t.vs_allocas = u.vs_allocas` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  irule slice_window_ghost_frame_mods >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE (rpt strip_tac >> simp[]))
QED

Finalise create_proxy_registered_frame_mods
