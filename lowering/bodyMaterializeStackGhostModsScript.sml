(* Linked ghost transport for the concrete ALLOCA/MSTORE materialization pair. *)
Theory bodyMaterializeStackGhostMods
Ancestors
  intCallMaterializeFull bodyFullShadowBodyInv intCallCallee bodyInvSplit
  robustCopyTransportPtr memoryValueEncoding exprSimProps
  bodyPtrDefs ptrDiscipline loweringStateRelDefs finite_map venomState list

Theorem stack_ghost_zero[local]:
  ghost_inv_at_mods D lo d ce cx es J qt us ==>
  ghost_inv_at D 0 d ce cx es J qt us
Proof
  simp[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >>
  strip_tac >> first_assum ACCEPT_TAC
QED

Theorem stack_ghost_restore_floor[local]:
  ghost_inv_at_mods D lo d ce cx es J qt us /\
  ghost_inv_at D 0 d
    (ce with ce_vars updated_by (\m. m |+ (nm,PtrVar (Var dst) sz)))
    cx es J2 qt2 ut /\
  mat_frame cs us ut /\ lo <= us.vs_alloca_next /\
  (!i. i < us.vs_alloca_next ==> (i IN qt2.t_mem <=> i IN qt.t_mem)) /\
  (!x. ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at cs x) /\
  dst = STRING #"%" (toString cs.cs_next_var) /\
  J2 = J |+ (dst,(us.vs_alloca_next,sz)) /\ qt2.t_var = qt.t_var |+ (dst,{}) /\
  allocas_from lo ut /\ lo <= ut.vs_alloca_next ==>
  ghost_inv_at_mods D lo d
    (ce with ce_vars updated_by (\m. m |+ (nm,PtrVar (Var dst) sz)))
    cx es J2 qt2 ut
Proof
  strip_tac >>
  `mem_bytes_at 0 lo ut.vs_memory = mem_bytes_at 0 lo us.vs_memory` by
    fs[mat_frame_def] >>
  gvs[ghost_inv_at_def, ghost_inv_at_mods_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >>
      `i < us.vs_alloca_next` by decide_tac >>
      `i IN qt.t_mem` by metis_tac[] >>
      `imm_section_dead_mods ce (mem_bytes_at 0 lo us.vs_memory) i` by
        metis_tac[] >>
      fs[imm_section_dead_mods_def]) >>
  gen_tac >> strip_tac >>
  `x <> STRING #"%" (toString cs.cs_next_var)` by
    (qpat_assum `!x. ce.ce_imm_alloca = SOME (Var x) ==> _`
       (drule_then (qspec_then `cs.cs_next_var` mp_tac o REWRITE_RULE [not_fresh_at_def])) >>
     simp[]) >>
  fs[op_taint_def, FLOOKUP_UPDATE]
QED

Theorem materialize_stack_ghost_bind_mods:
  ghost_inv_at_mods D lo d ce cx es J qt us /\ es.scopes = [env] /\
  mat_inv func ce env cs us f0 mr /\
  mat_pending ce env cs us f0 mr ((nm,T,Var p)::tail) /\
  (!n entry. FLOOKUP env n = SOME entry ==> value_has_type entry.type entry.value) /\
  FLOOKUP ce.ce_vars nm = SOME (MemLoc off sz) /\
  (!n q span. FLOOKUP ce.ce_vars n = SOME (PtrVar (Var q) span) ==>
     not_fresh_at cs q) /\
  (!x. ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at cs x) /\
  (!x span. ce.ce_return_buf = SOME (PtrVar (Var x) span) ==> not_fresh_at cs x) /\
  (!x span. ce.ce_return_pc = SOME (PtrVar (Var x) span) ==> not_fresh_at cs x) /\
  dst = STRING #"%" (toString cs.cs_next_var) /\
  us.vs_alloca_next + sz < dimword (:256) /\
  lookup_var p us = SOME w /\ op_taint qt (Var p) = {} /\
  step_inst_base (mk_inst cs.cs_next_id ALLOCA [Lit (n2w sz)] [dst]) us = OK u /\
  ut = mstore us.vs_alloca_next w u /\
  J2 = step_prov PG
    (step_prov PG J (mk_inst cs.cs_next_id ALLOCA [Lit (n2w sz)] [dst]) u)
    (mk_inst (cs.cs_next_id+1) MSTORE [Var dst;Var p] []) ut /\
  qt2 = step_taint (mk_inst (cs.cs_next_id+1) MSTORE [Var dst;Var p] []) u ut
    (step_taint (mk_inst cs.cs_next_id ALLOCA [Lit (n2w sz)] [dst]) us u qt) /\
  J2 = J |+ (dst,(us.vs_alloca_next,sz)) /\ qt2.t_var = qt.t_var |+ (dst,{}) /\
  (!i. i < us.vs_alloca_next ==> (i IN qt2.t_mem <=> i IN qt.t_mem)) /\
  lo <= f0 /\ mat_frame cs us ut /\
  mat_inv func
    (ce with ce_vars updated_by (\m. m |+ (nm,PtrVar (Var dst) sz)))
    env mid ut f0 mr ==>
  ghost_inv_at_mods D lo d
    (ce with ce_vars updated_by (\m. m |+ (nm,PtrVar (Var dst) sz)))
    cx es J2 qt2 ut
Proof
  strip_tac >>
  `local_ptrs_rel func ce es.scopes us /\ fresh_vars_wrt cs us /\
   f0 <= us.vs_alloca_next /\ FLOOKUP us.vs_allocas cs.cs_next_id = NONE` by
    (fs[mat_inv_def] >> simp[FLOOKUP_DEF] >> strip_tac >>
     qpat_x_assum `!aid. aid IN FDOM _ ==> _` drule >> simp[]) >>
  `?entry. FLOOKUP env nm = SOME entry /\ not_fresh_at cs p /\ 32 <= sz /\
     !b mem. mem_word_at b mem = w ==> val_in_memory entry.type entry.value b mem` by
    (qpat_x_assum `mat_pending _ _ _ _ _ _ (_::_)` mp_tac >>
     simp[mat_pending_def] >> strip_tac >>
     rename1 `FLOOKUP env nm = SOME entry` >>
     `value_has_type entry.type entry.value` by
       (qpat_assum `!n e. FLOOKUP env n = SOME e ==> _` drule >> simp[]) >>
     qexists_tac `entry` >> simp[] >>
     rpt strip_tac >> irule memory_value_rel_val_in_memory >>
     simp[] >> qpat_x_assum `!b m. mem_word_at b m = w ==> _` drule >> simp[]) >>
  `ghost_inv_at D 0 d ce cx es J qt us` by (drule stack_ghost_zero >> simp[]) >>
  `ghost_inv_at D 0 d
    (ce with ce_vars updated_by (\m. m |+ (nm,PtrVar (Var dst) sz)))
    cx es J2 qt2 ut` by
    (qpat_assum `J2 = step_prov _ _ _ _` (pure_once_rewrite_tac o single) >>
     qpat_assum `qt2 = step_taint _ _ _ _` (pure_once_rewrite_tac o single) >>
     qpat_assum `ut = mstore _ _ _` (pure_once_rewrite_tac o single) >>
     irule materialize_stack_bind_ghost_vars >>
     simp[] >> conj_tac >- (qexists_tac `cs` >> simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qexists_tac `func` >> fs[mat_inv_def] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `J2 = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `qt2 = step_taint _ _ _ _` kall_tac >>
  qpat_x_assum `ut = mstore _ _ _` kall_tac >>
  `allocas_from lo ut /\ lo <= ut.vs_alloca_next` by
    (fs[mat_inv_def, allocas_from_def] >> rpt strip_tac >>
     qpat_assum `!id b sz. FLOOKUP ut.vs_allocas id = _ ==> _` drule >> decide_tac) >>
  `lo <= us.vs_alloca_next` by decide_tac >>
  irule stack_ghost_restore_floor >>
  rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`J`, `cs`, `qt`, `us`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem materialize_stack_pending_tail_mods:
  mat_pending ce env cs us f0 mr tail /\
  ALL_DISTINCT (MAP FST ((nm,T,Var p)::tail)) /\
  f0 <= us.vs_alloca_next /\ mat_frame cs us ut /\
  dst = STRING #"%" (toString cs.cs_next_var) /\
  J2 = J |+ (dst,(us.vs_alloca_next,sz)) /\ qt2.t_var = qt.t_var |+ (dst,{}) /\
  (!i. i < us.vs_alloca_next ==> (i IN qt2.t_mem <=> i IN qt.t_mem)) /\
  EVERY (\c. op_taint qt (SND (SND c)) = {} /\
     (!q off span entry.
       ~FST (SND c) /\ SND (SND c) = Var q /\
       FLOOKUP ce.ce_vars (FST c) = SOME (MemLoc off span) /\
       FLOOKUP env (FST c) = SOME entry ==>
       ptr_covers J qt q us span /\
       !w mem. lookup_var q us = SOME w /\
         mem_agree_outside qt.t_mem us.vs_memory mem ==>
         val_in_memory entry.type entry.value (w2n w) mem)) tail ==>
  EVERY (\c. op_taint qt2 (SND (SND c)) = {} /\
     (!q off span entry.
       ~FST (SND c) /\ SND (SND c) = Var q /\
       FLOOKUP (ce.ce_vars |+ (nm,PtrVar (Var dst) sz)) (FST c) = SOME (MemLoc off span) /\
       FLOOKUP env (FST c) = SOME entry ==>
       ptr_covers J2 qt2 q ut span /\
       !w mem. lookup_var q ut = SOME w /\
         mem_agree_outside qt2.t_mem ut.vs_memory mem ==>
         val_in_memory entry.type entry.value (w2n w) mem)) tail
Proof
  simp[mat_pending_def, EVERY_MEM, MEM_MAP] >> strip_tac >>
  gen_tac >> strip_tac >>
  qpat_assum `!c. MEM c tail ==> ?q a off span entry. _` (drule_then strip_assume_tac) >>
  qpat_x_assum `!c. MEM c tail ==> op_taint _ _ = {} /\ _` (drule_then strip_assume_tac) >>
  rename1 `SND (SND c) = Var q` >>
  qpat_x_assum `dst = _` SUBST_ALL_TAC >>
  `STRING #"%" (toString cs.cs_next_var) <> q` by
    (qpat_assum `not_fresh_at cs q`
       (qspec_then `cs.cs_next_var` mp_tac o REWRITE_RULE [not_fresh_at_def]) >>
     simp[Once EQ_SYM_EQ]) >>
  `lookup_var q ut = lookup_var q us` by fs[mat_frame_def] >>
  `FST c <> nm` by metis_tac[] >>
  simp[FLOOKUP_UPDATE] >> conj_tac
  >- (qpat_x_assum `op_taint qt (SND (SND c)) = {}` mp_tac >>
      simp[op_taint_def, FLOOKUP_UPDATE]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  conj_tac
  >- (`op_taint qt2 (Var q) = {}` by
        (qpat_x_assum `op_taint qt (Var q) = {}` mp_tac >>
         simp[op_taint_def, FLOOKUP_UPDATE]) >>
      qpat_x_assum `ptr_covers J qt q us _` mp_tac >>
      simp[ptr_covers_def, FLOOKUP_UPDATE]) >>
  rename1 `lookup_var q us = SOME addr` >>
  rename1 `type_memory_size entry.type <= span` >>
  gen_tac >> strip_tac >>
  irule robust_val_in_memory_decreasing_taint_transport >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`us.vs_memory`, `ut.vs_memory`, `span`, `w2n addr`,
                `qt.t_mem`, `qt2.t_mem`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >> `w2n addr+i < us.vs_alloca_next` by decide_tac >>
      metis_tac[]) >>
  conj_tac
  >- (irule arithmeticTheory.LESS_EQ_TRANS >>
      qexists_tac `type_memory_size entry.type` >> simp[val_footprint_le]) >>
  conj_tac
  >- (`w2n addr + span <= us.vs_alloca_next` by decide_tac >> fs[mat_frame_def]) >>
  first_assum ACCEPT_TAC
QED
