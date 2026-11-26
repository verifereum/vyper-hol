(* Binding a borrowed parameter changes only the local map. *)
Theory bodyMaterializeBorrowGhostMods
Ancestors
  bodyFullShadowBodyInv intCallMaterializeFull bodyInvSplit bodyPtrDefs
  ptrDiscipline list finite_map

Theorem materialize_borrow_ghost_bind_mods:
  ghost_inv_at_mods D lo d ce cx es G tn s /\ es.scopes = [env] /\
  FLOOKUP env nm = SOME entry /\ ptr_covers G tn p s sz /\
  (!w mem. lookup_var p s = SOME w /\
     mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n w) mem) ==>
  ghost_inv_at_mods D lo d
    (ce with ce_vars updated_by (\m. m |+ (nm,PtrVar (Var p) sz)))
    cx es G tn s
Proof
  strip_tac >>
  `ghost_inv_at D 0 d ce cx es G tn s` by
    (fs[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >>
     first_assum ACCEPT_TAC) >>
  drule_all_then (strip_assume_tac o SIMP_RULE (srw_ss()) [ghost_inv_at_def])
    materialize_param_ghost_bind >>
  `!bytes i. imm_section_dead_mods
    (ce with ce_vars updated_by (\m. m |+ (nm,PtrVar (Var p) sz))) bytes i =
    imm_section_dead_mods ce bytes i` by simp[imm_section_dead_mods_def] >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
  simp[NoAsms, ghost_inv_at_mods_def] >> rpt conj_tac >>
  (first_assum ACCEPT_TAC ORELSE simp[])
QED

Theorem materialize_borrow_pending_tail_mods:
  ~MEM nm (MAP FST caps) /\
  EVERY (\c. op_taint tn (SND (SND c)) = {} /\
    (!p off sz entry.
       ~FST (SND c) /\ SND (SND c) = Var p /\
       FLOOKUP ce.ce_vars (FST c) = SOME (MemLoc off sz) /\
       FLOOKUP env (FST c) = SOME entry ==>
       ptr_covers G tn p s sz /\
       !w mem. lookup_var p s = SOME w /\
         mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory entry.type entry.value (w2n w) mem)) caps ==>
  EVERY (\c. op_taint tn (SND (SND c)) = {} /\
    (!p off sz entry.
       ~FST (SND c) /\ SND (SND c) = Var p /\
       FLOOKUP (ce with ce_vars updated_by (\m. m |+ (nm,PtrVar (Var q) span))).ce_vars
         (FST c) = SOME (MemLoc off sz) /\
       FLOOKUP env (FST c) = SOME entry ==>
       ptr_covers G tn p s sz /\
       !w mem. lookup_var p s = SOME w /\
         mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory entry.type entry.value (w2n w) mem)) caps
Proof
  simp[EVERY_MEM, MEM_MAP] >> strip_tac >> qx_gen_tac `cap` >> disch_tac >>
  `FST cap <> nm` by
    (qpat_assum `!y. _ = FST y ==> ~MEM y caps` (qspec_then `cap` mp_tac) >>
     simp[EQ_SYM_EQ]) >>
  qpat_assum `!c. MEM c caps ==> _` (qspec_then `cap` mp_tac) >>
  simp[FLOOKUP_UPDATE]
QED
