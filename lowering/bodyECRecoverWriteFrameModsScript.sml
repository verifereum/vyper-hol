(* Linked frame transport for the bounded nonallocating scratch writes used by
   the ECRecover fragment. *)
Theory bodyECRecoverWriteFrameMods
Ancestors
  bodyForRangeScalarFrameMods bodyFullShadowBodyInv bodyFullPostsMods
  bodyInvSplit bodyPtrDefs exprLoweringProps loweringStateRelDefs
  loweringSlice compileEnv valueEncodingProps ptrDiscipline
  venomState finite_map list pred_set

Theorem ecrecover_write_frame_mods:
  immutable_frame_mods func ce cx es s /\
  ghost_inv_at_mods D lo d ce cx es G tn s /\
  ghost_inv_at D 0 d ce cx es' G' tn' t /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\
       FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
  es'.scopes = es.scopes /\
  es'.immutables = es.immutables /\
  t.vs_data_section = s.vs_data_section /\
  t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  lo <= b /\
  (!p n. regions_disjoint b cap p n ==>
       mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory) /\
  (!i. i < lo /\ i IN tn'.t_mem ==> i IN tn.t_mem) /\
  (ce.ce_is_ctor ==> !src tops name tv v off.
     ALOOKUP ce.ce_modules src = SOME tops /\
     FLOOKUP (ce with ce_module := src).ce_module_vars (src,name) =
       SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
              | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
       regions_disjoint b cap off (type_memory_size tv)) ==>
  immutable_frame_mods func ce cx es' t /\
  ghost_inv_at_mods D lo d ce cx es' G' tn' t
Proof
  strip_tac >> fs[] >>
  `regions_disjoint b cap 0 lo` by
    (simp[regions_disjoint_def] >> disj2_tac >> qpat_assum `lo <= b` ACCEPT_TAC) >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    metis_tac[] >>
  qpat_assum `immutable_frame_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [immutable_frame_mods_def]) >>
  `immutables_rel_mods ce cx.txn.target ce.ce_is_ctor es' t <=>
   immutables_rel_mods ce cx.txn.target ce.ce_is_ctor es t` by
    (simp[immutables_rel_mods_def, immutables_rel_def] >>
     metis_tac[]) >>
  `immutables_rel_mods ce cx.txn.target ce.ce_is_ctor es' t` by
    (qpat_assum `immutables_rel_mods _ _ _ _ _ <=> _`
       (fn th => rw[th]) >> rw[immutables_rel_mods_def] >> rpt gen_tac >>
     irule immutables_rel_mem_agree >> qexists_tac `s` >>
     qpat_assum `es'.immutables = es.immutables`
       (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
     simp[] >> conj_tac
     >- (strip_tac >> rpt gen_tac >> strip_tac >>
         qpat_assum `ce.ce_is_ctor ==> !src tops name tv v off. _`
           (drule_then assume_tac) >>
         qpat_assum `!p n. regions_disjoint b cap p n ==> _` irule >>
         qpat_assum `!src tops name tv v off. _` (drule_all_then ACCEPT_TAC))
     >- (qpat_assum `immutables_rel_mods _ _ _ _ _`
           (mp_tac o REWRITE_RULE [immutables_rel_mods_def]) >>
         disch_then (qspecl_then [`src`,`tops`] mp_tac) >> simp[] >>
         first_assum ACCEPT_TAC)) >>
  `immutable_alloca_sep_mods func ce cx es' t` by
    (rw[immutable_alloca_sep_mods_def] >> rpt gen_tac >>
     irule immutable_alloca_sep_fields >> qexistsl_tac [`s`,`es`] >> simp[] >>
     conj_tac
     >- (rpt strip_tac >> qexists_tac `id` >>
         `local_region (ce with ce_module := src) es.scopes t id b' sz <=>
          local_region (ce with ce_module := src) es.scopes s id b' sz` by
           (irule local_region_lookup_cong >> simp[] >>
            metis_tac[local_ptrs_reserved_def]) >>
         gs[])
     >- (qpat_assum `immutable_alloca_sep_mods _ _ _ _ _`
           (mp_tac o REWRITE_RULE [immutable_alloca_sep_mods_def]) >>
         disch_then (qspecl_then [`src`,`tops`] mp_tac) >> simp[] >>
         first_assum ACCEPT_TAC)) >>
  conj_tac
  >- simp[immutable_frame_mods_def]
  >- (qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
      fs[ghost_inv_at_mods_def, ghost_inv_at_def, stor_taint_ok_at_def,
         allocas_from_def] >> rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- (rpt strip_tac >>
          qpat_assum `!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> _`
            (qspecl_then [`x`] assume_tac) >>
          qpat_assum `local_ptrs_reserved ce sa`
            (mp_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
          qpat_assum `!x. not_fresh_at sa x ==> _`
            (qspecl_then [`x`] assume_tac) >>
          metis_tac[])
      >- first_assum ACCEPT_TAC)
QED
