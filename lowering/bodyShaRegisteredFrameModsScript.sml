(* Lift a pure suffix frame to the linked ghost and immutable frame. *)
Theory bodyShaRegisteredFrameMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit loweringSlice
  loweringStateRelDefs loweringPosts exprLoweringProps ptrDiscipline
  compileEnv venomState finite_map alist pred_set

Theorem sha_registered_ghost[local]:
  ghost_inv_at_mods D lo d ce cx es G tn s /\
  ghost_inv_at D 0 d ce cx es G' tn' z /\
  local_ptrs_reserved ce sm /\
  (!x. not_fresh_at sm x ==>
       lookup_var x z = lookup_var x s /\
       FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
  mem_bytes_at 0 lo z.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
  (!i. i < lo /\ i IN tn'.t_mem ==> i IN tn.t_mem) /\
  s.vs_alloca_next <= z.vs_alloca_next /\
  (!aid a sz. FLOOKUP z.vs_allocas aid = SOME (a,sz) ==>
      FLOOKUP s.vs_allocas aid = SOME (a,sz) \/ s.vs_alloca_next <= a) ==>
  ghost_inv_at_mods D lo d ce cx es G' tn' z
Proof
  strip_tac >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by
    (fs[ghost_inv_at_mods_def, allocas_from_def] >> rpt strip_tac >>
     qpat_assum `!aid a sz. FLOOKUP z.vs_allocas aid = SOME (a,sz) ==> _`
       (drule_then strip_assume_tac) >- metis_tac[] >> decide_tac) >>
  fs[ghost_inv_at_mods_def, bodyPtrDefsTheory.ghost_inv_at_def] >>
  gvs[SUBSET_DEF, local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem sha_registered_immutables_rel[local]:
  immutables_rel_mods ce cx.txn.target ce.ce_is_ctor mid s /\
  immutable_alloca_sep_mods func ce cx mid z /\
  z.vs_data_section = s.vs_data_section /\
  LENGTH s.vs_memory <= LENGTH z.vs_memory /\
  pure_frame ce func mid sm s z ==>
  immutables_rel_mods ce cx.txn.target ce.ce_is_ctor mid z
Proof
  simp[immutables_rel_mods_def, immutable_alloca_sep_mods_def] >>
  strip_tac >> rpt strip_tac >>
  irule immutables_rel_mem_agree >> qexists_tac `s` >> simp[] >>
  disch_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `pure_frame _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[pure_frame_def]) >>
  qpat_assum `!off len. _` irule >> rpt gen_tac >> strip_tac >>
  `immutable_alloca_sep func (ce with ce_module := src) cx mid z` by
    metis_tac[] >>
  fs[immutable_alloca_sep_def] >> metis_tac[]
QED

Theorem sha_registered_frame_mods:
  ghost_inv_at_mods D lo d ce cx mid G tn s /\
  immutable_frame_mods func ce cx mid s /\
  ghost_inv_at D 0 d ce cx mid Gf tf z /\
  local_ptrs_reserved ce sm /\
  (!x. not_fresh_at sm x ==>
       lookup_var x z = lookup_var x s /\
       FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!i. i < lo /\ i IN tf.t_mem ==> i IN tn.t_mem) /\
  z.vs_data_section = s.vs_data_section /\
  LENGTH s.vs_memory <= LENGTH z.vs_memory /\
  s.vs_alloca_next <= z.vs_alloca_next /\
  (!aid a k. FLOOKUP z.vs_allocas aid = SOME (a,k) ==>
      FLOOKUP s.vs_allocas aid = SOME (a,k) \/ s.vs_alloca_next <= a) /\
  pure_frame ce func mid sm s z ==>
  ghost_inv_at_mods D lo d ce cx mid Gf tf z /\
  immutable_frame_mods func ce cx mid z
Proof
  strip_tac >>
  `lo <= s.vs_alloca_next` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` mp_tac >>
     fs[ghost_inv_at_mods_def]) >>
  `mem_bytes_at 0 lo z.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (qpat_assum `pure_frame _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[pure_frame_def]) >>
     qpat_assum `!off len. _` (qspecl_then [`0`,`lo`] mp_tac) >>
     impl_tac >- (
       rpt gen_tac >> strip_tac >>
       qpat_assum `!aid a k. _ ==> _` (drule_then strip_assume_tac) >>
       gvs[loweringStateRelDefsTheory.regions_disjoint_def] >>
       `allocas_from lo s` by fs[ghost_inv_at_mods_def] >>
       fs[allocas_from_def] >>
       metis_tac[]) >>
     simp[]) >>
  drule_all_then assume_tac sha_registered_ghost >>
  `immutable_alloca_sep_mods func ce cx mid z` by
    (qpat_assum `immutable_frame_mods _ _ _ _ _` mp_tac >>
     simp[immutable_frame_mods_def, immutable_alloca_sep_mods_def] >>
     rpt strip_tac >>
     irule immutable_alloca_sep_frame >>
     qexistsl_tac [`s`,`mid`] >> simp[] >> conj_tac
     >- (rpt strip_tac >> disj1_tac >> qexists_tac `id` >>
         fs[local_region_def, local_ptrs_reserved_def, lookup_var_def] >>
         metis_tac[])
     >- (qpat_assum `immutable_frame_mods _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE[immutable_frame_mods_def]) >>
         fs[immutable_alloca_sep_mods_def] >> first_assum ACCEPT_TAC)) >>
  fs[immutable_frame_mods_def] >>
  metis_tac[sha_registered_immutables_rel]
QED
