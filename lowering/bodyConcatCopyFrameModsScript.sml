(* Transport the linked Concat frame through either scratch-write arm. *)
Theory bodyConcatCopyFrameMods
Ancestors
  bodyConcatCutsMods assignTuplePtrCopyLen freshWrites bodyMemoryDefs
  bodyPtrBytestringBuiltinsWindowGhost exprSimProps loweringSlice
  exprLoweringProps valueEncodingProps exprSimFullBundleProps
  loweringStateRelDefs ptrDiscipline pred_set list bodyPtrDefs
  bodyInvSplit bodyFullPostsMods bodyFullShadowBodyInv loweringPosts
  finite_map compileEnv venomState bodyFullUnwrapRun stateRelProj

Theorem concat_copy_live[local]:
  concat_live_mods (func,cenv,lo) (dv,ov,ow,binst,oinst,B,bsz) (es,sa,s,G,tn) bs /\
  concat_copy_effect_mods (ctx,func,cenv,cx,lo,d) (dv,ov,ow,binst,oinst,B,bsz)
    (es,sa,s,G,tn) (sb,u,G',tn') bs added /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  local_ptrs_reserved cenv sa /\ 32 + LENGTH (bs ++ added) <= bsz ==>
  concat_live_mods (func,cenv,lo) (dv,ov,ow,binst,oinst,B,bsz)
    (es,sb,u,G',tn') (bs ++ added)
Proof
  rewrite_tac[concat_live_mods_def,concat_copy_effect_mods_def,expr_sim_full_endpoint_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!x n. not_fresh_at sa x /\ ptr_covers G tn x s n ==> ptr_covers G' tn' x u n` by
    (rpt gen_tac >> strip_tac >> irule ptr_covers_lookup_frame >>
     qexistsl_tac [`G`,`s`,`tn`] >>
     qpat_assum `!z. not_fresh_at sa z ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  `!name b n. local_region cenv es.scopes u name b n <=> local_region cenv es.scopes s name b n` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!i. B+32 <= i /\ i < B+32+LENGTH (bs ++ added) ==> i NOTIN tn'.t_mem` by
    (simp[] >> rpt strip_tac >> Cases_on `i < B+32+LENGTH bs`
     >- (`i IN tn.t_mem` by (fs[SUBSET_DEF] >> metis_tac[]) >>
         qpat_assum `!j. B+32 <= j /\ _ ==> j NOTIN tn.t_mem`
           (qspec_then `i` mp_tac) >> simp[]) >>
     qpat_assum `!j. B+32+LENGTH bs <= j /\ _ ==> j NOTIN tn'.t_mem`
       (qspec_then `i` mp_tac) >> simp[] >> decide_tac) >>
  `not_fresh_at sb dv /\ not_fresh_at sb ov` by
    (conj_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `lookup_var dv u = lookup_var dv s /\ lookup_var ov u = lookup_var ov s` by
    (conj_tac >> qpat_assum `!z. not_fresh_at sa z ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  `ptr_covers G' tn' dv u (bsz-32) /\ ptr_covers G' tn' ov u 32` by simp[] >>
  fs[allocas_from_def] >> rpt conj_tac >> asm_rewrite_tac[] >> decide_tac
QED

Theorem concat_copy_old[local]:
  concat_live_mods (func,cenv,lo) (dv,ov,ow,binst,oinst,B,bsz) (es,sa,s,G,tn) bs /\
  concat_copy_effect_mods (ctx,func,cenv,cx,lo,d) (dv,ov,ow,binst,oinst,B,bsz)
    (es,sa,s,G,tn) (sb,u,G',tn') bs added /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  local_ptrs_reserved cenv sa /\
  concat_old_frame_mods (func,cenv,lo,pure) (dv,ov,ow,binst,oinst,B,bsz)
    (e0,st0,s0,G0,tn0) (es,sa,s,G,tn) ==>
  concat_old_frame_mods (func,cenv,lo,pure) (dv,ov,ow,binst,oinst,B,bsz)
    (e0,st0,s0,G0,tn0) (es,sb,u,G',tn')
Proof
  rewrite_tac[concat_live_mods_def,concat_copy_effect_mods_def,concat_old_frame_mods_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!z. not_fresh_at st0 z ==> not_fresh_at sa z` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `st0` >> simp[]) >>
  `!name b n. local_region cenv es.scopes u name b n <=> local_region cenv es.scopes s name b n` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!name b n. local_region cenv e0.scopes s0 name b n ==>
     mem_bytes_at b n u.vs_memory = mem_bytes_at b n s.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!p n. _ ==> mem_bytes_at p n u.vs_memory = _` (qspecl_then [`b`,`n`] irule) >>
     `local_region cenv es.scopes s name b n` by metis_tac[] >>
     qpat_assum `!name b n. local_region cenv es.scopes s name b n ==> _`
       (qspecl_then [`name`,`b`,`n`] mp_tac) >> simp[] >> decide_tac) >>
  `locals_kept cenv e0 es s0 u` by
    (irule locals_kept_regions_tail >> qexists `s` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo cenv e0 st0 G0 tn0 s0 G' tn'` by
    (irule ghost_kept_at_clean_suffix >> qexistsl_tac [`G`,`tn`] >> simp[] >>
     rpt strip_tac >> `not_fresh_at sa x` by simp[] >>
     qpat_assum `!z. not_fresh_at sa z ==> _` (qspec_then `x` mp_tac) >> simp[]) >>
  `st0.cs_next_var <= sb.cs_next_var /\ st0.cs_next_id <= sb.cs_next_id` by decide_tac >>
  asm_simp_tac bool_ss [] >> rpt conj_tac
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      irule EQ_TRANS >> qexists `mem_bytes_at p n s.vs_memory` >> conj_tac
      >- (qpat_assum `!p n. _ ==> mem_bytes_at p n u.vs_memory = _` irule >> simp[]) >>
      qpat_assum `!aid p n. _ ==> mem_bytes_at p n s.vs_memory = _`
        (qspecl_then [`aid`,`p`,`n`] mp_tac) >> asm_simp_tac bool_ss [] >>
      (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  disch_tac >> qpat_x_assum `pure ==> _` (drule_then strip_assume_tac) >> conj_tac
  >- (qx_genl_tac [`name`,`lb`,`lsz`] >> disch_tac >>
      irule EQ_TRANS >> qexists `mem_bytes_at lb lsz s.vs_memory` >> conj_tac
      >- (qpat_assum `!name b n. local_region cenv e0.scopes s0 name b n ==>
            mem_bytes_at b n u.vs_memory = _`
            (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >> simp[]) >>
      qpat_assum `!name b n. local_region cenv e0.scopes s0 name b n ==>
        mem_bytes_at b n s.vs_memory = _`
        (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >> simp[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule EQ_TRANS >> qexists `mem_bytes_at p n s.vs_memory` >> conj_tac
  >- (qpat_assum `!p n. _ ==> mem_bytes_at p n u.vs_memory = _` irule >> simp[]) >>
  qpat_assum `!p n. _ ==> mem_bytes_at p n s.vs_memory = _`
    (qspecl_then [`p`,`n`] mp_tac) >> asm_simp_tac bool_ss [] >>
  (impl_tac >- first_assum ACCEPT_TAC) >> simp[]
QED

(* The constructor immutable slice fits outside both scratch allocations. *)
Theorem concat_copy_immutable[local]:
  concat_live_mods (func,cenv,lo) (dv,ov,ow,binst,oinst,B,bsz) (es,sa,s,G,tn) bs /\
  concat_copy_effect_mods (ctx,func,cenv,cx,lo,d) (dv,ov,ow,binst,oinst,B,bsz)
    (es,sa,s,G,tn) (sb,u,G',tn') bs added /\
  local_ptrs_reserved cenv sa /\ immutable_frame_mods func cenv cx es s ==>
  immutable_frame_mods func cenv cx es u
Proof
  rewrite_tac[concat_live_mods_def,concat_copy_effect_mods_def,
    immutable_frame_mods_def,immutables_rel_mods_def,immutable_alloca_sep_mods_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >> reverse conj_tac
  >- (rpt gen_tac >> disch_tac >>
      irule immutable_alloca_sep_fields >> qexistsl_tac [`s`,`es`] >> simp[] >>
      rpt strip_tac >> qexists `id` >>
      `local_region (cenv with ce_module := src) es.scopes u id b sz <=>
       local_region (cenv with ce_module := src) es.scopes s id b sz` by
        (irule local_region_lookup_cong >> simp[] >> metis_tac[local_ptrs_reserved_def]) >>
      gvs[]) >>
  qx_genl_tac [`src`,`tops`] >> disch_tac >>
  `immutables_rel cenv cx.txn.target src cenv.ce_is_ctor es s` by metis_tac[] >>
  qpat_x_assum `!src tops. _ ==> immutables_rel _ _ src _ _ s` kall_tac >>
  reverse (ASM_CASES_TAC ``cenv.ce_is_ctor``) >-
    (fs[immutables_rel_def] >> first_assum ACCEPT_TAC) >>
  fs[immutables_rel_def] >> qx_genl_tac [`name`,`tv`,`v`,`off`] >> strip_tac >>
  qpat_x_assum `!name tv v off. _ ==> immutable_value_admissible tv v /\ _`
    (qspecl_then [`name`,`tv`,`v`,`off`] mp_tac) >>
  simp[] >> strip_tac >>
  `immutable_alloca_sep func (cenv with ce_module := src) cx es s` by metis_tac[] >>
  qpat_x_assum `immutable_alloca_sep _ _ _ _ _`
    (mp_tac o cj 2 o REWRITE_RULE [immutable_alloca_sep_def]) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`name`,`tv`,`v`,`off`] mp_tac) >>
  simp[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `regions_disjoint off (type_memory_size tv) B bsz /\
   regions_disjoint off (type_memory_size tv) (w2n ow) 64` by
    (qpat_assum `!inst b sz. _ ==> regions_disjoint _ _ b sz` (fn th =>
       conj_tac
       >- (qspecl_then [`binst`,`B`,`bsz`] mp_tac th >> simp[]) >>
       qspecl_then [`oinst`,`w2n ow`,`64`] mp_tac th >> simp[])) >>
  `mem_bytes_at off (type_memory_size tv) u.vs_memory =
   mem_bytes_at off (type_memory_size tv) s.vs_memory` by
    (qpat_assum `!p n. _ ==> mem_bytes_at p n u.vs_memory = _`
       (qspecl_then [`off`,`type_memory_size tv`] irule) >> fs[regions_disjoint_def]) >>
  simp[] >> (irule val_in_memory_mem_agree >>
    (conj_tac >- simp[immutable_admissible_val_wf]) >>
    qexistsl_tac [`type_memory_size tv`,`s.vs_memory`] >> simp[])
QED

(* Transport ordinary roots at zero, then restore the linked low-memory obligations. *)
Theorem concat_copy_ghost[local]:
  concat_live_mods (func,cenv,lo) (dv,ov,ow,binst,oinst,B,bsz) (es,sa,s,G,tn) bs /\
  concat_copy_effect_mods (ctx,func,cenv,cx,lo,d) (dv,ov,ow,binst,oinst,B,bsz)
    (es,sa,s,G,tn) (sb,u,G',tn') bs added /\
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  ghost_inv_at_mods D lo d cenv cx es G tn s ==>
  ghost_inv_at_mods D lo d cenv cx es G' tn' u
Proof
  rewrite_tac[concat_live_mods_def,concat_copy_effect_mods_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ghost_inv_at D 0 d cenv cx es G tn s` by
    (fs[ghost_inv_at_mods_def,ghost_inv_at_def,allocas_from_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `local_ptrs_rel func cenv es.scopes s` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `mem_bytes_at 0 lo u.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (qpat_assum `!p n. _ ==> mem_bytes_at p n u.vs_memory = _`
       (qspecl_then [`0`,`lo`] irule) >> simp[]) >>
  `!name b n. local_region cenv es.scopes s name b n ==>
     mem_bytes_at b n u.vs_memory = mem_bytes_at b n s.vs_memory` by
    (qx_genl_tac [`name`,`b`,`n`] >> disch_tac >>
     qpat_assum `!p n. _ ==> mem_bytes_at p n u.vs_memory = _` irule >>
     qpat_assum `!name b n. local_region cenv es.scopes s name b n ==> _`
       (qspecl_then [`name`,`b`,`n`] mp_tac) >> simp[] >> decide_tac) >>
  `stor_taint_ok_at D tn' u` by
    (fs[ghost_inv_at_mods_def,stor_taint_ok_at_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at D 0 d cenv cx es G' tn' u` by
    (irule ghost_inv_at_local_window_transport >>
     simp[allocas_from_def] >>
     qexistsl_tac [`G`,`es`,`func`,`s`,`sa`,`tn`] >>
     `mem_bytes_at 0 0 u.vs_memory = mem_bytes_at 0 0 s.vs_memory` by
       simp[valueEncodingDefsTheory.mem_bytes_at_def] >>
     fs[SUBSET_DEF] >> rpt strip_tac >> simp[] >>
     qpat_assum `!name b n. local_region cenv es.scopes s name b n ==>
       mem_bytes_at b n u.vs_memory = _` (drule_then ACCEPT_TAC)) >>
  `allocas_from lo u` by
    (qpat_assum `allocas_from lo s` mp_tac >>
     rewrite_tac[allocas_from_def] >> asm_rewrite_tac[]) >>
  qpat_x_assum `ghost_inv_at D 0 _ _ _ _ _ _ u`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [ghost_inv_at_def]) >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ s`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [ghost_inv_at_mods_def]) >>
  rewrite_tac[ghost_inv_at_mods_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (asm_rewrite_tac[] >> NO_TAC)
  >- (qx_gen_tac `i` >> strip_tac >>
      `i IN tn.t_mem` by fs[SUBSET_DEF] >>
      qpat_assum `!i. i < lo /\ i IN tn.t_mem ==> _` (qspec_then `i` mp_tac) >> simp[]) >>
  qx_gen_tac `x` >> strip_tac >>
  `not_fresh_at sa x` by metis_tac[local_ptrs_reserved_def] >>
  qpat_assum `!z. not_fresh_at sa z ==> _` (qspec_then `x` mp_tac) >>
  qpat_assum `!z. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var z) ==> _`
    (qspec_then `x` mp_tac) >> simp[]
QED

Theorem concat_copy_frame_mods:
  concat_live_mods (func,cenv,lo) (dv,ov,ow,binst,oinst,B,bsz) (es,sa,s,G,tn) bs /\
  concat_old_frame_mods (func,cenv,lo,pure) (dv,ov,ow,binst,oinst,B,bsz) anchor
    (es,sa,s,G,tn) /\
  concat_copy_effect_mods (ctx,func,cenv,cx,lo,d) (dv,ov,ow,binst,oinst,B,bsz)
    (es,sa,s,G,tn) (sb,u,G',tn') bs added /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  stmt_state_rel (H : (bool # bytes32 # type_value) list # num list) ctx func cenv cx es s /\
  immutable_frame_mods func cenv cx es s /\
  storage_well_formed_on cx es (FST H) /\
  local_ptrs_reserved cenv sa /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  32 + LENGTH (bs ++ added) <= bsz /\ return_buf_frame d cenv sa s ==>
  concat_live_mods (func,cenv,lo) (dv,ov,ow,binst,oinst,B,bsz)
    (es,sb,u,G',tn') (bs ++ added) /\
  concat_old_frame_mods (func,cenv,lo,pure) (dv,ov,ow,binst,oinst,B,bsz) anchor
    (es,sb,u,G',tn') /\
  stmt_state_rel H ctx func cenv cx es u /\
  immutable_frame_mods func cenv cx es u /\
  storage_well_formed_on cx es (FST H) /\
  ghost_inv_at_mods D lo d cenv cx es G' tn' u /\
  return_buf_frame d cenv sb u
Proof
  PairCases_on `anchor` >> disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac >- (drule_all concat_copy_live >> simp[]) >>
  conj_tac >- (drule_all concat_copy_old >> simp[]) >>
  conj_tac >-
    (qpat_x_assum `concat_copy_effect_mods _ _ _ _ _ _` mp_tac >>
     rewrite_tac[concat_copy_effect_mods_def] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     first_assum irule >> first_assum ACCEPT_TAC) >>
  conj_tac >- (drule_all concat_copy_immutable >> simp[]) >>
  simp[] >> conj_tac >- (drule_all concat_copy_ghost >> simp[]) >>
  irule return_buf_frame_frame >> simp[] >> qexistsl_tac [`cenv`,`s`,`sa`] >>
  qpat_x_assum `concat_copy_effect_mods _ _ _ _ _ _` mp_tac >>
  simp[concat_copy_effect_mods_def]
QED
