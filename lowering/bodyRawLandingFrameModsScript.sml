(* Linked frames at the cursor immediately after the actual raw-call write. *)
Theory bodyRawLandingFrameMods
Ancestors
  bodyMethodIdScratchFrameMods bodyFullRawCallCallFrame bodyExtStatusWriteFrameMods
  bodyFullUnwrapRun stateRelProj allocaSiteResource exprSimHash loweringPosts
  freshWrites regularCallEmitSim valueEncodingProps valueEncodingProofs
  ptrDiscipline loweringStateRelDefs exprLoweringProps arithmetic finite_map words
  bodyFullShadowBodyInv bodyPtrDefs pred_set

Theorem raw_landing_window_shorten[local]:
  regions_disjoint b sz a len /\ b <= dst /\ dst + n <= b + sz ==>
  regions_disjoint dst n a len
Proof
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem raw_landing_write_kept[local]:
  (bytes = [] \/ n = 0 \/ regions_disjoint dst (LENGTH bytes) a n) ==>
  mem_bytes_at a n (write_memory_with_expansion dst bytes s).vs_memory =
  mem_bytes_at a n s.vs_memory
Proof
  Cases_on `bytes = []`
  >- (simp[] >> irule listTheory.LIST_EQ >>
      simp[valueEncodingProofsTheory.LENGTH_mem_bytes_at_proof] >>
      rpt strip_tac >>
      simp[valueEncodingProofsTheory.EL_mem_bytes_at, GSYM codegenRelTheory.read_byte_def,
           read_byte_write_memory_with_expansion]) >>
  Cases_on `n = 0` >- simp[valueEncodingDefsTheory.mem_bytes_at_def] >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def, DISJ_COMM] >>
  disch_tac >> irule valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint >>
  simp[]
QED

Theorem raw_landing_registered_write_kept[local]:
  alloca_inv t7 /\ aid < new_id /\
  FLOOKUP t7.vs_allocas aid = SOME (a,n) /\
  FLOOKUP t7.vs_allocas new_id = SOME (ob,sz) /\
  ob <= dst /\ dst + LENGTH bytes <= ob + sz ==>
  mem_bytes_at a n (write_memory_with_expansion dst bytes t7).vs_memory =
  mem_bytes_at a n t7.vs_memory
Proof
  strip_tac >>
  `aid <> new_id` by decide_tac >>
  `venomMemDefs$regions_disjoint (a,n) (ob,sz)` by
    (irule alloca_site_registered_disjoint >> qexistsl_tac [`aid`, `new_id`, `t7`] >> simp[]) >>
  irule raw_landing_write_kept >> Cases_on `bytes = []` >> simp[] >>
  `0 < LENGTH bytes` by (Cases_on `bytes` >> fs[]) >>
  fs[venomMemDefsTheory.regions_disjoint_def,
     loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem raw_landing_linked_ghost[local]:
  ghost_inv_at_mods D lo d cenv cx esK G7 tn7 t7 /\
  ghost_inv_at D 0 d cenv cx es2 Gq tnq q /\
  mem_bytes_at 0 lo q.vs_memory = mem_bytes_at 0 lo t7.vs_memory /\
  tnq.t_mem SUBSET tn7.t_mem /\ q.vs_allocas = t7.vs_allocas /\
  q.vs_alloca_next = t7.vs_alloca_next /\
  (!x. x <> status ==> FLOOKUP Gq x = FLOOKUP G7 x /\
                          op_taint tnq (Var x) = op_taint tn7 (Var x)) /\
  FLOOKUP Gq status = NONE /\ op_taint tnq (Var status) = {} ==>
  ghost_inv_at_mods D lo d cenv cx es2 Gq tnq q
Proof
  simp[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >>
  strip_tac >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (fs[SUBSET_DEF] >> rpt strip_tac >>
      qpat_assum `!j. _ ==> imm_section_dead_mods _ _ j` irule >> simp[]) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> strip_tac >> Cases_on `x = status` >> simp[] >>
  qpat_assum `!y. y <> status ==> _` (drule_then strip_assume_tac) >> simp[] >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[]
QED

Theorem raw_landing_wb[local]:
  wb_frame cenv es esK sa s0 t7 /\ local_ptrs_reserved cenv sa /\
  alloca_inv t7 /\ sa.cs_next_id <= new_id /\
  FLOOKUP t7.vs_allocas new_id = SOME (ob,sz) /\
  ob <= dst /\ dst + LENGTH bytes <= ob + sz /\
  (!name a n. local_region cenv esK.scopes t7 name a n ==>
    regions_disjoint dst (LENGTH bytes) a n) /\
  (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x t7) /\
  es2.scopes = esK.scopes /\ q.vs_allocas = t7.vs_allocas /\
  q.vs_memory = (write_memory_with_expansion dst bytes t7).vs_memory ==>
  wb_frame cenv es es2 sa s0 q
Proof
  strip_tac >>
  `wb_frame cenv es es2 sa s0 t7` by
    (pure_rewrite_tac[wb_frame_def, locals_kept_def, popped_kept_def] >>
     qpat_assum `es2.scopes = esK.scopes` (pure_rewrite_tac o single) >>
     qpat_assum `wb_frame _ _ esK _ _ _`
       (ACCEPT_TAC o PURE_REWRITE_RULE [wb_frame_def, locals_kept_def, popped_kept_def])) >>
  `MAP FDOM es.scopes = MAP FDOM esK.scopes` by
    gvs[wb_frame_def, locals_kept_def] >>
  irule wb_frame_allocating_tail >> simp[] >>
  qexistsl_tac [`t7`, `esK.scopes`, `sa`] >> simp[] >> conj_tac
  >- (rpt strip_tac >> simp[] >> irule raw_landing_write_kept >> metis_tac[]) >>
  rpt strip_tac >> simp[] >> irule raw_landing_registered_write_kept >> simp[] >>
  qexistsl_tac [`aid`, `new_id`, `ob`, `sz`] >> simp[] >> decide_tac
QED

Theorem raw_call_landing_frames_mods:
  stmt_state_rel H ctx func cenv cx esK t7 /\
  ghost_inv_at_mods (DF H) lo dframe cenv cx esK G7 tn7 t7 /\
  immutable_frame_mods func cenv cx esK t7 /\
  wb_frame cenv es esK sa s0 t7 /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G7 tn7 /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ci_mono sa s6 /\ ci_mono sa s7 /\ ~not_fresh_at s7 status /\
  (!x. x <> status ==> lookup_var x q = lookup_var x t7 /\
                       FLOOKUP Gq x = FLOOKUP G7 x /\
                       op_taint tnq (Var x) = op_taint tn7 (Var x)) /\
  FLOOKUP Gq status = NONE /\ op_taint tnq (Var status) = {} /\
  es2.scopes = esK.scopes /\ es2.immutables = esK.immutables /\
  q.vs_allocas = t7.vs_allocas /\ q.vs_alloca_next = t7.vs_alloca_next /\
  q.vs_data_section = t7.vs_data_section /\
  q.vs_memory = (write_memory_with_expansion (w2n (ro:256 word)) (TAKE cap rd) t7).vs_memory /\
  tnq.t_mem = tn7.t_mem DIFF {i | w2n ro <= i /\ i < w2n ro + LENGTH (TAKE cap rd)} /\
  stor_taint_ok_at (DF H) tnq q /\
  FLOOKUP t7.vs_allocas s6.cs_next_id = SOME (ob,capacity) /\
  ob <= w2n ro /\ w2n ro + LENGTH (TAKE cap rd) <= ob + capacity /\
  (!name lb sz. local_region cenv esK.scopes t7 name lb sz ==>
    regions_disjoint ob capacity lb sz) /\
  (cenv.ce_is_ctor ==> !src tops name tv v off.
    ALOOKUP cenv.ce_modules src = SOME tops /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP esK.immutables cx.txn.target of NONE => FEMPTY
             | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    regions_disjoint ob capacity off (type_memory_size tv)) ==>
  ghost_inv_at_mods (DF H) lo dframe cenv cx es2 Gq tnq q /\
  immutable_frame_mods func cenv cx es2 q /\
  wb_frame cenv es es2 sa s0 q /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gq tnq
Proof
  strip_tac >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `!x. not_fresh_at sa x ==> FLOOKUP Gq x = FLOOKUP G7 x /\
                            op_taint tnq (Var x) = op_taint tn7 (Var x) /\
                            lookup_var x q = lookup_var x t7` by
    (gen_tac >> disch_tac >>
     `x <> status` by (fs[ci_mono_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
     qpat_assum `!y. y <> status ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  `!name a len. local_region cenv esK.scopes t7 name a len ==>
                regions_disjoint (w2n ro) (LENGTH (TAKE cap rd)) a len` by
    (rpt strip_tac >> irule raw_landing_window_shorten >>
     qexistsl_tac [`ob`, `capacity`] >> simp[] >>
     qpat_assum `!nm b n. local_region _ _ _ nm b n ==> _` (drule_then ACCEPT_TAC)) >>
  `tnq.t_mem SUBSET tn7.t_mem` by simp[pred_setTheory.SUBSET_DEF] >>
  conj_tac
  >- (`lo <= w2n ro` by
        (`lo <= ob` by
           (fs[ghost_inv_at_mods_def, allocas_from_def] >>
            qpat_assum `!id b n. FLOOKUP t7.vs_allocas id = _ ==> _` (drule_then ACCEPT_TAC)) >>
         decide_tac) >>
      `mem_bytes_at 0 lo q.vs_memory = mem_bytes_at 0 lo t7.vs_memory` by
        (simp[] >> irule valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint >> simp[]) >>
      `ghost_inv_at (DF H) 0 dframe cenv cx es2 Gq tnq q` by
        (drule_then assume_tac method_id_ghost_at_zero >>
         drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`) raw_call_clean_write_ghost_at >>
         disch_then (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
         disch_then irule >> simp[] >> conj_tac
         >- (qexistsl_tac [`TAKE cap rd`, `w2n ro`] >> simp[] >> first_assum ACCEPT_TAC) >>
         qexists_tac `sa` >> simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`) raw_landing_linked_ghost >>
      disch_then irule >> simp[] >> qexists_tac `status` >> simp[] >>
      gen_tac >> disch_tac >>
      qpat_assum `!x. x <> status ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  conj_tac
  >- (drule_at (Pat `immutable_frame_mods _ _ _ _ _`)
        (INST_TYPE [alpha |-> ``:256``] extcall_status_write_immutable_frame_mods) >>
      disch_then irule >> simp[] >> conj_tac
      >- (qexistsl_tac [`cap`, `rd`, `ro`] >> simp[] >> rpt strip_tac >>
          irule raw_landing_window_shorten >> qexistsl_tac [`ob`, `capacity`] >> simp[] >>
          qpat_assum `cenv.ce_is_ctor ==> _` (drule_then (drule_all_then ACCEPT_TAC))) >>
      qexists_tac `sa` >> simp[] >> rpt strip_tac >>
      qpat_assum `!x. not_fresh_at sa x ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  conj_tac
  >- (drule_at (Pat `wb_frame _ _ _ _ _ _`) raw_landing_wb >>
      disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (_ , _)`)) >>
      disch_then irule >> fs[ci_mono_def] >>
      qexistsl_tac [`TAKE cap rd`, `w2n ro`] >> simp[] >> first_assum ACCEPT_TAC) >>
  drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`) ghost_kept_at_clean_suffix >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  qpat_assum `!x. not_fresh_at sa x ==> _` (drule_then strip_assume_tac)
QED
