(* Resource transport from the staged buffer to the counted slot endpoint. *)
Theory bodyAppendSlotEndpointFramesMods
Ancestors
  bodyFullPostsMods bodySlotCopyFieldsMods bodyFullPathHistory bodyFullUnwrapRun
  bodyFullShared bodyMemoryDefs exprSimCopy exprLoweringProps freshWrites
  bodyInvSplit stmtSimDefs bodyPtrDefs loweringStateRelDefs ptrDiscipline
  venomState finite_map pred_set

Theorem append_slot_endpoint_immutable[local]:
  immutable_frame_mods func cenv cx mid s /\
  ef.immutables = mid.immutables /\
  u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
  (!n b sz. local_region cenv ef.scopes u n b sz <=>
            local_region cenv mid.scopes s n b sz) ==>
  immutable_frame_mods func cenv cx ef u
Proof
  simp[immutable_frame_mods_def] >> strip_tac >> conj_tac
  >- (qpat_x_assum `immutables_rel_mods _ _ _ _ _` mp_tac >>
      simp[immutables_rel_mods_def,immutables_rel_def]) >>
  fs[immutable_alloca_sep_mods_def] >> rpt strip_tac >>
  irule immutable_alloca_sep_fields >> qexistsl_tac [`s`,`mid`] >> simp[] >>
  rpt gen_tac >> disch_tac >> qexists_tac `id` >>
  `!ce sc z. local_region (ce with ce_module := src) sc z id b sz <=>
             local_region ce sc z id b sz` by simp[local_region_def] >>
  gvs[]
QED

Theorem append_slot_endpoint_frames_mods:
  immutable_frame_mods func cenv cx mid s /\
  ghost_inv_at_mods D lo d cenv cx mid G tn s /\
  return_buf_frame d cenv sd s /\ return_buf_sep d cenv mid s /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  alloca_frame c0 es sa s0 cenv mid s /\
  sa.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= sf.cs_next_var /\
  local_ptrs_reserved cenv sd /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x) /\
  ef.scopes = mid.scopes /\ ef.immutables = mid.immutables /\
  u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
  (allocas_below_fmp u <=> allocas_below_fmp s) /\
  (!x. not_fresh_at sd x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_mem = tn.t_mem /\ stor_taint_ok_at D tf u /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK u,Gf,tf) ==>
  immutable_frame_mods func cenv cx ef u /\
  ghost_inv_at_mods D lo d cenv cx ef Gf tf u /\
  return_buf_frame d cenv sf u /\ return_buf_sep d cenv ef u /\
  alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf /\
  alloca_frame c0 es sa s0 cenv ef u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!n b sz. local_region cenv ef.scopes u n b sz <=>
             local_region cenv mid.scopes s n b sz` by
    (simp[] >> rpt gen_tac >> irule copy_buffer_local_region_frame >>
     qexists_tac `sd` >> simp[] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sd x` by
    metis_tac[not_fresh_at_mono] >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    metis_tac[] >>
  `immutable_frame_mods func cenv cx ef u` by
    (irule append_slot_endpoint_immutable >> qexistsl_tac [`mid`,`s`] >> simp[]) >>
  `ghost_inv_at_mods D lo d cenv cx ef Gf tf u` by
    (irule slot_copy_ghost_frame_mods >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`G`,`mid`,`s`,`sd`,`tn`] >>
     simp[] >> metis_tac[local_ptrs_reserved_imm_base]) >>
  `return_buf_frame d cenv sf u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s`,`sd`] >>
     simp[] >> metis_tac[]) >>
  `return_buf_sep d cenv ef u` by
    (irule return_buf_sep_transport >> conj_tac
     >- (rpt gen_tac >> disch_then SUBST_ALL_TAC >>
         fs[bodySimFullTheory.return_buf_sep_def,allocas_from_def] >>
         first_assum ACCEPT_TAC) >>
     qexistsl_tac [`cenv`,`mid`,`s`] >> simp[]) >>
  `alloca_history func u` by drule_all_then ACCEPT_TAC body_full_path_alloca_history >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf` by
    (irule ghost_kept_at_clean_suffix >> qexistsl_tac [`G`,`tn`] >>
     simp[] >> metis_tac[]) >>
  `alloca_frame c0 es sa s0 cenv ef u` by
    (qpat_x_assum `alloca_frame _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[alloca_frame_def] >>
     qpat_assum `!n b sz. local_region _ _ _ _ _ _ <=> _`
       (fn th => simp[th])) >>
  simp[] >> rpt gen_tac >> strip_tac >> metis_tac[]
QED
