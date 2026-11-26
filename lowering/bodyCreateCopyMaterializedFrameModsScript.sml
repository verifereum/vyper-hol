(* Linked frame transport across a materialized dynamic copy buffer. *)
Theory bodyCreateCopyMaterializedFrameMods
Ancestors
  bodyFullDynamicBuffer bodyFullPostsMods
  bodyFullShadowBodyInv bodyInvSplit bodyPtrDefs exprLoweringProps
  loweringSlice compileEnv loweringStateRelDefs venomState finite_map list pred_set

Theorem create_copy_materialized_frame_mods:
  ctx_has_dalloca ctx /\
  stmt_state_rel H0 ctx func cenv cx es s0 /\
  stmt_state_rel H ctx func cenv cx ee s /\
  ghost_inv_at_mods D lo d cenv cx ee G tn s /\
  immutable_frame_mods func cenv cx ee s /\
  wb_frame cenv es ee sa s0 s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  return_buf_frame d cenv sm s /\
  (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
            vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|>) = s /\
  B = w2n s.vs_fmp /\
  w2n t.vs_fmp = B + venomLayout$ceil32 N /\
  B+N <= LENGTH t.vs_memory /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP Gmat x = FLOOKUP G x /\
       op_taint tt (Var x) = op_taint tn (Var x)) /\
  tt.t_stor = tn.t_stor /\
  tt.t_trans = tn.t_trans /\
  tt.t_imm = tn.t_imm /\
  (!b k. b+k <= B ==> mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory) /\
  (!i. i < B /\ i IN tt.t_mem ==> i IN tn.t_mem) ==>
  stmt_state_rel H ctx func cenv cx ee t /\
  ghost_inv_at_mods D lo d cenv cx ee Gmat tt t /\
  wb_frame cenv es ee sa s0 t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gmat tt /\
  return_buf_frame d cenv sm t /\
  immutable_frame_mods func cenv cx ee t
Proof
  strip_tac >>
  `ghost_inv_at D 0 d cenv cx ee G tn s` by
    (qpat_assum `ghost_inv_at_mods D lo d cenv cx ee G tn s`
       (mp_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     fs[ghost_inv_at_def, ptrDisciplineTheory.allocas_from_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at 0 cenv es sa G0 tn0 s0 G tn` by
    (pure_rewrite_tac[ghost_kept_at_def] >>
     qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G tn`
       (ACCEPT_TAC o REWRITE_RULE [ghost_kept_at_def])) >>
  mp_tac (Q.INST [`lo` |-> `0`, `D` |-> `D`, `d` |-> `d`,
    `Gmat` |-> `Gmat`, `tt` |-> `tt`] dynamic_buffer_materialized_frame) >>
  simp[] >> strip_tac >>
  `s.vs_alloca_next <= B` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx ee s`
       (mp_then Any mp_tac stateRelProjTheory.stmt_state_rel_fmp_room) >>
     simp[fmp_room_def] >> strip_tac >> decide_tac) >>
  qpat_assum `ghost_inv_at_mods D lo d cenv cx ee G tn s`
    (mp_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `lo <= B` by intLib.COOPER_TAC >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (conj_tac
     >- qpat_assum `t with <|vs_vars := _; vs_inst_idx := _; vs_memory := _; vs_fmp := _|> = s`
          (fn th => ACCEPT_TAC
             (SIMP_RULE (srw_ss()) [] (AP_TERM ``\z:venom_state. z.vs_allocas`` th)))
     >- qpat_assum `t with <|vs_vars := _; vs_inst_idx := _; vs_memory := _; vs_fmp := _|> = s`
          (fn th => ACCEPT_TAC
             (SIMP_RULE (srw_ss()) [] (AP_TERM ``\z:venom_state. z.vs_alloca_next`` th)))) >>
  conj_tac >- suspend "ghost" >>
  conj_tac
  >- (pure_rewrite_tac[ghost_kept_at_def] >>
      qpat_assum `ghost_kept_at 0 cenv es sa G0 tn0 s0 Gmat tt`
        (ACCEPT_TAC o REWRITE_RULE [ghost_kept_at_def])) >>
  suspend "immutables"
QED

Resume create_copy_materialized_frame_mods[ghost]:
  fs[ghost_inv_at_mods_def, ghost_inv_at_def,
     ptrDisciplineTheory.allocas_from_def, stor_taint_ok_at_def] >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==> _`
        (qspec_then `x` assume_tac) >>
      qpat_assum `local_ptrs_reserved cenv sm`
        (mp_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
      qpat_assum `!x. not_fresh_at sm x ==> _`
        (qspec_then `x` assume_tac) >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==> _`
        (qspecl_then [`aid`,`b`,`sz`] assume_tac) >> metis_tac[])
QED

Resume create_copy_materialized_frame_mods[immutables]:
  qpat_assum `immutable_frame_mods _ _ _ _ s`
    (strip_assume_tac o REWRITE_RULE [immutable_frame_mods_def,
       immutables_rel_mods_def, immutable_alloca_sep_mods_def]) >>
  simp[immutable_frame_mods_def, immutables_rel_mods_def,
       immutable_alloca_sep_mods_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule immutables_rel_mem_agree >> qexists_tac `s` >> simp[] >>
      conj_tac
      >- (qpat_assum `t with <|vs_vars := _; vs_inst_idx := _; vs_memory := _; vs_fmp := _|> = s`
            (mp_tac o AP_TERM ``\z:venom_state. z.vs_data_section``) >> simp[]) >>
      strip_tac >> rpt gen_tac >> strip_tac >>
      qpat_assum `!b k. b+k <= B ==> _` irule >>
      qpat_assum `!src tops. _ ==> immutable_alloca_sep _ _ _ _ _`
        (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [immutable_alloca_sep_def])) >>
      first_x_assum (drule_all_then strip_assume_tac) >> decide_tac)
  >> rpt gen_tac >> strip_tac >>
  irule immutable_alloca_sep_fields >> qexistsl_tac [`s`,`ee`] >> simp[] >>
  rpt gen_tac >> strip_tac >> qexists_tac `id` >>
  `local_region (cenv with ce_module := src) ee.scopes t id b sz <=>
   local_region (cenv with ce_module := src) ee.scopes s id b sz` by
    (irule local_region_lookup_cong >> simp[] >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `local_ptrs_reserved cenv sm`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
     first_x_assum (drule_then strip_assume_tac) >> simp[]) >>
  fs[]
QED

Finalise create_copy_materialized_frame_mods
