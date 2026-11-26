(* Frame the linked state across materialization above the old free pointer. *)
Theory bodyCreateMaterializedWindowMods
Ancestors
  bodyFullDynamicBuffer bodyMethodIdScratchFrameMods
  bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit bodyPtrDefs
  bodyMemoryDefs loweringSlice loweringStateRelDefs loweringPosts
  exprLoweringProps stateRelProj stmtFragPtr ptrDiscipline memoryReadProps
  compileEnv venomState venomMemDefs finite_map alist words arithmetic pred_set

Theorem materialized_window_frame_mods:
  ctx_has_dalloca ctx /\
  stmt_state_rel H0 ctx func cenv cx es s0 /\
  stmt_state_rel H ctx func cenv cx ee s /\
  ghost_inv_at_mods D lo d cenv cx ee G tn s /\
  immutable_frame_mods func cenv cx ee s /\
  wb_frame cenv es ee sa s0 s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  return_buf_frame d cenv sm s /\
  (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
            vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|>) = s /\
  B = w2n s.vs_fmp /\ w2n t.vs_fmp = B + venomLayout$ceil32 N /\
  B + N <= LENGTH t.vs_memory /\ LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP Gmat x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)) /\
  tt.t_stor = tn.t_stor /\ tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
  (!b k. b+k <= B ==> read_memory b k t = read_memory b k s) /\
  (!i. i < B /\ i IN tt.t_mem ==> i IN tn.t_mem) ==>
  stmt_state_rel H ctx func cenv cx ee t /\
  ghost_inv_at_mods D lo d cenv cx ee Gmat tt t /\
  immutable_frame_mods func cenv cx ee t /\
  wb_frame cenv es ee sa s0 t /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gmat tt /\
  return_buf_frame d cenv sm t
Proof
  simp[read_memory_eq_mem_bytes_at] >> strip_tac >>
  `ghost_inv_at D 0 d cenv cx ee G tn s` by
    (irule method_id_ghost_at_zero >> qexists `lo` >> simp[]) >>
  `ghost_kept_at 0 cenv es sa G0 tn0 s0 G tn` by
    (qpat_assum `ghost_kept_at lo _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ghost_kept_at_def] >> disch_then ACCEPT_TAC) >>
  `stmt_state_rel H ctx func cenv cx ee t /\ ghost_inv_at D 0 d cenv cx ee Gmat tt t /\
   wb_frame cenv es ee sa s0 t /\ ghost_kept_at 0 cenv es sa G0 tn0 s0 Gmat tt /\
   return_buf_frame d cenv sm t` by
    (irule dynamic_buffer_materialized_frame >> simp[] >>
     conj_tac >- (qexists `H0` >> simp[]) >> qexistsl [`G`,`N`,`s`,`tn`] >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gmat tt` by
    (qpat_assum `ghost_kept_at 0 _ _ _ _ _ _ Gmat tt` mp_tac >>
     pure_rewrite_tac[ghost_kept_at_def] >> disch_then ACCEPT_TAC) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_data_section = s.vs_data_section` by
    (qpat_assum `t with <|vs_memory := _; vs_vars := _; vs_inst_idx := _; vs_fmp := _|> = s`
       (fn th => map_every (mp_tac o C AP_TERM th)
         [``venom_state_vs_allocas``,``venom_state_vs_alloca_next``,``venom_state_vs_data_section``]) >>
     simp[]) >>
  `s.vs_alloca_next <= B` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx ee s`
       (mp_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_fmp_room) >>
     simp[fmp_room_def] >> decide_tac) >>
  `lo <= s.vs_alloca_next` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[ghost_inv_at_mods_def]) >>
     first_assum ACCEPT_TAC) >>
  simp[] >> conj_tac
  >- suspend "ghost" >>
  suspend "immutables"
QED

Resume materialized_window_frame_mods[ghost]:
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (qpat_assum `!b k. b+k <= B ==> _` irule >> decide_tac) >>
  `!i. i < lo /\ i IN tt.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >> qpat_assum `!i. i < B /\ _ ==> _` irule >> simp[] >> decide_tac) >>
  fs[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >>
  `!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==>
       FLOOKUP Gmat x = NONE /\ op_taint tt (Var x) = {}` by
    (gen_tac >> strip_tac >>
     `not_fresh_at sm x` by metis_tac[local_ptrs_reserved_imm_base] >>
     qpat_assum `!x. not_fresh_at sm x ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. lo <> 0 /\ _ ==> _` (drule_all_then strip_assume_tac) >> simp[]) >>
  simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume materialized_window_frame_mods[immutables]:
  qpat_x_assum `immutable_frame_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[immutable_frame_mods_def,
                                    immutables_rel_mods_def, immutable_alloca_sep_mods_def]) >>
  simp[immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def] >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >> irule immutables_rel_mem_agree >> qexists `s` >>
      simp[] >> disch_tac >> rpt gen_tac >> strip_tac >>
      qpat_assum `!b k. b+k <= B ==> _` irule >>
      qpat_assum `!src tops. _ ==> immutable_alloca_sep _ _ _ _ s`
        (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [immutable_alloca_sep_def])) >>
      qpat_assum `cenv.ce_is_ctor ==> _`
        (qspecl_then [`name`,`tv`,`v`,`off`] mp_tac o UNDISCH) >>
      simp[] >> decide_tac) >>
  rpt gen_tac >> disch_tac >> irule immutable_alloca_sep_fields >>
  qexistsl [`s`,`ee`] >> simp[] >>
  map_every qx_gen_tac [`id`,`locb`,`sz`] >> disch_tac >> qexists `id` >>
  `local_region (cenv with ce_module := src) ee.scopes t id locb sz <=>
   local_region (cenv with ce_module := src) ee.scopes s id locb sz` by
    (irule local_region_lookup_cong >> simp[] >>
     rpt strip_tac >> `not_fresh_at sm p` by metis_tac[local_ptrs_reserved_def] >> simp[]) >>
  fs[]
QED

Finalise materialized_window_frame_mods
