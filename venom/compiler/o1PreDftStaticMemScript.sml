(* Static memory before DFT, with the initial readings fixed throughout. *)
Theory o1PreDftStaticMem
Ancestors
  o1SafeUpto o1PassContract o1PassLift o1ContractFmpLowering
  o1ContractMakeSsa o1ContractSimplifyCfg o1ContractSue
  o1ComposeSupport ctxSealAgree unitMemInv unitTransformDefs contextCodegenRel
  venomPassSchedule venomPassDispatcher unitShapeDefs venomWf
  list arithmetic pair

Theorem o1_static_mem_before_dft_transport:
  (!k. k < LENGTH o1_fn_passes ==>
    ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
      (stage k) (stage (SUC k))) /\
  (!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k)) /\
  (!k. k <= LENGTH o1_fn_passes ==> EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  fmp_free_ctx (stage 3) /\ callee_first names (stage 3).ctx_functions /\
  o1_run_state_ok vs /\ max_live_eom (stage 3) = SOME eom /\
  mem_inv (\ctx fn inst s. gas_cut n vs s ==> static_mem_ok eom ctx fn inst s)
    (stage 3) vs ==>
  max_live_eom (stage 7) = SOME eom /\
  mem_inv (\ctx fn inst s. gas_cut n vs s ==> static_mem_ok eom ctx fn inst s)
    (stage 7) vs
Proof
  strip_tac >>
  `ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering) (o1_walk_view rpolicy 3)
     (stage 3) (stage 4) /\
   ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) (o1_walk_view rpolicy 4)
     (stage 4) (stage 5) /\
   ctx_pass_stage rpolicy (CFP_Simple VP_SimplifyCFG) (o1_walk_view rpolicy 5)
     (stage 5) (stage 6) /\
   ctx_pass_stage rpolicy (CFP_Simple VP_SingleUseExpansion) (o1_walk_view rpolicy 6)
     (stage 6) (stage 7)` by
    (qpat_assum `!k. k < LENGTH _ ==> _`
       (fn th => map_every (fn n => assume_tac
         (SIMP_RULE (srw_ss()) [o1_fn_passes_def] (Q.SPEC n th))) [`3`,`4`,`5`,`6`]) >>
     simp[o1_fn_passes_def]) >>
  `o1_ctx_shape (stage 3) /\ o1_ctx_shape (stage 4) /\
   o1_ctx_shape (stage 5) /\ o1_ctx_shape (stage 6) /\
   EVERY (o1_fn_row 4) (stage 4).ctx_functions /\
   EVERY (o1_fn_row 5) (stage 5).ctx_functions /\
   EVERY (o1_fn_row 6) (stage 6).ctx_functions` by
    (qpat_assum `!k. k <= LENGTH _ ==> o1_ctx_shape _`
       (fn th => map_every (fn n => assume_tac
         (SIMP_RULE (srw_ss()) [o1_fn_passes_def] (Q.SPEC n th))) [`3`,`4`,`5`,`6`]) >>
     qpat_assum `!k. k <= LENGTH _ ==> EVERY _ _`
       (fn th => map_every (fn n => assume_tac
         (SIMP_RULE (srw_ss()) [o1_fn_passes_def] (Q.SPEC n th))) [`4`,`5`,`6`]) >>
     simp[o1_fn_passes_def]) >>
  `vs.vs_vars = FEMPTY /\ ~vs.vs_halted` by
    fs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `mem_corr_closed_rf
     (\ctx fn inst s. gas_cut n vs s ==> static_mem_ok eom ctx fn inst s)` by
    (`mem_corr_closed_rf (\ctx fn inst s.
        (\r. LENGTH vs.vs_gas_readings < n + LENGTH r) s.vs_gas_readings ==>
        static_mem_ok eom ctx fn inst s)` by
       (irule mem_corr_closed_rf_readings_guard >>
        simp[mem_corr_closed_rf_static_mem_ok]) >>
     fs[gas_cut_def]) >>
  suspend "sealed"
QED

Resume o1_static_mem_before_dft_transport[sealed]:
  markerLib.RESUME_TAC >> rpt disch_tac >>
  `EVERY (\fn. fn.fn_fmp_signature = NONE /\ no_raw_fmp_ops fn)
     (stage 3).ctx_functions` by fs[fmp_free_ctx_def] >>
  drule_all fmp_lowering_stage_sealed >> strip_tac >>
  `ctx_seal_eq (stage 3) (stage 4)` by
    (fs[ctx_seal_eq_def, ctx_pass_stage_def] >>
     irule LIST_REL_mono >> first_x_assum (irule_at Any) >>
     simp[fn_seal_eq_def]) >>
  `mem_inv (\ctx fn inst s. gas_cut n vs s ==> static_mem_ok eom ctx fn inst s)
     (stage 4) vs` by
    (irule mem_inv_seal_eq >>
     qexistsl_tac [`stage 3`,
       `\ctx fn inst s. gas_cut n vs s ==> static_mem_ok eom ctx fn inst s`] >>
     simp[] >> rpt strip_tac >> drule fn_seal_eq_fields >>
     fs[static_mem_ok_def, in_revert_forward_def, EVERY_MEM, FORALL_PROD] >>
     metis_tac[]) >>
  `EVERY make_ssa_input_ok (stage 4).ctx_functions /\
   EVERY wf_ssa (stage 5).ctx_functions /\
   EVERY wf_ssa (stage 6).ctx_functions` by fs[EVERY_MEM, o1_fn_row_def] >>
  `EVERY simplify_cfg_fn_ok (stage 5).ctx_functions` by
    (fs[EVERY_MEM] >> rpt strip_tac >> irule simplify_cfg_fn_ok_ssa >>
     fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `mem_inv (\ctx fn inst s. gas_cut n vs s ==> static_mem_ok eom ctx fn inst s)
     (stage 5) vs` by (drule_all make_ssa_stage_mem_inv >> simp[]) >>
  `mem_inv (\ctx fn inst s. gas_cut n vs s ==> static_mem_ok eom ctx fn inst s)
     (stage 6) vs` by (drule_all simplify_cfg_stage_mem_inv_rf >> simp[]) >>
  `mem_inv (\ctx fn inst s. gas_cut n vs s ==> static_mem_ok eom ctx fn inst s)
     (stage 7) vs` by (drule_all sue_stage_mem_inv_rf >> simp[]) >>
  conj_tac >- (
    `max_live_eom (stage 4) = max_live_eom (stage 3)` by
      (irule ctx_pass_stage_max_live_eom >>
       qexistsl_tac [`CFP_Simple VP_FmpLowering`, `rpolicy`, `o1_walk_view rpolicy 3`] >>
       simp[fn_pass_tag_def, fn_pass_static_layout_effect_def]) >>
    metis_tac[make_ssa_stage_max_live_eom, simplify_cfg_stage_max_live_eom,
              sue_stage_max_live_eom]) >> simp[]
QED

Finalise o1_static_mem_before_dft_transport
