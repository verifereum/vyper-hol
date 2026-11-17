Theory o1CodeEndFmpTransport
Ancestors
  o1ContractFmpLowering ctxSealAgree codegenSymRel o1PassContract
  o1ScheduleDecomp o1LabelFlowMiddleFmp o1ComposeSupport unitMemInv
  unitTransformDefs venomPassSchedule venomPassDispatcher o1DretDesugarContract
  venomInst ctxLookupAgreeHelpers contextCodegenRel pair list

(* Sealing changes signatures only: the active instruction and its state
   are literally unchanged, including the evaluated code_end offset. *)
Theorem code_end_offset_ok_seal_eq[local]:
  ctx_seal_eq C C' ==>
  (code_end_offset_ok (raw_reachable s) C <=>
   code_end_offset_ok (raw_reachable s) C')
Proof
  strip_tac >> simp[code_end_offset_ok_def] >> eq_tac >>
  rpt strip_tac >>
  `ctx_seal_eq C' C` by metis_tac[ctx_seal_eq_sym] >>
  drule_all raw_reachable_seal_eq >> strip_tac >>
  drule fn_seal_eq_fields >> strip_tac >>
  `code_end_var fn' x` by metis_tac[code_end_var_same_blocks] >>
  metis_tac[]
QED

Theorem fmp_lowering_code_end_run_contract:
  o1_stage_contract rpolicy D (EL 3 o1_fn_passes)
    (o1_walk_view rpolicy 3) (o1_pre 3)
    (\C s. o1_inv D 3 C s /\ EVERY no_raw_fmp_ops C.ctx_functions /\
      code_end_offset_ok (raw_reachable s) C)
    (\C s. o1_inv D 4 C s /\ code_end_offset_ok (raw_reachable s) C)
Proof
  simp[o1_stage_contract_def] >> rpt gen_tac >> strip_tac >>
  `EL 3 o1_fn_passes = CFP_Simple VP_FmpLowering` by EVAL_TAC >>
  fs[o1_inv_def, o1_static_inv_def, fmp_free_ctx_def] >>
  rename1 `max_live_eom C = SOME eom` >>
  `EVERY (\fn. fn.fn_fmp_signature = NONE /\ no_raw_fmp_ops fn)
     C.ctx_functions` by fs[EVERY_MEM] >>
  drule_all fmp_lowering_stage_sealed >> strip_tac >>
  `ctx_seal_eq C C'` by
    (fs[ctx_seal_eq_def, ctx_pass_stage_def] >>
     irule LIST_REL_mono >> first_x_assum (irule_at Any) >>
     simp[fn_seal_eq_def]) >>
  `ctx_sim_fuel I D C C' s s` by
    (`ctx_sim_fuel I D C C s s` by
       (irule ctx_sim_refl >> rpt strip_tac >>
        imp_res_tac lookup_function_MEM >>
        imp_res_tac lookup_function_selected_name >>
        fs[o1_ctx_shape_def, EVERY_MEM] >>
        metis_tac[o1_fn_shape_def]) >>
     fs[ctx_sim_fuel_def] >> metis_tac[run_context_seal_eq]) >>
  `max_live_eom C' = max_live_eom C` by
    (irule ctx_pass_stage_max_live_eom >>
     qexistsl_tac [`CFP_Simple VP_FmpLowering`, `rpolicy`, `o1_walk_view rpolicy 3`] >>
     simp[fn_pass_tag_def, fn_pass_static_layout_effect_def]) >>
  `mem_inv (lowered_mem_fact eom) C' s` by
    (irule mem_inv_seal_eq >>
     qexistsl_tac [`C`, `static_mem_ok eom`] >> simp[] >>
     rpt strip_tac >> drule fn_seal_eq_fields >>
     fs[static_mem_ok_def, lowered_mem_fact_def, lowered_mem_ok_def,
        in_revert_forward_def, EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
  `EVERY make_ssa_input_ok C'.ctx_functions` by
    (fs[o1_pre_def, EVERY_MEM, o1_fn_row_def] >> metis_tac[]) >>
  drule code_end_offset_ok_seal_eq >>
  disch_then (qspec_then `s` mp_tac) >>
  simp[o1_lowered_inv_def, pass_fuel_def]
QED
