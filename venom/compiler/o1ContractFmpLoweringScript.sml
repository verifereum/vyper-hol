(*
 * FmpLowering's O1 pass contract (o1_contract_fmp_lowering).  The step
 * half is fmpStepContract's.  The stage half is assembled here from the
 * stage simulation (fmpStageRunner) and the lowered memory phase
 * (fmpStageCoverage), at the raw input state: the real state with its
 * free-memory pointer fields set to the raw run's fmp.
 *
 * TOP-LEVEL:
 *   fmp_lowering_run_contract_gas - the stage half, row 3 to row 4
 *   o1_contract_fmp_lowering      - the pass contract
 *)
Theory o1ContractFmpLowering
Ancestors
  o1PassContract o1ScheduleDecomp fmpLowerDefs fmpAnalysisDefs
  venomPassDispatcher venomFnScheduleRunner venomPassSchedule
  venomCompilerTypes venomState venomInst o1ComposeSupport fmpStepContract
  fmpStageRunner fmpStageCoverage list
  o1RequestContract fcgDefs ctxLookupAgreeHelpers

(* Functions without raw FMP operations only acquire a sealed signature. *)
Theorem fmp_resolve_targets_some[local]:
  !targets t. fmp_resolve_targets ctx targets /\ MEM t targets ==>
              IS_SOME (lookup_function t ctx.ctx_functions)
Proof
  Induct >> rw[fmp_resolve_targets_def] >> gvs[]
QED

(* The analysis gives an FMP-free function with sealed F/F callees no
   need and no publication. *)
Theorem fmp_info_valid_seal_only[local]:
  fmp_info_valid ctx infos /\ MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = NONE /\ no_raw_fmp_ops fn /\
  (!name g. MEM name (fn_invoke_targets fn) /\
     lookup_function name ctx.ctx_functions = SOME g ==>
     g.fn_fmp_signature =
       SOME <| fms_has_fmp_param := F; fms_publishes := F |>) /\
  FLOOKUP infos fn.fn_name = SOME info ==>
  ~info.fi_needs_fmp /\ ~info.fi_publishes_fmp
Proof
  strip_tac >> fs[fmp_info_valid_def] >>
  first_x_assum (qspec_then `fn` mp_tac) >> simp[] >> strip_tac >>
  drule fmp_join_target_info_unneeded >> impl_tac
  >- (rpt strip_tac >>
      gvs[fmp_function_targets_def, AllCaseEqs()] >>
      drule_all fmp_resolve_targets_some >>
      simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
      rename1 `lookup_function t ctx.ctx_functions = SOME g` >>
      drule_all fmp_collect_invokes_targets >> strip_tac >>
      `g.fn_fmp_signature =
         SOME <| fms_has_fmp_param := F; fms_publishes := F |>`
        by (qpat_x_assum `!name g. _` (qspecl_then [`t`, `g`] mp_tac) >>
            simp[fn_invoke_targets_def, fcg_scan_function_def]) >>
      `MEM g ctx.ctx_functions /\ g.fn_name = t`
        by metis_tac[lookup_function_MEM, lookup_function_selected_name] >>
      first_x_assum drule >> simp[fmp_info_of_signature_def]) >>
  simp[fmp_direct_info_no_raw, fmp_info_bottom_def]
QED

(* Why: with no FMP opcode the direct info is bottom; every analysed
   target is an INVOKE label, so one of fn_invoke_targets, and resolves
   to a sealed function whose info is its signature's, here bottom; so
   fn's info is bottom, the pass takes the seal-only branch (or fails),
   and the seal writes needs = F, publishes = F. *)
Theorem fmp_lower_function_seal_only:
  fmp_lower_function ctx s fn = SOME (fn',s') /\
  fn.fn_fmp_signature = NONE /\ no_raw_fmp_ops fn /\
  (!name g. MEM name (fn_invoke_targets fn) /\
     lookup_function name ctx.ctx_functions = SOME g ==>
     g.fn_fmp_signature =
       SOME <| fms_has_fmp_param := F; fms_publishes := F |>) ==>
  fn' = fn with fn_fmp_signature :=
          SOME <| fms_has_fmp_param := F; fms_publishes := F |> /\
  s' = s
Proof
  strip_tac >>
  gvs[fmp_lower_function_def, fmp_lower_function_with_info_def,
      AllCaseEqs()] >>
  `MEM fn ctx.ctx_functions`
    by (fs[fmp_lower_input_def] >> metis_tac[lookup_function_MEM]) >>
  drule_all fmp_info_valid_seal_only >> strip_tac >> gvs[] >>
  gvs[fmp_checked_seal_def, fmp_seal_def, AllCaseEqs()] >>
  simp[venomInstTheory.ir_function_component_equality]
QED

(* The walk passes after FmpLowering all keep the FMP convention. *)
Theorem fn_steps_after_fmp_signature:
  fn_steps rpolicy (DROP 4 o1_fn_passes) g g' ==>
  g'.fn_fmp_signature = g.fn_fmp_signature
Proof
  simp[o1_fn_passes_def, fn_steps_def, fn_pass_step_def,
       fn_pass_effects_hold_def, fn_abi_effect_holds_def,
       fn_pass_abi_effect_def, fn_fmp_convention_eq_def, fn_pass_tag_def] >>
  rw[] >> gvs[]
QED

(* A callee named by an output function of the stage resolves there. *)
Theorem stage_callee_resolves[local]:
  ctx_pass_stage rpolicy pass view C C' /\ o1_ctx_shape C /\
  MEM fn C.ctx_functions /\ MEM name (fn_invoke_targets fn) ==>
  ?g'. lookup_function name C'.ctx_functions = SOME g'
Proof
  strip_tac >>
  `fn_invoke_ok (ctx_fn_names C) fn`
    by fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
  fs[fn_invoke_targets_def, fcg_scan_function_def] >>
  drule get_invoke_targets_mem >> strip_tac >>
  fs[fn_invoke_ok_def] >> first_x_assum drule >> simp[] >> strip_tac >>
  `ctx_fn_names C' = ctx_fn_names C`
    by (fs[ctx_pass_stage_def, ctx_fn_names_def, LIST_REL_EL_EQN] >>
        irule LIST_EQ >> rw[EL_MAP] >>
        first_x_assum (qspec_then `x` mp_tac) >> rw[fn_pass_step_def] >>
        gvs[]) >>
  Cases_on `lookup_function name C'.ctx_functions` >> simp[] >>
  drule lookup_function_not_mem >> gvs[ctx_fn_names_def]
QED

(* One function of the stage, given its callees' outputs are sealed F/F. *)
Theorem fmp_stage_step[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C C' /\
  o1_ctx_shape C /\
  EVERY (\fn. fn.fn_fmp_signature = NONE /\ no_raw_fmp_ops fn)
    C.ctx_functions /\
  i < LENGTH C.ctx_functions /\
  (!name g'. MEM name (fn_invoke_targets (EL i C.ctx_functions)) /\
     lookup_function name C'.ctx_functions = SOME g' ==>
     g'.fn_fmp_signature =
       SOME <| fms_has_fmp_param := F; fms_publishes := F |>) ==>
  EL i C'.ctx_functions =
    EL i C.ctx_functions with fn_fmp_signature :=
      SOME <| fms_has_fmp_param := F; fms_publishes := F |>
Proof
  strip_tac >>
  `MEM (EL i C.ctx_functions) C.ctx_functions` by simp[EL_MEM] >>
  qabbrev_tac `fn = EL i C.ctx_functions` >>
  `!name. MEM name (fn_invoke_targets fn) ==>
          ?g'. lookup_function name C'.ctx_functions = SOME g'`
    by metis_tac[stage_callee_resolves] >>
  `EVERY (\fn. fn.fn_fmp_signature = NONE /\ no_raw_fmp_ops fn)
     C.ctx_functions` by simp[] >>
  fs[ctx_pass_stage_def, LIST_REL_EL_EQN] >>
  first_x_assum drule >> strip_tac >>
  gvs[fn_pass_step_def, AllCaseEqs(), EVERY_MEM] >>
  `fn.fn_fmp_signature = NONE /\ no_raw_fmp_ops fn` by metis_tac[] >>
  drule fmp_lower_function_seal_only >> simp[] >> impl_tac
  >- (rpt strip_tac >>
      `?g'. lookup_function name C'.ctx_functions = SOME g'` by metis_tac[] >>
      fs[o1_walk_view_def, walk_view_def] >>
      first_x_assum drule_all >> strip_tac >> gvs[] >>
      drule fn_steps_from_fn_steps >> strip_tac >>
      drule fn_steps_after_fmp_signature >> metis_tac[]) >>
  simp[]
QED

Theorem fmp_lowering_stage_sealed:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C C' /\
  o1_ctx_shape C /\
  EVERY (\fn. fn.fn_fmp_signature = NONE /\ no_raw_fmp_ops fn)
    C.ctx_functions /\
  callee_first names C.ctx_functions ==>
  LIST_REL
    (\fn fn'. fn' = fn with fn_fmp_signature :=
                SOME <| fms_has_fmp_param := F; fms_publishes := F |>)
    C.ctx_functions C'.ctx_functions
Proof
  strip_tac >>
  `LENGTH C'.ctx_functions = LENGTH C.ctx_functions`
    by fs[ctx_pass_stage_def, LIST_REL_EL_EQN] >>
  `!n i. i < LENGTH C.ctx_functions /\
         (case list_index (EL i C.ctx_functions).fn_name names of
            SOME k => k | NONE => 0) = n ==>
         EL i C'.ctx_functions =
           EL i C.ctx_functions with fn_fmp_signature :=
             SOME <| fms_has_fmp_param := F; fms_publishes := F |>`
    suffices_by simp[LIST_REL_EL_EQN] >>
  completeInduct_on `n` >> rpt strip_tac >>
  drule fmp_stage_step >> disch_then irule >> simp[] >> rpt strip_tac >>
  drule venomInstTheory.lookup_function_MEM >> simp[MEM_EL] >> strip_tac >>
  rename1 `g' = EL j C'.ctx_functions` >> gvs[] >>
  `(EL j C.ctx_functions).fn_name = name`
    by (`(EL j C'.ctx_functions).fn_name = name`
          by metis_tac[lookup_function_selected_name] >>
        fs[ctx_pass_stage_def, LIST_REL_EL_EQN] >>
        qpat_x_assum `!n. n < LENGTH C.ctx_functions ==> ?observed s out. _`
          (qspec_then `j` mp_tac) >>
        simp[fn_pass_step_def] >> strip_tac >> gvs[]) >>
  `list_precedes name (EL i C.ctx_functions).fn_name names`
    by (fs[callee_first_def] >> first_x_assum irule >> simp[EL_MEM]) >>
  fs[list_precedes_def] >>
  Cases_on `list_index name names` >> fs[] >>
  Cases_on `list_index (EL i C.ctx_functions).fn_name names` >> fs[] >>
  rename1 `k1 < k2` >>
  first_x_assum (qspec_then `k1` mp_tac) >> simp[] >>
  disch_then (qspec_then `j` mp_tac) >> simp[]
QED

(* Why: the raw state is the real one with fmp in both free-memory pointer
   fields, a raw variant of it; the stage simulation and the lowered
   memory phase hold there, the static layout's end is the input's, which
   FmpLowering keeps, and row 4's function rows carry make_ssa_input_ok. *)
Theorem o1_static_stage_fmp_lowering_fixed:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C C' /\
  o1_pre 3 C C' /\ dead_wf D /\ o1_ctx_shape C /\
  o1_initial_state_ok vs' /\ vs'.vs_fmp = vs'.vs_initial_fmp /\
  code_layout_valid vs' ==>
  raw_variant fmp
    (vs' with <| vs_fmp := fmp; vs_initial_fmp := fmp |>) vs' /\
    (o1_inv D 3 C
       (vs' with <| vs_fmp := fmp; vs_initial_fmp := fmp |>) /\
     fmp_variant_room (SOME fmp) C' vs' ==>
     ctx_sim_fuel I D C C'
       (vs' with <| vs_fmp := fmp; vs_initial_fmp := fmp |>) vs' /\
     ctx_abort_rq D C C'
       (vs' with <| vs_fmp := fmp; vs_initial_fmp := fmp |>) vs' /\
     o1_inv D (SUC 3) C' vs')
Proof
  strip_tac >>
  conj_tac
  >- simp[raw_variant_def, gas_variant_def,
          venom_state_component_equality] >>
  strip_tac >>
  conj_tac >- metis_tac[fmp_lowering_stage_sim_static] >>
  conj_tac >- metis_tac[fmp_lowering_stage_abort_rq_static] >>
  `?eom. max_live_eom C = SOME eom` by
    (qpat_x_assum `o1_inv D 3 C _` mp_tac >>
     simp[o1_inv_def, o1_static_inv_def] >> metis_tac[]) >>
  `mem_inv (lowered_mem_fact eom) C' vs'` by
    metis_tac[fmp_lowering_stage_lowered_mem_static] >>
  `max_live_eom C' = max_live_eom C` by
    (irule ctx_pass_stage_max_live_eom >>
     qexistsl [`CFP_Simple VP_FmpLowering`, `rpolicy`, `o1_walk_view rpolicy 3`] >>
     simp[fn_pass_tag_def, fn_pass_static_layout_effect_def]) >>
  simp[o1_inv_def, o1_lowered_inv_def] >>
  fs[o1_pre_def, EVERY_MEM, o1_fn_row_def]
QED

Theorem o1_static_stage_fmp_lowering:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C C' /\
  o1_pre 3 C C' /\ dead_wf D /\ o1_ctx_shape C /\
  o1_initial_state_ok vs' /\ vs'.vs_fmp = vs'.vs_initial_fmp /\
  code_layout_valid vs' ==>
  ?vs. raw_variant fmp vs vs' /\
    (o1_inv D 3 C vs /\ fmp_variant_room (SOME fmp) C' vs' ==>
     ctx_sim_fuel I D C C' vs vs' /\ ctx_abort_rq D C C' vs vs' /\
     o1_inv D (SUC 3) C' vs')
Proof
  metis_tac[o1_static_stage_fmp_lowering_fixed]
QED

Theorem fmp_lowering_run_contract_gas:
  o1_run_contract_gas rpolicy D fmp 3
Proof
  `EL 3 o1_fn_passes = CFP_Simple VP_FmpLowering` by EVAL_TAC >>
  simp[o1_run_contract_gas_def, o1_stage_contract_gas_def,
       fmp_variant_def, pass_fuel_def] >>
  rpt gen_tac >> strip_tac >>
  `o1_initial_state_ok vs' /\ vs'.vs_fmp = vs'.vs_initial_fmp /\
   code_layout_valid vs'` by fs[o1_run_state_ok_def] >>
  drule_all o1_static_stage_fmp_lowering >> simp[] >> metis_tac[]
QED

Theorem o1_contract_fmp_lowering:
  o1_step_contract_at 3 rpolicy (CFP_Simple VP_FmpLowering) /\
  o1_run_contract_gas rpolicy D fmp 3
Proof
  simp[fmp_step_contract_at, fmp_lowering_run_contract_gas]
QED
