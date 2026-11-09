(*
 * FmpLowering's O1 pass contract (o1_contract_fmp_lowering).  The stage
 * half is proved here; the step half is fmpStepContract's.
 *
 * Today's source admits none of DALLOCA, DRET, GETFMP, SETFMP, RETFMP
 * (raw_opcode_ok), and no earlier pass seals a function, so FmpLowering's
 * input functions are unsealed and FMP-free (row 3's fmp_free_ctx), in a
 * callee-first order (row 3's callee_first).  On such a function whose
 * callees are already sealed with no FMP parameter and no publication,
 * the analysis finds nothing to thread and the pass only seals the
 * function the same way (fmp_lower_function_seal_only).  The O1 walk
 * runs callees first and the later passes keep signatures, so by
 * induction on a callee-first order every function of the stage is
 * sealed so (fmp_lowering_stage_sealed).  The output context is then the
 * input up to signatures, which the semantics never reads (ctxSealAgree),
 * so runs are equal and the static memory phase becomes the lowered one
 * (fmp_lowering_stage_seal_only).
 *
 * The general stage, with dynamic allocations, waits until the source may
 * have them: there the pass relocates allocations.
 *
 * TOP-LEVEL:
 *   fmp_lower_function_seal_only - one run on an FMP-free function
 *   fmp_lowering_stage_sealed    - a whole stage only seals
 *   fmp_lowering_stage_seal_only - equal runs, memory phase lowered
 *   fmp_lowering_run_contract    - the stage half, row 3 to row 4
 *   o1_contract_fmp_lowering     - the pass contract
 *)
Theory o1ContractFmpLowering
Ancestors
  o1PassContract o1ScheduleDecomp ctxSealAgree fmpLowerDefs
  fmpAnalysisDefs venomPassDispatcher venomFnScheduleRunner
  venomPassSchedule unitMemInv fcgDefs venomInst list ctxLookupAgreeHelpers
  unitShapeDefs venomWf contextCodegenRel irSupply venomFnScheduleRunnerProps
  o1DretDesugarContract fmpStepContract o1ComposeSupport

Theorem fmp_opcode_info_raw[local]:
  (fmp_opcode_needs_fmp op ==> is_raw_fmp_opcode op) /\
  (fmp_opcode_publishes_fmp op ==> is_raw_fmp_opcode op)
Proof
  rw[fmp_opcode_needs_fmp_def, fmp_opcode_publishes_fmp_def] >>
  simp[is_raw_fmp_opcode_def]
QED

Theorem fmp_scan_insts_no_raw[local]:
  !insts. EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) insts ==>
          fmp_scan_insts insts = fmp_info_bottom
Proof
  Induct >> rw[fmp_scan_insts_def] >>
  `~fmp_opcode_needs_fmp h.inst_opcode /\
   ~fmp_opcode_publishes_fmp h.inst_opcode` by metis_tac[fmp_opcode_info_raw] >>
  simp[fmp_info_join_def, fmp_info_bottom_def]
QED

Theorem fmp_direct_info_no_raw[local]:
  no_raw_fmp_ops fn ==> fmp_direct_info fn = fmp_info_bottom
Proof
  rw[no_raw_fmp_ops_def, fmp_direct_info_def] >>
  irule fmp_scan_insts_no_raw >> simp[EVERY_MEM]
QED

Theorem fmp_collect_invokes_targets[local]:
  !insts targets t.
    fmp_collect_invokes insts = SOME targets /\ MEM t targets ==>
    MEM t (MAP FST (get_invoke_targets insts))
Proof
  Induct >> simp[fmp_collect_invokes_def, get_invoke_targets_def] >>
  rw[fmp_invoke_target_def] >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem fmp_resolve_targets_some[local]:
  !targets t. fmp_resolve_targets ctx targets /\ MEM t targets ==>
              IS_SOME (lookup_function t ctx.ctx_functions)
Proof
  Induct >> rw[fmp_resolve_targets_def] >> gvs[]
QED

Theorem fmp_join_target_info_unneeded[local]:
  !targets acc out.
    fmp_join_target_info infos targets acc = SOME out /\
    (!t. MEM t targets ==>
         ?i. FLOOKUP infos t = SOME i /\ ~i.fi_needs_fmp) ==>
    out.fi_needs_fmp = acc.fi_needs_fmp /\
    out.fi_publishes_fmp = acc.fi_publishes_fmp
Proof
  Induct >> simp[fmp_join_target_info_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  `~info.fi_needs_fmp` by (first_x_assum (qspec_then `h` mp_tac) >> simp[]) >>
  first_x_assum drule >> simp[fmp_info_join_def]
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

Theorem get_invoke_targets_mem[local]:
  !insts name. MEM name (MAP FST (get_invoke_targets insts)) ==>
    ?inst rest. MEM inst insts /\ inst.inst_opcode = INVOKE /\
                inst.inst_operands = Label name :: rest
Proof
  Induct >> rw[get_invoke_targets_def] >> BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  metis_tac[]
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

Theorem fmp_lowering_stage_seal_only:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C C' /\
  o1_ctx_shape C /\
  EVERY (\fn. fn.fn_fmp_signature = NONE /\ no_raw_fmp_ops fn)
    C.ctx_functions /\
  callee_first names C.ctx_functions /\
  mem_inv (static_mem_ok eom) C vs ==>
  (!fuel. run_context fuel C' vs = run_context fuel C vs) /\
  mem_inv (lowered_mem_fact eom) C' vs
Proof
  strip_tac >> drule_all fmp_lowering_stage_sealed >> strip_tac >>
  `ctx_seal_eq C C'`
    by (fs[ctx_seal_eq_def, ctx_pass_stage_def] >>
        irule LIST_REL_mono >> first_x_assum (irule_at Any) >>
        simp[fn_seal_eq_def]) >>
  conj_tac >- metis_tac[run_context_seal_eq] >>
  `!fn fn' inst s. fn_seal_eq fn fn' /\ static_mem_ok eom C fn inst s ==>
                   lowered_mem_fact eom C' fn' inst s`
    by (rpt strip_tac >> drule fn_seal_eq_fields >>
        fs[static_mem_ok_def, lowered_mem_ok_def, lowered_mem_fact_def,
           in_revert_forward_def, EVERY_MEM, pairTheory.FORALL_PROD] >>
        metis_tac[]) >>
  metis_tac[mem_inv_seal_eq]
QED

Theorem o1_ctx_shape_entry_no_return[local]:
  o1_ctx_shape ctx /\ ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME fn ==>
  entry_fn_no_return fn
Proof
  rw[o1_ctx_shape_def, EVERY_MEM] >>
  imp_res_tac lookup_function_MEM >>
  imp_res_tac lookup_function_selected_name >>
  res_tac >> gvs[o1_fn_shape_def]
QED

(* Why: the stage only seals (fmp_lowering_stage_sealed), so the output
   runs as the input does, which simulates itself (its entry function
   never returns), and the static memory phase is a lowered one. *)
Theorem fmp_lowering_run_contract:
  o1_run_contract rpolicy D 3
Proof
  `EL 3 o1_fn_passes = CFP_Simple VP_FmpLowering` by EVAL_TAC >>
  simp[o1_run_contract_def, o1_stage_contract_def, o1_inv_def, o1_pre_def,
       o1_static_inv_def, o1_lowered_inv_def, fmp_free_ctx_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all fmp_lowering_stage_seal_only >> strip_tac >>
  drule_all fmp_lowering_stage_sealed >> strip_tac >>
  `ctx_sim D C C vs vs` by
    (irule ctx_sim_refl >> metis_tac[o1_ctx_shape_entry_no_return]) >>
  conj_tac >- fs[ctx_sim_def] >>
  drule ctx_pass_stage_max_live_eom >>
  simp[fn_pass_tag_def, fn_pass_static_layout_effect_def] >>
  strip_tac >> qexists_tac `eom` >> simp[]
QED

Theorem o1_contract_fmp_lowering:
  o1_step_contract_at 3 rpolicy (CFP_Simple VP_FmpLowering) /\
  o1_run_contract rpolicy D 3
Proof
  simp[fmp_step_contract_at, fmp_lowering_run_contract]
QED
