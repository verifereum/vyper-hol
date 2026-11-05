(*
 * DretDesugar's O1 contract (its pre-walk run).
 *
 * The stage shape forbids DRET (o1_fn_shape's no_dret: the source never
 * has one), and dret_desugar_function leaves a DRET-free function alone, so
 * the run is the identity on every stage context.  The stage contract then
 * needs a context to simulate itself, which holds because the entry
 * function has no internal return.  Being the identity, the run keeps any
 * stage invariant.
 *
 * TOP-LEVEL: o1_contract_dret_desugar_pre_walk.
 *)
Theory o1DretDesugarContract
Ancestors
  o1PassContract venomRetProps venomFnScheduleRunnerProps dretDesugarProofs
  ctxLookupAgreeHelpers passSimulationDefs stateEquiv venomExecSemantics
  unitTransformDefs venomInst list

(* A context whose entry function has no internal return simulates itself:
   its terminating runs end in Halt or Abort. *)
Theorem ctx_sim_refl:
  (!name fn. C.ctx_entry = SOME name /\
             lookup_function name C.ctx_functions = SOME fn ==>
             entry_fn_no_return fn) ==>
  ctx_sim D C C vs vs
Proof
  rw[ctx_sim_def] >> qexists_tac `fuel` >>
  irule unit_result_rel_dead_result_rel >>
  Cases_on `run_context fuel C vs` >>
  gvs[terminates_def, unit_result_rel_def, observable_equiv_def] >>
  metis_tac[run_context_not_int_ret, run_context_not_ok,
            entry_fn_no_return_def]
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

Theorem dret_desugar_step_identity[local]:
  fn_pass_step rpolicy (CFP_Simple VP_DretDesugar) observed s fn out /\
  no_dret fn ==>
  out = <| fpo_function := fn; fpo_label_map := []; fpo_supply := s |>
Proof
  rw[fn_pass_step_def] >> gvs[dret_desugar_function_identity]
QED

Theorem LIST_REL_identity[local]:
  !l l'. LIST_REL R l l' ==> (!x y. MEM x l /\ R x y ==> y = x) ==> l' = l
Proof
  Induct >> Cases_on `l'` >> rw[] >> metis_tac[]
QED

Theorem dret_desugar_stage_identity:
  ctx_pass_stage rpolicy (CFP_Simple VP_DretDesugar) view C C' /\
  o1_ctx_shape C ==> C' = C
Proof
  rw[ctx_pass_stage_def] >>
  simp[venom_context_component_equality] >>
  qpat_x_assum `LIST_REL _ _ _` (mp_tac o MATCH_MP LIST_REL_identity) >>
  impl_tac >> simp[] >>
  rw[] >> gvs[o1_ctx_shape_def, EVERY_MEM] >>
  `no_dret x` by (res_tac >> gvs[o1_fn_shape_def]) >>
  drule_all dret_desugar_step_identity >> simp[]
QED

Theorem o1_contract_dret_desugar_pre_walk:
  o1_step_contract rpolicy (CFP_Simple VP_DretDesugar) /\
  (!view I. o1_stage_contract rpolicy D (CFP_Simple VP_DretDesugar) view
              no_pre I I)
Proof
  conj_tac
  >- (simp[o1_step_contract_def] >> rpt gen_tac >> strip_tac >>
      `MEM fn observed.cu_context.ctx_functions` by
        (gvs[fn_pass_step_def] >> imp_res_tac lookup_unique_function_member) >>
      `o1_fn_shape observed.cu_context fn` by gvs[o1_ctx_shape_def, EVERY_MEM] >>
      `no_dret fn` by gvs[o1_fn_shape_def] >>
      drule_all dret_desugar_step_identity >> rw[] >>
      simp[fresh_names_ok_def, label_map_sources_ok_def]) >>
  rw[o1_stage_contract_def] >> drule_all dret_desugar_stage_identity >>
  rw[] >> irule ctx_sim_refl >> metis_tac[o1_ctx_shape_entry_no_return]
QED
