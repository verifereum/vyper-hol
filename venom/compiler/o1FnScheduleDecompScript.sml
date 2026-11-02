(*
 * One function's schedule, decomposed into its chain of pass runs.
 *
 * run_configured_fn_passes folds the pass list over one function, each
 * pass observing the unit with the function's current form, then applies
 * the accumulated label map to the whole unit.  Under the step contracts
 * (o1PassContract) the label map's sources are dead labels of the
 * function (label_map_dead), so applying it is the identity on code
 * (unitLabelMapIdentity), and the run is a fn_chain: the function's
 * trajectory through the passes and the units the passes observed
 * (run_configured_fn_passes_decomp).
 *)
Theory o1FnScheduleDecomp
Ancestors
  o1FnScheduleDecompHelpers o1PassContract unitLabelMapIdentity venomFnScheduleRunner
  venomFnScheduleRunnerProps venomPassDispatcher venomInst irSupply
  venomCompilerWf venomWf unitShapeDefs list rich_list

(* ===== Chains ===== *)

(* fs = [f_0; ...; f_n] is a function's trajectory through the passes,
   obs = [o_1; ...; o_n] the units the passes observed, with the supply
   threaded from s. *)
Definition fn_chain_def:
  (fn_chain rpolicy [] s fs obs <=> (?fn. fs = [fn]) /\ obs = []) /\
  (fn_chain rpolicy (pass::passes) s fs obs <=>
     ?fn fn' rest observed obs' out.
       fs = fn::fn'::rest /\ obs = observed::obs' /\
       fn_pass_step rpolicy pass observed s fn out /\
       out.fpo_function = fn' /\
       fn_chain rpolicy passes out.fpo_supply (fn'::rest) obs')
End

Theorem fn_chain_length:
  !passes s fs obs.
    fn_chain rpolicy passes s fs obs ==>
    LENGTH fs = SUC (LENGTH passes) /\ LENGTH obs = LENGTH passes
Proof
  Induct >> simp[fn_chain_def] >> rw[] >> res_tac >> simp[]
QED

Theorem fn_chain_step:
  !passes s fs obs k.
    fn_chain rpolicy passes s fs obs /\ k < LENGTH passes ==>
    ?s' out.
      fn_pass_step rpolicy (EL k passes) (EL k obs) s' (EL k fs) out /\
      out.fpo_function = EL (SUC k) fs
Proof
  Induct >> simp[fn_chain_def] >> rw[] >> Cases_on `k` >> gvs[]
  >- (qexistsl_tac [`s`,`out`] >> simp[])
  >> first_x_assum drule >> disch_then (qspec_then `n` mp_tac) >> simp[]
QED

Theorem fn_chain_fn_steps:
  !passes s fs obs k.
    fn_chain rpolicy passes s fs obs /\ k <= LENGTH passes ==>
    fn_steps rpolicy (DROP k passes) (EL k fs) (LAST fs)
Proof
  Induct
  >- (simp[fn_chain_def, fn_steps_def] >> rw[] >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  fs[fn_chain_def] >> gvs[] >>
  Cases_on `k`
  >- (simp[fn_steps_def] >>
      first_x_assum (drule_at Any) >>
      disch_then (qspec_then `0` mp_tac) >>
      simp[] >> metis_tac[]) >>
  gvs[] >> first_x_assum drule >> simp[]
QED

Theorem fn_chain_names:
  !passes s fs obs.
    fn_chain rpolicy passes s fs obs ==>
    EVERY (\f. f.fn_name = (HD fs).fn_name) fs
Proof
  Induct >> simp[fn_chain_def] >> rw[] >> res_tac >>
  gvs[fn_pass_step_def, EVERY_MEM]
QED

Theorem fn_chain_invoke_targets:
  !passes s fs obs.
    fn_chain rpolicy passes s fs obs ==>
    !f. MEM f fs ==> list_subset (fn_invoke_targets f) (fn_invoke_targets (HD fs))
Proof
  Induct
  >- (simp[fn_chain_def] >> rw[] >> gvs[list_subset_def, EVERY_MEM]) >>
  rpt gen_tac >> simp[fn_chain_def] >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  `list_subset (fn_invoke_targets out.fpo_function) (fn_invoke_targets fn)`
    by fs[fn_pass_step_def, introduces_no_invoke_edges_def,
          fn_invoke_targets_def, list_subset_def] >>
  fs[] >> rpt strip_tac >> gvs[]
  >- simp[list_subset_def, EVERY_MEM] >>
  irule list_subset_trans >> goal_assum (drule_at Any) >>
  first_x_assum irule >> simp[]
QED

(* ===== Replacing one function ===== *)

Definition replace_fn_def:
  replace_fn name g fns = MAP (\f. if f.fn_name = name then g else f) fns
End

Definition unit_with_fns_def:
  unit_with_fns unit fns =
    unit with cu_context := unit.cu_context with ctx_functions := fns
End

Theorem o1_fn_shape_ctx_eq:
  ctx_fn_names ctx' = ctx_fn_names ctx /\ ctx'.ctx_entry = ctx.ctx_entry ==>
  (o1_fn_shape ctx' fn <=> o1_fn_shape ctx fn)
Proof
  simp[o1_fn_shape_def]
QED

Theorem o1_ctx_shape_replace:
  o1_ctx_shape ctx /\ o1_fn_shape ctx g /\ g.fn_name = name ==>
  o1_ctx_shape (ctx with ctx_functions := replace_fn name g ctx.ctx_functions)
Proof
  simp[replace_fn_def] >> metis_tac[o1_ctx_shape_MAP_replace]
QED

(* ===== One function's schedule ===== *)

(* The sources of a label map are dead: original block labels of fn0 or
   fresh since s0, never the function's name or a reserved label, and
   gone from fn'. *)
Definition label_map_dead_def:
  label_map_dead s0 fn0 fn' label_map <=>
    EVERY (\e. (MEM (FST e) (fn_labels fn0) \/
                ~MEM (FST e) s0.irs_used_labels) /\
               FST e <> fn0.fn_name /\ ~reserved_label (FST e) /\
               ~MEM (FST e) (fn_labels fn')) label_map
End

Theorem step_map_dead_after_fold[local]:
  fn_pass_step rpolicy pass observed s fn out /\
  o1_fn_shape ctx fn /\
  label_map_sources_ok fn out.fpo_function out.fpo_label_map /\
  (!l. MEM l (fn_labels fn) ==>
       MEM l (fn_labels fn0) \/ ~MEM l s0.irs_used_labels) /\
  fn.fn_name = fn0.fn_name /\
  (!l. MEM l (fn_labels final) ==>
       MEM l (fn_labels out.fpo_function) \/ ~MEM l out.fpo_supply.irs_used_labels) ==>
  label_map_dead s0 fn0 final out.fpo_label_map
Proof
  strip_tac >>
  `MEM fn observed.cu_context.ctx_functions`
    by (fs[fn_pass_step_def] >> metis_tac[lookup_unique_function_member]) >>
  `!l. MEM l (fn_labels fn) ==> MEM l out.fpo_supply.irs_used_labels`
    by (fs[fn_pass_step_def] >> metis_tac[unit_supply_member_label]) >>
  fs[label_map_dead_def, label_map_sources_ok_def, EVERY_MEM] >>
  rpt strip_tac
  >- metis_tac[o1_fn_shape_labels_not_reserved] >>
  metis_tac[fresh_labels_exclude_used_dead]
QED

Theorem run_configured_fn_pass_fold_chain:
  !passes s fn label_map fn' label_map' s' s0 fn0.
    EVERY (o1_step_contract rpolicy) passes /\
    run_configured_fn_pass_fold execute_configured_fn_pass rpolicy passes
      unit s fn label_map = SOME (fn', label_map', s') /\
    o1_ctx_shape unit.cu_context /\
    MEM fn.fn_name (ctx_fn_names unit.cu_context) /\
    o1_fn_shape unit.cu_context fn /\ fn.fn_name = fn0.fn_name /\
    (!l. MEM l (fn_labels fn) ==>
         MEM l (fn_labels fn0) \/ ~MEM l s0.irs_used_labels) /\
    list_subset s0.irs_used_labels s.irs_used_labels
    ==>
    ?fs obs new.
      fn_chain rpolicy passes s fs obs /\ HD fs = fn /\ LAST fs = fn' /\
      label_map' = label_map ++ new /\
      (!k. k < LENGTH obs ==>
           EL k obs =
           unit_with_fns unit
             (replace_fn fn.fn_name (EL k fs) unit.cu_context.ctx_functions)) /\
      EVERY (o1_fn_shape unit.cu_context) fs /\
      label_map_dead s0 fn0 fn' new /\
      (!l. MEM l (fn_labels fn') ==>
           MEM l (fn_labels fn0) \/ ~MEM l s0.irs_used_labels)
Proof
  Induct
  >- (rpt gen_tac >> simp[run_configured_fn_pass_fold_def] >>
      strip_tac >> gvs[] >> qexistsl_tac [`[fn]`,`[]`] >>
      simp[fn_chain_def, label_map_dead_def]) >>
  rpt gen_tac >> pure_rewrite_tac[EVERY_DEF] >> strip_tac >>
  drule run_configured_fn_pass_fold_cons_step >> strip_tac >>
  drule_all observed_step_contract >> strip_tac >>
  `out.fpo_function.fn_name = fn.fn_name /\
   list_subset s.irs_used_labels out.fpo_supply.irs_used_labels`
    by fs[fn_pass_step_def, ir_supply_extends_def] >>
  `!l. MEM l (fn_labels out.fpo_function) ==>
       MEM l (fn_labels fn0) \/ ~MEM l s0.irs_used_labels`
    by (qpat_x_assum `!l. MEM l (fn_labels fn) ==> _` mp_tac >>
        qpat_x_assum `list_subset s0.irs_used_labels s.irs_used_labels` mp_tac >>
        qpat_x_assum `fresh_names_ok s fn out.fpo_function` mp_tac >>
        rpt (pop_assum kall_tac) >>
        simp[fresh_names_ok_def, list_subset_def, EVERY_MEM] >> metis_tac[]) >>
  `list_subset s0.irs_used_labels out.fpo_supply.irs_used_labels`
    by (irule list_subset_trans >> goal_assum (drule_at Any) >> simp[]) >>
  `MEM out.fpo_function.fn_name (ctx_fn_names unit.cu_context)` by metis_tac[] >>
  `out.fpo_function.fn_name = fn0.fn_name` by metis_tac[] >>
  first_x_assum drule_all >> strip_tac >>
  drule_all contracted_fold_invariant >> strip_tac >>
  `label_map_dead s0 fn0 fn' out.fpo_label_map`
    by (drule_all step_map_dead_after_fold >> simp[]) >>
  `fs <> []` by (drule fn_chain_length >> strip_tac >> Cases_on `fs` >> fs[]) >>
  Cases_on `fs` >- fs[] >>
  rename1 `fn_chain rpolicy passes out.fpo_supply (next::rest) obs` >>
  gvs[] >>
  qexistsl_tac [`fn::out.fpo_function::rest`,
    `(unit_with_fns unit (replace_fn fn0.fn_name fn unit.cu_context.ctx_functions))::obs`] >>
  simp[LAST_DEF, APPEND_ASSOC, label_map_dead_def, unit_with_fns_def, replace_fn_def] >>
  conj_tac
  >- (simp[fn_chain_def] >> metis_tac[]) >>
  reverse conj_tac
  >- fs[label_map_dead_def, LAST_DEF] >>
  Cases >> simp[] >> fs[unit_with_fns_def, replace_fn_def]
QED

(* No label operand of the candidate unit is a dead source. *)
Theorem label_map_dead_no_refs:
  o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\
  ir_supply_covers_unit s0 unit /\
  lookup_unique_function fn0.fn_name unit.cu_context.ctx_functions = SOME fn0 /\
  o1_fn_shape unit.cu_context fn' /\ fn'.fn_name = fn0.fn_name /\
  label_map_dead s0 fn0 fn' label_map /\
  MEM g (replace_fn fn0.fn_name fn' unit.cu_context.ctx_functions) /\
  MEM inst (fn_insts g) /\ MEM (Label l) inst.inst_operands ==>
  ~MEM l (MAP FST label_map)
Proof
  rewrite_tac[label_map_dead_def, replace_fn_def] >>
  MATCH_ACCEPT_TAC dead_sources_replacement_no_refs
QED

Theorem run_configured_fn_passes_decomp:
  EVERY (o1_step_contract rpolicy) passes /\
  run_configured_fn_passes execute_configured_fn_pass rpolicy passes name
    unit s = SOME (unit', s') /\
  o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) ==>
  ?fn fs obs.
    lookup_unique_function name unit.cu_context.ctx_functions = SOME fn /\
    fn_chain rpolicy passes s fs obs /\ HD fs = fn /\
    (!k. k < LENGTH obs ==>
         EL k obs =
         unit_with_fns unit
           (replace_fn name (EL k fs) unit.cu_context.ctx_functions)) /\
    EVERY (o1_fn_shape unit.cu_context) fs /\
    unit'.cu_context =
      unit.cu_context with ctx_functions :=
        replace_fn name (LAST fs) unit.cu_context.ctx_functions /\
    unit_labels_wf unit'
Proof
  strip_tac >> drule run_configured_fn_passes_success >> strip_tac >>
  drule lookup_unique_function_member >> strip_tac >>
  `o1_fn_shape unit.cu_context fn` by fs[o1_ctx_shape_def, EVERY_MEM] >>
  `MEM fn.fn_name (ctx_fn_names unit.cu_context)`
    by (simp[ctx_fn_names_def, MEM_MAP] >> metis_tac[]) >>
  drule_at (Pat `run_configured_fn_pass_fold _ _ _ _ _ _ _ = _`)
    run_configured_fn_pass_fold_chain >>
  disch_then (qspecl_then [`s`,`fn`] mp_tac) >>
  simp[list_subset_def, EVERY_MEM] >> strip_tac >>
  drule replace_unique_function_MAP >> strip_tac >>
  `o1_fn_shape unit.cu_context fn'`
    by (drule fn_chain_length >> strip_tac >>
        `fs <> []` by (Cases_on `fs` >> fs[]) >>
        metis_tac[MEM_LAST_NOT_NIL]) >>
  `!g inst l. MEM g (replace_fn fn.fn_name fn' unit.cu_context.ctx_functions) /\
      MEM inst (fn_insts g) /\ MEM (Label l) inst.inst_operands ==>
      ~MEM l (MAP FST labels)`
    by (rpt gen_tac >> strip_tac >>
        `lookup_unique_function fn.fn_name unit.cu_context.ctx_functions = SOME fn`
          by simp[] >>
        `fn'.fn_name = fn.fn_name` by metis_tac[] >>
        drule_all label_map_dead_no_refs >> simp[]) >>
  `unit'.cu_context = unit.cu_context with ctx_functions :=
      replace_fn name fn' unit.cu_context.ctx_functions`
    by (drule apply_unit_label_map_context >>
        simp[replace_fn_def] >> metis_tac[replace_fn_def]) >>
  qexistsl_tac [`fs`,`obs`] >> simp[]
QED

