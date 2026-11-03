(*
 * Helpers for o1FnScheduleDecomp: replacing one function in a context
 * (the *_MAP_replace lemmas), what o1_fn_shape says about a function's
 * labels and names, and why a step's label-map sources stay dead
 * (dead_source_*, fresh_labels_*, contracted_fold_invariant).
 *)
Theory o1FnScheduleDecompHelpers
Ancestors
  o1PassContract unitLabelMapIdentity venomFnScheduleRunner
  venomFnScheduleRunnerProps venomPassDispatcher venomInst irSupply
  venomCompilerWf venomWf unitShapeDefs list rich_list

Theorem MAP_replace_fn_names:
  g.fn_name = name ==>
  MAP (\f. f.fn_name) (MAP (\f. if f.fn_name = name then g else f) fns) =
  MAP (\f. f.fn_name) fns
Proof
  strip_tac >> simp[MAP_MAP_o, combinTheory.o_DEF] >>
  irule MAP_CONG >> simp[] >> rw[]
QED

Theorem MEM_MAP_replace_fn:
  MEM f (MAP (\f. if f.fn_name = name then g else f) fns) ==>
  f = g \/ (MEM f fns /\ f.fn_name <> name)
Proof
  simp[MEM_MAP, PULL_EXISTS] >> qx_gen_tac `f0` >> rpt strip_tac >>
  Cases_on `f0.fn_name = name` >> gvs[]
QED

Theorem ctx_fn_names_MAP_replace:
  g.fn_name = name ==>
  ctx_fn_names (ctx with ctx_functions :=
    MAP (\f. if f.fn_name = name then g else f) ctx.ctx_functions) =
  ctx_fn_names ctx
Proof
  simp[ctx_fn_names_def, MAP_replace_fn_names]
QED

Theorem ctx_wf_MAP_replace:
  ctx_wf ctx /\ g.fn_name = name ==>
  ctx_wf (ctx with ctx_functions :=
    MAP (\f. if f.fn_name = name then g else f) ctx.ctx_functions)
Proof
  simp[ctx_wf_def, ctx_distinct_fn_names_def, ctx_has_entry_def,
       ctx_fn_names_MAP_replace]
QED

Theorem o1_ctx_shape_MAP_replace:
  o1_ctx_shape ctx /\ o1_fn_shape ctx g /\ g.fn_name = name ==>
  o1_ctx_shape (ctx with ctx_functions :=
    MAP (\f. if f.fn_name = name then g else f) ctx.ctx_functions)
Proof
  strip_tac >>
  `ctx_fn_names (ctx with ctx_functions :=
     MAP (\f. if f.fn_name = name then g else f) ctx.ctx_functions) =
   ctx_fn_names ctx` by simp[ctx_fn_names_MAP_replace] >>
  fs[o1_ctx_shape_def] >> conj_tac
  >- simp[ctx_wf_MAP_replace] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  drule MEM_MAP_replace_fn >> strip_tac >> gvs[] >>
  fs[EVERY_MEM, o1_fn_shape_def] >> metis_tac[]
QED

Theorem replace_unique_function_MAP:
  replace_unique_function name g fns = SOME fns' ==>
  g.fn_name = name /\
  fns' = MAP (\f. if f.fn_name = name then g else f) fns
Proof
  simp[replace_unique_function_def, AllCaseEqs()] >>
  Cases_on `g.fn_name = name` >> simp[] >>
  Cases_on `FILTER (\f. f.fn_name = name) fns` >> simp[] >>
  rename1 `_ :: tail` >> Cases_on `tail` >> simp[]
QED

Theorem unit_with_current_fn_MAP:
  unit_with_current_fn unit fn = SOME observed ==>
  observed = unit with cu_context := unit.cu_context with ctx_functions :=
    MAP (\f. if f.fn_name = fn.fn_name then fn else f)
      unit.cu_context.ctx_functions
Proof
  simp[unit_with_current_fn_def, AllCaseEqs()] >> strip_tac >>
  drule replace_unique_function_MAP >> strip_tac >> gvs[]
QED

(* A supply that covers a unit and a function covers the unit with that
   function put in. *)
Theorem covers_unit_replace:
  ir_supply_covers_unit s
    (unit with cu_context := unit.cu_context with ctx_functions :=
       MAP (\f. if f.fn_name = name then g else f) fns) /\
  ir_supply_covers_fn s g' /\ g'.fn_name = name ==>
  ir_supply_covers_unit s
    (unit with cu_context := unit.cu_context with ctx_functions :=
       MAP (\f. if f.fn_name = name then g' else f) fns)
Proof
  simp[ir_supply_covers_unit_def, ir_supply_covers_fn_def, list_subset_def,
       EVERY_MEM, unit_ir_inst_ids_def, unit_ir_vars_def, unit_ir_labels_def,
       MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> gvs[COND_RAND, COND_EXPAND_OR] >> metis_tac[]
QED

Theorem run_configured_fn_pass_fold_cons_step:
  run_configured_fn_pass_fold execute_configured_fn_pass rpolicy
    (pass::passes) unit s fn labels = SOME result /\
  ir_supply_covers_unit s
    (unit with cu_context := unit.cu_context with ctx_functions :=
       MAP (\f. if f.fn_name = fn.fn_name then fn else f)
         unit.cu_context.ctx_functions) ==>
  ?observed out.
    fn_pass_step rpolicy pass observed s fn out /\
    observed = (unit with cu_context := unit.cu_context with ctx_functions :=
      MAP (\f. if f.fn_name = fn.fn_name then fn else f)
        unit.cu_context.ctx_functions) /\
    ir_supply_covers_unit out.fpo_supply
      (unit with cu_context := unit.cu_context with ctx_functions :=
         MAP (\f. if f.fn_name = fn.fn_name then out.fpo_function else f)
           unit.cu_context.ctx_functions) /\
    run_configured_fn_pass_fold execute_configured_fn_pass rpolicy passes
      unit out.fpo_supply out.fpo_function (labels ++ out.fpo_label_map) =
      SOME result
Proof
  simp[run_configured_fn_pass_fold_def, AllCaseEqs()] >> rpt strip_tac >>
  drule unit_with_current_fn_lookup >> strip_tac >>
  drule unit_with_current_fn_MAP >> strip_tac >>
  qexists_tac `out` >> gvs[fn_pass_step_def] >>
  irule covers_unit_replace >> simp[] >>
  qexists_tac `fn` >> simp[]
QED

Theorem run_configured_fn_passes_success:
  run_configured_fn_passes runner rpolicy passes name unit s = SOME (unit',s') ==>
  ir_supply_covers_unit s unit /\ unit_labels_wf unit' /\
  ?fn fn' labels fns.
    lookup_unique_function name unit.cu_context.ctx_functions = SOME fn /\
    run_configured_fn_pass_fold runner rpolicy passes unit s fn [] =
      SOME (fn',labels,s') /\
    replace_unique_function name fn' unit.cu_context.ctx_functions = SOME fns /\
    apply_unit_label_map labels
      (unit with cu_context := unit.cu_context with ctx_functions := fns) =
      SOME unit'
Proof
  simp[run_configured_fn_passes_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem o1_fn_shape_name_label:
  o1_fn_shape ctx f ==> MEM f.fn_name (fn_labels f)
Proof
  simp[o1_fn_shape_def, fn_shape_ok_def, fn_entry_label_def, entry_block_def] >>
  Cases_on `f.fn_blocks` >> simp[fn_labels_def]
QED

Theorem o1_fn_shape_labels_not_reserved:
  o1_fn_shape ctx f /\ MEM l (fn_labels f) ==> ~reserved_label l
Proof
  simp[o1_fn_shape_def, fn_shape_ok_def, fn_labels_def, EVERY_MEM, MEM_MAP] >>
  metis_tac[]
QED

Theorem invoke_label_operand_target:
  label_positions_ok inst /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label target :: args /\ MEM (Label l) inst.inst_operands ==>
  l = target
Proof
  strip_tac >> gvs[label_positions_ok_def, EVERY_MEM,
                    stackPlanTypesTheory.is_label_operand_def] >>
  metis_tac[stackPlanTypesTheory.is_label_operand_def]
QED

Theorem o1_fn_shape_label_operand:
  o1_fn_shape ctx f /\ MEM inst (fn_insts f) /\
  MEM (Label l) inst.inst_operands ==>
  MEM l (fn_labels f) \/ reserved_label l \/ MEM l (ctx_fn_names ctx)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (fs[o1_fn_shape_def, fn_invoke_ok_def, fn_shape_ok_def, EVERY_MEM] >>
      first_x_assum drule >> simp[] >> strip_tac >>
      `label_positions_ok inst` by metis_tac[inst_shape_ok_def] >>
      drule_all invoke_label_operand_target >> strip_tac >> gvs[]) >>
  fs[o1_fn_shape_def, fn_label_refs_ok_def] >> metis_tac[]
QED

Theorem distinct_flat_map_members_disjoint:
  !xs a b l.
    ALL_DISTINCT (FLAT (MAP labels xs)) /\ MEM a xs /\ MEM b xs /\ a <> b /\
    MEM l (labels a) ==> ~MEM l (labels b)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >> gvs[ALL_DISTINCT_APPEND] >>
  metis_tac[MEM_FLAT, MEM_MAP]
QED

Theorem unit_distinct_function_labels:
  ALL_DISTINCT (unit_label_namespace unit) /\
  MEM f unit.cu_context.ctx_functions /\ MEM g unit.cu_context.ctx_functions /\
  f <> g /\ MEM l (fn_labels f) ==> ~MEM l (fn_labels g)
Proof
  simp[unit_label_namespace_def] >>
  metis_tac[distinct_flat_map_members_disjoint]
QED

Theorem unit_supply_member_label:
  ir_supply_covers_unit s unit /\ MEM f unit.cu_context.ctx_functions /\
  MEM l (fn_labels f) ==> MEM l s.irs_used_labels
Proof
  simp[ir_supply_covers_unit_def, list_subset_def, EVERY_MEM,
       fn_labels_def, MEM_MAP] >> metis_tac[unit_ir_labels_block]
QED

Theorem dead_source_other_function:
  o1_ctx_shape unit.cu_context /\ ALL_DISTINCT (unit_label_namespace unit) /\
  ir_supply_covers_unit s unit /\
  MEM f unit.cu_context.ctx_functions /\ MEM g unit.cu_context.ctx_functions /\
  l <> f.fn_name /\ (MEM l (fn_labels f) \/ ~MEM l s.irs_used_labels) /\
  g.fn_name <> f.fn_name ==> ~MEM l (fn_labels g)
Proof
  strip_tac >> `f <> g` by metis_tac[] >>
  metis_tac[unit_distinct_function_labels, unit_supply_member_label]
QED

Theorem dead_source_not_function_name:
  o1_ctx_shape unit.cu_context /\ ALL_DISTINCT (unit_label_namespace unit) /\
  ir_supply_covers_unit s unit /\
  MEM f unit.cu_context.ctx_functions /\ l <> f.fn_name /\
  (MEM l (fn_labels f) \/ ~MEM l s.irs_used_labels) ==>
  ~MEM l (ctx_fn_names unit.cu_context)
Proof
  strip_tac >> simp[ctx_fn_names_def, MEM_MAP] >> qx_gen_tac `g` >>
  rpt strip_tac >> gvs[] >>
  `o1_fn_shape unit.cu_context g` by fs[o1_ctx_shape_def, EVERY_MEM] >>
  drule o1_fn_shape_name_label >> strip_tac >>
  metis_tac[dead_source_other_function]
QED

Theorem dead_sources_replacement_no_refs:
  o1_ctx_shape unit.cu_context /\ ALL_DISTINCT (unit_label_namespace unit) /\
  ir_supply_covers_unit s0 unit /\
  lookup_unique_function fn0.fn_name unit.cu_context.ctx_functions = SOME fn0 /\
  o1_fn_shape unit.cu_context fn' /\ fn'.fn_name = fn0.fn_name /\
  EVERY (\e. (MEM (FST e) (fn_labels fn0) \/
                ~MEM (FST e) s0.irs_used_labels) /\
               FST e <> fn0.fn_name /\ ~reserved_label (FST e) /\
               ~MEM (FST e) (fn_labels fn')) label_map /\
  MEM g (MAP (\f. if f.fn_name = fn0.fn_name then fn' else f)
    unit.cu_context.ctx_functions) /\
  MEM inst (fn_insts g) /\ MEM (Label l) inst.inst_operands ==>
  ~MEM l (MAP FST label_map)
Proof
  strip_tac >> drule lookup_unique_function_member >> strip_tac >>
  spose_not_then assume_tac >>
  qpat_x_assum `MEM l (MAP FST label_map)` mp_tac >>
  pure_rewrite_tac[MEM_MAP] >> strip_tac >>
  rename1 `MEM e label_map` >>
  qpat_x_assum `EVERY _ label_map`
    (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then (qspec_then `e` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~MEM l (ctx_fn_names unit.cu_context)`
    by metis_tac[dead_source_not_function_name] >>
  drule MEM_MAP_replace_fn >> strip_tac
  >- (gvs[] >> metis_tac[o1_fn_shape_label_operand]) >>
  `o1_fn_shape unit.cu_context g`
    by (fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `~MEM l (fn_labels g)` by metis_tac[dead_source_other_function] >>
  metis_tac[o1_fn_shape_label_operand]
QED

Theorem fresh_labels_exclude_used_dead:
  (!l. MEM l (fn_labels after) ==>
       MEM l (fn_labels before) \/ ~MEM l s.irs_used_labels) /\
  ~MEM l (fn_labels before) /\ MEM l s.irs_used_labels ==>
  ~MEM l (fn_labels after)
Proof
  metis_tac[]
QED

Theorem observed_step_contract:
  o1_step_contract rpolicy pass /\
  fn_pass_step rpolicy pass observed s fn out /\
  observed = (unit with cu_context := unit.cu_context with ctx_functions :=
    MAP (\f. if f.fn_name = fn.fn_name then fn else f)
      unit.cu_context.ctx_functions) /\
  o1_ctx_shape unit.cu_context /\ o1_fn_shape unit.cu_context fn /\
  ir_supply_inst_ok s ==>
  o1_fn_shape unit.cu_context out.fpo_function /\
  fresh_names_ok s fn out.fpo_function /\
  label_map_sources_ok fn out.fpo_function out.fpo_label_map /\
  ir_supply_inst_ok out.fpo_supply
Proof
  strip_tac >>
  `o1_ctx_shape observed.cu_context`
    by (gvs[] >> irule o1_ctx_shape_MAP_replace >> simp[]) >>
  `ctx_fn_names observed.cu_context = ctx_fn_names unit.cu_context`
    by gvs[ctx_fn_names_MAP_replace] >>
  `o1_fn_shape observed.cu_context out.fpo_function /\
   fresh_names_ok s fn out.fpo_function /\
   label_map_sources_ok fn out.fpo_function out.fpo_label_map /\
   ir_supply_inst_ok out.fpo_supply`
    by metis_tac[o1_step_contract_def] >>
  gvs[o1_fn_shape_def]
QED

Theorem observed_step_contract_at:
  o1_step_contract_at k rpolicy pass /\
  fn_pass_step rpolicy pass observed s fn out /\
  observed = (unit with cu_context := unit.cu_context with ctx_functions :=
    MAP (\f. if f.fn_name = fn.fn_name then fn else f)
      unit.cu_context.ctx_functions) /\
  o1_ctx_shape unit.cu_context /\ o1_fn_shape unit.cu_context fn /\
  ir_supply_inst_ok s /\ o1_fn_row k fn ==>
  o1_fn_shape unit.cu_context out.fpo_function /\
  fresh_names_ok s fn out.fpo_function /\
  label_map_sources_ok fn out.fpo_function out.fpo_label_map /\
  ir_supply_inst_ok out.fpo_supply /\
  o1_fn_row (SUC k) out.fpo_function
Proof
  strip_tac >>
  `o1_ctx_shape observed.cu_context`
    by (gvs[] >> irule o1_ctx_shape_MAP_replace >> simp[]) >>
  `ctx_fn_names observed.cu_context = ctx_fn_names unit.cu_context`
    by gvs[ctx_fn_names_MAP_replace] >>
  `o1_fn_shape observed.cu_context out.fpo_function /\
   fresh_names_ok s fn out.fpo_function /\
   label_map_sources_ok fn out.fpo_function out.fpo_label_map /\
   ir_supply_inst_ok out.fpo_supply /\ o1_fn_row (SUC k) out.fpo_function`
    by metis_tac[o1_step_contract_at_def] >>
  gvs[o1_fn_shape_def]
QED

Theorem contracted_fold_invariant:
  !passes k s fn labels fn' labels' s' name.
    o1_step_contracts_from rpolicy k passes /\ o1_fn_row k fn /\
    run_configured_fn_pass_fold execute_configured_fn_pass rpolicy passes
      unit s fn labels = SOME (fn',labels',s') /\
    o1_ctx_shape unit.cu_context /\ o1_fn_shape unit.cu_context fn /\
    fn.fn_name = name /\
    ir_supply_covers_unit s
      (unit with cu_context := unit.cu_context with ctx_functions :=
         MAP (\f. if f.fn_name = name then fn else f)
           unit.cu_context.ctx_functions) /\
    ir_supply_inst_ok s ==>
    fn'.fn_name = fn.fn_name /\ o1_fn_shape unit.cu_context fn' /\
    ir_supply_inst_ok s' /\ o1_fn_row (k + LENGTH passes) fn' /\
    list_subset s.irs_used_labels s'.irs_used_labels /\
    (!l. MEM l (fn_labels fn') ==>
         MEM l (fn_labels fn) \/ ~MEM l s.irs_used_labels)
Proof
  Induct
  >- simp[run_configured_fn_pass_fold_def, list_subset_def, EVERY_MEM] >>
  rpt gen_tac >> pure_rewrite_tac[o1_step_contracts_from_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  drule_all run_configured_fn_pass_fold_cons_step >> strip_tac >>
  drule_all observed_step_contract_at >> strip_tac >>
  `out.fpo_function.fn_name = fn.fn_name` by fs[fn_pass_step_def] >>
  `ir_supply_covers_unit out.fpo_supply
     (unit with cu_context := unit.cu_context with ctx_functions :=
        MAP (\f. if f.fn_name = out.fpo_function.fn_name then out.fpo_function
                 else f) unit.cu_context.ctx_functions)` by
    (qpat_x_assum `out.fpo_function.fn_name = fn.fn_name`
       (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  first_x_assum drule_all >> strip_tac >>
  fs[fn_pass_step_def, ir_supply_extends_def, fresh_names_ok_def] >>
  conj_tac >- (`k + SUC (LENGTH passes) = LENGTH passes + SUC k` by simp[] >>
               asm_rewrite_tac[]) >>
  conj_tac
  >- (irule list_subset_trans >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `!l. MEM l (fn_labels out.fpo_function) ==> _` mp_tac >>
  qpat_x_assum `!l. MEM l (fn_labels fn') ==> _` mp_tac >>
  qpat_x_assum `list_subset s.irs_used_labels out.fpo_supply.irs_used_labels` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[list_subset_def, EVERY_MEM] >> metis_tac[]
QED
