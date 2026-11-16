Theory o1SymStaticSchedule
Ancestors
  o1ScheduleDecomp o1FnScheduleDecomp o1FnScheduleDecompHelpers
  o1PartialSchedule o1PassContract venomInst unitShapeDefs list rich_list
  venomFnScheduleRunnerProps venomPipelineRunner venomWf

(* Carry a backwards predicate through the existing row contracts.  The
   fixed proposition B records provenance in the initial context. *)
Theorem rows_step_contract_reflect:
  rows_step_contract R k rp pass /\
  (!observed s fn out.
    fn_pass_step rp pass observed s fn out /\
    o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
    EVERY (\g. ?j. R j g) observed.cu_context.ctx_functions /\ R k fn ==>
    (P out.fpo_function ==> P fn)) ==>
  rows_step_contract (\j fn. R j fn /\ (P fn ==> B)) k rp pass
Proof
  strip_tac >> simp[rows_step_contract_def] >> rpt gen_tac >> strip_tac >>
  `EVERY (\g. ?j. R j g) observed.cu_context.ctx_functions` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `rows_step_contract _ _ _ _`
    (mp_tac o REWRITE_RULE [rows_step_contract_def]) >>
  disch_then drule_all >> strip_tac >> simp[] >> metis_tac[]
QED

Theorem rows_step_contracts_reflect:
  !passes k.
  rows_step_contracts_from R rp k passes /\
  (!pass observed s fn out j.
    MEM pass passes /\ fn_pass_step rp pass observed s fn out /\
    o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
    EVERY (\g. ?i. R i g) observed.cu_context.ctx_functions /\ R j fn ==>
    (P out.fpo_function ==> P fn)) ==>
  rows_step_contracts_from (\j fn. R j fn /\ (P fn ==> B)) rp k passes
Proof
  Induct >> simp[rows_step_contracts_from_def] >> rpt strip_tac
  >- (irule rows_step_contract_reflect >> simp[] >> metis_tac[]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem run_named_fn_schedules_rows:
  rows_step_contracts_from R rp 0 passes /\
  EVERY (R 0) unit.cu_context.ctx_functions /\
  run_named_fn_schedules execute_configured_fn_pass rp passes names unit s =
    SOME (unit',s') /\
  o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\ ALL_DISTINCT names /\
  (!n. MEM n names <=> MEM n (ctx_fn_names unit.cu_context)) /\
  ir_supply_inst_ok s ==>
  EVERY (R (LENGTH passes)) unit'.cu_context.ctx_functions
Proof
  strip_tac >> drule_all run_named_fn_schedules_decomp >> strip_tac >>
  gvs[] >> irule stage_ctx_rows >> simp[] >>
  qexistsl_tac [`names`,`passes`,`rp`] >> simp[]
QED

Theorem run_named_fn_schedules_reflect:
  rows_step_contracts_from R rp 0 passes /\
  EVERY (R 0) unit.cu_context.ctx_functions /\
  (!pass observed s fn out j.
    MEM pass passes /\ fn_pass_step rp pass observed s fn out /\
    o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
    EVERY (\g. ?i. R i g) observed.cu_context.ctx_functions /\ R j fn ==>
    (P out.fpo_function ==> P fn)) /\
  run_named_fn_schedules execute_configured_fn_pass rp passes names unit s =
    SOME (unit',s') /\
  o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\ ALL_DISTINCT names /\
  (!n. MEM n names <=> MEM n (ctx_fn_names unit.cu_context)) /\
  ir_supply_inst_ok s ==>
  ((?fn. MEM fn unit'.cu_context.ctx_functions /\ P fn) ==>
   (?fn. MEM fn unit.cu_context.ctx_functions /\ P fn))
Proof
  strip_tac >>
  `rows_step_contracts_from
     (\j fn. R j fn /\ (P fn ==> ?g. MEM g unit.cu_context.ctx_functions /\ P g))
     rp 0 passes` by (irule rows_step_contracts_reflect >> metis_tac[]) >>
  `EVERY (\fn. R 0 fn /\
      (P fn ==> ?g. MEM g unit.cu_context.ctx_functions /\ P g))
     unit.cu_context.ctx_functions` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `rows_step_contracts_from R _ _ _` kall_tac >>
  mp_tac (Q.INST
    [`R` |-> `\j fn. R j fn /\ (P fn ==> ?g. MEM g unit.cu_context.ctx_functions /\ P g)`]
    run_named_fn_schedules_rows) >>
  simp[] >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem run_configured_fn_passes_reflect:
  rows_step_contracts_from R rp 0 passes /\
  EVERY (\g. ?j. R j g) unit.cu_context.ctx_functions /\
  (!fn. lookup_unique_function name unit.cu_context.ctx_functions = SOME fn ==>
        R 0 fn) /\
  (!pass observed s fn out j.
    MEM pass passes /\ fn_pass_step rp pass observed s fn out /\
    o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
    EVERY (\g. ?i. R i g) observed.cu_context.ctx_functions /\ R j fn ==>
    (P out.fpo_function ==> P fn)) /\
  run_configured_fn_passes execute_configured_fn_pass rp passes name unit s =
    SOME (unit',s') /\
  o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\ ir_supply_inst_ok s ==>
  ((?fn. MEM fn unit'.cu_context.ctx_functions /\ P fn) ==>
   (?fn. MEM fn unit.cu_context.ctx_functions /\ P fn))
Proof
  strip_tac >>
  `rows_step_contracts_from
     (\j fn. R j fn /\ (P fn ==> ?g. MEM g unit.cu_context.ctx_functions /\ P g))
     rp 0 passes` by (irule rows_step_contracts_reflect >> metis_tac[]) >>
  mp_tac (Q.INST
    [`R` |-> `\j fn. R j fn /\ (P fn ==> ?g. MEM g unit.cu_context.ctx_functions /\ P g)`]
    (Q.INST [`rpolicy` |-> `rp`] run_configured_fn_passes_decomp)) >>
  simp[] >> (impl_tac >-
    (conj_tac >- (gvs[EVERY_MEM] >> metis_tac[]) >>
     rpt strip_tac >> drule lookup_unique_function_member >> metis_tac[])) >>
  strip_tac >>
  `LENGTH fs = SUC (LENGTH passes)` by metis_tac[fn_chain_length] >>
  `fs <> []` by (Cases_on `fs` >> gvs[]) >>
  `P (LAST fs) ==> ?g. MEM g unit.cu_context.ctx_functions /\ P g` by
    (simp[LAST_EL] >> first_x_assum (qspec_then `LENGTH passes` mp_tac) >> simp[]) >>
  gvs[replace_fn_def] >> rpt strip_tac >>
  drule MEM_MAP_replace_fn >> metis_tac[]
QED

Theorem run_mapped_functions_reflect:
  o1_step_contract rp pass /\
  (!observed s fn out.
    fn_pass_step rp pass observed s fn out /\
    o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s ==>
    (P out.fpo_function ==> P fn)) /\
  run_mapped_functions rp pass unit s = SOME (unit',s') /\
  o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\ ir_supply_inst_ok s ==>
  ((?fn. MEM fn unit'.cu_context.ctx_functions /\ P fn) ==>
   (?fn. MEM fn unit.cu_context.ctx_functions /\ P fn))
Proof
  strip_tac >>
  `rows_step_contracts_from (\k fn. T) rp 0 [pass]` by
    metis_tac[o1_step_contract_rows_plain] >>
  mp_tac (Q.INST [`R` |-> `\k fn. T`, `passes` |-> `[pass]`,
    `names` |-> `ctx_fn_names unit.cu_context`] run_named_fn_schedules_reflect) >>
  simp[] >> (impl_tac >-
    (conj_tac >- metis_tac[] >>
     conj_tac >- gvs[run_mapped_functions_def] >>
     gvs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def])) >>
  simp[]
QED
