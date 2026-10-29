Theory fmpAliasProps
Ancestors
  fmpAliasDefs dfHelperProps arithmetic list finite_map

Theorem fmp_capture_step_preserves:
  !insts vars v. MEM v vars ==> MEM v (fmp_capture_step insts vars)
Proof
  Induct >> simp[fmp_capture_step_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >>
  simp[] >> IF_CASES_TAC >> simp[list_union_mem]
QED

Theorem fmp_capture_rounds_preserve:
  !n insts vars v. MEM v vars ==>
    MEM v (FUNPOW (fmp_capture_step insts) n vars)
Proof
  Induct >> simp[FUNPOW_SUC] >> metis_tac[fmp_capture_step_preserves]
QED

Theorem fmp_capture_closure_root:
  fmp_capture_closure insts root = SOME vars ==> MEM root vars
Proof
  simp[fmp_capture_closure_def] >>
  strip_tac >> gvs[] >>
  irule fmp_capture_rounds_preserve >> simp[]
QED

Theorem fmp_capture_closure_closed:
  fmp_capture_closure insts root = SOME vars ==>
  fmp_capture_closed insts vars
Proof
  simp[fmp_capture_closure_def] >> strip_tac >> gvs[]
QED

Theorem fmp_capture_closure_propagates:
  fmp_capture_closure insts root = SOME vars /\ MEM inst insts /\
  fmp_transparent_opcode inst.inst_opcode /\
  LENGTH inst.inst_outputs = 1 /\ fmp_inst_uses_any vars inst /\
  MEM out inst.inst_outputs ==> MEM out vars
Proof
  strip_tac >> drule fmp_capture_closure_closed >>
  simp[fmp_capture_closed_def, EVERY_MEM] >> metis_tac[]
QED

Theorem fmp_live_capture_veto:
  fmp_capture_closure insts root = SOME vars /\
  MEM v vars /\ MEM v live ==> fmp_capture_query_veto insts live root
Proof
  simp[fmp_capture_query_veto_def, EXISTS_MEM] >> metis_tac[]
QED

Theorem fmp_unknown_capture_veto:
  fmp_capture_closure insts root = NONE ==>
  fmp_capture_query_veto insts live root
Proof
  simp[fmp_capture_query_veto_def]
QED

Theorem fmp_escaping_occurrence:
  MEM v (fmp_escaping_operands inst) <=>
  ~fmp_pointer_propagation inst.inst_opcode /\ MEM v (inst_uses inst) /\
  LENGTH (FILTER ($= (Var v)) (fmp_safe_operands inst)) <
  LENGTH (FILTER ($= v) (inst_uses inst))
Proof
  simp[fmp_escaping_operands_def] >> IF_CASES_TAC >> simp[MEM_FILTER] >> metis_tac[]
QED

Theorem fmp_bases_accumulate:
  MEM id (fmp_bases (fmp_accumulate_bases env out ids) v) <=>
  MEM id (fmp_bases env v) \/ (v = out /\ MEM id ids)
Proof
  Cases_on `v = out` >>
  simp[fmp_accumulate_bases_def, fmp_bases_def, FLOOKUP_UPDATE,
       list_union_mem] >> metis_tac[]
QED

Theorem fmp_base_transfer_preserves:
  MEM id (fmp_bases env v) ==>
  MEM id (fmp_bases (fmp_base_transfer inst env) v)
Proof
  simp[fmp_base_transfer_def] >>
  Cases_on `fmp_base_output inst` >> simp[fmp_bases_accumulate]
QED

Theorem fmp_base_sweep_preserves:
  !insts env v id. MEM id (fmp_bases env v) ==>
  MEM id (fmp_bases (fmp_base_sweep insts env) v)
Proof
  Induct >> simp[fmp_base_sweep_def] >>
  metis_tac[fmp_base_transfer_preserves]
QED

Theorem fmp_base_analyze_closed:
  fmp_base_analyze insts = SOME env ==> fmp_base_closed insts env
Proof
  simp[fmp_base_analyze_def] >> strip_tac >> gvs[]
QED

Theorem fmp_base_analyze_stable:
  fmp_base_analyze insts = SOME env ==>
  fmp_base_env_eq insts (fmp_base_sweep insts env) env
Proof
  simp[fmp_base_analyze_def] >> strip_tac >> gvs[]
QED

Theorem fmp_base_analyze_unique_sites:
  fmp_base_analyze insts = SOME env ==>
  ALL_DISTINCT (MAP (\inst. inst.inst_id) insts)
Proof
  simp[fmp_base_analyze_def] >> strip_tac >> gvs[]
QED

Theorem fmp_base_env_eq_membership:
  fmp_base_env_eq insts env1 env2 /\
  MEM v (FLAT (MAP (\inst. inst.inst_outputs) insts)) ==>
  (MEM id (fmp_bases env1 v) <=> MEM id (fmp_bases env2 v))
Proof
  simp[fmp_base_env_eq_def, EVERY_MEM] >> metis_tac[]
QED

Theorem fmp_base_analyze_propagates:
  fmp_base_analyze insts = SOME env /\ MEM inst insts /\
  fmp_base_output inst = SOME out /\
  MEM id (fmp_generated_bases env inst) ==> MEM id (fmp_bases env out)
Proof
  strip_tac >> drule fmp_base_analyze_closed >>
  simp[fmp_base_closed_def, EVERY_MEM] >>
  disch_then (qspec_then `inst` mp_tac) >> simp[]
QED

Theorem fmp_dalloca_query_exact:
  fmp_dalloca_query insts env v = SOME id <=>
  fmp_bases env v = [id] /\
  EXISTS (\inst. inst.inst_id = id /\ inst.inst_opcode = DALLOCA) insts
Proof
  Cases_on `fmp_bases env v` >> simp[fmp_dalloca_query_def] >>
  Cases_on `t` >> simp[] >> metis_tac[]
QED

Theorem fmp_allocation_live_variable:
  MEM v live /\ MEM id (fmp_bases env v) ==>
  fmp_allocation_live env insts live id
Proof
  simp[fmp_allocation_live_def, EXISTS_MEM] >> metis_tac[]
QED

Theorem fmp_allocation_live_escape:
  MEM inst insts /\ MEM v (fmp_escaping_operands inst) /\
  MEM id (fmp_bases env v) ==> fmp_allocation_live env insts live id
Proof
  simp[fmp_allocation_live_def, EXISTS_MEM] >> metis_tac[]
QED

val _ = List.app (fn (name,th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th))) then ()
  else raise Fail ("unexpected oracle dependency in " ^ name))
  (DB.thms "fmpAliasProps");
