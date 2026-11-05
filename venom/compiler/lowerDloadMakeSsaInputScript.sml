(*
 * LowerDload keeps make_ssa_input_ok, function by function.
 *
 * The expansion keeps labels, terminators, CFG edges and every PHI where
 * it was; it only replaces each DLOAD/DLOADBYTES by a run of
 * instructions whose new variables come from the supply and are defined
 * before their uses in the same run.  Distinct instruction ids pin a use
 * to one position of its block, which def_on_all_paths needs: it asks
 * for a definition before some occurrence of the use; instruction
 * well-formedness keeps DLOADBYTES output-free, since the expansion
 * would drop its outputs.
 *
 * TOP-LEVEL:
 *   lower_dload_fn_pass_step_make_ssa_input_ok
 *)
Theory lowerDloadMakeSsaInput
Ancestors
  o1ContractLowerDload o1PassContract lowerDloadDefs venomPassDispatcher
  venomFnScheduleRunner irSupply venomWf cfgWf venomInst list

Theorem lower_dload_step_supply[local]:
  fn_pass_step rpolicy (CFP_Simple VP_LowerDload) observed s fn out ==>
  ir_supply_covers_fn s fn /\
  ?s'. lower_dload_function_supply s fn = (out.fpo_function,s')
Proof
  strip_tac >> gvs[fn_pass_step_def, AllCaseEqs()] >>
  `MEM fn observed.cu_context.ctx_functions` by
    (gvs[lookup_unique_function_def, AllCaseEqs()] >>
     `MEM fn (FILTER (\f. f.fn_name = fn.fn_name)
               observed.cu_context.ctx_functions)` by simp[] >>
     gvs[MEM_FILTER]) >>
  gvs[ir_supply_covers_unit_def, ir_supply_covers_fn_def,
      list_subset_def, unit_ir_inst_ids_def, unit_ir_vars_def,
      unit_ir_labels_def, EVERY_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem lower_dload_inst_supply_output_survives[local]:
  lower_dload_inst_supply s i = (xs,t) /\ inst_wf i /\
  MEM v i.inst_outputs ==> ?j. MEM j xs /\ MEM v j.inst_outputs
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      simp[RIGHT_AND_OVER_OR, EXISTS_OR_THM]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (rpt strip_tac >> gvs[inst_wf_def]) >>
  rpt strip_tac >> gvs[lower_dload_inst_supply_def]
QED

Theorem lower_dload_inst_supply_output_count[local]:
  lower_dload_inst_supply s i = (xs,t) /\ inst_wf i /\
  MEM v s.irs_used_vars ==>
  LENGTH (FILTER (\j. MEM v j.inst_outputs) xs) =
  if MEM v i.inst_outputs then 1 else 0
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> imp_res_tac (cj 1 fresh_ir_var_contract) >>
      imp_res_tac (cj 2 fresh_ir_var_contract) >>
      gvs[inst_wf_def] >> rpt IF_CASES_TAC >> gvs[] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> imp_res_tac (cj 1 fresh_ir_var_contract) >>
      imp_res_tac (cj 2 fresh_ir_var_contract) >>
      gvs[inst_wf_def] >> rpt IF_CASES_TAC >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >> gvs[lower_dload_inst_supply_def] >>
  Cases_on `MEM v i.inst_outputs` >> simp[]
QED

Theorem lower_dload_inst_supply_ordered_operand[local]:
  lower_dload_inst_supply s i = (xs,t) /\ xs = pre ++ j::post /\
  j.inst_opcode <> PHI /\ MEM (Var v) j.inst_operands ==>
  (?d. MEM d pre /\ MEM v d.inst_outputs) \/
  (i.inst_opcode <> PHI /\ MEM (Var v) i.inst_operands)
Proof
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >>
      gvs[] >> qpat_x_assum `_ = _ ++ _` (mp_tac o SYM) >>
      simp[APPEND_EQ_CONS] >> rpt strip_tac >>
      gvs[RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
      metis_tac[]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >>
      gvs[] >> qpat_x_assum `_ = _ ++ _` (mp_tac o SYM) >>
      simp[APPEND_EQ_CONS] >> rpt strip_tac >>
      gvs[RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
      metis_tac[]) >>
  rpt strip_tac >> gvs[lower_dload_inst_supply_def] >>
  qpat_x_assum `_ = _ ++ _` (mp_tac o SYM) >>
  simp[APPEND_EQ_CONS] >> rpt strip_tac >> gvs[]
QED

(* Intuition, per conjunct of make_ssa_input_ok:
   - all_reachable and the PHI rows: the CFG (labels, edges, entry) is the
     same, and PHIs are kept unchanged in their same-labelled block
     (lower_dload_function_supply_cfg_edge, _labels, _retained_location).
   - the single-definition rows: fn_pass_step's ir_supply_covers_unit
     covers the observed unit, which contains fn (lookup_unique_function),
     so the supply's fresh variables avoid every variable of fn and no
     variable of fn gets a second definition.
   - fn_defs_reach_uses: a Var operand of an expanded instruction is a
     fresh variable defined earlier in the same expansion, or an operand of
     the original (non-PHI) instruction.  The original's definition before
     its occurrence (or in an earlier block of the path) is still there,
     before the expansion.  fn_inst_ids_distinct makes the occurrence
     unique, which matters because def_on_all_paths asks for a definition
     before SOME occurrence of the use.  fn_inst_wf keeps DLOADBYTES
     output-free (the expansion drops a DLOADBYTES's outputs) and gives
     DLOAD its one operand and output. *)
Theorem lower_dload_fn_pass_step_make_ssa_input_ok:
  fn_pass_step rpolicy (CFP_Simple VP_LowerDload) observed s fn out /\
  fn_inst_ids_distinct fn /\ fn_inst_wf fn /\ make_ssa_input_ok fn ==>
  make_ssa_input_ok out.fpo_function
Proof
  cheat
QED
