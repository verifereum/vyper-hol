Theory deployOutcomesFreeFrames
Ancestors
  loweringBudgetFrameOracleTransport
  ptrDiscipline deployOutcomesFreeStep venomState venomExecSemantics codegenRel contextCodegenRel ctxLookupAgreeHelpers

(* Outcome-update invariance facts from the frame oracle transport. *)
val _ = export_rewrites
  ["loweringBudgetFrameOracleTransport.operand_outcomes_update",
   "loweringBudgetFrameOracleTransport.step_prov_outcomes_update",
   "loweringBudgetFrameOracleTransport.entry_prov_outcomes_update",
   "loweringBudgetFrameOracleTransport.entry_taint_outcomes_update",
   "loweringBudgetFrameOracleTransport.write_ranges_outcomes_update",
   "loweringBudgetFrameOracleTransport.ghost_components_outcomes_update"];

Theorem outcomes_lookup_var[simp]:
  lookup_var v (s with vs_outcomes := os) = lookup_var v s
Proof
  simp[lookup_var_def]
QED

Theorem outcomes_taint_parts[simp]:
  written_taint tn inst (s with vs_outcomes := os) = written_taint tn inst s /\
  ret_taint tn inst (s with vs_outcomes := os) = ret_taint tn inst s
Proof
  simp[written_taint_def, ret_taint_def]
QED


Theorem outcomes_memory_read_ranges[simp]:
  source_memory_read_ranges inst (s with vs_outcomes := os) = source_memory_read_ranges inst s
Proof
  simp[source_memory_read_ranges_def, dret_memory_read_ranges_def,
       memory_range_of_operands_def, eval_operands_outcomes_update]
QED


Theorem outcomes_state_predicates[simp]:
  access_ok lo G fn inst (s with vs_outcomes := os) = access_ok lo G fn inst s /\
  taint_ok fn tn inst (s with vs_outcomes := os) = taint_ok fn tn inst s /\
  allocas_from lo (s with vs_outcomes := os) = allocas_from lo s /\
  allocas_below_fmp (s with vs_outcomes := os) = allocas_below_fmp s
Proof
  simp[access_ok_def, taint_ok_def, about_to_revert_def, in_revert_forward_def,
       active_inst_def, allocas_from_def, allocas_below_fmp_def]
QED
