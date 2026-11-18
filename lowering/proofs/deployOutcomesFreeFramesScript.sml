Theory deployOutcomesFreeFrames
Ancestors
  loweringBudgetFrameOracleTransport
  ptrDiscipline deployOutcomesFreeStep venomState venomExecSemantics codegenRel contextCodegenRel ctxLookupAgreeHelpers

Theorem outcomes_operand[simp]:
  eval_operand op (s with vs_outcomes := os) = eval_operand op s /\
  lookup_var v (s with vs_outcomes := os) = lookup_var v s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem outcomes_provenance[simp]:
  step_prov PG G inst (s with vs_outcomes := os) = step_prov PG G inst s /\
  entry_prov fn (s with vs_outcomes := os) G = entry_prov fn s G /\
  entry_taint_vars fn (s with vs_outcomes := os) tn = entry_taint_vars fn s tn
Proof
  simp[step_prov_def, out_prov_def, entry_prov_def, entry_taint_vars_def]
QED

Theorem outcomes_taint_parts[simp]:
  written_taint tn inst (s with vs_outcomes := os) = written_taint tn inst s /\
  out_taint tn inst (s with vs_outcomes := os) = out_taint tn inst s /\
  store_taint opc tn inst (s with vs_outcomes := os) X = store_taint opc tn inst s X /\
  imm_taint tn inst (s with vs_outcomes := os) = imm_taint tn inst s /\
  ret_taint tn inst (s with vs_outcomes := os) = ret_taint tn inst s
Proof
  simp[written_taint_def, out_taint_def, store_taint_def, imm_taint_def,
       ret_taint_def]
QED


Theorem outcomes_memory_ranges[simp]:
  source_memory_write_ranges inst (s with vs_outcomes := os) = source_memory_write_ranges inst s /\
  source_memory_read_ranges inst (s with vs_outcomes := os) = source_memory_read_ranges inst s
Proof
  simp[source_memory_write_ranges_def, source_memory_read_ranges_def,
       fixed_source_write_range_def, sized_source_write_range_def,
       dret_memory_read_ranges_def, memory_range_of_operands_def,
       eval_operands_outcomes_update]
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
