Theory makeSsaCurrentMemRanges
Ancestors
  makeSsaCurrentOrdinary unitMemInv contextCodegenRel codegenRel
  makeSsaCurrentDefs stateFrame venomExecSemantics list pair

Theorem current_dret_memory_ranges_agree:
  inst.inst_opcode = DRET /\ inst'.inst_opcode = inst.inst_opcode /\
  inst'.inst_operands = rename_current_operands rs inst.inst_operands /\
  execution_frame st = execution_frame st' /\
  current_name_agree rs (venomInst$operand_vars inst.inst_operands) st st' ==>
  source_memory_read_ranges inst st = source_memory_read_ranges inst' st' /\
  source_memory_write_ranges inst st = source_memory_write_ranges inst' st'
Proof
  strip_tac >>
  `parse_dret_shape inst' = parse_dret_shape inst`
    by (irule current_parse_dret_shape >> qexists_tac `rs` >> simp[]) >>
  `eval_operands inst'.inst_operands st' = eval_operands inst.inst_operands st`
    by (simp[] >> irule current_eval_operands_subset >> metis_tac[]) >>
  `st.vs_call_entry_fmp = st'.vs_call_entry_fmp`
    by (qpat_x_assum `execution_frame _ = _`
          (mp_tac o AP_TERM ``\s:venom_state. s.vs_call_entry_fmp``) >>
        simp[execution_frame_def]) >>
  simp[source_memory_write_ranges_def, source_memory_read_ranges_def,
       dret_memory_read_ranges_def]
QED
