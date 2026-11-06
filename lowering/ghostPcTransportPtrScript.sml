(* Ghost updates depend on data, not on the instruction cursor. *)
Theory ghostPcTransportPtr
Ancestors bodyPtrDefs ptrDiscipline venomState venomExecSemantics codegenRel

Theorem eval_operand_inst_idx[simp]:
  eval_operand op (s with vs_inst_idx := k) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem eval_operands_inst_idx[simp]:
  eval_operands ops (s with vs_inst_idx := k) = eval_operands ops s
Proof
  Induct_on `ops` >> simp[eval_operands_def]
QED

Theorem step_prov_inst_idx[simp]:
  step_prov PG G inst (s with vs_inst_idx := k) = step_prov PG G inst s
Proof
  simp[step_prov_def, out_prov_def, lookup_var_def]
QED

Theorem ptr_covers_inst_idx[simp]:
  ptr_covers G tn p (s with vs_inst_idx := k) C <=> ptr_covers G tn p s C
Proof
  simp[ptr_covers_def, lookup_var_def]
QED

Theorem step_taint_inst_idx[simp]:
  step_taint inst (s with vs_inst_idx := k) (t with vs_inst_idx := j) tn =
  step_taint inst s t tn
Proof
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, written_taint_def, out_taint_def,
       store_taint_def, imm_taint_def, eval_operand_def, lookup_var_def,
       source_memory_write_ranges_def, sized_source_write_range_def,
       fixed_source_write_range_def]
QED

Theorem step_taint_inst_idx_left[simp]:
  step_taint inst (s with vs_inst_idx := k) t tn = step_taint inst s t tn
Proof
  mp_tac (Q.INST [`j` |-> `t.vs_inst_idx`] step_taint_inst_idx) >>
  simp[Excl "step_taint_inst_idx"]
QED

Theorem write_memory_with_expansion_inst_idx[simp]:
  write_memory_with_expansion off bs (s with vs_inst_idx := k) =
  (write_memory_with_expansion off bs s) with vs_inst_idx := k
Proof
  simp[write_memory_with_expansion_def, write_memory_def, expand_memory_def]
QED

Theorem step_taint_inst_idx_right[simp]:
  step_taint inst s (t with vs_inst_idx := j) tn = step_taint inst s t tn
Proof
  mp_tac (Q.INST [`k` |-> `s.vs_inst_idx`] step_taint_inst_idx) >>
  simp[Excl "step_taint_inst_idx"]
QED
