Theory entryCodePredicate
Ancestors
  compileEnv vyperCompiler list

Definition entry_code_pred_def:
  entry_code_pred P st <=>
    EVERY P st.cs_current_insts /\
    EVERY (\b. EVERY P b.bb_instructions) st.cs_blocks
End

Definition entry_preserves_code_def:
  entry_preserves_code P m <=>
    !st x st'. entry_code_pred P st /\ m st = (x,st') ==>
      entry_code_pred P st'
End

Theorem entry_preserves_code_apply:
  entry_preserves_code P m /\ entry_code_pred P st /\
  m st = (x,st') ==> entry_code_pred P st'
Proof
  simp[entry_preserves_code_def] >> metis_tac[]
QED

Theorem entry_code_return:
  entry_preserves_code P (comp_return x)
Proof
  simp[entry_preserves_code_def, comp_return_def]
QED

Theorem entry_code_bind:
  entry_preserves_code P m /\
  (!x. entry_preserves_code P (f x)) ==>
  entry_preserves_code P (comp_bind m f)
Proof
  rw[entry_preserves_code_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >> metis_tac[]
QED

Theorem entry_code_ignore_bind:
  entry_preserves_code P m /\ entry_preserves_code P n ==>
  entry_preserves_code P (comp_ignore_bind m n)
Proof
  strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  irule entry_code_bind >> simp[]
QED

Theorem entry_code_emit:
  P i ==> entry_preserves_code P (emit i)
Proof
  simp[entry_preserves_code_def, emit_def, entry_code_pred_def]
QED

Theorem entry_code_new_block:
  entry_preserves_code P (new_block label)
Proof
  simp[entry_preserves_code_def, new_block_def, entry_code_pred_def]
QED

Theorem entry_code_fresh_var:
  entry_preserves_code P fresh_var
Proof
  simp[entry_preserves_code_def, fresh_var_def, entry_code_pred_def]
QED

Theorem entry_code_fresh_id:
  entry_preserves_code P fresh_id
Proof
  simp[entry_preserves_code_def, fresh_id_def, entry_code_pred_def]
QED

Theorem entry_code_fresh_label:
  entry_preserves_code P (fresh_label suffix)
Proof
  simp[entry_preserves_code_def, fresh_label_def, entry_code_pred_def]
QED

Theorem entry_code_get:
  entry_preserves_code P comp_get
Proof
  simp[entry_preserves_code_def, comp_get_def]
QED

Theorem entry_code_set:
  entry_code_pred P replacement ==>
  entry_preserves_code P (comp_set replacement)
Proof
  simp[entry_preserves_code_def, comp_set_def]
QED

Theorem entry_code_data_section:
  entry_preserves_code P (emit_data_section label)
Proof
  simp[entry_preserves_code_def, emit_data_section_def, entry_code_pred_def]
QED

Theorem entry_code_data_item:
  entry_preserves_code P (emit_data_item item)
Proof
  rw[entry_preserves_code_def, emit_data_item_def] >>
  gvs[AllCaseEqs(), entry_code_pred_def]
QED

Theorem entry_code_initial:
  entry_code_pred P (initial_compile_state label)
Proof
  simp[entry_code_pred_def, initial_compile_state_def]
QED
