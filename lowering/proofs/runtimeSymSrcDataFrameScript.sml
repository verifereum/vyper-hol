(* A single metadata projection frame avoids expanding the state monad in
   consumers. Data-writing dispatch operations deliberately have no rule. *)
Theory runtimeSymSrcDataFrame
Ancestors
  symbolicSourceCompilerFrame
  compileEnv emitHelper exprCallBounds

Definition runtime_data_frame_def:
  runtime_data_frame (m : 'a compiler) <=>
    !st. (SND (m st)).cs_data_sections = st.cs_data_sections
End

Theorem symbolic_frame_runtime:
  symbolic_frame (\data s t. s = t /\ s.cs_data_sections = data) m <=>
  runtime_data_frame m
Proof
  simp[symbolic_frame_def, runtime_data_frame_def] >> metis_tac[]
QED

fun specialize_frame theorem =
  REWRITE_RULE [symbolic_frame_runtime]
    (Q.ISPEC `\data (s:compile_state) t. s = t /\ s.cs_data_sections = data` (Q.GEN `R` theorem))

fun apply_symbolic_frame theorem = match_mp_tac (specialize_frame theorem)

Theorem runtime_data_frame_apply:
  runtime_data_frame m /\ m st = (x,st') ==>
  st'.cs_data_sections = st.cs_data_sections
Proof
  simp[runtime_data_frame_def] >> metis_tac[pairTheory.SND]
QED

Theorem runtime_data_frame_return[simp]:
  runtime_data_frame (comp_return x)
Proof
  MATCH_ACCEPT_TAC (specialize_frame symbolic_frame_return)
QED

Theorem runtime_data_frame_bind[simp]:
  runtime_data_frame m /\ (!x. runtime_data_frame (f x)) ==>
  runtime_data_frame (comp_bind m f)
Proof
  MATCH_ACCEPT_TAC (specialize_frame symbolic_frame_bind)
QED

Theorem runtime_data_frame_ignore_bind[simp]:
  runtime_data_frame m /\ runtime_data_frame n ==>
  runtime_data_frame (comp_ignore_bind m n)
Proof
  MATCH_ACCEPT_TAC (specialize_frame symbolic_frame_ignore_bind)
QED

Theorem runtime_data_frame_get[simp]:
  runtime_data_frame comp_get
Proof
  simp[runtime_data_frame_def, comp_get_def]
QED

Theorem runtime_data_frame_fresh_var[simp]:
  runtime_data_frame fresh_var
Proof
  apply_symbolic_frame symbolic_frame_fresh_var >> simp[]
QED

Theorem runtime_data_frame_fresh_id[simp]:
  runtime_data_frame fresh_id
Proof
  apply_symbolic_frame symbolic_frame_fresh_id >> simp[]
QED

Theorem runtime_data_frame_fresh_label[simp]:
  runtime_data_frame (fresh_label suffix)
Proof
  apply_symbolic_frame symbolic_frame_fresh_label >> simp[]
QED

Theorem runtime_data_frame_emit[simp]:
  runtime_data_frame (emit inst)
Proof
  apply_symbolic_frame symbolic_frame_emit >> simp[]
QED

Theorem runtime_data_frame_new_block[simp]:
  runtime_data_frame (new_block label)
Proof
  apply_symbolic_frame symbolic_frame_new_block >> simp[]
QED

Theorem runtime_data_frame_emit_inst[simp]:
  runtime_data_frame (emit_inst opc ops outs)
Proof
  apply_symbolic_frame symbolic_frame_emit_inst >> simp[]
QED

Theorem runtime_data_frame_emit_void[simp]:
  runtime_data_frame (emit_void opc ops)
Proof
  apply_symbolic_frame symbolic_frame_emit_void >> simp[]
QED

Theorem runtime_data_frame_emit_op[simp]:
  runtime_data_frame (emit_op opc ops)
Proof
  apply_symbolic_frame symbolic_frame_emit_op >> simp[]
QED

Theorem runtime_data_frame_fresh_vars[simp]:
  !n. runtime_data_frame (fresh_vars n)
Proof
  apply_symbolic_frame symbolic_frame_fresh_vars >> simp[]
QED

Theorem runtime_data_frame_emit_multi_op[simp]:
  runtime_data_frame (emit_multi_op opc ops n)
Proof
  apply_symbolic_frame symbolic_frame_emit_multi_op >> simp[]
QED

Theorem runtime_data_frame_emit_jmp_if_not_terminated[simp]:
  runtime_data_frame (emit_jmp_if_not_terminated label)
Proof
  apply_symbolic_frame symbolic_frame_jmp_if_not_terminated >> simp[]
QED

Theorem runtime_data_frame_invalid_expr_call[simp]:
  runtime_data_frame (invalid_expr_call ty)
Proof
  match_mp_tac (specialize_frame symbolic_frame_invalid_expr_call) >> simp[]
QED
