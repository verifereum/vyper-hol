(* A single metadata projection frame avoids expanding the state monad in
   consumers. Data-writing dispatch operations deliberately have no rule. *)
Theory runtimeSymSrcDataFrame
Ancestors
  compileEnv emitHelper exprCallBounds

Definition runtime_data_frame_def:
  runtime_data_frame (m : 'a compiler) <=>
    !st. (SND (m st)).cs_data_sections = st.cs_data_sections
End

Theorem runtime_data_frame_apply:
  runtime_data_frame m /\ m st = (x,st') ==>
  st'.cs_data_sections = st.cs_data_sections
Proof
  simp[runtime_data_frame_def] >> metis_tac[pairTheory.SND]
QED

Theorem runtime_data_frame_return[simp]:
  runtime_data_frame (comp_return x)
Proof
  simp[runtime_data_frame_def, comp_return_def]
QED

Theorem runtime_data_frame_bind[simp]:
  runtime_data_frame m /\ (!x. runtime_data_frame (f x)) ==>
  runtime_data_frame (comp_bind m f)
Proof
  rw[runtime_data_frame_def, comp_bind_def] >>
  Cases_on `m st` >> gvs[] >> metis_tac[pairTheory.SND]
QED

Theorem runtime_data_frame_ignore_bind[simp]:
  runtime_data_frame m /\ runtime_data_frame n ==>
  runtime_data_frame (comp_ignore_bind m n)
Proof
  simp[comp_ignore_bind_def]
QED

Theorem runtime_data_frame_get[simp]:
  runtime_data_frame comp_get
Proof
  simp[runtime_data_frame_def, comp_get_def]
QED

Theorem runtime_data_frame_fresh_var[simp]:
  runtime_data_frame fresh_var
Proof
  simp[runtime_data_frame_def, fresh_var_def]
QED

Theorem runtime_data_frame_fresh_id[simp]:
  runtime_data_frame fresh_id
Proof
  simp[runtime_data_frame_def, fresh_id_def]
QED

Theorem runtime_data_frame_fresh_label[simp]:
  runtime_data_frame (fresh_label suffix)
Proof
  simp[runtime_data_frame_def, fresh_label_def]
QED

Theorem runtime_data_frame_emit[simp]:
  runtime_data_frame (emit inst)
Proof
  simp[runtime_data_frame_def, emit_def]
QED

Theorem runtime_data_frame_new_block[simp]:
  runtime_data_frame (new_block label)
Proof
  simp[runtime_data_frame_def, new_block_def]
QED

Theorem runtime_data_frame_emit_inst[simp]:
  runtime_data_frame (emit_inst opc ops outs)
Proof
  simp[emit_inst_def]
QED

Theorem runtime_data_frame_emit_void[simp]:
  runtime_data_frame (emit_void opc ops)
Proof
  simp[emit_void_def]
QED

Theorem runtime_data_frame_emit_op[simp]:
  runtime_data_frame (emit_op opc ops)
Proof
  simp[emit_op_def]
QED

Theorem runtime_data_frame_fresh_vars[simp]:
  !n. runtime_data_frame (fresh_vars n)
Proof
  Induct >> simp[fresh_vars_def]
QED

Theorem runtime_data_frame_emit_multi_op[simp]:
  runtime_data_frame (emit_multi_op opc ops n)
Proof
  simp[emit_multi_op_def]
QED

Theorem runtime_data_frame_emit_jmp_if_not_terminated[simp]:
  runtime_data_frame (emit_jmp_if_not_terminated label)
Proof
  simp[emit_jmp_if_not_terminated_def] >>
  irule runtime_data_frame_bind >> simp[] >>
  gen_tac >> IF_CASES_TAC >> simp[]
QED

Theorem runtime_data_frame_invalid_expr_call[simp]:
  runtime_data_frame (invalid_expr_call ty)
Proof
  simp[runtime_data_frame_def, invalid_expr_call_def,
       emit_inst_def, comp_bind_def, fresh_id_def, emit_def]
QED

(* Callback probe: the premise is uniform in states and all child inputs. *)
Theorem runtime_data_frame_expr_child_callback:
  (!cenv ty e. runtime_data_frame (cfn cenv ty e)) ==>
  runtime_data_frame (expr_child_callback bound cfn cenv ty e)
Proof
  rw[runtime_data_frame_def, expr_child_callback_def] >>
  IF_CASES_TAC >> simp[] >>
  metis_tac[runtime_data_frame_invalid_expr_call, runtime_data_frame_def]
QED
