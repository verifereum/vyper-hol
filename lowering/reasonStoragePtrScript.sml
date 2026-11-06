(* Storage and transient reason normalization boundaries. *)
Theory reasonStoragePtr
Ancestors
  bodyPtrDefs compileEnv ptrDiscipline vyperValue pred_set

(* The length slot is live even when the string is empty.  Unlike payload
   slots it cannot inherit any of the type-relative dead-byte taint. *)
Theorem reason_located_string_head_clean:
  ptr_vv_ok cx t tv (LocatedValue t' p) es G tn s /\
  eval_operand p.ptr_operand s = SOME w /\
  evaluate_type (get_tenv cx) t = SOME (BaseTV (StringT max)) ==>
  (p.ptr_location = LocStorage ==> key_taint tn.t_stor w = {}) /\
  (p.ptr_location = LocTransient ==> key_taint tn.t_trans w = {})
Proof
  simp[ptr_vv_ok_def] >> rpt strip_tac >>
  simp[key_taint_def, EXTENSION] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`w`, `BaseTV (StringT max)`, `w`, `x`] mp_tac) >>
  simp[type_slot_size_def, dead_bytes_def, dyn_bytes_dead_def] >>
  metis_tac[]
QED
