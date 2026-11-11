Theory frameRelocationControl
Ancestors frameRelocationLocal frameRelocationValues venomState

(* Different updates and different observations are intentional: instruction
   positions can change, and an observation need not ignore those positions. *)
Definition control_transport_def:
  control_transport Rel Next U V <=> !s t. Rel s t ==> Next (U s) (V t)
End

Theorem control_transport_elim:
  control_transport Rel Next U V /\ Rel s t ==> Next (U s) (V t)
Proof
  simp[control_transport_def]
QED

Theorem control_transport_identity:
  control_transport Rel Rel (\s. s) (\t. t)
Proof
  simp[control_transport_def]
QED

Theorem control_transport_compose:
  control_transport Rel Next U V /\ control_transport Next Final U' V' ==>
  control_transport Rel Final (U' o U) (V' o V)
Proof
  simp[control_transport_def] >> metis_tac[]
QED

Theorem local_rel_index_transport:
  control_transport Obs Obs'
    (\s. s with vs_inst_idx := i) (\t. t with vs_inst_idx := j) ==>
  control_transport (local_rel P ptr_rel B R Obs)
    (local_rel P ptr_rel B R Obs')
    (\s. s with vs_inst_idx := i) (\t. t with vs_inst_idx := j)
Proof
  simp[control_transport_def, local_rel_def, variable_domains_def,
    variables_agree_on_def, local_values_def, lookup_var_def] >>
  metis_tac[]
QED

val _ = export_theory();
