(* Checked boundary probes for the external return interface audit. *)
Theory externalReturnInterfaceProbe
Ancestors
  loweringPosts valueEncoding vyperInterpreter venomMemDefs venomExecSemantics fragGasMode runFromGasPath

Theorem short_bytes_footprint_probe:
  val_footprint (BaseTV (BytesT (Dynamic 100))) (BytesV [1w;2w;3w]) = 35
Proof
  EVAL_TAC
QED

Theorem empty_struct_footprint_probe:
  val_footprint (StructTV []) (StructV []) = 0
Proof
  EVAL_TAC
QED

Theorem reused_alloca_probe:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (64,32) ==>
  exec_alloca inst s 100w = OK (update_var out 64w s)
Proof
  simp[exec_alloca_def]
QED

Theorem short_bytes_not_capacity_probe:
  val_footprint (BaseTV (BytesT (Dynamic 100))) (BytesV [1w;2w;3w]) <
  type_memory_size (BaseTV (BytesT (Dynamic 100)))
Proof
  EVAL_TAC
QED

Theorem empty_struct_no_owner_probe:
  evaluate_type (get_tenv cx) ty = SOME (StructTV []) /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==> tv = StructTV []) /\
  eval_operand op s = SOME w ==>
  expr_val_at cenv cx ty sa sb es (StructV []) op s
Proof
  simp[expr_val_at_def] >> rpt strip_tac >>
  gvs[val_footprint_def, val_wf_def, type_memory_size_def] >>
  metis_tac[]
QED

Theorem exiting_run_marked_probe:
  run_from fuel ctx func s = r /\ exit_result r /\ ~s.vs_halted ==>
  ?n. gas_marked_path F ctx func s n r
Proof
  simp[gas_marked_path_def] >> metis_tac[run_from_gas_path]
QED

Theorem return_state_projection_probe:
  abstract_machine_from_state srcs exps layouts
    (es with <|gas_obs := tail; scopes := []|>) =
  abstract_machine_from_state srcs exps layouts es
Proof
  simp[abstract_machine_from_state_def]
QED
