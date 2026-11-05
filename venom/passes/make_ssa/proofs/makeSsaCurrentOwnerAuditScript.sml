Theory makeSsaCurrentOwnerAudit
Ancestors makeSsaCurrentLiveOriginTransfer venomWf venomExecSemantics venomState finite_map

Definition owner_audit_inst_def:
  owner_audit_inst = <| inst_id := 0; inst_opcode := INVOKE;
    inst_operands := [Label "callee"]; inst_outputs := ["x";"x"] |>
End

Definition owner_audit_supply_def:
  owner_audit_supply = <| irs_next_inst := 1; irs_next_var := 0;
    irs_next_label := 0; irs_used_inst_ids := [0];
    irs_used_vars := ["x"]; irs_used_labels := ["callee"] |>
End

Theorem owner_audit_wf:
  inst_wf owner_audit_inst /\ inst_wf_exec owner_audit_inst /\
  ~ALL_DISTINCT owner_audit_inst.inst_outputs
Proof
  EVAL_TAC
QED

Theorem owner_audit_names:
  ?rs s. rename_current_outputs owner_audit_supply ([],[]) ["x";"x"] =
    (rs,s,["x";"formal_var_0"]) /\
    latest_current_name rs "x" = "formal_var_0"
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

(* Unlike parallel PHIs, call returns use sequential updates: last output wins. *)
Theorem owner_audit_bind:
  bind_outputs ["x";"x"] [1w;2w] st =
    SOME (update_var "x" 2w (update_var "x" 1w st)) /\
  lookup_var "x" (update_var "x" 2w (update_var "x" 1w st)) = SOME 2w /\
  bind_outputs ["x";"formal_var_0"] [1w;2w] st =
    SOME (update_var "formal_var_0" 2w (update_var "x" 1w st)) /\
  lookup_var "formal_var_0"
    (update_var "formal_var_0" 2w (update_var "x" 1w st)) = SOME 2w
Proof
  simp[bind_outputs_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

(* The first-binding symbolic abstraction is not the INVOKE write semantics. *)
Theorem owner_audit_symbolic_first:
  current_origin_write ms n ["x";"x"] "x" =
    SOME (CurrentOccurrence n 0)
Proof
  EVAL_TAC
QED
