Theory simplifyCfgStruct
Ancestors
  simplifyCfgLabelProps simplifyCfgCompute cfgWf venomWf venomInst

(* Boundary probes: wf_function intentionally does not require inst_wf. *)
Definition struct_cycle_def:
  struct_cycle = mk_raw_function "cycle"
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 JNZ [Var "c"; Label "back"; Label "exit"] []] |>;
     <| bb_label := "back"; bb_instructions :=
        [mk_inst 1 NOP [] []; mk_inst 2 JMP [Label "entry"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 3 STOP [] []] |>]
End

Definition struct_bypass_def:
  struct_bypass = mk_raw_function "bypass"
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 JNZ [Var "c"; Label "back"; Label "exit"] []] |>;
     <| bb_label := "back"; bb_instructions :=
        [mk_inst 1 JMP [Label "entry"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 2 STOP [] []] |>]
End

Definition struct_phi_def:
  struct_phi = mk_raw_function "phi"
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 PHI [] ["x"];
         mk_inst 1 PHI [Var "bad"] ["y"];
         mk_inst 2 PHI [Var "bad"; Var "w"] ["z"];
         mk_inst 3 STOP [] []] |>]
End

Theorem struct_inputs_wf:
  wf_function struct_cycle /\ wf_function struct_bypass /\
  wf_function struct_phi
Proof
  EVAL_TAC
QED

Theorem struct_outputs_wf:
  wf_function (simplify_cfg_fn struct_cycle) /\
  wf_function (simplify_cfg_fn struct_bypass) /\
  wf_function (simplify_cfg_fn struct_phi)
Proof
  EVAL_TAC
QED

Theorem struct_outputs_ssa:
  ssa_form (simplify_cfg_fn struct_cycle) /\
  ssa_form (simplify_cfg_fn struct_bypass) /\
  ssa_form (simplify_cfg_fn struct_phi)
Proof
  EVAL_TAC
QED

Theorem struct_cycle_blocks:
  (simplify_cfg_fn struct_cycle).fn_blocks =
    [<| bb_label := "back"; bb_instructions :=
        [mk_inst 1 NOP [] [];
         mk_inst 0 JNZ [Var "c"; Label "back"; Label "exit"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 3 STOP [] []] |>]
Proof
  EVAL_TAC
QED

Theorem struct_bypass_blocks:
  (simplify_cfg_fn struct_bypass).fn_blocks =
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 JNZ [Var "c"; Label "entry"; Label "exit"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 2 STOP [] []] |>]
Proof
  EVAL_TAC
QED

Theorem struct_phi_blocks:
  (simplify_cfg_fn struct_phi).fn_blocks =
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 1 PHI [Var "bad"] ["y"];
         mk_inst 0 NOP [] [];
         mk_inst 2 ASSIGN [Var "w"] ["z"];
         mk_inst 3 STOP [] []] |>]
Proof
  EVAL_TAC
QED

Theorem struct_outputs_reachable:
  all_reachable (simplify_cfg_fn struct_cycle) /\
  all_reachable (simplify_cfg_fn struct_bypass) /\
  all_reachable (simplify_cfg_fn struct_phi)
Proof
  simp[all_reachable_def, fn_reachable_def, fn_entry_label_def,
       entry_block_def, struct_cycle_blocks, struct_bypass_blocks,
       struct_phi_blocks] >>
  rpt conj_tac >> rpt strip_tac >> gvs[] >>
  irule relationTheory.RTC_SINGLE >>
  simp[fn_cfg_edge_def, struct_cycle_blocks, struct_bypass_blocks,
       bb_succs_def, mk_inst_def, get_successors_def,
       RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC
QED
