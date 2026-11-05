(* Proof interfaces for the supply-aware renamer.  Demand is local to an
   alignment point; it does not assert agreement on dead historical names. *)
Theory makeSsaCurrentSimDefs
Ancestors
  makeSsaCurrentDefs stateFrame venomState venomInst finite_map

Datatype:
  current_sim_phase = BeforePhis | AfterPhis | CleanupCopies | OrdinaryCode
End

(* The three origins are intentionally distinct even when an inserted PHI
   and an original PHI define the same source spelling. *)
Datatype:
  current_inst_origin = OriginalInst num | InsertedPhi string string
                      | CleanupCopy string string
End

Definition current_name_agree_def:
  current_name_agree rs demand st st' <=>
    !v. MEM v demand ==>
      lookup_var v st = lookup_var (latest_current_name rs v) st'
End

(* Positions are supplied by the static alignment certificate, not assumed
   equal. Control fields are not part of execution_frame. *)
Definition current_phase_rel_def:
  current_phase_rel phase positions rs demand st st' <=>
    execution_frame st = execution_frame st' /\
    st.vs_current_bb = st'.vs_current_bb /\
    st.vs_prev_bb = st'.vs_prev_bb /\
    MEM (phase,st.vs_inst_idx,st'.vs_inst_idx) positions /\
    current_name_agree rs demand st st'
End

Theorem current_name_agree_empty:
  st.vs_vars = FEMPTY /\ st'.vs_vars = FEMPTY ==>
  current_name_agree rs demand st st'
Proof
  simp[current_name_agree_def, lookup_var_def]
QED

Theorem current_name_agree_mono:
  current_name_agree rs demand st st' /\
  (!v. MEM v smaller ==> MEM v demand) ==>
  current_name_agree rs smaller st st'
Proof
  simp[current_name_agree_def] >> metis_tac[]
QED

Theorem current_phase_rel_frame:
  current_phase_rel phase positions rs demand st st' ==>
  execution_frame st = execution_frame st'
Proof
  simp[current_phase_rel_def]
QED

Theorem current_phase_rel_entry:
  st.vs_vars = FEMPTY /\ st'.vs_vars = FEMPTY /\
  execution_frame st = execution_frame st' /\
  st.vs_current_bb = st'.vs_current_bb /\
  st.vs_prev_bb = st'.vs_prev_bb /\
  MEM (BeforePhis,st.vs_inst_idx,st'.vs_inst_idx) positions ==>
  current_phase_rel BeforePhis positions rs demand st st'
Proof
  simp[current_phase_rel_def, current_name_agree_empty]
QED

Theorem current_eval_operands_agree:
  !ops. execution_frame st = execution_frame st' /\
  current_name_agree rs (operand_vars ops) st st' ==>
  eval_operands (rename_current_operands rs ops) st' = eval_operands ops st
Proof
  Induct >> simp[rename_current_operands_def, eval_operands_def] >>
  Cases_on `h` >>
  simp[rename_current_operands_def, operand_vars_def, operand_var_def,
       current_name_agree_def, eval_operands_def, eval_operand_def] >>
  rpt strip_tac >> gvs[] >>
  `st.vs_labels = st'.vs_labels` by
    (qpat_x_assum `execution_frame _ = _`
       (mp_tac o AP_TERM ``\s:venom_state. s.vs_labels``) >>
     simp[execution_frame_def]) >> simp[]
QED

(* Small executable boundary tests. *)
Definition current_probe_inst_def:
  current_probe_inst id opc ops outs =
    <| inst_id := id; inst_opcode := opc;
       inst_operands := ops; inst_outputs := outs |>
End

Definition current_probe_supply_def:
  current_probe_supply =
    <| irs_next_inst := 10; irs_next_var := 0; irs_next_label := 0;
       irs_used_inst_ids := [0;1;2;3;4;5];
       irs_used_vars := ["a";"b";"v"];
       irs_used_labels := ["E";"D";"X"] |>
End

Definition current_probe_loop_def:
  current_probe_loop = mk_raw_function "probe"
    [<| bb_label := "E"; bb_instructions :=
        [current_probe_inst 0 ASSIGN [Lit 1w] ["a"];
         current_probe_inst 1 JMP [Label "D"] []] |>;
     <| bb_label := "D"; bb_instructions :=
        [current_probe_inst 2 PHI
           [Label "E"; Var "a"; Label "D"; Var "b"] ["v"];
         current_probe_inst 3 ASSIGN [Lit 2w] ["b"];
         current_probe_inst 4 JNZ [Var "v"; Label "D"; Label "X"] []] |>;
     <| bb_label := "X"; bb_instructions :=
        [current_probe_inst 5 STOP [] []] |>]
End

Theorem current_probe_loop_opcodes:
  MAP (\bb. MAP (\i. i.inst_opcode) bb.bb_instructions)
    (FST (make_ssa_current_fn current_probe_supply current_probe_loop)).fn_blocks =
  [[ASSIGN; JMP]; [PHI; ASSIGN; ASSIGN; JNZ]; [STOP]]
Proof
  EVAL_TAC
QED

Theorem current_probe_loop_header:
  (EL 1 (FST (make_ssa_current_fn current_probe_supply
                current_probe_loop)).fn_blocks).bb_instructions =
  [current_probe_inst 10 PHI
     [Label "E"; Var "a"; Label "D"; Var "b"] ["formal_var_0"];
   current_probe_inst 2 ASSIGN [Var "formal_var_0"] ["v"];
   current_probe_inst 3 ASSIGN [Lit 2w] ["b"];
   current_probe_inst 4 JNZ [Var "formal_var_0"; Label "D"; Label "X"] []]
Proof
  EVAL_TAC
QED

Theorem current_probe_phi_free:
  make_ssa_current_fn current_probe_supply
    (mk_raw_function "straight"
      [<| bb_label := "E"; bb_instructions :=
          [current_probe_inst 0 ASSIGN [Lit 1w] ["a"];
           current_probe_inst 1 ASSIGN [Var "a"] ["a"];
           current_probe_inst 2 STOP [] []] |>]) =
  (mk_raw_function "straight"
      [<| bb_label := "E"; bb_instructions :=
          [current_probe_inst 0 ASSIGN [Lit 1w] ["a"];
           current_probe_inst 1 ASSIGN [Var "a"] ["formal_var_0"];
           current_probe_inst 2 STOP [] []] |>],
   current_probe_supply with <| irs_next_var := 1;
     irs_used_vars := "formal_var_0"::current_probe_supply.irs_used_vars |>)
Proof
  EVAL_TAC
QED

Theorem current_probe_self_edge_cleanup:
  simplify_current_phi_prefix
    [current_probe_inst 10 PHI
       [Label "E"; Var "v"; Label "D"; Var "p"] ["v"];
     current_probe_inst 2 PHI
       [Label "E"; Var "a"; Label "D"; Var "b"] ["p"];
     current_probe_inst 3 STOP [] []] =
    [current_probe_inst 10 PHI
       [Label "E"; Var "a"; Label "D"; Var "b"] ["p"];
     current_probe_inst 2 ASSIGN [Var "p"] ["v"];
     current_probe_inst 3 STOP [] []]
Proof
  EVAL_TAC
QED
