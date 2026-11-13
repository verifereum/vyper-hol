Theory concretizePtrLedgerProbe
Ancestors
  concretizePtrPrefixRelation concretizePtrBytes concretizePtrPrefixLedger concretizePtrPrefixProbe concretizePtrChronologicalHistory contextCodegenRel
  regularCallEmitSim venomMemProps codegenRel mem2varBlockSimHelpers concretizeMemLocDefs venomExecSemantics venomState ptrDiscipline venomInst words list finite_map
Libs wordsLib

Definition ptr_ledger_probe_source_def:
  ptr_ledger_probe_source = ptr_probe_fn
    [mk_inst 10 ALLOCA [Lit 32w] ["p"];
     mk_inst 11 MSTORE [Var "p"; Lit 42w] [];
     mk_inst 12 NOP [] [];
     mk_inst 13 MLOAD [Var "p"] ["r"];
     mk_inst 14 STOP [] []]
End

Definition ptr_ledger_probe_target_def:
  ptr_ledger_probe_target = (ptr_probe_fn
    [mk_inst 10 ASSIGN [Lit 0w] ["p"];
     mk_inst 11 MSTORE [Var "p"; Lit 42w] [];
     mk_inst 13 MLOAD [Var "p"] ["r"];
     mk_inst 14 STOP [] []]) with
    <| fn_eom := SOME 32; fn_mems_used := [(Allocation 10,0,32)] |>
End

Theorem ptr_ledger_probe_production_transform:
  concretize_function_fuel_in_context 100
    (mk_venom_context [ptr_ledger_probe_source] (SOME "probe")) []
    ptr_ledger_probe_source = SOME ptr_ledger_probe_target
Proof
  EVAL_TAC
QED

(* Ordinary observations keep the actual operational ghosts. *)
Definition ptr_ledger_next_def:
  ptr_ledger_next obs inst post = ptr_observe obs.po_stack obs.po_params
    (step_prov obs.po_params obs.po_prov obs.po_inst post)
    (step_taint obs.po_inst obs.po_state post obs.po_taint)
    obs.po_fn inst (post with vs_inst_idx := SUC obs.po_state.vs_inst_idx)
End

Theorem ptr_ledger_next_step:
  active_inst obs.po_fn obs.po_inst obs.po_state /\
  ~is_terminator obs.po_inst.inst_opcode /\ obs.po_inst.inst_opcode <> INVOKE /\
  step_inst fuel ctx obs.po_inst obs.po_state = OK post /\
  active_inst obs.po_fn inst (post with vs_inst_idx := SUC obs.po_state.vs_inst_idx) ==>
  ptr_chrono_step ctx obs (ptr_ledger_next obs inst post)
Proof
  strip_tac >> Cases_on `obs` >>
  gvs[ptr_ledger_next_def, ptr_observe_def] >>
  simp[Once ptr_chrono_step_cases, ptr_observe_def,
    ptr_observation_component_equality] >>
  qexistsl_tac [`post`,`fuel`] >> simp[]
QED

Theorem ptr_ledger_next_history[local]:
  ptr_chrono_history initial ctx h obs /\
  active_inst obs.po_fn obs.po_inst obs.po_state /\
  ~is_terminator obs.po_inst.inst_opcode /\ obs.po_inst.inst_opcode <> INVOKE /\
  step_inst fuel ctx obs.po_inst obs.po_state = OK post /\
  active_inst obs.po_fn inst (post with vs_inst_idx := SUC obs.po_state.vs_inst_idx) ==>
  ptr_chrono_history initial ctx (h ++ [ptr_ledger_next obs inst post])
    (ptr_ledger_next obs inst post)
Proof
  strip_tac >> irule (cj 2 ptr_chrono_history_rules) >>
  qexists_tac `obs` >> simp[] >>
  irule ptr_ledger_next_step >> metis_tac[]
QED

(* A bounded ordinary suffix is computed from successful execution, not
   supplied as a source-history hypothesis. The instruction list is checked
   against active_inst at every boundary. *)
Definition ptr_ledger_follow_def:
  (ptr_ledger_follow ctx [] obs = SOME []) /\
  (ptr_ledger_follow ctx (inst::rest) obs =
    if active_inst obs.po_fn obs.po_inst obs.po_state /\
       ~is_terminator obs.po_inst.inst_opcode /\ obs.po_inst.inst_opcode <> INVOKE
    then
      case step_inst 0 ctx obs.po_inst obs.po_state of
        OK post =>
          if active_inst obs.po_fn inst
               (post with vs_inst_idx := SUC obs.po_state.vs_inst_idx)
          then OPTION_MAP (CONS (ptr_ledger_next obs inst post))
            (ptr_ledger_follow ctx rest (ptr_ledger_next obs inst post))
          else NONE
      | _ => NONE
    else NONE)
End

Theorem ptr_ledger_follow_history:
  !rest obs tail h endpoint.
    ptr_ledger_follow ctx rest obs = SOME tail /\
    ptr_chrono_history initial ctx h obs ==>
    ptr_chrono_history initial ctx (h ++ tail)
      (if tail = [] then obs else LAST tail)
Proof
  Induct >> simp[ptr_ledger_follow_def] >> rpt gen_tac >>
  strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `step_inst 0 ctx obs.po_inst obs.po_state = OK post` >>
  rename1 `ptr_ledger_follow ctx rest (ptr_ledger_next obs inst post) = SOME suffix` >>
  rename1 `ptr_chrono_history initial ctx history obs` >>
  `ptr_chrono_history initial ctx (history ++ [ptr_ledger_next obs inst post])
     (ptr_ledger_next obs inst post)` by
    (irule ptr_ledger_next_history >> metis_tac[]) >>
  first_x_assum drule >> disch_then drule >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  Cases_on `suffix` >> simp[LAST_DEF]
QED

Definition ptr_ledger_source_entry_def:
  ptr_ledger_source_entry s = ptr_observe [] [] FEMPTY entry_taint
    ptr_ledger_probe_source (mk_inst 10 ALLOCA [Lit 32w] ["p"])
    (ptr_probe_entry_state s)
End

Theorem ptr_ledger_next_projections[simp]:
  (ptr_ledger_next obs inst post).po_fn = obs.po_fn /\
  (ptr_ledger_next obs inst post).po_inst = inst /\
  (ptr_ledger_next obs inst post).po_state =
    post with vs_inst_idx := SUC obs.po_state.vs_inst_idx
Proof
  simp[ptr_ledger_next_def, ptr_observe_def]
QED

Theorem ptr_ledger_source_active[local,simp]:
  active_inst ptr_ledger_probe_source inst s <=>
    s.vs_current_bb = "entry" /\ s.vs_inst_idx < 5 /\
    EL s.vs_inst_idx
      [mk_inst 10 ALLOCA [Lit 32w] ["p"];
       mk_inst 11 MSTORE [Var "p"; Lit 42w] [];
       mk_inst 12 NOP [] [];
       mk_inst 13 MLOAD [Var "p"] ["r"];
       mk_inst 14 STOP [] []] = inst
Proof
  simp[active_inst_def, ptr_ledger_probe_source_def, ptr_probe_fn_def,
    mk_raw_function_def, EQ_SYM_EQ]
QED

Theorem ptr_ledger_source_entry_projections[local,simp]:
  (ptr_ledger_source_entry s).po_fn = ptr_ledger_probe_source /\
  (ptr_ledger_source_entry s).po_inst = mk_inst 10 ALLOCA [Lit 32w] ["p"] /\
  (ptr_ledger_source_entry s).po_state = ptr_probe_entry_state s
Proof
  simp[ptr_ledger_source_entry_def, ptr_observe_def]
QED


Definition ptr_ledger_s1_def:
  ptr_ledger_s1 s = ptr_probe_allocated_state 10 "p" (32w : bytes32)
    (ptr_probe_entry_state s) with vs_inst_idx := 1
End
Definition ptr_ledger_s2_def:
  ptr_ledger_s2 s = mstore (w2n (n2w s.vs_alloca_next : bytes32)) 42w
    (ptr_ledger_s1 s) with vs_inst_idx := 2
End
Definition ptr_ledger_s3_def:
  ptr_ledger_s3 s = ptr_ledger_s2 s with vs_inst_idx := 3
End
Definition ptr_ledger_s4_def:
  ptr_ledger_s4 s = update_var "r"
    (mload (w2n (n2w s.vs_alloca_next : bytes32)) (ptr_ledger_s3 s))
    (ptr_ledger_s3 s) with vs_inst_idx := 4
End

Theorem ptr_ledger_s1_fields[local,simp]:
  (ptr_ledger_s1 s).vs_current_bb = "entry" /\
  (ptr_ledger_s1 s).vs_inst_idx = 1 /\
  lookup_var "p" (ptr_ledger_s1 s) = SOME (n2w s.vs_alloca_next : bytes32)
Proof
  simp[ptr_ledger_s1_def, ptr_probe_allocated_state_def,
    ptr_probe_entry_state_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem ptr_ledger_s2_fields[local,simp]:
  (ptr_ledger_s2 s).vs_current_bb = "entry" /\
  (ptr_ledger_s2 s).vs_inst_idx = 2 /\
  lookup_var "p" (ptr_ledger_s2 s) = SOME (n2w s.vs_alloca_next : bytes32)
Proof
  simp[ptr_ledger_s2_def, mstore_preserves, lookup_var_mstore_idx]
QED

Theorem ptr_ledger_s3_fields[local,simp]:
  (ptr_ledger_s3 s).vs_current_bb = "entry" /\
  (ptr_ledger_s3 s).vs_inst_idx = 3 /\
  lookup_var "p" (ptr_ledger_s3 s) = SOME (n2w s.vs_alloca_next : bytes32)
Proof
  simp[ptr_ledger_s3_def, ptr_ledger_s2_def, mstore_preserves,
    lookup_var_mstore_idx]
QED

Theorem ptr_ledger_s4_fields[local,simp]:
  (ptr_ledger_s4 s).vs_current_bb = "entry" /\
  (ptr_ledger_s4 s).vs_inst_idx = 4
Proof
  simp[ptr_ledger_s4_def, update_var_def]
QED

Theorem ptr_ledger_alloca_edge[local]:
  s.vs_allocas = FEMPTY ==>
  step_inst fuel ctx (mk_inst 10 ALLOCA [Lit 32w] ["p"])
    (ptr_probe_entry_state s) = OK (ptr_ledger_s1 s with vs_inst_idx := 0)
Proof
  simp[ptr_probe_alloca_step, ptr_probe_entry_state_def, ptr_ledger_s1_def,
    ptr_probe_allocated_state_def, update_var_def]
QED

Theorem ptr_ledger_store_edge[local]:
  step_inst fuel ctx (mk_inst 11 MSTORE [Var "p"; Lit 42w] [])
    (ptr_ledger_s1 s) = OK (ptr_ledger_s2 s with vs_inst_idx := 1)
Proof
  simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def,
    exec_write2_def, eval_operand_def, ptr_ledger_s2_def] >>
  simp[ptr_ledger_s1_def, ptr_probe_allocated_state_def,
    ptr_probe_entry_state_def, update_var_def, mstore_def]
QED

Theorem ptr_ledger_nop_edge:
  step_inst fuel ctx (mk_inst 12 NOP [] []) s = OK s
Proof
  simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def]
QED

Theorem ptr_ledger_load_edge[local]:
  step_inst fuel ctx (mk_inst 13 MLOAD [Var "p"] ["r"])
    (ptr_ledger_s3 s) = OK (ptr_ledger_s4 s with vs_inst_idx := 3)
Proof
  simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def,
    exec_read1_def, eval_operand_def, ptr_ledger_s4_def, update_var_def,
    venom_state_component_equality]
QED

Definition ptr_ledger_o1_def:
  ptr_ledger_o1 s = ptr_ledger_next (ptr_ledger_source_entry s)
    (mk_inst 11 MSTORE [Var "p"; Lit 42w] [])
    (ptr_ledger_s1 s with vs_inst_idx := 0)
End
Definition ptr_ledger_o2_def:
  ptr_ledger_o2 s = ptr_ledger_next (ptr_ledger_o1 s)
    (mk_inst 12 NOP [] []) (ptr_ledger_s2 s with vs_inst_idx := 1)
End
Definition ptr_ledger_o3_def:
  ptr_ledger_o3 s = ptr_ledger_next (ptr_ledger_o2 s)
    (mk_inst 13 MLOAD [Var "p"] ["r"]) (ptr_ledger_s2 s)
End
Definition ptr_ledger_o4_def:
  ptr_ledger_o4 s = ptr_ledger_next (ptr_ledger_o3 s)
    (mk_inst 14 STOP [] []) (ptr_ledger_s4 s with vs_inst_idx := 3)
End

Theorem ptr_ledger_o1_fields[local,simp]:
  (ptr_ledger_o1 s).po_fn = ptr_ledger_probe_source /\
  (ptr_ledger_o1 s).po_inst = mk_inst 11 MSTORE [Var "p"; Lit 42w] [] /\
  (ptr_ledger_o1 s).po_state = ptr_ledger_s1 s
Proof
  simp[ptr_ledger_o1_def, ptr_probe_entry_state_def,
    venom_state_component_equality]
QED
Theorem ptr_ledger_o2_fields[local,simp]:
  (ptr_ledger_o2 s).po_fn = ptr_ledger_probe_source /\
  (ptr_ledger_o2 s).po_inst = mk_inst 12 NOP [] [] /\
  (ptr_ledger_o2 s).po_state = ptr_ledger_s2 s
Proof
  simp[ptr_ledger_o2_def, venom_state_component_equality]
QED
Theorem ptr_ledger_o3_fields[local,simp]:
  (ptr_ledger_o3 s).po_fn = ptr_ledger_probe_source /\
  (ptr_ledger_o3 s).po_inst = mk_inst 13 MLOAD [Var "p"] ["r"] /\
  (ptr_ledger_o3 s).po_state = ptr_ledger_s3 s
Proof
  simp[ptr_ledger_o3_def, ptr_ledger_s3_def]
QED
Theorem ptr_ledger_o4_fields[local,simp]:
  (ptr_ledger_o4 s).po_fn = ptr_ledger_probe_source /\
  (ptr_ledger_o4 s).po_inst = mk_inst 14 STOP [] [] /\
  (ptr_ledger_o4 s).po_state = ptr_ledger_s4 s
Proof
  simp[ptr_ledger_o4_def, venom_state_component_equality]
QED

Theorem ptr_ledger_instruction_opcode[simp]:
  (mk_inst iid opc ops outs).inst_opcode = opc
Proof
  simp[mk_inst_def]
QED

Theorem ptr_ledger_entry_fields[local,simp]:
  (ptr_probe_entry_state s).vs_current_bb = "entry" /\
  (ptr_probe_entry_state s).vs_inst_idx = 0
Proof
  simp[ptr_probe_entry_state_def]
QED

Theorem ptr_ledger_source_follows:
  s.vs_allocas = FEMPTY ==>
  ptr_ledger_follow ctx
    [mk_inst 11 MSTORE [Var "p"; Lit 42w] [];
     mk_inst 12 NOP [] [];
     mk_inst 13 MLOAD [Var "p"] ["r"];
     mk_inst 14 STOP [] []] (ptr_ledger_source_entry s) =
    SOME [ptr_ledger_o1 s; ptr_ledger_o2 s; ptr_ledger_o3 s; ptr_ledger_o4 s]
Proof
  strip_tac >>
  simp[Once ptr_ledger_follow_def, ptr_ledger_alloca_edge,
    is_terminator_def, GSYM ptr_ledger_o1_def] >>
  simp[Once ptr_ledger_follow_def, ptr_ledger_store_edge,
    is_terminator_def, GSYM ptr_ledger_o2_def] >>
  simp[Once ptr_ledger_follow_def, ptr_ledger_nop_edge,
    is_terminator_def, GSYM ptr_ledger_o3_def, ptr_ledger_s3_fields] >>
  simp[Once ptr_ledger_follow_def, ptr_ledger_load_edge,
    is_terminator_def, GSYM ptr_ledger_o4_def] >>
  simp[ptr_ledger_follow_def]
QED

Theorem ptr_ledger_source_entry_history[local]:
  ptr_chrono_history s
    (mk_venom_context [ptr_ledger_probe_source] (SOME "probe"))
    [ptr_ledger_source_entry s] (ptr_ledger_source_entry s)
Proof
  simp[ptr_ledger_source_entry_def, ptr_ledger_probe_source_def,
    GSYM ptr_probe_ctx_def] >>
  irule ptr_probe_entry_history >> simp[]
QED

Theorem ptr_ledger_source_history:
  s.vs_allocas = FEMPTY ==>
  ptr_chrono_history s
    (mk_venom_context [ptr_ledger_probe_source] (SOME "probe"))
    [ptr_ledger_source_entry s; ptr_ledger_o1 s; ptr_ledger_o2 s;
     ptr_ledger_o3 s; ptr_ledger_o4 s] (ptr_ledger_o4 s)
Proof
  strip_tac >>
  qspec_then `s` assume_tac (GEN_ALL ptr_ledger_source_entry_history) >>
  drule (GEN_ALL ptr_ledger_source_follows) >>
  disch_then (qspec_then
    `mk_venom_context [ptr_ledger_probe_source] (SOME "probe")` assume_tac) >>
  drule_all ptr_ledger_follow_history >> simp[]
QED

Definition ptr_ledger_target_entry_def:
  ptr_ledger_target_entry s = ptr_observe [] [] FEMPTY entry_taint
    ptr_ledger_probe_target (mk_inst 10 ASSIGN [Lit 0w] ["p"])
    (ptr_probe_entry_state s)
End
Definition ptr_ledger_t1_def:
  ptr_ledger_t1 s = update_var "p" 0w (ptr_probe_entry_state s) with vs_inst_idx := 1
End
Definition ptr_ledger_t2_def:
  ptr_ledger_t2 s = mstore 0 42w (ptr_ledger_t1 s) with vs_inst_idx := 2
End
Definition ptr_ledger_t3_def:
  ptr_ledger_t3 s = update_var "r" (mload 0 (ptr_ledger_t2 s))
    (ptr_ledger_t2 s) with vs_inst_idx := 3
End

Theorem ptr_ledger_target_active[local,simp]:
  active_inst ptr_ledger_probe_target inst s <=>
    s.vs_current_bb = "entry" /\ s.vs_inst_idx < 4 /\
    EL s.vs_inst_idx
      [mk_inst 10 ASSIGN [Lit 0w] ["p"];
       mk_inst 11 MSTORE [Var "p"; Lit 42w] [];
       mk_inst 13 MLOAD [Var "p"] ["r"];
       mk_inst 14 STOP [] []] = inst
Proof
  simp[active_inst_def, ptr_ledger_probe_target_def, ptr_probe_fn_def,
    mk_raw_function_def, EQ_SYM_EQ]
QED
Theorem ptr_ledger_target_entry_fields[local,simp]:
  (ptr_ledger_target_entry s).po_fn = ptr_ledger_probe_target /\
  (ptr_ledger_target_entry s).po_inst = mk_inst 10 ASSIGN [Lit 0w] ["p"] /\
  (ptr_ledger_target_entry s).po_state = ptr_probe_entry_state s
Proof
  simp[ptr_ledger_target_entry_def, ptr_observe_def]
QED
Theorem ptr_ledger_t1_fields[local,simp]:
  (ptr_ledger_t1 s).vs_current_bb = "entry" /\
  (ptr_ledger_t1 s).vs_inst_idx = 1 /\
  lookup_var "p" (ptr_ledger_t1 s) = SOME 0w
Proof
  simp[ptr_ledger_t1_def, ptr_probe_entry_state_def,
    update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED
Theorem ptr_ledger_t2_fields[local,simp]:
  (ptr_ledger_t2 s).vs_current_bb = "entry" /\
  (ptr_ledger_t2 s).vs_inst_idx = 2 /\
  lookup_var "p" (ptr_ledger_t2 s) = SOME 0w
Proof
  simp[ptr_ledger_t2_def, mstore_preserves, lookup_var_mstore_idx]
QED
Theorem ptr_ledger_t3_fields[local,simp]:
  (ptr_ledger_t3 s).vs_current_bb = "entry" /\
  (ptr_ledger_t3 s).vs_inst_idx = 3
Proof
  simp[ptr_ledger_t3_def, update_var_def]
QED
Theorem ptr_ledger_target_assign_edge[local]:
  step_inst fuel ctx (mk_inst 10 ASSIGN [Lit 0w] ["p"])
    (ptr_probe_entry_state s) = OK (ptr_ledger_t1 s with vs_inst_idx := 0)
Proof
  simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def,
    eval_operand_def, ptr_ledger_t1_def, ptr_probe_entry_state_def, update_var_def]
QED
Theorem ptr_ledger_target_store_edge[local]:
  step_inst fuel ctx (mk_inst 11 MSTORE [Var "p"; Lit 42w] [])
    (ptr_ledger_t1 s) = OK (ptr_ledger_t2 s with vs_inst_idx := 1)
Proof
  simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def,
    exec_write2_def, eval_operand_def, ptr_ledger_t2_def] >>
  simp[ptr_ledger_t1_def, ptr_probe_entry_state_def, update_var_def, mstore_def]
QED
Theorem ptr_ledger_target_load_edge[local]:
  step_inst fuel ctx (mk_inst 13 MLOAD [Var "p"] ["r"])
    (ptr_ledger_t2 s) = OK (ptr_ledger_t3 s with vs_inst_idx := 2)
Proof
  simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def,
    exec_read1_def, eval_operand_def, ptr_ledger_t3_def, update_var_def,
    venom_state_component_equality]
QED

Definition ptr_ledger_q1_def:
  ptr_ledger_q1 s = ptr_ledger_next (ptr_ledger_target_entry s)
    (mk_inst 11 MSTORE [Var "p"; Lit 42w] [])
    (ptr_ledger_t1 s with vs_inst_idx := 0)
End
Definition ptr_ledger_q2_def:
  ptr_ledger_q2 s = ptr_ledger_next (ptr_ledger_q1 s)
    (mk_inst 13 MLOAD [Var "p"] ["r"]) (ptr_ledger_t2 s with vs_inst_idx := 1)
End
Definition ptr_ledger_q3_def:
  ptr_ledger_q3 s = ptr_ledger_next (ptr_ledger_q2 s)
    (mk_inst 14 STOP [] []) (ptr_ledger_t3 s with vs_inst_idx := 2)
End
Theorem ptr_ledger_q1_fields[local,simp]:
  (ptr_ledger_q1 s).po_fn = ptr_ledger_probe_target /\
  (ptr_ledger_q1 s).po_inst = mk_inst 11 MSTORE [Var "p"; Lit 42w] [] /\
  (ptr_ledger_q1 s).po_state = ptr_ledger_t1 s
Proof
  simp[ptr_ledger_q1_def, venom_state_component_equality]
QED
Theorem ptr_ledger_q2_fields[local,simp]:
  (ptr_ledger_q2 s).po_fn = ptr_ledger_probe_target /\
  (ptr_ledger_q2 s).po_inst = mk_inst 13 MLOAD [Var "p"] ["r"] /\
  (ptr_ledger_q2 s).po_state = ptr_ledger_t2 s
Proof
  simp[ptr_ledger_q2_def, venom_state_component_equality]
QED
Theorem ptr_ledger_q3_fields[local,simp]:
  (ptr_ledger_q3 s).po_fn = ptr_ledger_probe_target /\
  (ptr_ledger_q3 s).po_inst = mk_inst 14 STOP [] [] /\
  (ptr_ledger_q3 s).po_state = ptr_ledger_t3 s
Proof
  simp[ptr_ledger_q3_def, venom_state_component_equality]
QED
Theorem ptr_ledger_target_follows:
  ptr_ledger_follow ctx
    [mk_inst 11 MSTORE [Var "p"; Lit 42w] [];
     mk_inst 13 MLOAD [Var "p"] ["r"];
     mk_inst 14 STOP [] []] (ptr_ledger_target_entry s) =
    SOME [ptr_ledger_q1 s; ptr_ledger_q2 s; ptr_ledger_q3 s]
Proof
  simp[Once ptr_ledger_follow_def, ptr_ledger_target_assign_edge,
    is_terminator_def, GSYM ptr_ledger_q1_def] >>
  simp[Once ptr_ledger_follow_def, ptr_ledger_target_store_edge,
    is_terminator_def, GSYM ptr_ledger_q2_def] >>
  simp[Once ptr_ledger_follow_def, ptr_ledger_target_load_edge,
    is_terminator_def, GSYM ptr_ledger_q3_def] >>
  simp[ptr_ledger_follow_def]
QED

Theorem ptr_ledger_target_entry_history[local]:
  ptr_chrono_history s
    (mk_venom_context [ptr_ledger_probe_target] (SOME "probe"))
    [ptr_ledger_target_entry s] (ptr_ledger_target_entry s)
Proof
  simp[ptr_ledger_target_entry_def] >> irule (cj 1 ptr_chrono_history_rules) >>
  simp[ptr_ledger_probe_target_def, ptr_probe_fn_def, ptr_probe_entry_state_def,
    mk_venom_context_def, mk_raw_function_def, lookup_function_def,
    fn_entry_label_def, enters_block_def, active_inst_def, lookup_block_def,
    eval_phis_def, phi_prefix_length_def, FIND_def, INDEX_FIND_def,
    entry_block_def, mk_inst_def]
QED

Theorem ptr_ledger_target_history:
  ptr_chrono_history s
    (mk_venom_context [ptr_ledger_probe_target] (SOME "probe"))
    [ptr_ledger_target_entry s; ptr_ledger_q1 s; ptr_ledger_q2 s;
     ptr_ledger_q3 s] (ptr_ledger_q3 s)
Proof
  qspec_then `s` assume_tac (GEN_ALL ptr_ledger_target_entry_history) >>
  `ptr_ledger_follow (mk_venom_context [ptr_ledger_probe_target] (SOME "probe"))
    [mk_inst 11 MSTORE [Var "p"; Lit 42w] [];
     mk_inst 13 MLOAD [Var "p"] ["r"];
     mk_inst 14 STOP [] []] (ptr_ledger_target_entry s) =
    SOME [ptr_ledger_q1 s; ptr_ledger_q2 s; ptr_ledger_q3 s]` by
    simp[ptr_ledger_target_follows] >>
  drule_all ptr_ledger_follow_history >> simp[]
QED

Theorem ptr_ledger_read_ranges:
  source_memory_read_ranges (ptr_ledger_o3 s).po_inst
    (ptr_ledger_o3 s).po_state =
      [(w2n (n2w s.vs_alloca_next : bytes32),32)] /\
  source_memory_read_ranges (ptr_ledger_q2 s).po_inst
    (ptr_ledger_q2 s).po_state = [(0,32)]
Proof
  simp[source_memory_read_ranges_def, mk_inst_def, eval_operand_def]
QED

Theorem ptr_ledger_o2_memory_taint[local]:
  (ptr_ledger_o2 s).po_taint.t_mem =
    (ptr_ledger_o1 s).po_taint.t_mem DIFF
      range_bytes [(w2n (n2w s.vs_alloca_next : bytes32),32)]
Proof
  simp[ptr_ledger_o2_def, ptr_ledger_next_def, ptr_observe_def,
    step_taint_def, mem_taint_def, mk_inst_def, step_writes_def,
    source_memory_write_ranges_def, fixed_source_write_range_def,
    eval_operand_def, written_taint_def, op_taint_def, new_site_bytes_def,
    ptr_ledger_s2_def, mstore_preserves] >>
  simp[FLOOKUP_DEF] >> SET_TAC[]
QED

Theorem ptr_ledger_o3_memory_taint[local]:
  (ptr_ledger_o3 s).po_taint.t_mem = (ptr_ledger_o2 s).po_taint.t_mem
Proof
  simp[ptr_ledger_o3_def, ptr_ledger_next_def, ptr_observe_def,
    step_taint_def, mem_taint_def, mk_inst_def, step_writes_def,
    source_memory_write_ranges_def, written_taint_def, new_site_bytes_def,
    FLOOKUP_DEF, range_bytes_def] >> SET_TAC[]
QED

Theorem ptr_ledger_source_read_demand:
  ptr_ledger_read_demand (ptr_ledger_o3 s) =
    range_bytes [(w2n (n2w s.vs_alloca_next : bytes32),32)]
Proof
  simp[ptr_ledger_read_demand_def, ptr_ledger_read_ranges,
    ptr_ledger_o3_memory_taint, ptr_ledger_o2_memory_taint] >> SET_TAC[]
QED

Theorem ptr_ledger_target_read_demand:
  ptr_ledger_read_demand (ptr_ledger_q2 s) = range_bytes [(0,32)]
Proof
  simp[ptr_ledger_read_demand_def, ptr_ledger_read_ranges,
    ptr_ledger_q2_def, ptr_ledger_next_def, ptr_observe_def,
    step_taint_def, mem_taint_def, mk_inst_def, step_writes_def,
    source_memory_write_ranges_def, fixed_source_write_range_def,
    eval_operand_def, written_taint_def, op_taint_def, new_site_bytes_def,
    ptr_ledger_t2_def, mstore_preserves, FLOOKUP_DEF] >> SET_TAC[]
QED

(* The paired write supplies these bytes regardless of initial memory. *)
Theorem ptr_ledger_written_bytes:
  k < 32 ==>
  read_byte (w2n (n2w s.vs_alloca_next : bytes32) + k)
    (ptr_ledger_s2 s).vs_memory =
  read_byte k (ptr_ledger_t2 s).vs_memory
Proof
  strip_tac >>
  simp[ptr_ledger_s2_def, ptr_ledger_t2_def, mstore_eq_write_mem,
    read_byte_write_memory_with_expansion]
QED

Theorem ptr_ledger_read_bytes:
  k < 32 ==>
  read_byte (w2n (n2w s.vs_alloca_next : bytes32) + k)
    (ptr_ledger_o3 s).po_state.vs_memory =
  read_byte k (ptr_ledger_q2 s).po_state.vs_memory
Proof
  strip_tac >>
  qspecl_then [`s`, `k`] mp_tac (GEN_ALL ptr_ledger_written_bytes) >>
  simp[ptr_ledger_s3_def]
QED

Theorem ptr_ledger_paired_store_steps[local]:
  ptr_chrono_step C (ptr_ledger_o1 s) (ptr_ledger_o2 s) /\
  ptr_chrono_step Ct (ptr_ledger_q1 s) (ptr_ledger_q2 s)
Proof
  conj_tac
  >- (pure_rewrite_tac[ptr_ledger_o2_def] >> irule ptr_ledger_next_step >>
      simp[ptr_ledger_store_edge, is_terminator_def, ptr_ledger_s2_fields]) >>
  pure_rewrite_tac[ptr_ledger_q2_def] >> irule ptr_ledger_next_step >>
  simp[ptr_ledger_target_store_edge, is_terminator_def, ptr_ledger_t2_fields]
QED

Theorem ptr_ledger_probe_write_pair:
  ptr_ledger_write_pair C Ct
    (\i. i - w2n (n2w s.vs_alloca_next : bytes32))
    (ptr_ledger_o1 s) (ptr_ledger_o2 s)
    (ptr_ledger_q1 s) (ptr_ledger_q2 s)
Proof
  simp[ptr_ledger_write_pair_def, ptr_ledger_paired_store_steps,
    step_writes_def, is_terminator_def, mk_inst_def,
    source_memory_write_ranges_def, fixed_source_write_range_def,
    eval_operand_def, ptr_bytes_agree_def, range_bytes_def] >>
  rpt strip_tac >> gvs[] >>
  qspecl_then [`s`, `i - w2n (n2w s.vs_alloca_next : bytes32)`]
    mp_tac (GEN_ALL ptr_ledger_written_bytes) >> simp[]
QED

Definition ptr_ledger_probe_registry_def:
  ptr_ledger_probe_registry = FEMPTY |+ (0:num,
    <| pla_source := ptr_ledger_probe_source;
       pla_target := ptr_ledger_probe_target;
       pla_parent := NONE; pla_call := NONE; pla_target_entry := 0 |>)
End

Definition ptr_ledger_probe_births_def:
  ptr_ledger_probe_births s =
    (FEMPTY : (num # num,num # num) fmap) |+ ((0,10), (s.vs_alloca_next,32))
End

Theorem ptr_ledger_probe_owned_site:
  ptr_ledger_owned_site ptr_ledger_probe_registry (ptr_ledger_probe_births s)
    0 10 s.vs_alloca_next 32 0
Proof
  simp[ptr_ledger_owned_site_def, ptr_ledger_probe_registry_def,
    ptr_ledger_probe_births_def, FLOOKUP_UPDATE, ptr_ledger_probe_target_def]
QED

Theorem ptr_ledger_probe_birth_actual:
  FLOOKUP (ptr_ledger_o1 s).po_state.vs_allocas 10 =
    FLOOKUP (ptr_ledger_probe_births s) (0,10)
Proof
  simp[ptr_ledger_probe_births_def, ptr_ledger_s1_def,
    ptr_probe_allocated_state_def, ptr_probe_entry_state_def,
    update_var_def, FLOOKUP_UPDATE]
QED

Theorem ptr_ledger_probe_owner_erasure:
  ptr_ledger_erases (ptr_ledger_probe_births s)
    (FEMPTY |+ ("p",(0,10))) (ptr_ledger_o1 s).po_prov
Proof
  simp[ptr_ledger_erases_def, ptr_ledger_probe_births_def,
    ptr_ledger_o1_def, ptr_ledger_next_def, ptr_observe_def,
    ptr_ledger_source_entry_def, step_prov_def, mk_inst_def,
    ptr_ledger_s1_def, ptr_probe_allocated_state_def, update_var_def,
    FLOOKUP_UPDATE] >>
  simp[set_prov_def, out_prov_def, ptr_probe_entry_state_def,
    FLOOKUP_UPDATE] >> gen_tac >> Cases_on `v = "p"` >> simp[]
QED

Theorem ptr_ledger_probe_owner_read_erasure:
  ptr_ledger_erases (ptr_ledger_probe_births s)
    (FEMPTY |+ ("p",(0,10))) (ptr_ledger_o3 s).po_prov
Proof
  ` (ptr_ledger_o3 s).po_prov = (ptr_ledger_o1 s).po_prov` by
    simp[ptr_ledger_o3_def, ptr_ledger_o2_def, ptr_ledger_next_def,
      ptr_observe_def, step_prov_def, mk_inst_def, set_prov_def,
      fmap_EXT, DRESTRICT_DEF] >>
  simp[ptr_ledger_probe_owner_erasure]
QED

Theorem ptr_ledger_probe_owned_read_byte:
  s.vs_alloca_next < dimword (:256) /\ k < 32 ==>
  ptr_ledger_owned_byte ptr_ledger_probe_registry (ptr_ledger_probe_births s)
    0 10 k (w2n (n2w s.vs_alloca_next : bytes32) + k) k
Proof
  strip_tac >> simp[ptr_ledger_owned_byte_def] >>
  qexists_tac `32` >> simp[ptr_ledger_probe_owned_site]
QED

Theorem ptr_ledger_probe_alignment:
  ptr_ledger_block_alignment (FEMPTY |+ (Allocation 10,0))
    (HD ptr_ledger_probe_source.fn_blocks).bb_instructions
    (HD ptr_ledger_probe_target.fn_blocks).bb_instructions [0;1;3;4]
Proof
  EVAL_TAC
QED

Theorem ptr_ledger_read_var_lookups[local]:
  lookup_var v (ptr_ledger_s3 s) =
    (if v = "p" then SOME (n2w s.vs_alloca_next : bytes32)
     else lookup_var v s) /\
  lookup_var v (ptr_ledger_t2 s) =
    (if v = "p" then SOME 0w else lookup_var v s)
Proof
  simp[ptr_ledger_s3_def, ptr_ledger_s2_def, ptr_ledger_t2_def,
    lookup_var_mstore_idx] >>
  simp[ptr_ledger_s1_def, ptr_ledger_t1_def,
    ptr_probe_allocated_state_def, ptr_probe_entry_state_def,
    update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem ptr_ledger_read_vars[local]:
  reloc (s.vs_alloca_next,32) = SOME (0w : bytes32) ==>
  ptr_prefix_vars reloc (ptr_ledger_o3 s).po_prov
    (ptr_ledger_o3 s).po_taint.t_var
    (ptr_ledger_o3 s).po_state (ptr_ledger_q2 s).po_state
Proof
  strip_tac >>
  qspec_then `s` mp_tac (GEN_ALL ptr_ledger_probe_owner_read_erasure) >>
  simp[ptr_ledger_erases_def, ptr_ledger_probe_births_def, FLOOKUP_UPDATE] >>
  strip_tac >> pure_rewrite_tac[ptr_prefix_vars_def] >> gen_tac >>
  pure_rewrite_tac[ptr_ledger_read_var_lookups] >>
  first_x_assum (qspec_then `v` assume_tac) >>
  Cases_on `v = "p"`
  >- (asm_simp_tac bool_ss [ptr_prefix_value_def, WORD_SUB_REFL,
        WORD_SUB_RZERO, optionTheory.option_CLAUSES, pairTheory.PAIR_EQ,
        pairTheory.pair_case_thm, optionTheory.option_case_def]) >>
  Cases_on `lookup_var v s` >>
  simp[ptr_prefix_value_def, word_agree_except_def]
QED

Definition ptr_ledger_root_read_ready_def:
  ptr_ledger_root_read_ready C Ct s R B G rho reloc <=>
    R = ptr_ledger_probe_registry /\ B = ptr_ledger_probe_births s /\
    G = (FEMPTY |+ ("p",(0,10))) /\
    ptr_ledger_erases B G (ptr_ledger_o3 s).po_prov /\
    ptr_ledger_owned_site R B 0 10 s.vs_alloca_next 32 0 /\
    ptr_ledger_write_pair C Ct rho (ptr_ledger_o1 s) (ptr_ledger_o2 s)
      (ptr_ledger_q1 s) (ptr_ledger_q2 s) /\
    (!i. i IN ptr_ledger_read_demand (ptr_ledger_o3 s) ==>
      ?k. k < 32 /\ ptr_ledger_owned_byte R B 0 10 k i (rho i)) /\
    ptr_bytes_agree (ptr_ledger_read_demand (ptr_ledger_o3 s)) rho
      (ptr_ledger_o3 s).po_state.vs_memory (ptr_ledger_q2 s).po_state.vs_memory /\
    reloc (s.vs_alloca_next,32) = SOME (0w : bytes32) /\
    ptr_prefix_vars reloc (ptr_ledger_o3 s).po_prov
      (ptr_ledger_o3 s).po_taint.t_var
      (ptr_ledger_o3 s).po_state (ptr_ledger_q2 s).po_state
End

Theorem ptr_ledger_root_read_ready_exists:
  s.vs_alloca_next < dimword (:256) ==>
  ?R B G rho reloc. ptr_ledger_root_read_ready C Ct s R B G rho reloc
Proof
  strip_tac >>
  qexistsl_tac [`ptr_ledger_probe_registry`, `ptr_ledger_probe_births s`,
    `FEMPTY |+ ("p",(0,10))`,
    `\i. i - w2n (n2w s.vs_alloca_next : bytes32)`,
    `\site. if site = (s.vs_alloca_next,32) then SOME (0w : bytes32) else NONE`] >>
  simp[ptr_ledger_root_read_ready_def, ptr_ledger_probe_owner_read_erasure,
    ptr_ledger_probe_owned_site, ptr_ledger_probe_write_pair, ptr_ledger_read_vars] >>
  conj_tac
  >- (simp[ptr_ledger_source_read_demand, range_bytes_def] >>
      rpt strip_tac >> qexists_tac `i - s.vs_alloca_next` >>
      qspecl_then [`s`, `i - s.vs_alloca_next`] mp_tac
        (GEN_ALL ptr_ledger_probe_owned_read_byte) >> simp[]) >>
  simp[ptr_bytes_agree_def, ptr_ledger_source_read_demand, range_bytes_def] >>
  rpt strip_tac >>
  qspecl_then [`s`, `i - s.vs_alloca_next`] mp_tac
    (GEN_ALL ptr_ledger_read_bytes) >> simp[]
QED
