Theory concretizePtrReadInterferenceProbe
Ancestors concretizePtrLedgerProbe concretizePtrPrefixProbe
  concretizePtrLoadTransport concretizePtrPlacementBounds concretizeMemLocDefs
  concretizePtrStoreSteps spillSim
  concretizePtrChronologicalHistory codegenRel contextCodegenRel venomMemProps mem2varBlockSimHelpers
  venomState venomExecSemantics venomInst ptrDiscipline list words finite_map

Theorem ptr_interference_size_eval[local]:
  w2n (32w : bytes32) = 32
Proof
  simp[dimword_def]
QED

val _ = computeLib.add_funs [ptr_interference_size_eval];

Definition ptr_interference_source_def:
  ptr_interference_source = ptr_probe_fn
    [mk_inst 20 ALLOCA [Lit 32w] ["a"];
     mk_inst 21 ALLOCA [Lit 32w] ["b"];
     mk_inst 22 MSTORE [Var "a"; Lit 42w] [];
     mk_inst 23 NOP [] [];
     mk_inst 24 MSTORE [Var "b"; Lit 99w] [];
     mk_inst 25 MLOAD [Var "a"] ["r"];
     mk_inst 26 STOP [] []]
End

Definition ptr_interference_target_def:
  ptr_interference_target = (ptr_probe_fn
    [mk_inst 20 ASSIGN [Lit 32w] ["a"];
     mk_inst 21 ASSIGN [Lit 0w] ["b"];
     mk_inst 22 MSTORE [Var "a"; Lit 42w] [];
     mk_inst 24 MSTORE [Var "b"; Lit 99w] [];
     mk_inst 25 MLOAD [Var "a"] ["r"];
     mk_inst 26 STOP [] []]) with
    <|fn_eom := SOME 64;
      fn_mems_used := [(Allocation 20,32,32); (Allocation 21,0,32)]|>
End

Theorem ptr_interference_cfg:
  cfg_analyze ptr_interference_source =
    <|cfg_succs := FEMPTY |+ ("entry",[]) |+ ("entry",[]);
      cfg_preds := FEMPTY |+ ("entry",[]);
      cfg_reachable := FEMPTY |+ ("entry",T);
      cfg_dfs_post := ["entry"]; cfg_dfs_pre := ["entry"]|>
Proof
  EVAL_TAC
QED

Theorem ptr_interference_bp:
  bp_analyze_fuel 10 (cfg_analyze ptr_interference_source)
    ptr_interference_source =
    FEMPTY |+ ("a",[Ptr (Allocation 20) (SOME 0)])
           |+ ("b",[Ptr (Allocation 21) (SOME 0)])
           |+ ("a",[Ptr (Allocation 20) (SOME 0)])
           |+ ("b",[Ptr (Allocation 21) (SOME 0)])
Proof
  rewrite_tac[ptr_interference_cfg] >> EVAL_TAC
QED

Theorem ptr_interference_shape[local]:
  ~fn_has_static_layout ptr_interference_source /\
  fn_needs_liveness_allocation ptr_interference_source /\
  static_alloca_items ptr_interference_source =
    SOME [(Allocation 20,32); (Allocation 21,32)] /\
  ptr_interference_source.fn_forced_alloc_positions = FEMPTY /\
  imported_mems_used
    (mk_venom_context [ptr_interference_source] (SOME "probe"))
    ptr_interference_source = []
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem ptr_interference_livesets[local]:
  context_mem_livesets 10
    (mk_venom_context [ptr_interference_source] (SOME "probe"))
    ptr_interference_source
    (bp_analyze_fuel 10 (cfg_analyze ptr_interference_source) ptr_interference_source)
    (cfg_analyze ptr_interference_source) =
    FEMPTY |+ (Allocation 20,[("entry",2)])
      |+ (Allocation 20,[("entry",2);("entry",3)])
      |+ (Allocation 20,[("entry",2);("entry",3);("entry",4);("entry",5)])
      |+ (Allocation 21,[("entry",4)])
Proof
  rewrite_tac[ptr_interference_bp, ptr_interference_cfg] >>
  CONV_TAC (LAND_CONV EVAL) >> simp[dimword_def] >> EVAL_TAC >>
  simp[fmap_EXT, FAPPLY_FUPDATE_THM]
QED

Theorem ptr_interference_production_transform:
  concretize_function_fuel_in_context 10
    (mk_venom_context [ptr_interference_source] (SOME "probe")) []
    ptr_interference_source = SOME ptr_interference_target
Proof
  EVAL_TAC >> simp[dimword_def] >> EVAL_TAC
QED

Definition ptr_interference_entry_def:
  ptr_interference_entry fn s = ptr_observe [] [] FEMPTY entry_taint fn
    (HD (fn_insts fn)) (ptr_probe_entry_state s)
End

Definition ptr_interference_suffix_def:
  ptr_interference_suffix fn = TAKE (LENGTH (fn_insts fn) - 2) (TL (fn_insts fn))
End

Theorem ptr_interference_source_active[local,simp]:
  active_inst ptr_interference_source inst s <=>
    s.vs_current_bb = "entry" /\ s.vs_inst_idx < 7 /\
    EL s.vs_inst_idx
      [mk_inst 20 ALLOCA [Lit 32w] ["a"];
       mk_inst 21 ALLOCA [Lit 32w] ["b"];
       mk_inst 22 MSTORE [Var "a"; Lit 42w] [];
       mk_inst 23 NOP [] [];
       mk_inst 24 MSTORE [Var "b"; Lit 99w] [];
       mk_inst 25 MLOAD [Var "a"] ["r"];
       mk_inst 26 STOP [] []] = inst
Proof
  simp[active_inst_def, ptr_interference_source_def, ptr_probe_fn_def,
    mk_raw_function_def, EQ_SYM_EQ]
QED

Definition ptr_interference_s1_def:
  ptr_interference_s1 s = ptr_probe_allocated_state 20 "a" (32w : bytes32)
    (ptr_probe_entry_state s) with vs_inst_idx := 1
End
Definition ptr_interference_s2_def:
  ptr_interference_s2 s = ptr_probe_allocated_state 21 "b" (32w : bytes32)
    (ptr_interference_s1 s) with vs_inst_idx := 2
End
Definition ptr_interference_s3_def:
  ptr_interference_s3 s = mstore (w2n (n2w s.vs_alloca_next : bytes32)) 42w
    (ptr_interference_s2 s) with vs_inst_idx := 3
End
Definition ptr_interference_s4_def:
  ptr_interference_s4 s = ptr_interference_s3 s with vs_inst_idx := 4
End
Definition ptr_interference_s5_def:
  ptr_interference_s5 s =
    mstore (w2n (n2w (s.vs_alloca_next + 32) : bytes32)) 99w
      (ptr_interference_s4 s) with vs_inst_idx := 5
End

Theorem ptr_interference_source_fields[local,simp]:
  (ptr_interference_s1 s).vs_current_bb = "entry" /\
  (ptr_interference_s1 s).vs_inst_idx = 1 /\
  (ptr_interference_s2 s).vs_current_bb = "entry" /\
  (ptr_interference_s2 s).vs_inst_idx = 2 /\
  (ptr_interference_s3 s).vs_current_bb = "entry" /\
  (ptr_interference_s3 s).vs_inst_idx = 3 /\
  (ptr_interference_s4 s).vs_current_bb = "entry" /\
  (ptr_interference_s4 s).vs_inst_idx = 4 /\
  (ptr_interference_s5 s).vs_current_bb = "entry" /\
  (ptr_interference_s5 s).vs_inst_idx = 5
Proof
  simp[ptr_interference_s1_def, ptr_interference_s2_def,
    ptr_interference_s3_def, ptr_interference_s4_def, ptr_interference_s5_def,
    ptr_probe_allocated_state_def, ptr_probe_entry_state_def,
    update_var_def, mstore_preserves]
QED

Theorem ptr_interference_alloca_edges[local]:
  s.vs_allocas = FEMPTY ==>
  step_inst fuel ctx (mk_inst 20 ALLOCA [Lit 32w] ["a"])
    (ptr_probe_entry_state s) = OK (ptr_interference_s1 s with vs_inst_idx := 0) /\
  step_inst fuel ctx (mk_inst 21 ALLOCA [Lit 32w] ["b"])
    (ptr_interference_s1 s) = OK (ptr_interference_s2 s with vs_inst_idx := 1)
Proof
  strip_tac >> conj_tac
  >- simp[ptr_probe_alloca_step, ptr_probe_entry_state_def, ptr_interference_s1_def,
      ptr_probe_allocated_state_def, update_var_def] >>
  `FLOOKUP (ptr_interference_s1 s).vs_allocas 21 = NONE` by
    simp[ptr_interference_s1_def, ptr_probe_allocated_state_def,
      ptr_probe_entry_state_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[ptr_probe_alloca_step, ptr_interference_s2_def,
    ptr_probe_allocated_state_def, update_var_def,
    venom_state_component_equality]
QED

Theorem ptr_interference_source_vars[local,simp]:
  lookup_var "a" (ptr_interference_s2 s) = SOME (n2w s.vs_alloca_next : bytes32) /\
  lookup_var "b" (ptr_interference_s4 s) =
    SOME (n2w (s.vs_alloca_next + 32) : bytes32)
Proof
  simp[ptr_interference_s4_def, ptr_interference_s3_def, lookup_var_mstore_idx] >>
  simp[ptr_interference_s2_def, ptr_interference_s1_def,
    ptr_probe_allocated_state_def, ptr_probe_entry_state_def,
    lookup_var_def, update_var_def, FLOOKUP_UPDATE, ptr_interference_size_eval]
QED

Theorem ptr_interference_store_edges[local]:
  step_inst fuel ctx (mk_inst 22 MSTORE [Var "a"; Lit 42w] [])
    (ptr_interference_s2 s) = OK (ptr_interference_s3 s with vs_inst_idx := 2) /\
  step_inst fuel ctx (mk_inst 24 MSTORE [Var "b"; Lit 99w] [])
    (ptr_interference_s4 s) = OK (ptr_interference_s5 s with vs_inst_idx := 4)
Proof
  simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def,
    exec_write2_def, eval_operand_def, ptr_interference_s3_def,
    ptr_interference_s5_def] >>
  simp[venom_state_component_equality] >>
  simp[mstore_def]
QED

Definition ptr_interference_o1_def:
  ptr_interference_o1 s = ptr_ledger_next (ptr_interference_entry ptr_interference_source s)
    (mk_inst 21 ALLOCA [Lit 32w] ["b"]) (ptr_interference_s1 s with vs_inst_idx := 0)
End
Definition ptr_interference_o2_def:
  ptr_interference_o2 s = ptr_ledger_next (ptr_interference_o1 s)
    (mk_inst 22 MSTORE [Var "a"; Lit 42w] []) (ptr_interference_s2 s with vs_inst_idx := 1)
End
Definition ptr_interference_o3_def:
  ptr_interference_o3 s = ptr_ledger_next (ptr_interference_o2 s)
    (mk_inst 23 NOP [] []) (ptr_interference_s3 s with vs_inst_idx := 2)
End
Definition ptr_interference_o4_def:
  ptr_interference_o4 s = ptr_ledger_next (ptr_interference_o3 s)
    (mk_inst 24 MSTORE [Var "b"; Lit 99w] []) (ptr_interference_s3 s)
End
Definition ptr_interference_o5_def:
  ptr_interference_o5 s = ptr_ledger_next (ptr_interference_o4 s)
    (mk_inst 25 MLOAD [Var "a"] ["r"]) (ptr_interference_s5 s with vs_inst_idx := 4)
End

Theorem ptr_interference_entry_fields[local,simp]:
  (ptr_interference_entry ptr_interference_source s).po_fn = ptr_interference_source /\
  (ptr_interference_entry ptr_interference_source s).po_inst =
    mk_inst 20 ALLOCA [Lit 32w] ["a"] /\
  (ptr_interference_entry ptr_interference_source s).po_state = ptr_probe_entry_state s
Proof
  simp[ptr_interference_entry_def, ptr_observe_def, ptr_interference_source_def,
    fn_insts_def, fn_insts_blocks_def, ptr_probe_fn_def, mk_raw_function_def]
QED

Theorem ptr_interference_observation_states[local,simp]:
  (ptr_interference_o1 s).po_state = ptr_interference_s1 s /\
  (ptr_interference_o2 s).po_state = ptr_interference_s2 s /\
  (ptr_interference_o3 s).po_state = ptr_interference_s3 s /\
  (ptr_interference_o4 s).po_state = ptr_interference_s4 s /\
  (ptr_interference_o5 s).po_state = ptr_interference_s5 s
Proof
  conj_asm1_tac
  >- simp[ptr_interference_o1_def, ptr_ledger_next_def, ptr_observe_def,
      ptr_probe_entry_state_def, venom_state_component_equality] >>
  conj_asm1_tac
  >- simp[ptr_interference_o2_def, ptr_ledger_next_def, ptr_observe_def,
      venom_state_component_equality] >>
  conj_asm1_tac
  >- simp[ptr_interference_o3_def, ptr_ledger_next_def, ptr_observe_def,
      venom_state_component_equality] >>
  conj_asm1_tac
  >- simp[ptr_interference_o4_def, ptr_ledger_next_def, ptr_observe_def,
      ptr_interference_s4_def] >>
  simp[ptr_interference_o5_def, ptr_ledger_next_def, ptr_observe_def,
    venom_state_component_equality]
QED

Theorem ptr_interference_observation_cursors[local,simp]:
  (ptr_interference_o1 s).po_fn = ptr_interference_source /\
  (ptr_interference_o2 s).po_fn = ptr_interference_source /\
  (ptr_interference_o3 s).po_fn = ptr_interference_source /\
  (ptr_interference_o4 s).po_fn = ptr_interference_source /\
  (ptr_interference_o5 s).po_fn = ptr_interference_source /\
  (ptr_interference_o1 s).po_inst = mk_inst 21 ALLOCA [Lit 32w] ["b"] /\
  (ptr_interference_o2 s).po_inst = mk_inst 22 MSTORE [Var "a"; Lit 42w] [] /\
  (ptr_interference_o3 s).po_inst = mk_inst 23 NOP [] [] /\
  (ptr_interference_o4 s).po_inst = mk_inst 24 MSTORE [Var "b"; Lit 99w] [] /\
  (ptr_interference_o5 s).po_inst = mk_inst 25 MLOAD [Var "a"] ["r"]
Proof
  simp[ptr_interference_o5_def, ptr_ledger_next_def, ptr_observe_def] >>
  simp[ptr_interference_o4_def, ptr_ledger_next_def, ptr_observe_def] >>
  simp[ptr_interference_o3_def, ptr_ledger_next_def, ptr_observe_def] >>
  simp[ptr_interference_o2_def, ptr_ledger_next_def, ptr_observe_def] >>
  simp[ptr_interference_o1_def, ptr_ledger_next_def, ptr_observe_def]
QED

Theorem ptr_interference_source_follows:
  s.vs_allocas = FEMPTY ==>
  ptr_ledger_follow ctx (ptr_interference_suffix ptr_interference_source)
    (ptr_interference_entry ptr_interference_source s) =
  SOME [ptr_interference_o1 s; ptr_interference_o2 s; ptr_interference_o3 s;
    ptr_interference_o4 s; ptr_interference_o5 s]
Proof
  strip_tac >>
  `ptr_interference_suffix ptr_interference_source =
     [mk_inst 21 ALLOCA [Lit 32w] ["b"];
      mk_inst 22 MSTORE [Var "a"; Lit 42w] [];
      mk_inst 23 NOP [] []; mk_inst 24 MSTORE [Var "b"; Lit 99w] [];
      mk_inst 25 MLOAD [Var "a"] ["r"]]` by EVAL_TAC >>
  simp[Once ptr_ledger_follow_def, ptr_interference_alloca_edges,
    is_terminator_def, GSYM ptr_interference_o1_def] >>
  simp[ptr_probe_entry_state_def] >>
  simp[Once ptr_ledger_follow_def, ptr_interference_alloca_edges,
    is_terminator_def, GSYM ptr_interference_o2_def] >>
  simp[Once ptr_ledger_follow_def, ptr_interference_store_edges,
    is_terminator_def, GSYM ptr_interference_o3_def] >>
  `step_inst 0 ctx (mk_inst 23 NOP [] []) (ptr_interference_s3 s) =
    OK (ptr_interference_s3 s)` by
    simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def] >>
  simp[Once ptr_ledger_follow_def,
    is_terminator_def, GSYM ptr_interference_o4_def,
    GSYM ptr_interference_s4_def] >>
  simp[Once ptr_ledger_follow_def, ptr_interference_store_edges,
    is_terminator_def, GSYM ptr_interference_o5_def] >>
  simp[ptr_ledger_follow_def]
QED

Theorem ptr_interference_source_history:
  s.vs_allocas = FEMPTY ==>
  ptr_chrono_history s
    (mk_venom_context [ptr_interference_source] (SOME "probe"))
    [ptr_interference_entry ptr_interference_source s;
     ptr_interference_o1 s; ptr_interference_o2 s; ptr_interference_o3 s;
     ptr_interference_o4 s; ptr_interference_o5 s] (ptr_interference_o5 s)
Proof
  strip_tac >>
  `ptr_chrono_history s
     (mk_venom_context [ptr_interference_source] (SOME "probe"))
     [ptr_interference_entry ptr_interference_source s]
     (ptr_interference_entry ptr_interference_source s)` by
    (simp[ptr_interference_entry_def, ptr_interference_source_def,
       fn_insts_def, fn_insts_blocks_def, ptr_probe_fn_def, mk_raw_function_def] >>
     simp[GSYM mk_raw_function_def, GSYM ptr_probe_fn_def, GSYM ptr_probe_ctx_def] >>
     irule ptr_probe_entry_history >> simp[]) >>
  drule (GEN_ALL ptr_interference_source_follows) >>
  disch_then (qspec_then
    `mk_venom_context [ptr_interference_source] (SOME "probe")` assume_tac) >>
  drule_all ptr_ledger_follow_history >> simp[]
QED

Definition ptr_interference_t1_def:
  ptr_interference_t1 s = update_var "a" 32w (ptr_probe_entry_state s) with vs_inst_idx := 1
End
Definition ptr_interference_t2_def:
  ptr_interference_t2 s = update_var "b" 0w (ptr_interference_t1 s) with vs_inst_idx := 2
End
Definition ptr_interference_t3_def:
  ptr_interference_t3 s = mstore 32 42w (ptr_interference_t2 s) with vs_inst_idx := 3
End
Definition ptr_interference_t4_def:
  ptr_interference_t4 s = mstore 0 99w (ptr_interference_t3 s) with vs_inst_idx := 4
End

Theorem ptr_interference_target_active[local,simp]:
  active_inst ptr_interference_target inst s <=>
    s.vs_current_bb = "entry" /\ s.vs_inst_idx < 6 /\
    EL s.vs_inst_idx
      [mk_inst 20 ASSIGN [Lit 32w] ["a"];
       mk_inst 21 ASSIGN [Lit 0w] ["b"];
       mk_inst 22 MSTORE [Var "a"; Lit 42w] [];
       mk_inst 24 MSTORE [Var "b"; Lit 99w] [];
       mk_inst 25 MLOAD [Var "a"] ["r"];
       mk_inst 26 STOP [] []] = inst
Proof
  simp[active_inst_def, ptr_interference_target_def, ptr_probe_fn_def,
    mk_raw_function_def, EQ_SYM_EQ]
QED

Theorem ptr_interference_target_fields[local,simp]:
  (ptr_interference_t1 s).vs_current_bb = "entry" /\
  (ptr_interference_t1 s).vs_inst_idx = 1 /\
  (ptr_interference_t2 s).vs_current_bb = "entry" /\
  (ptr_interference_t2 s).vs_inst_idx = 2 /\
  (ptr_interference_t3 s).vs_current_bb = "entry" /\
  (ptr_interference_t3 s).vs_inst_idx = 3 /\
  (ptr_interference_t4 s).vs_current_bb = "entry" /\
  (ptr_interference_t4 s).vs_inst_idx = 4
Proof
  simp[ptr_interference_t1_def, ptr_interference_t2_def,
    ptr_interference_t3_def, ptr_interference_t4_def,
    ptr_probe_entry_state_def, update_var_def, mstore_preserves]
QED

Theorem ptr_interference_target_vars[local,simp]:
  lookup_var "a" (ptr_interference_t2 s) = SOME 32w /\
  lookup_var "b" (ptr_interference_t3 s) = SOME 0w
Proof
  simp[ptr_interference_t3_def, lookup_var_mstore_idx] >>
  simp[ptr_interference_t2_def, ptr_interference_t1_def,
    lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem ptr_interference_target_edges[local]:
  step_inst fuel ctx (mk_inst 20 ASSIGN [Lit 32w] ["a"])
    (ptr_probe_entry_state s) = OK (ptr_interference_t1 s with vs_inst_idx := 0) /\
  step_inst fuel ctx (mk_inst 21 ASSIGN [Lit 0w] ["b"])
    (ptr_interference_t1 s) = OK (ptr_interference_t2 s with vs_inst_idx := 1) /\
  step_inst fuel ctx (mk_inst 22 MSTORE [Var "a"; Lit 42w] [])
    (ptr_interference_t2 s) = OK (ptr_interference_t3 s with vs_inst_idx := 2) /\
  step_inst fuel ctx (mk_inst 24 MSTORE [Var "b"; Lit 99w] [])
    (ptr_interference_t3 s) = OK (ptr_interference_t4 s with vs_inst_idx := 3)
Proof
  conj_tac
  >- simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def, eval_operand_def,
      ptr_interference_t1_def, ptr_probe_entry_state_def, update_var_def] >>
  conj_tac
  >- simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def, eval_operand_def,
      ptr_interference_t2_def, update_var_def, venom_state_component_equality] >>
  simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def,
    exec_write2_def, eval_operand_def] >>
  simp[ptr_interference_t3_def, ptr_interference_t4_def, dimword_def] >>
  simp[venom_state_component_equality] >> simp[mstore_def]
QED

Definition ptr_interference_q1_def:
  ptr_interference_q1 s = ptr_ledger_next (ptr_interference_entry ptr_interference_target s)
    (mk_inst 21 ASSIGN [Lit 0w] ["b"]) (ptr_interference_t1 s with vs_inst_idx := 0)
End
Definition ptr_interference_q2_def:
  ptr_interference_q2 s = ptr_ledger_next (ptr_interference_q1 s)
    (mk_inst 22 MSTORE [Var "a"; Lit 42w] []) (ptr_interference_t2 s with vs_inst_idx := 1)
End
Definition ptr_interference_q3_def:
  ptr_interference_q3 s = ptr_ledger_next (ptr_interference_q2 s)
    (mk_inst 24 MSTORE [Var "b"; Lit 99w] []) (ptr_interference_t3 s with vs_inst_idx := 2)
End
Definition ptr_interference_q4_def:
  ptr_interference_q4 s = ptr_ledger_next (ptr_interference_q3 s)
    (mk_inst 25 MLOAD [Var "a"] ["r"]) (ptr_interference_t4 s with vs_inst_idx := 3)
End

Theorem ptr_interference_target_entry_fields[local,simp]:
  (ptr_interference_entry ptr_interference_target s).po_fn = ptr_interference_target /\
  (ptr_interference_entry ptr_interference_target s).po_inst =
    mk_inst 20 ASSIGN [Lit 32w] ["a"] /\
  (ptr_interference_entry ptr_interference_target s).po_state = ptr_probe_entry_state s
Proof
  simp[ptr_interference_entry_def, ptr_observe_def, ptr_interference_target_def,
    fn_insts_def, fn_insts_blocks_def, ptr_probe_fn_def, mk_raw_function_def]
QED

Theorem ptr_interference_target_observation_states[local,simp]:
  (ptr_interference_q1 s).po_state = ptr_interference_t1 s /\
  (ptr_interference_q2 s).po_state = ptr_interference_t2 s /\
  (ptr_interference_q3 s).po_state = ptr_interference_t3 s /\
  (ptr_interference_q4 s).po_state = ptr_interference_t4 s
Proof
  conj_asm1_tac
  >- simp[ptr_interference_q1_def, ptr_ledger_next_def, ptr_observe_def,
      ptr_probe_entry_state_def, venom_state_component_equality] >>
  conj_asm1_tac
  >- simp[ptr_interference_q2_def, ptr_ledger_next_def, ptr_observe_def,
      venom_state_component_equality] >>
  conj_asm1_tac
  >- simp[ptr_interference_q3_def, ptr_ledger_next_def, ptr_observe_def,
      venom_state_component_equality] >>
  simp[ptr_interference_q4_def, ptr_ledger_next_def, ptr_observe_def,
    venom_state_component_equality]
QED

Theorem ptr_interference_target_observation_cursors[local,simp]:
  (ptr_interference_q1 s).po_fn = ptr_interference_target /\
  (ptr_interference_q2 s).po_fn = ptr_interference_target /\
  (ptr_interference_q3 s).po_fn = ptr_interference_target /\
  (ptr_interference_q4 s).po_fn = ptr_interference_target /\
  (ptr_interference_q1 s).po_inst = mk_inst 21 ASSIGN [Lit 0w] ["b"] /\
  (ptr_interference_q2 s).po_inst = mk_inst 22 MSTORE [Var "a"; Lit 42w] [] /\
  (ptr_interference_q3 s).po_inst = mk_inst 24 MSTORE [Var "b"; Lit 99w] [] /\
  (ptr_interference_q4 s).po_inst = mk_inst 25 MLOAD [Var "a"] ["r"]
Proof
  simp[ptr_interference_q4_def, ptr_ledger_next_def, ptr_observe_def] >>
  simp[ptr_interference_q3_def, ptr_ledger_next_def, ptr_observe_def] >>
  simp[ptr_interference_q2_def, ptr_ledger_next_def, ptr_observe_def] >>
  simp[ptr_interference_q1_def, ptr_ledger_next_def, ptr_observe_def]
QED

Theorem ptr_interference_target_follows:
  ptr_ledger_follow ctx (ptr_interference_suffix ptr_interference_target)
    (ptr_interference_entry ptr_interference_target s) =
  SOME [ptr_interference_q1 s; ptr_interference_q2 s;
    ptr_interference_q3 s; ptr_interference_q4 s]
Proof
  `ptr_interference_suffix ptr_interference_target =
     [mk_inst 21 ASSIGN [Lit 0w] ["b"];
      mk_inst 22 MSTORE [Var "a"; Lit 42w] [];
      mk_inst 24 MSTORE [Var "b"; Lit 99w] [];
      mk_inst 25 MLOAD [Var "a"] ["r"]]` by EVAL_TAC >>
  simp[Once ptr_ledger_follow_def, ptr_interference_target_edges,
    is_terminator_def, GSYM ptr_interference_q1_def] >>
  simp[ptr_probe_entry_state_def] >>
  simp[Once ptr_ledger_follow_def, ptr_interference_target_edges,
    is_terminator_def, GSYM ptr_interference_q2_def] >>
  simp[Once ptr_ledger_follow_def, ptr_interference_target_edges,
    is_terminator_def, GSYM ptr_interference_q3_def] >>
  simp[Once ptr_ledger_follow_def, ptr_interference_target_edges,
    is_terminator_def, GSYM ptr_interference_q4_def] >>
  simp[ptr_ledger_follow_def]
QED

Theorem ptr_interference_target_history:
  s.vs_allocas = FEMPTY ==>
  ptr_chrono_history s
    (mk_venom_context [ptr_interference_target] (SOME "probe"))
    [ptr_interference_entry ptr_interference_target s;
     ptr_interference_q1 s; ptr_interference_q2 s;
     ptr_interference_q3 s; ptr_interference_q4 s] (ptr_interference_q4 s)
Proof
  strip_tac >>
  `ptr_chrono_history s
     (mk_venom_context [ptr_interference_target] (SOME "probe"))
     [ptr_interference_entry ptr_interference_target s]
     (ptr_interference_entry ptr_interference_target s)` by
    (simp[ptr_interference_entry_def, ptr_interference_target_def,
       fn_insts_def, fn_insts_blocks_def, ptr_probe_fn_def, mk_raw_function_def] >>
     irule (cj 1 ptr_chrono_history_rules) >>
     simp[ptr_interference_entry_def, ptr_interference_target_def,
       ptr_probe_fn_def, ptr_probe_entry_state_def, ptr_observe_def,
       mk_venom_context_def, mk_raw_function_def, lookup_function_def,
       fn_entry_label_def, enters_block_def, active_inst_def,
       lookup_block_def, eval_phis_def, phi_prefix_length_def,
       fn_insts_def, fn_insts_blocks_def,
       FIND_def, INDEX_FIND_def, entry_block_def]) >>
  qspec_then `mk_venom_context [ptr_interference_target] (SOME "probe")`
    assume_tac (Q.GEN `ctx` ptr_interference_target_follows) >>
  drule_all ptr_ledger_follow_history >> simp[]
QED

Theorem ptr_interference_write_exclusion:
  k < 32 ==>
  ~(s.vs_alloca_next + 32 <= s.vs_alloca_next + k /\
    s.vs_alloca_next + k < s.vs_alloca_next + 32 + 32) /\
  ~(0 <= 32 + k /\ 32 + k < 0 + 32)
Proof
  decide_tac
QED

Theorem ptr_interference_read_bytes:
  s.vs_alloca_next + 64 <= dimword (:256) /\ k < 32 ==>
  read_byte (s.vs_alloca_next + k) (ptr_interference_s5 s).vs_memory =
  read_byte (32 + k) (ptr_interference_t4 t).vs_memory
Proof
  strip_tac >>
  `s.vs_alloca_next < dimword (:256) /\
   s.vs_alloca_next + 32 < dimword (:256)` by decide_tac >>
  simp[ptr_interference_s5_def, ptr_interference_t4_def] >>
  simp[] >>
  `~(s.vs_alloca_next + 32 <= s.vs_alloca_next + k /\
      s.vs_alloca_next + k < s.vs_alloca_next + 32 + 32)` by decide_tac >>
  `~(0 <= 32 + k /\ 32 + k < 0 + 32)` by decide_tac >>
  simp[read_byte_mstore_outside] >>
  simp[ptr_interference_s4_def, ptr_interference_s3_def,
    ptr_interference_t3_def] >>
  simp[read_byte_mstore_outside] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule ptr_mstore_written_bytes >> simp[]
QED

Theorem ptr_interference_masked_read:
  s.vs_alloca_next + 64 <= dimword (:256) ==>
  word_agree_except (mem_word_taint M s.vs_alloca_next)
    (mload s.vs_alloca_next (ptr_interference_s5 s))
    (mload 32 (ptr_interference_t4 t))
Proof
  strip_tac >> irule ptr_mload_masked_value >> simp[ptr_interference_read_bytes]
QED

Theorem ptr_interference_load_edges:
  s.vs_alloca_next + 64 <= dimword (:256) ==>
  step_inst fuel C (mk_inst 25 MLOAD [Var "a"] ["r"])
    (ptr_interference_s5 s) =
    OK (update_var "r" (mload s.vs_alloca_next (ptr_interference_s5 s))
      (ptr_interference_s5 s)) /\
  step_inst fuel C' (mk_inst 25 MLOAD [Var "a"] ["r"])
    (ptr_interference_t4 t) =
    OK (update_var "r" (mload 32 (ptr_interference_t4 t))
      (ptr_interference_t4 t))
Proof
  strip_tac >>
  `s.vs_alloca_next < dimword (:256)` by decide_tac >>
  `lookup_var "a" (ptr_interference_s5 s) =
     SOME (n2w s.vs_alloca_next : bytes32)` by
    (simp[ptr_interference_s5_def, ptr_interference_s4_def,
       ptr_interference_s3_def, lookup_var_mstore_idx] >>
     simp[ptr_interference_s2_def, ptr_interference_s1_def,
       ptr_probe_allocated_state_def, ptr_probe_entry_state_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `lookup_var "a" (ptr_interference_t4 t) = SOME 32w` by
    (simp[ptr_interference_t4_def, ptr_interference_t3_def,
       lookup_var_mstore_idx] >>
     simp[ptr_interference_t2_def, ptr_interference_t1_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def,
    exec_read1_def, eval_operand_def, dimword_def]
QED

Theorem ptr_interference_load_results:
  s.vs_alloca_next + 64 <= dimword (:256) ==>
  ?s' t' x y.
    step_inst fuel C (mk_inst 25 MLOAD [Var "a"] ["r"])
      (ptr_interference_s5 s) = OK s' /\
    step_inst fuel C' (mk_inst 25 MLOAD [Var "a"] ["r"])
      (ptr_interference_t4 t) = OK t' /\
    lookup_var "r" s' = SOME x /\ lookup_var "r" t' = SOME y /\
    word_agree_except (mem_word_taint M s.vs_alloca_next) x y
Proof
  strip_tac >>
  drule ptr_interference_load_edges >>
  disch_then (qspecl_then [`t`, `fuel`, `C'`, `C`] strip_assume_tac) >>
  simp[] >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    ptr_interference_masked_read]
QED
