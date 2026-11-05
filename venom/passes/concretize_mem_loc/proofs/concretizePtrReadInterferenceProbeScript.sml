Theory concretizePtrReadInterferenceProbe
Ancestors concretizePtrLedgerProbe concretizePtrPrefixProbe
  concretizePtrLoadTransport concretizePtrPlacementBounds concretizeMemLocDefs
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
