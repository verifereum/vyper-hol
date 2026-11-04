Theory algebraicOptFreshnessProbe
Ancestors
  algebraicOptReachabilityProofs codegenReadyCompute

(* Syntax abbreviations only: no semantic definition is changed. *)
Overload ao_fresh_entry = ``<| bb_label := "entry"; bb_instructions :=
  [mk_inst 0 ASSIGN [Lit 0w] ["x0"];
   mk_inst 1 JMP [Label "header"] []] |>``
Overload ao_fresh_header = ``<| bb_label := "header"; bb_instructions :=
  [mk_inst 2 PHI [Label "entry"; Var "x0"; Label "body"; Var "y"] ["x"];
   mk_inst 3 PHI [Label "entry"; Var "x0"; Label "body"; Var "z"] ["q"];
   mk_inst 4 ISZERO [Var "x"] ["z"];
   mk_inst 5 ISZERO [Var "z"] ["r"];
   mk_inst 8 JMP [Label "body"] []] |>``
Overload ao_fresh_body = ``<| bb_label := "body"; bb_instructions :=
  [mk_inst 6 ASSIGN [Lit 1w] ["y"];
   mk_inst 7 JMP [Label "header"] []] |>``
Overload ao_fresh_fn = ``mk_raw_function "freshness"
  [ao_fresh_entry; ao_fresh_header; ao_fresh_body]``

Theorem ao_fresh_fixture_wf:
  wf_function ao_fresh_fn /\ wf_ssa ao_fresh_fn /\
  fn_inst_wf ao_fresh_fn /\
  EVERY label_positions_ok (fn_insts ao_fresh_fn)
Proof
  EVAL_TAC >> CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >> EVAL_TAC
QED

Overload ao_fresh_s0 = ``init_venom_state "entry"``
Overload ao_fresh_h1 = ``jump_to "header" (update_var "x0" 0w ao_fresh_s0)``
Overload ao_fresh_p1 = ``(update_var "x" 0w (update_var "q" 0w ao_fresh_h1))
  with vs_inst_idx := 2``
Overload ao_fresh_a1 = ``(update_var "z" 1w ao_fresh_p1) with vs_inst_idx := 3``
Overload ao_fresh_b1 = ``jump_to "body" (update_var "r" 0w ao_fresh_a1)``
Overload ao_fresh_h2 = ``jump_to "header" (update_var "y" 1w ao_fresh_b1)``
Overload ao_fresh_p2 = ``(update_var "x" 1w (update_var "q" 1w ao_fresh_h2))
  with vs_inst_idx := 2``
Overload ao_fresh_a2 = ``(update_var "z" 0w ao_fresh_p2) with vs_inst_idx := 3``

Theorem ao_fresh_entry_exec:
  exec_block 5 (mk_venom_context [] NONE) ao_fresh_entry ao_fresh_s0 =
  OK ao_fresh_h1
Proof
  EVAL_TAC >> CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >> EVAL_TAC
QED

Theorem ao_fresh_first_phis:
  eval_phis ao_fresh_h1 ao_fresh_header.bb_instructions =
    OK (update_var "x" 0w (update_var "q" 0w ao_fresh_h1))
Proof
  EVAL_TAC >> CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >> EVAL_TAC
QED

Theorem ao_fresh_first_header_exec:
  exec_block 4 (mk_venom_context [] NONE) ao_fresh_header ao_fresh_p1 =
    OK ao_fresh_b1
Proof
  EVAL_TAC >> CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >> EVAL_TAC
QED

Theorem ao_fresh_body_exec:
  exec_block 4 (mk_venom_context [] NONE) ao_fresh_body ao_fresh_b1 =
    OK ao_fresh_h2
Proof
  EVAL_TAC >> CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >> EVAL_TAC
QED

Theorem ao_fresh_second_phis:
  eval_phis ao_fresh_h2 ao_fresh_header.bb_instructions =
    OK (update_var "x" 1w (update_var "q" 1w ao_fresh_h2))
Proof
  EVAL_TAC >> CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >> EVAL_TAC
QED

Theorem ao_fresh_second_producer:
  step_inst 3 (mk_venom_context [] NONE)
    (mk_inst 4 ISZERO [Var "x"] ["z"]) ao_fresh_p2 =
    OK (update_var "z" 0w ao_fresh_p2)
Proof
  EVAL_TAC >> CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >> EVAL_TAC
QED

(* The backedge PHI reads old z and old x from the SAME predecessor state.
   Post-batch x is new, while z remains old until its producer executes. *)
Theorem ao_fresh_observations:
  eval_operand (Var "x") ao_fresh_h2 = SOME 0w /\
  lookup_var "z" ao_fresh_h2 = SOME 1w /\
  eval_one_phi ao_fresh_h2 (EL 1 ao_fresh_header.bb_instructions) =
    SOME ("q",1w) /\
  eval_operand (Var "x") ao_fresh_p2 = SOME 1w /\
  lookup_var "z" ao_fresh_p2 = SOME 1w /\
  lookup_var "q" ao_fresh_p2 = SOME 1w /\
  lookup_var "z" ao_fresh_a2 = SOME 0w /\
  eval_operand (Var "x") ao_fresh_a2 = SOME 1w
Proof
  EVAL_TAC >> CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >> EVAL_TAC
QED

Theorem ao_fresh_unrestricted_transport_fails:
  lookup_var "z" ao_fresh_p2 <>
    OPTION_MAP (\w. bool_to_word (w = 0w))
      (eval_operand (Var "x") ao_fresh_p2)
Proof
  EVAL_TAC >> CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >> EVAL_TAC
QED

Theorem ao_fresh_selected_edge_and_ordinary_equations:
  lookup_var "z" ao_fresh_h2 =
    OPTION_MAP (\w. bool_to_word (w = 0w))
      (eval_operand (Var "x") ao_fresh_h2) /\
  lookup_var "z" ao_fresh_a2 =
    OPTION_MAP (\w. bool_to_word (w = 0w))
      (eval_operand (Var "x") ao_fresh_a2)
Proof
  EVAL_TAC >> CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >> EVAL_TAC
QED

(* INTERFACE PROPOSALS (not asserted as proved theorems).

Ordinary consumer proposal, with all variables universally quantified:

  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  s0.vs_inst_idx = 0 /\ s0.vs_prev_bb = NONE /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  (!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==>
     lookup_var x s0 = NONE) /\
  ao_source_prefix ctx fn s0 n k F s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME use /\
  use.inst_opcode <> PHI /\ MEM (Var z) use.inst_operands /\
  MEM prod (fn_insts fn) /\ prod.inst_opcode = ISZERO /\
  prod.inst_operands = [op] /\ prod.inst_outputs = [z] ==>
  ?w. eval_operand op s = SOME w /\
      lookup_var z s = SOME (bool_to_word (w = 0w))

Selected PHI edge proposal (same static and initial-state premises):

  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  s0.vs_inst_idx = 0 /\ s0.vs_prev_bb = NONE /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  (!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==>
     lookup_var x s0 = NONE) /\
  ao_source_prefix ctx fn s0 n k T s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI /\
  s.vs_prev_bb = SOME pred /\
  resolve_phi pred phi.inst_operands = SOME (Var z) /\
  MEM prod (fn_insts fn) /\ prod.inst_opcode = ISZERO /\
  prod.inst_operands = [op] /\ prod.inst_outputs = [z] ==>
  ?w. eval_operand op s = SOME w /\
      lookup_var z s = SOME (bool_to_word (w = 0w))

Audit and remaining obligations:
- def_dominates_uses gives def_available_at at an ordinary consumer, hence
  producer block dominance and strict same-block producer-before-use order.
  Applied to prod, it also gives operand-definition-before-producer order
  when op is a variable. Literals need no stability argument.
- phi_edge_uses_wf gives exact predecessor coverage, unique incoming pairs,
  and def_available_at at the named predecessor with endpoint NONE. That
  endpoint is the completed predecessor, NOT the post-PHI successor. Need
  a resolve_phi-to-phi_pairs bridge and a successful-prefix-to-actual-edge
  bridge before applying this availability to the selected input.
- ssa_form identifies each dynamic writer with its unique static producer;
  it does NOT forbid repeated dynamic executions of that producer.
- Existing ao_iszero_historical_operand provides some reachable producer
  event. It does not provide the last event or the suffix since that event.
  Need a finite chronological prefix witness and a last-producer split.
- Need to project that *actual* successful execution witness to a CFG path
  and instruction positions, preserving PHI entry/ordinary boundary order.
  Need no-writer suffix lookup preservation (atomic PHI batches included).
- Need the dynamic order result: after the last producer, any execution of
  its operand's unique writer forces another execution of the producer
  before this ordinary consumer, or before this selected predecessor exit.
  This uses both dominance constraints and strict same-block order, and
  must cover loops/repeated block labels and batch PHI operand writers.
- removeUnusedProofs.is_fn_path_suffix and dominates_path_no_revisit are
  local static-path facts; the latter constructs SOME path and cannot
  replace reasoning about the actual dynamic suffix. Neither was copied.
- The fixture's second PHI boundary refutes the unrestricted reachable-state
  interface only; it is not a counterexample to function correctness.
*)
