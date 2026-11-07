(* Why codegen_ready_inst requires a NOP to have no operands.

   Without that conjunct, the block below meets every other part of
   codegen_ready_fn and every premise of block_plan_state_static at its RET,
   yet the planner leaves the OFFSET's output on the stack after the RET: the
   planner skips a NOP, so the variable it reads is never consumed, and that
   read keeps the variable live, so nothing pops it.  RET's conjunct of
   block_plan_state_static (an empty stack after RET) fails there. *)
Theory fnBlockPlanStaticNopWitness
Ancestors
  fnBlockPlanStatic fnPlanLineage stackPlanGen venomInst venomWf livenessDefs
  dfgDefs cfgDefs
Libs finite_mapLib

val () = computeLib.upd_compset add_finite_map_compset;

Definition nop_witness_bb_def:
  nop_witness_bb = <| bb_label := "entry"; bb_instructions :=
    [mk_inst 0 OFFSET [Lit 0w; Label "entry"] ["x"];
     mk_inst 1 NOP [Var "x"] [];
     mk_inst 2 RET [Lit 0w] []] |>
End

Definition nop_witness_fn_def:
  nop_witness_fn = mk_raw_function "f" [nop_witness_bb]
End

Definition nop_witness_initial_def:
  nop_witness_initial = init_cleanup_plan_state NONE [] 0 0
End

Definition nop_witness_middle_def:
  nop_witness_middle = nop_witness_initial with ps_stack := [Var "x"]
End

(* Every part of codegen_ready_fn holds but the NOP conjunct of
   codegen_ready_inst, which holds once the NOP's operand is dropped. *)
Theorem nop_witness_ready_but_nop:
  canonical_param_prefix nop_witness_fn /\
  wf_function nop_witness_fn /\
  fn_inst_wf nop_witness_fn /\
  ssa_form nop_witness_fn /\
  def_dominates_uses nop_witness_fn /\
  single_use_form nop_witness_fn /\
  cfg_is_normalized (cfg_analyze nop_witness_fn) nop_witness_fn /\
  block_entries_ready (cfg_analyze nop_witness_fn) nop_witness_fn /\
  phi_operands_ready nop_witness_fn /\
  codegen_ready_inst (EL 0 nop_witness_bb.bb_instructions) /\
  codegen_ready_inst
    ((EL 1 nop_witness_bb.bb_instructions) with inst_operands := []) /\
  codegen_ready_inst (EL 2 nop_witness_bb.bb_instructions) /\
  offset_outputs_used nop_witness_fn /\
  phis_at_joins (cfg_analyze nop_witness_fn) nop_witness_fn /\
  ~codegen_ready_fn nop_witness_fn
Proof
  rpt conj_tac >> EVAL_TAC >> simp[]
QED

Theorem nop_witness_entry:
  lineage_state (liveness_analyze nop_witness_fn)
    (dfg_build_function nop_witness_fn) (cfg_analyze nop_witness_fn)
    nop_witness_fn nop_witness_initial "entry" nop_witness_initial /\
  dfs_block_state (liveness_analyze nop_witness_fn)
    (dfg_build_function nop_witness_fn) (cfg_analyze nop_witness_fn)
    nop_witness_fn nop_witness_initial "entry" nop_witness_initial
Proof
  conj_tac
  >- (irule lineage_state_entry >> EVAL_TAC)
  >> rewrite_tac[dfs_block_state_def]
  >> qexistsl_tac [`[]`, `[]`]
  >> simp[] >> irule dfs_aux_call_entry >> EVAL_TAC
QED

Theorem nop_witness_prefix:
  block_plan_state (liveness_analyze nop_witness_fn)
    (dfg_build_function nop_witness_fn) (cfg_analyze nop_witness_fn)
    nop_witness_fn nop_witness_bb nop_witness_initial 2 nop_witness_middle
Proof
  rewrite_tac[block_plan_state_def] >> EVAL_TAC >> simp[]
QED

Theorem nop_witness_replay_initial:
  nop_witness_initial with
    <|ps_cleanup_height := NONE; ps_cleanup_promised := F|> =
  nop_witness_initial
Proof
  EVAL_TAC
QED

(* The premises of block_plan_state_static but codegen_ready_fn, at the RET
   (k = 2, h = NONE, promised = F). *)
Theorem nop_witness_premises:
  ?fn_ops ps_end block_ops ps_after.
    generate_fn_plan_with_cleanup_analyzed (liveness_analyze nop_witness_fn)
      (dfg_build_function nop_witness_fn) (cfg_analyze nop_witness_fn) NONE []
      nop_witness_fn 0 0 = SOME (fn_ops, ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) nop_witness_fn.fn_blocks /\
    lookup_block "entry" nop_witness_fn.fn_blocks = SOME nop_witness_bb /\
    lineage_state (liveness_analyze nop_witness_fn)
      (dfg_build_function nop_witness_fn) (cfg_analyze nop_witness_fn)
      nop_witness_fn nop_witness_initial "entry" nop_witness_initial /\
    dfs_block_state (liveness_analyze nop_witness_fn)
      (dfg_build_function nop_witness_fn) (cfg_analyze nop_witness_fn)
      nop_witness_fn nop_witness_initial "entry" nop_witness_initial /\
    generate_block_plan (liveness_analyze nop_witness_fn)
      (dfg_build_function nop_witness_fn) (cfg_analyze nop_witness_fn)
      nop_witness_fn nop_witness_bb nop_witness_initial =
      SOME (block_ops, ps_after) /\
    generate_block_plan (liveness_analyze nop_witness_fn)
      (dfg_build_function nop_witness_fn) (cfg_analyze nop_witness_fn)
      nop_witness_fn nop_witness_bb
      (nop_witness_initial with
         <|ps_cleanup_height := NONE; ps_cleanup_promised := F|>) =
      SOME (block_ops, ps_after) /\
    block_plan_state (liveness_analyze nop_witness_fn)
      (dfg_build_function nop_witness_fn) (cfg_analyze nop_witness_fn)
      nop_witness_fn nop_witness_bb
      (nop_witness_initial with
         <|ps_cleanup_height := NONE; ps_cleanup_promised := F|>)
      2 nop_witness_middle /\
    phi_prefix_length nop_witness_bb.bb_instructions <= 2 /\
    2 < LENGTH nop_witness_bb.bb_instructions /\
    EL 2 nop_witness_bb.bb_instructions = mk_inst 2 RET [Lit 0w] [] /\
    [] = live_vars_at (liveness_analyze nop_witness_fn)
           nop_witness_bb.bb_label (2 + 1) /\
    F = (2 + 1 < LENGTH nop_witness_bb.bb_instructions /\
         is_terminator (EL (2 + 1) nop_witness_bb.bb_instructions).inst_opcode)
Proof
  simp[nop_witness_replay_initial, nop_witness_entry, nop_witness_prefix]
  >> EVAL_TAC >> simp[]
QED

(* The RET leaves the OFFSET's output on the stack. *)
Theorem nop_witness_ret_leftover:
  ?ops ps'.
    generate_inst_plan (liveness_analyze nop_witness_fn)
      (dfg_build_function nop_witness_fn) (cfg_analyze nop_witness_fn)
      nop_witness_fn (mk_inst 2 RET [Lit 0w] []) []
      (bb_is_halting nop_witness_bb) F nop_witness_bb.bb_label
      nop_witness_middle = SOME (ops, ps') /\
    ps'.ps_stack = [Var "x"]
Proof
  EVAL_TAC >> simp[]
QED
