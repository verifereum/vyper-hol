(* Why codegen_ready_inst forbids Label operands on a terminator other than
   JMP, JNZ and DJMP.

   The CFG takes every Label operand of a block's terminator as a successor
   edge.  Without that conjunct, the function below meets every other part of
   codegen_ready_fn and every premise of block_plan_state_static at its RET,
   yet the RET's label makes "use" a successor of "entry", so x is live across
   the RET and the planner leaves it on the stack.  RET's conjunct of
   block_plan_state_static (an empty stack after RET) fails there. *)
Theory fnBlockPlanStaticRetWitness
Ancestors
  fnBlockPlanStatic fnPlanLineage stackPlanGen stackPlanTypes venomInst
  venomWf livenessDefs dfgDefs cfgDefs fnPlanPrefix
Libs finite_mapLib

val () = computeLib.upd_compset add_finite_map_compset;
val () = computeLib.add_persistent_funs ["stackModel.stack_find_def"];

Definition ret_label_probe_fn_def:
  ret_label_probe_fn = mk_raw_function "f"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 OFFSET [Lit 0w; Label "entry"] ["x"];
          mk_inst 1 RET [Label "use"] []] |>;
     <| bb_label := "use"; bb_instructions :=
         [mk_inst 2 ASSERT [Var "x"] []; mk_inst 3 STOP [] []] |>]
End

(* Every part of codegen_ready_fn holds but the terminator-label conjunct of
   codegen_ready_inst, which holds once the RET's label is dropped; the RET's
   label is a CFG edge. *)
Theorem ret_label_probe_ready_but_label:
  canonical_param_prefix ret_label_probe_fn /\
  wf_function ret_label_probe_fn /\
  fn_inst_wf ret_label_probe_fn /\
  ssa_form ret_label_probe_fn /\
  def_dominates_uses ret_label_probe_fn /\
  single_use_form ret_label_probe_fn /\
  cfg_is_normalized (cfg_analyze ret_label_probe_fn) ret_label_probe_fn /\
  block_entries_ready (cfg_analyze ret_label_probe_fn) ret_label_probe_fn /\
  phi_operands_ready ret_label_probe_fn /\
  EVERY (\bb. EVERY (\inst. codegen_ready_inst
                       (if inst.inst_opcode = RET
                        then inst with inst_operands := [] else inst))
                bb.bb_instructions) ret_label_probe_fn.fn_blocks /\
  offset_outputs_used ret_label_probe_fn /\
  phis_at_joins (cfg_analyze ret_label_probe_fn) ret_label_probe_fn /\
  ~codegen_ready_fn ret_label_probe_fn /\
  fn_cfg_edge ret_label_probe_fn "entry" "use"
Proof
  rpt conj_tac
  >- (EVAL_TAC >> simp[]) >- (EVAL_TAC >> simp[]) >- (EVAL_TAC >> simp[])
  >- (EVAL_TAC >> simp[]) >- (EVAL_TAC >> simp[]) >- (EVAL_TAC >> simp[])
  >- (EVAL_TAC >> simp[]) >- (EVAL_TAC >> simp[]) >- (EVAL_TAC >> simp[])
  >- (EVAL_TAC >> simp[]) >- (EVAL_TAC >> simp[]) >- (EVAL_TAC >> simp[])
  >- (EVAL_TAC >> simp[])
  >> rewrite_tac[fn_cfg_edge_def]
  >> qexists_tac `HD ret_label_probe_fn.fn_blocks` >> EVAL_TAC
QED

Theorem ret_label_probe_function_success:
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze ret_label_probe_fn) (dfg_build_function ret_label_probe_fn)
    (cfg_analyze ret_label_probe_fn) NONE [] ret_label_probe_fn 0 0)
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem ret_label_probe_block_result:
  ?ops ps'.
    generate_block_plan (liveness_analyze ret_label_probe_fn)
      (dfg_build_function ret_label_probe_fn) (cfg_analyze ret_label_probe_fn)
      ret_label_probe_fn (HD ret_label_probe_fn.fn_blocks)
      (init_cleanup_plan_state NONE [] 0 0) = SOME (ops, ps') /\
    ps'.ps_stack = [Var "x"]
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem ret_label_probe_entry_states:
  !lv dg cg ps0.
    lineage_state lv dg cg ret_label_probe_fn ps0 "entry" ps0 /\
    dfs_block_state lv dg cg ret_label_probe_fn ps0 "entry" ps0
Proof
  rpt gen_tac >> conj_tac
  >- (irule lineage_state_entry >> EVAL_TAC)
  >> simp[dfs_block_state_def] >> qexistsl_tac [`[]`, `[]`]
  >> simp[] >> irule dfs_aux_call_entry >> EVAL_TAC
QED

Definition ret_label_probe_before_def:
  ret_label_probe_before = SND (THE (generate_block_insts_prefix
    (liveness_analyze ret_label_probe_fn) (dfg_build_function ret_label_probe_fn)
    (cfg_analyze ret_label_probe_fn) ret_label_probe_fn "entry" F 0 2 0 1
    (HD ret_label_probe_fn.fn_blocks).bb_instructions
    (init_cleanup_plan_state NONE [] 0 0)))
End

Theorem ret_label_probe_prefix:
  ?ops.
    generate_block_insts_prefix
      (liveness_analyze ret_label_probe_fn) (dfg_build_function ret_label_probe_fn)
      (cfg_analyze ret_label_probe_fn) ret_label_probe_fn "entry" F 0 2 0 1
      (HD ret_label_probe_fn.fn_blocks).bb_instructions
      (init_cleanup_plan_state NONE [] 0 0) =
      SOME (ops, ret_label_probe_before)
Proof
  qexists_tac `[SOPushOfst "entry" 0]` >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem ret_label_probe_ret_nonempty:
  ?ops ps'.
    generate_inst_plan
      (liveness_analyze ret_label_probe_fn) (dfg_build_function ret_label_probe_fn)
      (cfg_analyze ret_label_probe_fn) ret_label_probe_fn
      (mk_inst 1 RET [Label "use"] [])
      (live_vars_at (liveness_analyze ret_label_probe_fn) "entry" 2)
      F F "entry" ret_label_probe_before = SOME (ops, ps') /\
    ps'.ps_stack = [Var "x"]
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem ret_label_probe_live_and_stack:
  live_vars_at (liveness_analyze ret_label_probe_fn) "entry" 2 = ["x"] /\
  ret_label_probe_before.ps_stack = [Var "x"]
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem ret_label_probe_block_state:
  block_plan_state
    (liveness_analyze ret_label_probe_fn) (dfg_build_function ret_label_probe_fn)
    (cfg_analyze ret_label_probe_fn) ret_label_probe_fn
    (HD ret_label_probe_fn.fn_blocks) (init_cleanup_plan_state NONE [] 0 0)
    1 ret_label_probe_before
Proof
  rewrite_tac[block_plan_state_def] >>
  qexistsl_tac [`[]`, `init_cleanup_plan_state NONE [] 0 0`,
               `[]`, `init_cleanup_plan_state NONE [] 0 0`] >>
  qexists_tac `[SOPushOfst "entry" 0]` >> simp[] >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

(* The premises of block_plan_state_static but codegen_ready_fn, at a RET
   that leaves a slot on the stack. *)
Theorem ret_label_witness_premises:
  ?liveness dfg cfg ch growth spill_base lbl_ctr fn fn_ops ps_end lbl bb
   ps_l ps_dfs ps_dfs_after h promised block_ops ps_after k ps inst next_live
   next_is_term.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    lineage_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps_l /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs =
      SOME (block_ops, ps_dfs_after) /\
    generate_block_plan liveness dfg cfg fn bb
      (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
      SOME (block_ops, ps_after) /\
    block_plan_state liveness dfg cfg fn bb
      (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)
      k ps /\
    phi_prefix_length bb.bb_instructions <= k /\
    k < LENGTH bb.bb_instructions /\
    EL k bb.bb_instructions = inst /\
    next_live = live_vars_at liveness bb.bb_label (k + 1) /\
    next_is_term =
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode) /\
    inst.inst_opcode = RET /\
    ?ops ps'.
      generate_inst_plan liveness dfg cfg fn inst next_live (bb_is_halting bb)
        next_is_term bb.bb_label ps = SOME (ops, ps') /\ ps'.ps_stack <> []
Proof
  mp_tac ret_label_probe_function_success >>
  pure_rewrite_tac[optionTheory.IS_SOME_EXISTS, pairTheory.EXISTS_PROD] >>
  strip_tac >>
  rename1 `generate_fn_plan_with_cleanup_analyzed _ _ _ _ _ _ _ _ = SOME result` >>
  PairCases_on `result` >>
  rename1 `generate_fn_plan_with_cleanup_analyzed _ _ _ _ _ _ _ _ =
    SOME (fn_ops, ps_end)` >>
  mp_tac ret_label_probe_block_result >> strip_tac >>
  rename1 `generate_block_plan _ _ _ _ _ _ = SOME (block_ops, ps_after)` >>
  qexistsl_tac [`liveness_analyze ret_label_probe_fn`,
    `dfg_build_function ret_label_probe_fn`, `cfg_analyze ret_label_probe_fn`,
    `NONE`, `[]`, `0`, `0`, `ret_label_probe_fn`, `fn_ops`, `ps_end`,
    `"entry"`, `HD ret_label_probe_fn.fn_blocks`,
    `init_cleanup_plan_state NONE [] 0 0`, `init_cleanup_plan_state NONE [] 0 0`,
    `ps_after`, `(init_cleanup_plan_state NONE [] 0 0).ps_cleanup_height`,
    `(init_cleanup_plan_state NONE [] 0 0).ps_cleanup_promised`,
    `block_ops`, `ps_after`, `1`, `ret_label_probe_before`,
    `mk_inst 1 RET [Label "use"] []`,
    `live_vars_at (liveness_analyze ret_label_probe_fn) "entry" 2`, `F`] >>
  `init_cleanup_plan_state NONE [] 0 0 with ps_cleanup_height := NONE =
   init_cleanup_plan_state NONE [] 0 0` by EVAL_TAC >>
  simp[ret_label_probe_entry_states,
       ret_label_probe_block_state] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  `(HD ret_label_probe_fn.fn_blocks).bb_label = "entry"` by EVAL_TAC >>
  `bb_is_halting (HD ret_label_probe_fn.fn_blocks) = F` by EVAL_TAC >>
  mp_tac ret_label_probe_ret_nonempty >> simp[] >> strip_tac >>
  rename1 `SOME (ret_ops, ret_after) = generate_inst_plan _ _ _ _ _ _ _ _ _ _` >>
  qexistsl_tac [`ret_ops`, `ret_after`] >> simp[]
QED
