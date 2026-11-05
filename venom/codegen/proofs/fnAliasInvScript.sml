(*
 * The cross-block DFG alias invariant of the block induction behind
 * venomToAsmProps$gen_fn_frame_simulation.
 *
 * gen_fn_frame_simulation assumes that every operand on the planner's
 * stack or in its spill map has the value of its ASSIGN-chain root
 * (normalize_operand), read through the frame view.  The planner's
 * alias-only reorder steps rely on it.  The induction must re-establish
 * it at the successor block, whose lineage state carries the stack and
 * spill map the current block's code leaves (fnPlanLineage).
 *
 * TOP-LEVEL:
 *   lineage_alias_successor — CHEATED: one block preserves the invariant
 *)

Theory fnAliasInv
Ancestors
  fnPlanLineage frameRel codegenRel unitShapeDefs stackPlanGen stackPlanTypes
  venomExecSemantics venomState livenessDefs dfgDefs cfgDefs
  fnAliasInvOrdering fnAliasInvAvailability dfgAnalysisProps allocaRemapSSA
  venomInst venomInstProps venomWf venomExecProps list rich_list

(* Actual single steps followed by normalize_operand, including literal roots. *)
Definition alias_assign_step_def:
  alias_assign_step dfg at src <=>
    ?v inst. at = Var v /\ FLOOKUP dfg.dfg_defs v = SOME inst /\
      inst.inst_opcode = ASSIGN /\ inst.inst_operands = [src]
End

Theorem alias_assign_source_available:
  wf_function fn /\ ssa_form fn /\ def_dominates_uses fn /\
  alias_assign_step (dfg_build_function fn) (Var x) (Var y) /\
  alias_path_available fn l i x ==>
  alias_path_available fn l i y
Proof
  strip_tac >>
  `?assign. dfg_get_def (dfg_build_function fn) x = SOME assign /\
      assign.inst_opcode = ASSIGN /\ assign.inst_operands = [Var y]` by
    gvs[alias_assign_step_def, dfg_get_def_def] >>
  drule dfg_build_function_correct >> strip_tac >>
  `!bb j. MEM bb fn.fn_blocks /\ j < LENGTH bb.bb_instructions /\
       MEM x (inst_defs (EL j bb.bb_instructions)) ==>
       alias_path_available fn bb.bb_label j y` by
    (rpt strip_tac >>
     `EL j bb.bb_instructions = assign` by
       (irule ssa_unique_output >> conj_tac
        >- (qexists_tac `fn` >>
            gvs[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[EL_MEM]) >>
        qexists_tac `x` >> gvs[inst_defs_def]) >>
     irule alias_ordinary_use_available >>
     simp[inst_uses_def, operand_vars_def, operand_var_def]) >>
  rewrite_tac[alias_path_available_def] >> rpt strip_tac >>
  qpat_x_assum `alias_path_available fn l i x` mp_tac >>
  rewrite_tac[alias_path_available_def] >>
  disch_then (qspec_then `path` mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac
  >- (`?j. j < LENGTH bb.bb_instructions /\
           EL j bb.bb_instructions = inst` by metis_tac[MEM_EL] >>
      `alias_path_available fn bb.bb_label j y` by
        metis_tac[lookup_block_MEM] >>
      `!p n. is_fn_path fn p ==> is_fn_path fn (TAKE n p)` by
        (Induct >- simp[is_fn_path_def] >>
         qx_gen_tac `head` >> Cases >- simp[is_fn_path_def] >>
         Cases_on `p` >> simp[is_fn_path_def] >>
         Cases_on `n'` >> simp[is_fn_path_def] >> strip_tac >>
         qpat_x_assum `!n. is_fn_path fn (h::t) ==> _`
           (qspec_then `SUC n` mp_tac) >> simp[]) >>
      qpat_x_assum `alias_path_available fn bb.bb_label j y` mp_tac >>
      rewrite_tac[alias_path_available_def] >>
      disch_then (qspec_then `TAKE (SUC k) path` mp_tac) >>
      impl_tac >- (simp[LENGTH_TAKE, HD_TAKE, LAST_EL, EL_TAKE] >>
                    metis_tac[lookup_block_label]) >>
      simp[LENGTH_TAKE, EL_TAKE] >> strip_tac >> disj1_tac
      >- (gvs[EL_TAKE] >> qexistsl_tac [`k'`,`bb'`,`inst'`] >> simp[] >> decide_tac) >>
      `bb.bb_label = EL k path` by metis_tac[lookup_block_label] >>
      gvs[] >> qexistsl_tac [`k`,`bb`,`EL j' bb.bb_instructions`] >>
      simp[EL_MEM]) >>
  `alias_path_available fn bb.bb_label j y` by
    metis_tac[lookup_block_MEM] >>
  qpat_x_assum `alias_path_available fn bb.bb_label j y` mp_tac >>
  rewrite_tac[alias_path_available_def] >>
  disch_then (qspec_then `path` mp_tac) >>
  impl_tac >- metis_tac[lookup_block_label] >>
  strip_tac >- metis_tac[] >>
  `bb.bb_label = l` by metis_tac[lookup_block_label] >> gvs[] >>
  disj2_tac >> qexists_tac `j'` >> simp[]
QED

Theorem normalize_operand_assign_chain:
  !dfg visited at.
    normalize_operand dfg visited at <> at ==>
    TC (alias_assign_step dfg) at (normalize_operand dfg visited at)
Proof
  recInduct normalize_operand_ind >>
  rpt strip_tac >>
  gvs[Once normalize_operand_def, AllCaseEqs()] >>
  Cases_on `FLOOKUP dfg.dfg_defs v` >> gvs[] >>
  rename1 `FLOOKUP dfg.dfg_defs v = SOME inst` >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  rename1 `inst.inst_operands = src::rest` >>
  Cases_on `rest` >> gvs[] >>
  gvs[Once normalize_operand_def] >>
  `alias_assign_step dfg (Var v) src` by
    (simp[alias_assign_step_def] >> metis_tac[]) >>
  Cases_on `normalize_operand dfg (v::visited) src = src`
  >- metis_tac[relationTheory.TC_SUBSET] >>
  metis_tac[relationTheory.TC_RULES]
QED

(* Inventory boundaries do not depend on cleanup metadata or allocator fields. *)
Definition plan_holds_def:
  plan_holds ps at <=> MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
End

Theorem plan_holds_cleanup_update[simp]:
  plan_holds
    (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) at
  <=> plan_holds ps at
Proof
  simp[plan_holds_def]
QED

Theorem plan_holds_inventory_update[simp]:
  plan_holds (ps with <| ps_stack := stk; ps_spilled := spilled |>) at
  <=> MEM at stk \/ at IN FDOM spilled
Proof
  simp[plan_holds_def]
QED

Theorem plan_holds_init_cleanup[simp]:
  ~plan_holds (init_cleanup_plan_state ch growth spill_base lbl_ctr) at
Proof
  simp[plan_holds_def, init_cleanup_plan_state_def, init_plan_state_def]
QED

(* A successful PHI plan does not, by itself, establish demand coverage. *)
Theorem generate_phi_plan_absent_slot:
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack =
    NONE ==>
  generate_phi_plan inst next_liveness is_halting ps = ([], ps)
Proof
  simp[generate_phi_plan_def]
QED

(* OFFSET bypasses dead-output filtering. Such names must not be confused
   with nontrivial ASSIGN aliases by a static support invariant. *)
Theorem generate_offset_plan_holds_output:
  inst.inst_operands = [Lit n; Label lbl] /\ inst.inst_outputs = [out] ==>
  plan_holds (SND (generate_offset_plan inst ps)) (Var out)
Proof
  simp[generate_offset_plan_def, plan_holds_def, stackModelTheory.stack_push_def]
QED

(* Small computation fixture: an actual DFG, not an assumed equivalence. *)
Definition alias_probe_fn_def:
  alias_probe_fn = mk_raw_function "alias_probe"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 0 PARAM [] ["r"];
       mk_inst 1 ASSIGN [Var "r"] ["a"];
       mk_inst 2 STOP [] []] |>]
End

(* The published path predicate permits inter-block exits before the terminator.
   This witnesses only an interface limitation, not analyzed liveness. *)
Definition alias_path_probe_fn_def:
  alias_path_probe_fn = mk_raw_function "path_probe"
    [<| bb_label := "A"; bb_instructions :=
       [mk_inst 0 PARAM [] ["r"];
        mk_inst 1 ASSIGN [Var "r"] ["a"];
        mk_inst 2 JMP [Label "B"] []] |>;
     <| bb_label := "B"; bb_instructions :=
       [mk_inst 3 ADD [Var "a"; Lit 1w] ["b"];
        mk_inst 4 STOP [] []] |>]
End

Theorem alias_path_probe_early_exit:
  cfg_exec_path (cfg_analyze alias_path_probe_fn) [("A",0);("B",0)] /\
  used_before_defined alias_path_probe_fn.fn_blocks "a" [("A",0);("B",0)] /\
  normalize_operand (dfg_build_function alias_path_probe_fn) [] (Var "a") =
    Var "r" /\
  ~MEM "a" (live_vars_at (liveness_analyze alias_path_probe_fn) "A" 0)
Proof
  EVAL_TAC >> qexists_tac `1` >> simp[] >> EVAL_TAC
QED

Theorem alias_probe_normalize:
  normalize_operand (dfg_build_function alias_probe_fn) [] (Var "a") = Var "r"
Proof
  EVAL_TAC
QED

Theorem alias_probe_phi_slots:
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    ["p"] F ((init_plan_state 0) with ps_stack := [Var "a"; Var "b"]))).ps_stack =
    [Var "a"; Var "p"] /\
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    ["p"] F ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "p"]
Proof
  EVAL_TAC
QED

Theorem alias_probe_phi_live_and_dead:
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    ["a"; "p"] F ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "a"; Var "p"] /\
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    [] F ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack = [] /\
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    [] F ((init_plan_state 0) with ps_stack := [Var "a"; Var "a"]))).ps_stack =
    [Var "a"]
Proof
  EVAL_TAC
QED

Theorem alias_probe_regular_consumption:
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ISZERO [Var "a"] ["z"])
    [] F F "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack = [] /\
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ISZERO [Var "a"] ["z"])
    [] F F "entry" ((init_plan_state 0) with ps_stack := [Var "a"; Var "a"]))).ps_stack =
    [Var "a"]
Proof
  EVAL_TAC >> simp[]
QED

Definition alias_probe_clean_def:
  alias_probe_clean inputs stk height promised =
    clean_stack_plan
      <| ds_inst := FEMPTY |++ [(("pred",0),["a"; "b"]); (("edge",0),inputs)];
         ds_boundary := FEMPTY |>
      (ARB with <| cfg_preds := FEMPTY |+ ("edge",["pred"]);
                   cfg_succs := FEMPTY |+ ("pred",["edge"; "other"]) |>)
      (mk_raw_function "clean_probe"
        [<| bb_label := "pred"; bb_instructions := [] |>])
      <| bb_label := "edge"; bb_instructions := [] |>
      ((init_plan_state 0) with <| ps_stack := stk;
        ps_cleanup_height := height; ps_cleanup_promised := promised |> )
End

Theorem alias_probe_clean_slots:
  (SND (alias_probe_clean ["b"] [Var "a"; Var "b"] NONE T)).ps_stack =
    [dead_stack_marker; Var "b"] /\
  (SND (alias_probe_clean ["b"] [Var "a"; Var "b"] NONE F)).ps_stack =
    [Var "b"] /\
  (SND (alias_probe_clean ["a"; "b"] [Var "a"; Var "b"] NONE T)).ps_stack =
    [Var "a"; Var "b"] /\
  (SND (alias_probe_clean [] [Var "a"; Var "b"] NONE T)).ps_stack =
    [dead_stack_marker; dead_stack_marker] /\
  (SND (alias_probe_clean ["a"] [Var "a"; Var "b"] NONE T)).ps_stack =
    [Var "a"]
Proof
  EVAL_TAC
QED

Theorem alias_probe_jmp_residual:
  (SND (reorder_plan (dfg_build_function alias_probe_fn) [Var "b"]
    ((init_plan_state 0) with ps_stack := [Var "a"; Var "b"]))).ps_stack =
    [Var "a"; Var "b"] /\
  (SND (reorder_plan (dfg_build_function alias_probe_fn) [Var "r"; Var "a"]
    ((init_plan_state 0) with ps_stack := [Var "a"; Var "r"]))).ps_stack =
    [Var "r"; Var "a"]
Proof
  EVAL_TAC
QED

Theorem alias_probe_spilled_phi:
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    ["p"] F ((init_plan_state 0) with ps_spilled := FEMPTY |+ (Var "a",0))))
      .ps_spilled = FEMPTY |+ (Var "a",0) /\
  (release_dead_spills []
    ((init_plan_state 0) with ps_spilled := FEMPTY |+ (Var "a",0))).ps_spilled = FEMPTY
Proof
  EVAL_TAC >> simp[]
QED

Definition alias_probe_loop_fn_def:
  alias_probe_loop_fn = mk_raw_function "loop_probe"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 JMP [Label "header"] []] |>;
     <| bb_label := "header"; bb_instructions :=
         [mk_inst 1 CALLDATASIZE [] ["r"];
          mk_inst 2 JMP [Label "body"] []] |>;
     <| bb_label := "body"; bb_instructions :=
         [mk_inst 3 ASSIGN [Var "r"] ["a"];
          mk_inst 4 ISZERO [Var "a"] ["z"];
          mk_inst 5 JNZ [Var "z"; Label "header"; Label "exit"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 6 STOP [] []] |>]
End

Theorem alias_probe_loop_liveness:
  ~MEM "a" (live_vars_at (liveness_analyze alias_probe_loop_fn) "header" 0) /\
  MEM "a" (live_vars_at (liveness_analyze alias_probe_loop_fn) "body" 1) /\
  ~MEM "a" (live_vars_at (liveness_analyze alias_probe_loop_fn) "body" 2) /\
  normalize_operand (dfg_build_function alias_probe_loop_fn) [] (Var "a") = Var "r"
Proof
  EVAL_TAC >> simp[]
QED

(* Without dominance, liveness alone admits a stale alias at a root write. *)
Definition alias_probe_bad_loop_fn_def:
  alias_probe_bad_loop_fn = mk_raw_function "bad_loop_probe"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 JMP [Label "header"] []] |>;
     <| bb_label := "header"; bb_instructions :=
         [mk_inst 1 CALLDATASIZE [] ["r"];
          mk_inst 2 ISZERO [Var "a"] ["z"];
          mk_inst 3 JMP [Label "body"] []] |>;
     <| bb_label := "body"; bb_instructions :=
         [mk_inst 4 ASSIGN [Var "r"] ["a"];
          mk_inst 5 JMP [Label "header"] []] |>]
End

Theorem alias_probe_bad_loop_liveness:
  MEM "a" (live_vars_at (liveness_analyze alias_probe_bad_loop_fn) "header" 0) /\
  normalize_operand (dfg_build_function alias_probe_bad_loop_fn) [] (Var "a") = Var "r"
Proof
  EVAL_TAC >> simp[]
QED

Theorem eval_one_phi_without_predecessor:
  s.vs_prev_bb = NONE ==> eval_one_phi s inst = NONE
Proof
  simp[eval_one_phi_def] >> Cases_on `inst.inst_outputs` >> simp[]
QED

(* Used at each jump of the block induction, for the successor's alias
   premise.  The invariant reads only ps_stack and ps_spilled, so the
   lineage entry state of the successor (its DFS state with ps_after's
   stack and spill map, lineage_entry) inherits it from ps_after.  The
   block's code is the one lineage_state_block_plan regenerates from the
   lineage state ps, with the cleanup fields it chooses.

   The ownership premise is the planner's static entry invariant: every
   variable live into the block along the edge taken is on the stack or
   spilled.  Without it a block could copy (ASSIGN) a variable the planner
   doesn't hold, whose value need not be its root's after a loop
   iteration, and push the copy.

   Why it should hold: a variable defined in the block by ASSIGN of an
   owned operand takes that operand's value, which is its root's; any
   other definition is its own root.  A root's value only changes when
   its definition runs again, and by SSA and def_dominates_uses a
   variable derived from it is then no longer live, so the planner has
   dropped it: popped, overwritten by a PHI poke, or left behind at the
   join reorder of a JMP (every loop header is a join).  An INVOKE
   changes only its own outputs among the caller's variables.  Return-PC
   variables all read ra in the frame view, and so do their roots. *)

(* Notes from a statement check (intuition, not a prescribed proof):
   - Where the planner drops names (stackPlanGen): an operand dead after
     its instruction is consumed rather than duplicated; dead outputs are
     popped at the end of generate_regular_inst_plan when the block does
     not halt (PHI outputs likewise); after a JNZ clean_stack_plan pops
     dead names or marks them dead_stack_marker; release_dead_spills
     drops dead spills after each regular instruction.  reorder_one's
     alias step only swaps the names of two slots.  So a name in ps_after
     is a name of ps (stack or spill map) or an output of bb.
   - A name z live out of bb, not defined in bb, whose root is defined in
     bb, is impossible: bb dominates z's definition (def_dominates_uses,
     transitively along the ASSIGN chain), and an entry path that meets
     bb only at its end, followed by liveness_sound's witness path, misses
     z's definition.  A bb entered around a loop is a join (entry block
     has no predecessors), entered only by JMP (block_entries_ready),
     whose reorder leaves only names live into it.
   - The ps premises tie ps to vs only through ownership and the alias
     premise; ps's names beyond those are bounded by a static invariant
     of lineage states (their names are live out of the lineage
     predecessor, and the vars live along that edge are all held), which
     also covers a run with vs_prev_bb = NONE at a non-entry block.  The
     entry block has no live-in variables.
   - dead_stack_marker is Label "", and Lit/Label operands are fixed by
     normalize_operand, so only Var operands matter.  PHI and INVOKE
     outputs are their own roots.  For return-PC variables, copy_phi_var
     and retpc_shape_ok keep every link of the chain a return-PC
     variable, so both sides read ra. *)
Theorem lineage_alias_successor:
  !fuel ctx lo liveness dfg cfg ch growth spill_base lbl_ctr fn lbl bb ps h
   promised block_ops ps_after ra vs vs'.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    retpc_shape_ok fn /\ opaque_use_ok fn /\
    lineage_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    vs.vs_current_bb = lbl /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan liveness dfg cfg fn bb
      (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
      SOME (block_ops, ps_after) /\
    (!pred x. vs.vs_prev_bb = SOME pred /\
       MEM x (input_vars_from pred bb.bb_instructions
                (live_vars_at liveness lbl 0)) ==>
       MEM (Var x) ps.ps_stack \/ Var x IN FDOM ps.ps_spilled) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    run_block fuel ctx bb vs = OK vs' /\ ~vs'.vs_halted
    ==>
    !at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
      operand_val (frame_view fn ra vs') lo at =
      operand_val (frame_view fn ra vs') lo (normalize_operand dfg [] at)
Proof
  cheat
QED
