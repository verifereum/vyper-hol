(*
 * Static facts about the planner state partway through a block: the
 * state block_plan_state names at instruction index k, when the block is
 * planned from its lineage state (fnPlanLineage, fnLineageStatic).  The
 * block body's induction (fnBlockBody) needs them at each instruction for
 * the planner-only premises of the instruction frame lemmas (fnFrameDeep),
 * of revert forwarding (fnFrameStepsRevertForwardDeep) and of the alias
 * step (fnAliasStep).
 *
 * TOP-LEVEL:
 *   block_plan_state         - the planner state at an instruction index
 *   block_plan_state_static  - CHEATED: at an instruction past the PHI
 *                              prefix, the state is well formed, holds the
 *                              instruction's variable operands, and nothing
 *                              on its stack or in its spill map stands for
 *                              one of the instruction's outputs
 *)

Theory fnBlockPlanStatic
Ancestors
  fnLineageStatic fnPlanPrefix fnPlanLineage reorderSim contextCodegenRel
  stackPlanGen stackPlanOps stackPlanTypes venomExecSemantics venomWf
  livenessDefs dfgDefs cfgDefs

(* The planner state at instruction index k of bb, when generate_block_plan
   plans bb from ps_in: the parameter and cleanup prefixes, then the
   non-parameter instructions before k. *)
Definition block_plan_state_def:
  block_plan_state liveness dfg cfg fn bb ps_in k ps <=>
    ?param_ops ps1 clean_ops ps2 pre_ops.
      (if bb = HD fn.fn_blocks then prepare_params_plan liveness fn ps_in
       else ([], ps_in)) = (param_ops, ps1) /\
      (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
       then clean_stack_plan liveness cfg fn bb ps1
       else ([], ps1)) = (clean_ops, ps2) /\
      LENGTH (get_params bb.bb_instructions) <= k /\
      generate_block_insts_prefix liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) 0
        (k - LENGTH (get_params bb.bb_instructions))
        (non_param_insts bb) ps2 = SOME (pre_ops, ps)
End

(* Used at each instruction of the block body's induction, for the
   planner-only premises of the step it takes there.  next_live and
   next_is_term are the lookahead generate_block_insts_plan passes for
   instruction k (live_vars_at at k + 1 in both of its cases, since the
   block length is k + 1 when k is last).  The opcode-guarded clauses are
   the premises of gen_jnz_frame_sim_deep, gen_jmp_frame_sim_deep,
   gen_ret_frame_sim_deep and (at a revert forwarding's RETURNDATACOPY)
   revert_forward_frame_sim_deep that the general ones don't cover.

   PHI-operand slots: lineage_state_static's freshness exempts the PHI
   operands of a join (a loop header x = phi(.., L: v) whose body
   redefines v is entered from L with v in x's slot).  None survives the
   PHI prefix: generate_phi_plan finds the topmost slot holding one of the
   PHI's variable operands (stack_get_phi_depth) and, when that operand is
   not live after the PHI, pokes the output over it (SOPoke dist ret)
   instead of duplicating it.  phi_block_ready (codegen_ready_fn) keeps
   every PHI operand dead after the prefix and out of the other PHIs, so
   the poke is the case taken.  This relies on the entry stack holding
   one operand per PHI, the one from the edge taken (input_vars_from);
   lineage_state_static does not say so of slots below the join's target
   stack.

   Why it should hold: lineage_state_static gives well-formedness and
   freshness at the block's entry.  The cleanup prefix only pops or marks
   slots, the PHI prefix overwrites its operands' slots (above), and each
   instruction before k pushes only its own outputs, distinct from inst's
   by SSA (ssa_form), whose ASSIGN-chain roots are defined before them and
   so are not inst's outputs either (def_dominates_uses).  A variable
   operand of inst is live before it, and the planner holds every live
   variable on its stack or in its spill map: the join entry stack is the
   live-in set, a single-predecessor block gets its predecessor's live-out
   set, and an instruction consumes a variable only at its last use.  The
   same holds for the JMP target's live-in variables, and the operands of
   a revert forwarding's instructions not defined inside it.  A RET block
   is not on a must-halt path, so it has no dead_stack_marker slots, and
   every slot but RET's operands is dead and popped before it (the DFS
   premises tie h and promised: the replay must emit the DFS block's ops,
   so its cleanup pops where the DFS one does).  A revert forwarding's code
   from k on has no spill or restore: its REVERT ends bb and its
   RETURNDATACOPY is in bb, so generate_block_plan would have rejected the
   replay (revert_block_spills) had the instruction ops, of which these
   are a suffix, held one.  OPEN: a dead OFFSET
   output is pushed and never popped (generate_offset_plan), which leaves
   a slot at RET; this conjunct needs that excluded.  The
   marker clauses hold since no instruction has the marker as an operand,
   and normalize_operand only follows ASSIGNs of operands. *)
Theorem block_plan_state_static:
  !liveness dfg cfg ch growth spill_base lbl_ctr fn fn_ops ps_end lbl bb
   ps_l ps_dfs ps_dfs_after h promised block_ops ps_after k ps inst next_live
   next_is_term.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
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
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
    ==>
    generated_plan_state_wf_marked spill_base ps /\
    MEM inst (fn_insts fn) /\ inst_wf inst /\
    ~is_param_opcode inst.inst_opcode /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_live ps)).ps_stack /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v inst.inst_outputs) /\
    (inst.inst_opcode = JNZ ==>
     !cond_op if_nz if_z.
       inst.inst_operands = [cond_op; Label if_nz; Label if_z] ==>
       1 <= LENGTH (SND (emit_input_plan JNZ [cond_op] next_live ps)).ps_stack /\
       (is_var_operand cond_op ==>
         IS_SOME (stack_get_depth cond_op ps.ps_stack) \/
         IS_SOME (FLOOKUP ps.ps_spilled cond_op)) /\
       cond_op <> dead_stack_marker /\
       (!at. operand_equiv dfg cond_op at ==> at <> dead_stack_marker)) /\
    (inst.inst_opcode = JMP ==>
     !target target_bb target_stack.
       inst.inst_operands = [Label target] /\
       lookup_block target fn.fn_blocks = SOME target_bb /\
       target_stack =
         MAP Var (input_vars_from bb.bb_label target_bb.bb_instructions
                    (live_vars_at liveness target 0)) ==>
       pending_inventory_wf target_stack ps) /\
    (inst.inst_opcode = JMP ==>
     !target target_bb target_stack.
       inst.inst_operands = [Label target] /\
       lookup_block target fn.fn_blocks = SOME target_bb /\
       target_stack =
         MAP Var (input_vars_from bb.bb_label target_bb.bb_instructions
                    (live_vars_at liveness target 0)) ==>
       LENGTH target_stack <=
         LENGTH (SND (restore_spilled_plan target_stack ps)).ps_stack /\
       EVERY (\op. op <> dead_stack_marker /\
         !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
         target_stack) /\
    (inst.inst_opcode = RET ==>
     !ops ps'.
       generate_inst_plan liveness dfg cfg fn inst next_live (bb_is_halting bb)
         next_is_term bb.bb_label ps = SOME (ops, ps') ==>
       ps'.ps_stack = []) /\
    (!j. revert_forward_pair bb k j ==>
     !k' inst' op.
       k <= k' /\ get_instruction bb k' = SOME inst' /\
       MEM op (compute_operands inst') /\ is_var_operand op /\
       (!k'' inst'' x. k <= k'' /\ k'' < k' /\
                       get_instruction bb k'' = SOME inst'' /\
                       op = Var x ==> ~MEM x inst''.inst_outputs) ==>
       MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!j. revert_forward_pair bb k j ==>
     !ops ps_end.
       generate_block_insts_plan liveness dfg cfg fn bb.bb_label
         (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
         (LENGTH bb.bb_instructions) (k - LENGTH (get_params bb.bb_instructions))
         (DROP k bb.bb_instructions) ps = SOME (ops, ps_end) ==>
       !off. ~MEM (SORestore off) ops /\ ~MEM (SOSpill off) ops)
Proof
  cheat
QED
