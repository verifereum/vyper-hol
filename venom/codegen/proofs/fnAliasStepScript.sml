(*
 * One instruction's step preserves the slot alias invariant of the block
 * induction (fnAliasInv): every operand on the planner's stack or in its
 * spill map has the value of its ASSIGN-chain root (normalize_operand),
 * read through the frame view.  The block body (fnBlockBody) carries it
 * from instruction to instruction; lineage_alias_successor carries it
 * across a whole block from the block's entry.
 *
 * TOP-LEVEL:
 *   alias_step_preserve - CHEATED: an instruction whose step is OK keeps
 *                         the invariant from its planner state to the next
 *)

Theory fnAliasStep
Ancestors
  fnAliasInv reorderSim frameRel codegenRel unitShapeDefs stackPlanGen
  stackPlanOps stackPlanTypes venomExecSemantics venomState livenessDefs
  dfgDefs cfgDefs

(* Used at each instruction of the block body whose step is OK: every
   non-terminator (INVOKE included), and a JMP or JNZ, after which ps' is
   the state the successor's lineage entry inherits its stack and spill
   map from.  Its static premises are fnBlockPlanStatic's
   block_plan_state_static conclusions.  The label premise is needed at
   vs only: operand_val reads labels from lo, but an ASSIGN of a label
   gives its output the value vs_labels has.

   Why it should hold: a step that is OK changes no variable but inst's
   outputs (step_inst_base; INVOKE binds its outputs into the caller's
   state, merge_callee_state).  By the freshness premise, no slot of ps
   is an output or has one as its root, so each slot of ps keeps both
   values.  Each slot of ps' is a slot of ps (moved, duplicated, restored
   or spilled), a literal or label (its own root, as is
   dead_stack_marker), or an output of inst.  The emitted operands are
   owned (ownership premise), and a JMP's join reorder may relabel an
   equivalent slot as a target variable, which pending_inventory_wf keeps
   to variables the state holds.  An output's root is itself unless inst
   is an ASSIGN (dfg_build_function and SSA make inst its dfg_defs
   entry); an ASSIGN's output takes its operand's value: an owned
   variable's, which is its root's by the invariant at vs; a literal; or
   a label's, which is lo's by the label premise.  Return-PC variables are
   copied only into return-PC variables (retpc_shape_ok), so the frame
   view reads ra on both sides of such an ASSIGN. *)
Theorem alias_step_preserve:
  !fuel ctx lo fn ra liveness dfg cfg inst next_live is_halting next_is_term
   bb_label ps ops ps' vs vs1.
    dfg = dfg_build_function fn /\ codegen_ready_fn fn /\ retpc_shape_ok fn /\
    MEM inst (fn_insts fn) /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v inst.inst_outputs) /\
    (inst.inst_opcode = JMP ==>
     !target target_bb target_stack.
       inst.inst_operands = [Label target] /\
       lookup_block target fn.fn_blocks = SOME target_bb /\
       target_stack =
         MAP Var (input_vars_from bb_label target_bb.bb_instructions
                    (live_vars_at liveness target 0)) ==>
       pending_inventory_wf target_stack ps) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    generate_inst_plan liveness dfg cfg fn inst next_live is_halting
      next_is_term bb_label ps = SOME (ops, ps') /\
    step_inst fuel ctx inst vs = OK vs1
    ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
      operand_val (frame_view fn ra vs1) lo at =
      operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)
Proof
  cheat
QED
