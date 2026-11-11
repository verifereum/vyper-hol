(*
 * The instruction frame lemmas the block induction composes, restated for
 * any stack depth and for a planner state with cleanup markers.
 *
 * The planner reaches an operand deeper than DUP16 by spilling the slots
 * above it, DUP16 and restoring them (stackPlanOps' do_dup), and nothing
 * bounds the stack's depth; a cleanup elision (clean_stack_plan's
 * mark_dead_stack) leaves dead_stack_marker in several stack slots.  Each
 * <lemma>_deep is <lemma>'s statement with
 *   - ownership "on the stack at depth <= 15, or spilled" weakened to "on
 *     the stack at any depth, or spilled";
 *   - generated_plan_state_wf weakened to generated_plan_state_wf_marked
 *     (fnPlanPrefix), which allows repeated marker slots;
 *   - prefix_spill_wf (gen_jmp_frame_sim: reorder_steps_spill_ready)
 *     weakened to an address bound on the plan's spill and restore
 *     offsets: an abstract spill map keyed by operand can't hold two
 *     marker slots spilled together;
 *   - for gen_jmp_frame_sim, no bound on the target stack's length.
 * Each lives in its own leaf, collected here.
 *
 * TOP-LEVEL (by ancestry):
 *   gen_inst_frame_sim_deep         - fnFrameDeepInst
 *   gas_inst_frame_sim_owned_deep   - fnFrameDeepGas
 *   gen_inst_halt_frame_sim_deep    - fnFrameDeepHalt
 *   gen_inst_abort_frame_sim_deep   - fnFrameDeepAbort
 *   gen_ret_frame_sim_deep          - fnFrameDeepRet
 *   gen_invoke_frame_sim_deep       - fnFrameDeepInvoke
 *   gen_jnz_frame_sim_deep          - fnFrameDeepJnz
 *   gen_jmp_frame_sim_deep          - fnFrameDeepJmp
 *)

Theory fnFrameDeep
Ancestors
  fnFrameDeepInst fnFrameDeepGas fnFrameDeepHalt fnFrameDeepAbort
  fnFrameDeepRet fnFrameDeepInvoke fnFrameDeepJnz fnFrameDeepJmp
