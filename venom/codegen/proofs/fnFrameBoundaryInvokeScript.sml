(*
 * Helpers for fnFrameBoundary$gen_invoke_frame_sim: the INVOKE step
 * against frameRel$fn_frame_inv, given the callee's function simulation.
 *
 * Notes from the statement check (intuition only; read or ignore):
 * - Label arguments: unit_shape_ok gives fn_shape_ok fn, whose
 *   label_positions_ok forbids Label operands among INVOKE's arguments
 *   (unitShapeDefs), so compute_operands inst = arg_ops.
 * - Callee arity: fmp_lowered_context_wf gives invoke_layout_wf;
 *   invoke_input_arity_ok with canonical_param_prefix (callLayoutDefs)
 *   gives LENGTH args + 1 = LENGTH (get_params entry block) when the
 *   callee has a RETPC_PARAM.
 * - INVOKE arguments and outputs are never return-PC variables
 *   (opaque_use_ok / retpc_use_ok; retpc_shape_ok), so the frame view
 *   reads them as the plain state does.
 * - The caller's spill slots lie in its own region r (spill_alloc_layout_wf,
 *   allocMono's fixed spill base / growing next offset); ordered_spill_regions
 *   makes two MEM regions sharing a byte the same region, so a caller slot
 *   in the callee's closure means fcg_path nm fn.fn_name, a reachable cycle
 *   with the edge fn -> nm (fcgPostorder's reachable_fcg_acyclic lemmas).
 * - The asm semantics has no stack limit and JUMP only looks up o2pc.
 * - INVOKE can have several outputs, so the dead-output popmany postfix
 *   needs a general lemma (regularPostfixSim's structural lemma covers at
 *   most one output).
 * - fnBoundaryProps is downstream of fnFrameBoundary (via venomToAsmProps),
 *   so its small boundary lemmas can't be imported here.
 *)

Theory fnFrameBoundaryInvoke
Ancestors
  fnFrameBoundaryGenRet genFrameSim frameRel contextCodegenRel codegenRel
  regularPostfixSim preparedPrefixSim asmFrame prefixSim stackOpSim
  unitShapeDefs genBlockSim stackPlanGen stackPlanTypes planExec asmSem
  venomExecSemantics venomState venomInst fcgDefs livenessDefs dfgDefs
  venomWf venomEffects stackPlanOps asmIR frameViewFacts finite_map
  callLayoutDefs fmpWfDefs list rich_list reorderSim planWf stackModel
