Theory bodyPtrBopInLiteralBoundary
Ancestors
  exprLowering compileEnv ptrDiscipline
  codegenRel contextCodegenRel memLocDefs list

Theorem list_membership_empty:
  compile_list_membership_in needle [] st = (Lit 0w, st) /\
  compile_list_membership_notin needle [] st = (Lit 1w, st)
Proof
  simp[compile_list_membership_in_def, compile_list_membership_notin_def,
       emit_membership_eqs_def, comp_bind_def, comp_return_def]
QED

Theorem membership_eq_access:
  inst.inst_opcode = EQ /\
  (!v. MEM (Var v) inst.inst_operands ==> v NOTIN FDOM G) ==>
  access_ok lo G fn inst s
Proof
  strip_tac >>
  simp[access_ok_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, mem_write_ops_def, mem_read_ops_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[MEM]
QED

Theorem membership_eq_taint:
  inst.inst_opcode = EQ /\
  (!op. MEM op inst.inst_operands ==> op_taint tn op = {}) ==>
  taint_ok fn tn inst s
Proof
  strip_tac >>
  simp[taint_ok_def, source_memory_read_ranges_def, mem_read_ops_def] >>
  metis_tac[]
QED

(* Literal-specific interface diagnostic (not an operand-composition theorem).
 *
 * Available expression interface:
 * - bodyPtrDefs.expr_sim_ptr_def, successful post (lines 234-241):
 *   expr_post ... /\ ghost_inv ... /\ ptr_val_ok ... /\ ghost_kept ...,
 *   and the compiler endpoint cursor. expr_post (loweringPosts, 251-265)
 *   keeps lookup_var for not_fresh_at entry variables and old allocations.
 * - exprSimOperators.expr_sim_pre_lower_value_word_shape (106-112):
 *   lower_value ... = (op,sb), expr_sim_pre, word typing give cs_extends,
 *   monotone counters, op=Var z ==> not_fresh_at sb z, and op<>Label l.
 * - bodyPtrDefs.ghost_kept_def (100-117) preserves FLOOKUP G and op_taint
 *   for not_fresh_at entry variables. Thus a live needle's taint and any
 *   already-established absent provenance survive the element judgment.
 * - exprSimOperands.expr_post_operand_kept (213-222) keeps expr_val_rel
 *   and expr_val_in_alloca, given operand shape, scope-domain stability,
 *   local_ptrs_reserved, counter monotonicity, and both expression posts.
 * - bodyPtrPreds.body_exprs_ptr_ok_def (61-67) exposes its tail only after
 *   actual successful eval_expr AND read_result; not an EVERY judgment.
 *
 * Missing derivations, not assumed by these lemmas:
 * - ptr_val_ok (bodyPtrDefs 136-140) gives clean op_taint for word values,
 *   but no condition on G. ghost_inv (80-93) constrains live local pointers,
 *   return-buffer coverage, return-PC taint and storage taint, not absence
 *   of provenance on arbitrary word results. A compiler/path boundary must
 *   establish absent provenance for produced word Vars (or the matching
 *   region alternative of access_ok). Shape/freshness alone is not that fact.
 * - No counted compile_multi_exprs pointer composition interface was found;
 *   it must carry earlier operand values, taints/provenance and conditional
 *   source-success witnesses while composing the actual gas_outcome paths.
 *
 * Singleton suffix obligation table (exprLowering 705-729):
 * In: EQ [needle;elem]. NotIn: same EQ, then ISZERO [eq_result].
 * EQ access: no memory ranges; for two Vars with either in FDOM G require
 *   both in one positive-size region and both evaluated addresses inside
 *   its closed bounds. membership_eq_access handles the absent alternative.
 * EQ taint: both operands clean (membership_eq_taint).
 * ISZERO access: no memory ranges and no pointer comparison condition.
 * ISZERO taint: EQ result clean; must derive from step_taint for EQ.
 * Both: ambient allocas_from, dalloca bound, request/halt side conditions
 *   of ptr_inst_ok, instruction lookup and successful concrete execution;
 *   step_prov/step_taint output facts, ghost_inv and ghost_kept preservation,
 *   plus cursor/boolean-value post. Counted edges must be constructed with
 *   fragGasSeqPtr.straight_line_ptr_edge or run_inst_seq_gas_path_ptr; erased
 *   S1 paths do not supply any of these ghost or per-edge checks.
 *)
