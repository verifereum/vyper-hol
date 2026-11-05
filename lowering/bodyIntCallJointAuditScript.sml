(* Diagnostic only: this quotation checks the proposed producer's binders and
   types. It does NOT assert the producer, and is not a simulation theorem.
   No new logical definition or axiom is introduced. *)
Theory bodyIntCallJointAudit
Ancestors
  bodyIntCallJointTuple bodyIntCallArgLifetime bodyIntCallGasPrefix
  bodyIntCallJointCounted bodyIntCallJointSingleton
  exprSimHypsDefs gasOutcome gasContext

val _ = ``
  !ctx func ce cx env e es ty sa sb vv s0 hs.
  expr_sim_pre ce cx env e es /\ supported_pure_expr (cx_tops cx) e /\
  compile_expr ce ty e sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\(off,len).
    (?aid b sz. aid < sa.cs_next_id /\
      FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\
      b <= off /\ off + len <= b + sz) \/
    (?name b sz. local_region ce es.scopes s0 name b sz /\
      b <= off /\ off + len <= b + sz)) hs ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee u. ?tv. res = INL tv /\
      vv_post ctx func ce cx e es sa sb s0 ee tv vv u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ee = es with <|outcomes := ee.outcomes; gas_obs := ee.gas_obs|> /\
      EVERY (\(off,len). mem_bytes_at off len u.vs_memory =
                            mem_bytes_at off len s0.vs_memory) hs /\
      (ce.ce_is_ctor ==> !name tv0 v off.
        FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
        FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
          NONE => FEMPTY | SOME imms => get_source_immutables ce.ce_module imms)
          name = SOME (tv0,v) ==>
        mem_bytes_at off (type_memory_size tv0) u.vs_memory =
        mem_bytes_at off (type_memory_size tv0) s0.vs_memory))
    (\res ee r. expr_exit res r)
``;

(* INTERFACE AUDIT (not a proof of the quoted proposition).

   Actual singleton child entry:
     sz = type_memory_bytes ce (expr_type e)
     t0 = t with vs_inst_idx := LENGTH sm.cs_current_insts
   where literal_alloc_buffer_run supplies the SAME p with
     eval_operand buf.buf_operand t0 = SOME p
     FLOOKUP t0.vs_allocas sa.cs_next_id = SOME (w2n p,sz).
   The compiler must supply sa.cs_next_id < sm.cs_next_id and
   safe_operand sm buf.buf_operand (the emitted buffer operand is a Var).
   Instantiate the quoted producer at sm, sn, t0, not sa, sb, s.

   PASS / MISSING implication matrix, assuming its ordinary vv_post at u:
   PASS: old lookup_var values, and every old allocation-map entry, directly
     from vv_post_def. In particular the original allocation id has the SAME
     pair (w2n p,sz) at u; no fresh existential pointer is selected.
   PASS conditional on compiler reservation: safe_operand sm buf.buf_operand
     and eval_operand buf.buf_operand t0 = SOME p imply its value at u is
     SOME p, using safe_operand_value_preserved. The general reserved-operand
     lemma additionally needs label equality; the safe Var needs none.
   PASS conditional on entry separation: old id < sm.next_id and disjointness
     from ALL entry locals imply preservation of this entire allocation's
     bytes, and of subwindows, by vv_post_old_allocation_window.
   PASS conditional on source frame: MAP FDOM es.scopes = MAP FDOM ee.scopes,
     entry local_ptrs_rel and reservation, together with vv_post's variables,
     give local_region ce ee.scopes u n b len ==> local_region ce es.scopes
     t0 n b len (local_region_frame). Thus entry buffer/local separation
     yields endpoint separation. Byte equality alone does not give this.
   MISSING from vv_post alone: EVERY protected-window byte equality for a
     window inside an entry allocation which overlaps a local, or inside a
     local region. locals_kept is not equality of every local byte.
   MISSING from vv_post alone: equality on initialized constructor immutable
     type_memory_size windows. stmt_state_rel supplies immutable semantics
     and allocation separation, not this concrete byte-equality assertion.
   MISSING as compiler side obligations: produced src is reserved at sn,
     hence different from sn's fresh ADD output; the output is not a source
     local pointer. These are not semantic consequences of vv_post.

   The quoted source-state equality supplies scope domains and the SAME
   immutable map for endpoint reasoning; it deliberately allows outcomes and
   gas_obs to change. supported_eval_expr_outcomes is the source boundary.
   Uninitialized immutable capacity beyond type_memory_size is NOT covered.

   Allocating-parent induction test:
   Entry hs windows must remain eligible at t0: old allocation records and
   increasing next_id transport the first alternative; local_region_frame_fwd
   transports the second. For the new parent buffer, add (w2n p,sz) to the
   child hs if its bytes must survive. It is now an old allocation at sm,
   regardless of whether it was fresh or reused at the parent entry.
   Parent writes require separation of this buffer from every original hs;
   joint_alloc_buffer_write proves that under exactly these two ownership
   alternatives. The child's additional full-window equality and constructor
   equality are still genuinely new induction conclusions, not IH facts
   obtained from body_expr_ok. Compose byte equalities t0 -> u -> suffix
   with the prefix equality s -> t0, keeping the SAME p throughout.

   Counted test:
   The allocation prefix currently gives gas_path 0, not a marked witness.
   Need the corresponding all-F marked prefix; then gas_outcome_zero_prefix
   transports the child outcome including exempt-certificate origin/focus.
   An ordinary child success needs an actual marked zero-read ADD/STORE
   suffix; the existing gas_path suffix alone does not certify the marked
   join. Error paths skip that suffix. Exempt outcomes carry no success post
   and must NOT be required to satisfy the above resource clauses.

   MsgGas test / smallest next genuine producer:
   Specialize the quoted proposition to e = Builtin ann (Env MsgGas) args
   and ty = expr_type e. In fact its hs ownership premise can be dropped:
   the concrete target endpoint is update_var out w of the entry with only
   vs_gas_readings dropped and vs_inst_idx advanced, so ALL memory windows
   are unchanged. Use the existing compile_msg_gas_prefix_outcome premises
   (expr_sim_pre, compile_expr, code/distinctness, reservation, state relation,
   not halted and entry PC); the semantic held-prefix premise is unnecessary
   for this byte-only post. Its [T] marked path supplies an ordinary outcome
   for all observation tails, source consumption w::tail -> tail. Its error
   post is false. gas_admissible may be retained to match the general API
   but is not used by that concrete proof. Reconstruct this strengthened post
   on the SAME concrete endpoint, not by combining its existential outcome
   with an independently chosen memory-frame outcome.

   Verdict: proposal typechecks; singleton ordinary resource consumption is
   feasible under the stated compiler/source side conditions, but the full
   window post and marked recursive composition remain unproved. This file
   neither implements a recursive producer nor closes the internal-call case.
*)
