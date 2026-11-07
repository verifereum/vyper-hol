Theory bodyPtrStructLitCutProbe
Ancestors fragGasPathPtr fragExec venomExecSemantics
  bodyPtrStructLitPhaseInvariant bodyPtrStructLitPathBoundary

(* A successful ordinary fall-through cannot enter instruction zero of a
   block. This tests a real incoming-edge restriction, not a count argument:
   the edge count is arbitrary and may be zero. *)
Theorem structlit_zero_index_incoming_terminator:
  gas_path_ptr_edge D lo ctx fn PG G tn s n H un (OK t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  t.vs_inst_idx = 0 ==>
  is_terminator inst.inst_opcode
Proof
  simp[gas_path_ptr_edge_def] >> rpt strip_tac >>
  gvs[fragExecTheory.exit_result_def] >>
  qpat_x_assum `OK _ = _` (assume_tac o SYM) >>
  fs[fragExecTheory.exit_result_def]
QED

(* Concrete consumer ledger (diagnostic, not a dominance theorem).

   There is no assembled general aggregate simulation consumer in source:
   bodyPtrStructLitScript still contains only the frozen target admission.
   The available child boundary is expr_sim_ptr_def (bodyPtrDefs:267-294).
   Its initial cursor is sa.cs_current_bb, LENGTH sa.cs_current_insts; its
   NORMAL supplied endpoint is sb.cs_current_bb, LENGTH sb.cs_current_insts.
   The actual aggregate allocation precedes fields: exprLowering:2984-2995
   computes compile_alloc_buffer total_size sa=(buf_alloc,st2), then
   compile_struct_lit ... st2=(_,st3). At each field, the child starts at
   that field's compiler entry, NOT at the aggregate's sa. Consequently a
   phase intended to recover the aggregate allocation from a child path
   cannot silently assert that the child starts before that allocation:
   its initial alternative must be C, which is precisely an outer resource
   to be carried through the child simulation.

   The other concrete endpoint consumer is UniversalCandidate:69-80:
   lower_value compile_expr structlit_universal_env
     (expr_type structlit_universal_call) structlit_universal_call
     (initial_compile_state "caller")
   emits ALLOCA id=0 p="%0" size=128 at ("caller",0), then INVOKE id=1,
   ending at ("caller",2). The 160-byte annotated capacity obstruction
   needs the actual supplied final ghost binding, not a freshly selected
   execution endpoint. Its existing fixture does not supply body_inv or a
   successful actual unit, so it is NOT a legal frozen-target counterexample.

   Exact proposed contract shape for that call in a legal general frame:
     body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
     lower_value compile_expr ce ty e sa=(Var p,sb) /\
     fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
     local_ptrs_reserved ce sa /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
     (!x sz. ce.ce_return_buf=SOME(PtrVar(Var x)sz) ==> not_fresh_at sa x) /\
     (!x sz. ce.ce_return_pc=SOME(PtrVar(Var x)sz) ==> not_fresh_at sa x) /\
     gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
     stmt_state_rel ctx fn ce cx es s0 /\ ghost_inv d ce cx es G0 tn0 s0 /\
     ~s0.vs_halted /\ s0.vs_current_bb=sa.cs_current_bb /\
     s0.vs_inst_idx=LENGTH sa.cs_current_insts /\
     gas_path_ptr (cx_dead cx) 0 ctx fn PG G0 tn0 s0 k G tn (OK t) /\
     expr_post ctx fn ce cx e es sa sb s0 ee v (Var p) t /\
     t.vs_current_bb=sb.cs_current_bb /\ t.vs_inst_idx=LENGTH sb.cs_current_insts
     ==> ?b. FLOOKUP G p = SOME(b,128).
   Here e must be the linked narrow-return call and its exact emitted prefix
   must be established from the compiler equation (not added reachability).
   The other normal child conjuncts ghost_inv, ptr_val_ok, ptr_buf_ok and
   ghost_kept may also be used. Their inclusion does not itself prove the
   displayed conclusion. The fixed UniversalCandidate cannot be substituted
   into this contract without constructing the legal body_inv-linked frame.

   Candidate B s = (s.vs_current_bb=sa.cs_current_bb /\
                     s.vs_inst_idx <= LENGTH sa.cs_current_insts).
   Candidate C H un s = (?b. FLOOKUP H p=SOME(b,128)).
   For the exact two-instruction call, start cursor implies B; end cursor
   implies ~B. For the aggregate's buffer across a child, start is generally
   outside B and initial C must instead come from the outer allocation.
   This B does NOT yet meet the phase theorem's global crossing premise:
   every earlier index in the block lies in B, including instructions before
   the fragment. A terminator there may leave B without allocating p.
   Restricting B to the one allocation PC removes those earlier states but
   still permits exits and re-entry through other blocks; it does not solve
   C preservation outside B. No justified global B is established here.
   If the desired conclusion is a witnessed allocation edge rather than a
   ghost-state binding, the phase theorem cannot encode that history at all;
   a snoc/history argument would be needed, without count-decrease induction.

   Incoming-edge ledger, exactly gas_path_ptr_edge_def alternatives:
   * ordinary nonterminator: destination idx=SUC source idx, ghost_step.
     The checked theorem above excludes entry at index zero. For a nonzero
     allocation continuation ordinary fall-through still needs exact source
     instruction identification and its step_prov transfer. Ownership alone
     says which instruction can write p, not that this predecessor was run.
   * JUMP/JNZ: terminator entry may evaluate phis, giving phi_prefix_length,
     or the forward alternative may give jump_to lbl s and unchanged ghost.
     Thus other blocks can enter a prefix. Need actual label/phi/control
     facts at the selected boundary; arbitrary suffix confinement is invalid.
   * INVOKE: outer step_inst summarizes a nested callee run, then an ordinary
     continuation can increment caller index. The nested execution is NOT an
     outer gas_path_ptr subpath. C preservation needs the actual ghost_step
     INVOKE behavior and linkage/callee facts. CallPath rules out using the
     obsolete literal return-frame MLOAD branch to exclude all linked calls.
   * return/exit: halted terminators give Halt, and exit_result branches do
     not give a successful OK endpoint. They cannot be ignored before normal
     outcome selection. A callee return inside INVOKE is summarized above.
   * revert-forward: non-INVOKE terminator forward edge leaves ghost unchanged;
     ptr_safe_step retains its own in_revert_forward behavior. There is no
     blanket pointer exemption in gas_path_ptr_edge itself. gas_outcome_ptr
     separately permits gas_exempt_cert, which gives no checked path; a cut
     argument must be conditional on the normal gas_summary/path alternative.
   * reflexive success: success_snoc allows k=0,t=s0,G=G0,tn=tn0. Only distinct
     actual cursor equations (not merely source success) exclude this case.
   * ALLOCA edge itself has count zero (structlit_alloca_counted_edge), so even
     a nonreflexive path may have k=0. Counts cannot witness allocation.

   Decision: the ordinary-entry exclusion is checked, but global crossing
   and INVOKE ghost preservation are NOT supplied by the consumer premises.
   Next strategy review must choose between an actual region incoming-edge
   contract plus a linked INVOKE preservation theorem, or a producer/call
   simulation interface. Do not manufacture either as an unexplained new
   premise. Static unit writer uniqueness is now available (OwnershipUnits)
   and does not fill this control-position/history gap. This diagnostic does
   not certify the cut or refute structlit_expr_ptr_ok.
*)
