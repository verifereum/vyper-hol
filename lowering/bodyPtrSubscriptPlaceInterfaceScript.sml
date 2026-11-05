(* Consumer-boundary diagnostic, not a concrete strengthening of J. *)
Theory bodyPtrSubscriptPlaceInterface
Ancestors
  loweringPosts bodyPtrPreds bodyPtrDefs targetPlaceSimCases

(* Identity depends only on compiler-local pointer lookups, not memory
   bytes. This does NOT transport read_result or place_readable. *)
Theorem place_ptr_rel_lookup_cong:
  (!x. lookup_var x s = lookup_var x t) ==>
  (place_ptr_rel cenv cx s pv w loc vt <=>
   place_ptr_rel cenv cx t pv w loc vt)
Proof
  strip_tac >> Cases_on `pv` >> simp[place_ptr_rel_def] >>
  Cases_on `p` >> simp[place_ptr_rel_def]
QED

(* Interface table (all four rows share the same ordinary implication):
   body_expr_ptr_ok_def, given body_inv and expr_body_pre, yields both
   expr_sim_ptr and expr_vv_sim_ptr. Under the full compiler/frame,
   gas_admissible and ghost hypotheses of expr_vv_sim_ptr_def, the latter
   yields gas_outcome_ptr with exactly vv_post, landing PC, ghost_inv,
   ptr_vv_ok, buffer coverage and ghost_kept. This is the checked ordinary
   counted contract, NOT an assertion of a normal run for every input.

   Constructor      ordinary contract   place identity    mapping extension
   Name             yes (above)         not supplied      not supplied
   TopLevelName     yes (above)         not supplied      not supplied
   IfExp            yes (above)         not supplied      not supplied
   Pop              yes (above)         not supplied      not supplied

   'not supplied' means no implication has been established here; it does
   not claim the constructor's actual compiler execution is unsound.
   The missing premise for the proposed whole-expression lift is a
   counted execution post relating the operand to the captured source
   place, plus a separate extended input-domain execution theorem for
   mapping-typed roots. Neither is a conjunct of body_expr_ptr_ok.

   Source of the distinction: vv_holds_def gives a read value's memory
   representation at the evaluated operand; vv_at_def gives allocation
   containment or local_val_at. Neither states place_ptr_rel for tv.
   The memory local in vv_at need not be the local named by the source
   place. ptr_vv_ok/buffer coverage adds provenance, not that identity.

   Name and TopLevelName can plausibly acquire identity from independent
   compiler leaf proofs, but the ordinary judgment is not that theorem.
   TopLevelName's mapping roots also fail the value-only typing premise.
   IfExp may retain an aggregate MemoryPlace via conditional_result_def;
   compile_expr uses compile_ifexp_arm to lay out each arm in memory.
   A source place and a copied representation must not be identified
   merely because their values agree. conditional_result rejects maps.
   Pop returns a captured element MemoryPlace or StoragePlace, while its
   ordinary pointer judgment records its value. Immutable pop returns a
   Value, not a source place. No uniform identity lifting is justified.

   Temporal boundary: place_ptr_rel_vars_frame is the existing general
   transport theorem (reused, not copied). Its hypotheses are an initial
   relation, local_ptrs_reserved at sa, and lookup equality at all old
   variables. The checked lookup congruence above isolates all remaining
   compiler-state dependence without any source read-value premise.
   The initial relation remains an additional obligation: transport does
   not manufacture it from vv_post. Compiler memory may change, and source
   scopes may change, without changing this address relation.

   In x[i][x[i].pop()], source pop_place_def shortens the array and records
   popped history before returning a captured path. place_readable_def's
   comment explicitly warns about this case. Capturing an address before
   the index runs does not assert that read_result at the old and new
   source states agrees. Child readability and representation must be
   established at the post-index source state, separately from address
   transport. No unchanged-value lemma is proposed.

   Feasibility verdict: do not instantiate the accepted induction kernel
   with ordinary safety plus universal place identity on current evidence.
   Its nonselector lift provides only the whole-expression ordinary
   judgment, not operand IHs or an identity-producing execution theorem.
   Mapping-only J still needs independent root execution. Strategist
   review is required to choose a copy-tolerant consumer invariant or
   expose constructor-specific strengthened premises in the kernel.
   This diagnostic is not a counterexample to the frozen target.
*)
