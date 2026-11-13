Theory fnPlanLineageStages
Ancestors
  fnPlanLineageReplay stackPlanGen stackModel

(* Exact record frame: in particular neither output freshness nor liveness
   is needed, and every non-stack field is unchanged. *)
Theorem generate_offset_plan_frame:
  inst.inst_operands = [Lit v; Label l] /\ inst.inst_outputs = [x] ==>
  generate_offset_plan inst ps =
    ([SOPushOfst l (w2n v)],
     ps with ps_stack := ps.ps_stack ++ [Var x])
Proof
  simp[generate_offset_plan_def, stack_push_def, listTheory.SNOC_APPEND]
QED

(* Proposed integrated certificate, for strategist review, not a theorem:

   Parameters: program point, common physical suffix K, residuals P and Q,
   query footprint U, cleanup candidate list D, and a common allocator a.
   p.stack = P ++ K and q.stack = Q ++ K. K includes dead OFFSET outputs;
   neither residual nor K is required to be a set or fresh on loop visits.
   p.alloc = q.alloc = a, with equal label counter and other static fields;
   cleanup bookkeeping is independent on the two sides.

   Query shielding means every search used at the next stage is either a
   common hit within K or an agreed miss in BOTH full stacks and spill maps.
   PHI searches the physical stack top-first for membership in its operand
   alternatives, NOT the alternatives in operand order. It needs equal
   selected depths and matching renamed suffixes, not equality of incoming
   names or just each live variable's membership. Length-sensitive swaps/dups additionally need the
   touched window to lie within K (or a separate saturation equivalence).
   Persistent spills must agree on all future-observable variables and their
   slots; scratch spilling must return equal allocator effects and preserve
   that agreement. Equal emitted ops alone supplies neither condition.

   Cleanup requires equality of its to_pop and to_keep lists and the
   below_all_live test, plus a proved relation for the remaining residuals.
   For arbitrary variable prefixes this is NOT supplied by marker-prefix
   cleanup. A reset may change K/P/Q but must re-establish these conditions,
   not delete physical cells on the strength of semantic deadness.

   Premise / proposed producer / current validation
   -------------------------------------------------------------
   OFFSET record frame / generate_offset_plan_frame / proved above;
     extends K by [Var x] without freshness, frames all other fields.
   Repeated name / instruction-list path / bounded residual_loop_laps;
     repeated r survives in bottom prefix; no ALL_DISTINCT producer exists.
   Shared live query hit / liveness transfer + previous certificate /
     MISSING global producer: live membership alone does not locate a hit
     in the common suffix, nor rule out stale PHI alternatives.
   PHI depth/rename agreement / phi_operands_ready + edge certificate /
     MISSING: readiness is syntactic, not top-first physical search shielding.
   Matching cleanup lists / previous certificate + cleanup partition /
     existing Inventory clean_stack_plan_prefix_replay handles marker
     prefixes only; MISSING arbitrary-variable-prefix producer.
   Bounded physical windows / previous stage + primitive preconditions /
     Inventory do_dup_prefix_replay provides conditional replay only;
     MISSING reachable-stage producer of top_n and depth hypotheses.
   Persistent spill alignment / previous stage, release_dead_spills and
     joint allocator transitions / MISSING global preservation producer;
     bounded loop and diamond have empty spills, equal allocator.
   Join target suffix / join_reached + liveness convergence /
     SOME guarantees suffix, not residual erasure, query shielding or spill
     alignment. residual_loop_laps shows bottom dead duplicates accumulate.
   Initial static fields / init_cleanup_plan_state and frozen lineage
     splice / syntactically available; initialization of full certificate
     and DFS establishment still need separate proofs.

   These are open producer obligations, NOT extra hypotheses allowed on the
   frozen theorem. The bounded ready, whole-plan-SOME tests in ResidualProbe
   validate only the frame and local reset behavior. They do not establish
   this certificate or refute lineage_state_block_plan. The universal
   residual_loop_header_symbolic/body_symbolic equations and
   residual_loop_unbounded recurrence now validate arbitrarily many laps
   with exact full-record frames. residual_loop_splice checks the syntactic
   stack/spill splice. This loop still has empty spills and trivial cleanup;
   it supplies none of the missing general producers above, and does not
   prove frozen-predicate reachability. Review this interface before any
   global preservation proof is attempted.
*)
