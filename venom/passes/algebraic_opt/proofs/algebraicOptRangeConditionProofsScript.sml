Theory algebraicOptRangeConditionProofs
Ancestors
  rangeAnalysisProofs rangeAnalysisDefs dfgAnalysis venomInst finite_map

(* Conditional interfaces: producer provenance is a separate obligation. *)
Theorem ao_range_condition_assign_local:
  !dfg fuel v inst op b rs env.
    dfg_get_def dfg v = SOME inst /\ inst.inst_opcode = ASSIGN /\
    inst.inst_operands = [op] /\
    in_range_state (range_apply_condition dfg fuel op b rs) env ==>
    in_range_state (range_apply_condition dfg (SUC fuel) (Var v) b rs) env
Proof
  rpt strip_tac >> simp[Once range_apply_condition_def]
QED

Theorem ao_range_condition_iszero_local:
  !dfg fuel v inst u b rs env.
    dfg_get_def dfg v = SOME inst /\ inst.inst_opcode = ISZERO /\
    inst.inst_operands = [Var u] /\ in_range_state rs env /\
    (b ==> FLOOKUP env u = SOME 0w) /\
    (~b ==> !w. FLOOKUP env u = SOME w ==> w <> 0w) ==>
    in_range_state (range_apply_condition dfg (SUC fuel) (Var v) b rs) env
Proof
  rpt strip_tac >> simp[Once range_apply_condition_def] >>
  irule range_apply_iszero_sound >> metis_tac[optionTheory.SOME_11]
QED

(* Runtime-premise audit (not additional asserted invariants).

   range_apply_condition recurses only through ASSIGN. ISZERO, EQ and
   LT/GT/SLT/SGT are terminal refinements; PHI and other producers are identity.
   Thus an ASSIGN chain needs current evaluation equality at every link,
   followed by operand facts for one terminal producer, not global dfg_sound.

   Checked obstruction: algebraicOptFreshnessProbe.ao_fresh_fixture_wf and
   ao_fresh_second_phis describe entry -> header -> body -> header. After
   the second parallel PHI batch, x=1 and old z=1, although z=ISZERO x.
   ao_fresh_unrestricted_transport_fails checks this mismatch by evaluation.
   The PHI selecting old z observes the predecessor state (old x=0), not
   the post-batch state. At the next actual ordinary use of z, its ISZERO
   producer has executed again: ao_fresh_selected_edge_and_ordinary_equations
   checks these two legitimate observation points. This refutes universal
   stored-producer equations, not correctness of a used branch condition.

   Available source boundary: ao_source_trace_last_iszero in
   algebraicOptFreshnessProofs supplies a last successful producer event,
   output-value preservation, and operand-evaluation transport to an ordinary
   observation with def_available_at. Its selected_phi counterpart observes
   the selected predecessor before PHIs. Together with ao_iszero_producer_step
   these justify the ISZERO relation at that observation, conditional on its
   stated lookup, producer-location and availability premises. A branch's
   evaluated Var condition supplies the non-NONE lookup. Frozen wf_ssa gives
   availability for its actual ordinary use. Trace initialization and source
   location bridges must still be discharged, not silently assumed.

   Missing generalization for ASSIGN-chain integration: from a last execution
   of each used ASSIGN, transport its operand value to the branch observation,
   and justify availability of that operand there even though it is not a
   syntactic operand of JNZ. The ISZERO-specific last-event theorem is not a
   generic producer-stability theorem and cannot simply be applied to ASSIGN,
   EQ or comparisons. Need an actual trace suffix with no writes to the
   relevant operands, justified by dynamic order/dominance, not arbitrary
   all-stored-variable stability. No such general implication is claimed here.

   Terminal signature ledger (rangeAnalysisProofs):
   - range_apply_iszero_sound needs zero/nonzero consequences for the current
     operand lookup; ao_range_condition_iszero_local exposes a sufficient form.
   - range_apply_eq_sound needs, on a true condition, defined variable operands,
     variable/literal equality, and equality of variable/variable values.
     Historical EQ execution alone is insufficient without operand transport.
     False EQ adds no refinement and needs no equality equation.
   - range_apply_compare_sound needs the actual signed/unsigned comparison
     truth equivalence for each variable/literal orientation. Variable/variable
     comparisons do not refine ranges. Again current operand transport is the
     missing provenance obligation, not a new numeric narrowing proof.

   These conditional boundaries do not establish reachable range soundness.
*)
