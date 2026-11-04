(* Safety-only observation boundaries for the LowerDload memory contract. *)
Theory lowerDloadSafetyBoundary
Ancestors
  o1PassContract unitTransformDefs unitShapeDefs lowerDloadRelocationBoundary

Theorem lower_dload_initial_allocations:
  o1_run_state_ok s ==>
  s.vs_allocas = FEMPTY /\ s.vs_vars = FEMPTY /\ s.vs_memory = [] /\
  ~s.vs_halted /\ s.vs_fmp = s.vs_initial_fmp
Proof
  simp[o1_run_state_ok_def, o1_initial_state_ok_def]
QED

Theorem shape_retpc_operand_boundary:
  fn_shape_ok fn /\ retpc_var fn x /\ MEM inst (fn_insts fn) /\
  MEM (Var x) inst.inst_operands ==>
  inst.inst_opcode = ASSIGN \/ inst.inst_opcode = PHI \/
  (inst.inst_opcode = RET /\
   ?front. inst.inst_operands = front ++ [Var x] /\ ~MEM (Var x) front)
Proof
  strip_tac >>
  `opaque_use_ok fn` by gvs[fn_shape_ok_def] >>
  drule_all opaque_use_ok_retpc_use >>
  simp[retpc_use_ok_def]
QED

(* C1.11.a consumer inventory (semantic definitions, not proof consumers).

   vs_requests: consume_call_outcome -> record_request appends rq (or leaves
   the list alone for computed precompiles); merge_callee_state copies it.
   No semantic helper selects from it or tests its length/content. It may
   be omitted from a safety-only relation; no historical taint mask needed.

   vs_logs: LOG appends an event; extract_venom_result appends new logs;
   consume_call_outcome/adopt_outcome appends oracle logs on success;
   merge_callee_state copies. No semantic consumer branches on old logs or
   imports them into accounts, transient state, operands or call input.
   make_venom_call_state/make_venom_create_state create fresh subcontexts,
   not subcontexts seeded with vs_logs. Omit historical logs for safety.

   vs_pending_deletions: consume_call_outcome/adopt_outcome_deletions prepend
   the oracle's co_toDelete on successful nonstatic calls; merge copies.
   Never inspected by a Venom instruction (no finalization inside run_context).
   May be omitted for safety, not for observational equivalence.

   vs_outcomes: consume_call_outcome calls take_outcome, which inspects the
   head on noncomputed calls, choosing success, returndata, account state
   and transient state. This field MUST remain related (equality suffices).
   Computed precompiles leave it unchanged. Equal outcomes alone is not
   enough: request target/data/static and relevant snapshot state still
   require their own input boundaries. Historical requests are not inputs
   to take_outcome. No numerical pointer is stored in an oracle queue by
   the LowerDload expansion.

   vs_return_pc_token: initialized from LAST args by setup_callee, read ONLY
   by RETPC_PARAM, restored from saved caller by merge_callee_state, and
   untouched by adopt_return_fmp. RETPC_PARAM places it in an ordinary
   variable, hence omission needs opaque-variable treatment, not blanket
   equality of untainted variables. shape_retpc_operand_boundary checks
   that all statically token-derived uses are ASSIGN, PHI or the UNIQUE
   final RET operand. RET evaluates its operand list but discards its final
   value with FRONT; it does not compare that value to any continuation.
   Numeric token values therefore need not agree, but definedness and
   propagation through selected copy/phi still must be in the relation.
   This restriction does NOT permit ignoring PARAM: a LAST args value read
   through PARAM uses the ordinary scalar/pointer relation, not opacity.

   Initial state: lower_dload_initial_allocations proves the map is EMPTY,
   not merely wellformed; identity initialization needs no initial sites.
   o1_run_state_ok by itself gives NO numerical bound on vs_alloca_next.
   It only constrains that field via downstream reachable-state premises
   in o1_src_inv (raw/headroom) and ptr_discipline's initial lo bound. A
   target-entry proof must use those premises and entry reachability,
   rather than invent an extra initial frontier assumption.

   Sources inspected: venomExecSemantics definitions exec_alloca,
   step_inst_base, extract_venom_result, setup_callee, merge_callee_state,
   adopt_return_fmp and call/create state constructors; venomCallOracleDefs
   consume_call_outcome and venom_call_request; extCallOracle take_outcome,
   record_request, adopt_outcome and adopt_outcome_deletions. State helper
   eval_operand/eval_operands read vars/labels, never historical fields.
   Full projected-step preservation is deliberately NOT claimed here.
*)
