(* Safety-only observation boundaries for the LowerDload memory contract. *)
Theory lowerDloadSafetyBoundary
Ancestors
  o1PassContract unitTransformDefs unitShapeDefs lowerDloadRelocationBoundary
  ptrDiscipline finite_map list fcgDefs

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

Theorem provenance_operand_erasure:
  !e H op. op_prov (e o_f H) op = OPTION_MAP e (op_prov H op)
Proof
  Cases_on `op` >> simp[op_prov_def, FLOOKUP_o_f] >>
  rpt gen_tac >> Cases_on `FLOOKUP H s` >> simp[]
QED

Theorem provenance_arguments_erasure:
  !e H ops.
    MAP (op_prov (e o_f H)) ops = MAP (OPTION_MAP e) (MAP (op_prov H) ops)
Proof
  Induct_on `ops` >> simp[provenance_operand_erasure]
QED

Theorem provenance_phi_erasure:
  !e H prev inst.
    phi_prov prev (e o_f H) inst = OPTION_MAP e (phi_prov prev H inst)
Proof
  rpt gen_tac >> Cases_on `prev` >> simp[phi_prov_def] >>
  Cases_on `resolve_phi x inst.inst_operands` >>
  simp[provenance_operand_erasure]
QED

Theorem provenance_return_erasure:
  !e H outs.
    e o_f (DRESTRICT H (COMPL (set outs))) =
    DRESTRICT (e o_f H) (COMPL (set outs))
Proof
  rpt gen_tac >> simp[fmap_eq_flookup] >> gen_tac >>
  Cases_on `x IN set outs` >> simp[FLOOKUP_o_f, FLOOKUP_DRESTRICT]
QED

Theorem provenance_param_erasure:
  !e Q H inst s idx.
    inst.inst_opcode = PARAM /\ inst.inst_operands = [Lit idx] ==>
    out_prov (MAP (OPTION_MAP e) Q) (e o_f H) inst s =
    OPTION_MAP e (out_prov Q H inst s)
Proof
  rpt strip_tac >> simp[out_prov_def] >>
  Cases_on `w2n idx < LENGTH Q` >> simp[EL_MAP]
QED

(* C1.11.b selected-identity feasibility equations.

   Represent an identity by num#num (activation serial, source aid). Choose
   a TOTAL erasure e : (num#num)->(num#num) for the currently live identities;
   e(serial,aid)=(source base,size). A total map is harmless outside selected
   identities, where it is not used. Maintain G=e o_f H and
   PG=MAP (OPTION_MAP e) Q. This does not invert e. Zero-sized identities
   can be distinct even when e maps them to the same pair.

   PARAM: the selected identity output is EL (w2n idx) Q when in bounds,
   NONE otherwise. provenance_param_erasure proves the corresponding
   out_prov equation. Scalar arguments at declared pointer positions use
   NONE, not an arbitrary site; static pointer membership need NOT imply
   dynamic identity presence. Invalid indices do not produce a successor.

   PHI: use resolve_phi prev operands to select exactly the same operand
   in H as in G. provenance_phi_erasure proves the selection equation.
   At an entry run all PHIs in parallel from H0, updating output identities
   from selected H0 operands; scalar selected alternatives stay NONE.
   No domain completeness assumption on syntactic pointer variables is valid.

   Caller push: for Var v select FLOOKUP H v, otherwise NONE, exactly
   op_prov H. provenance_arguments_erasure gives the PG erasure equation.
   Save H,Q alongside cf_prov,cf_params. This permits scalar arguments to
   declared pointer positions without inventing identities.

   Return: DRESTRICT H (COMPL (set inv.inst_outputs)); restore saved Q.
   provenance_return_erasure checks this commutes with G erasure. Returned
   results have no selected identity. That is sound only if pointer-valued
   operands cannot be ordinary return values: fn_ptr_ok/ptr_use_ok forbids
   syntactic pointer-derived variables in RET (RET has no mem access operand
   and is not pointer-preserving). The final opaque RETPC_PARAM-derived
   operand instead uses shape_retpc_operand_boundary and is discarded by RET.

   Needed completeness shape, NOT proved here: each bound original variable
   is either (a) selected H identity with modular pointer agreement, (b)
   retpc_var fn with arbitrary but defined opaque word, or (c) scalar with
   word_agree_except its source taint. If a variable is not syntactically
   pointer-derived it cannot have a selected identity. The converse fails:
   pointer-declared PARAM may receive a scalar, and selected PHI may select
   such a scalar. Thus G=e o_f H suffices for source provenance erasure but
   must be accompanied by this dynamic VALUE classification in a relation.
   ASSIGN and scalar-selected PHI preserve (c); affine ADD/SUB needs the
   existing fn_ptr_ok affine_pointer_ops restriction for (a). Opaque copies
   are handled independently of pointer identity; overlap of static classes
   requires checking the chosen priority, not demanding both word equations.

   These equations validate the proposed ghost interface only. They are not
   a provenance-completeness induction or a paired execution proof.
*)

Theorem list_precedes_transitive:
  !xs x y z.
    list_precedes x y xs /\ list_precedes y z xs ==>
    list_precedes x z xs
Proof
  simp[list_precedes_iff] >> rpt strip_tac >> gvs[] >>
  qexistsl_tac [`i`, `j'`] >> simp[] >> decide_tac
QED

Theorem list_precedes_distinct:
  !xs x y. list_precedes x y xs ==> x <> y
Proof
  simp[list_precedes_iff] >> rpt strip_tac >> gvs[]
QED

(* C1.11.c stack charging and prefix interface diagnostic.

   Strict stack invariant proposed for frame_reachable vs C stk PG G tn fn i s:
     EVERY (\f. MEM f.cf_fn C.ctx_functions) stk /\
     MEM fn C.ctx_functions /\
     (!k. k < LENGTH stk ==>
         list_precedes fn.fn_name (EL k stk).cf_fn.fn_name names) /\
     (!j k. j < k /\ k < LENGTH stk ==>
         list_precedes (EL j stk).cf_fn.fn_name
                       (EL k stk).cf_fn.fn_name names).
   Stack order is most recent caller first; function names increase with
   stack index. On call, callee_first gives callee BEFORE current caller,
   not after. list_precedes_transitive propagates this to older frames;
   list_precedes_distinct excludes recursive active-name reuse. On return
   remove the active callee and the top caller record, restoring that caller.
   Membership must come from lookup_function and context shape, not from
   list_precedes alone. A general frame_reachable stack invariant remains
   to be proved; these two checked order lemmas validate its order boundary.

   Scratch accounting: for each active frame f keep E_f, the set of DLOAD
   source ids whose private ALLOCA has already executed successfully in f.
   Charge q = SUM (MAP CARD E_f) over the active frame and suspended callers.
   Current frontier equation t.next = s.next + 32*q uses ALL these charges,
   because setup_callee inherits the current frontier. Each suspended caller
   separately stores its prefix q_at_push and its two saved frontiers.
   - first scratch at d: E_f'=E_f UNION {d}, q'=q+1;
   - reused scratch at d: E_f'=E_f, q'=q;
   - new original ALLOCA: both frontiers increase by identical size, q'=q;
   - push: E_new={}, q'=q, new frame map empty;
   - pop: restore caller saved frontiers and q_at_push, discard callee E;
     this is NOT subtraction from an arbitrary current cumulative count.
   Distinct active names and per-function distinct source ids give injection
   of charged pairs into context DLOAD occurrences, hence q<=ctx_dload_count C.
   Repeated sibling calls reuse bytes but do not accumulate active charges.
   Headroom at the matching source state gives t.next<dimword(:256).

   Target phase table (positions BEFORE executing active instruction).
   Let source inst d be active in frame_reachable at s; let p be its lowered
   start index, with fresh vars a,z and fresh ids ai,zi,ci,mi from supply.
   For DLOAD [off] [out]:
     phase 0: index p,   ALLOCA ai [32] [a]; source witness s before d.
       Frontier equation with current E, scratch may already be allocated.
     phase 1: index p+1, ADD zi [off;Label code_end] [z]; same source s.
       Scratch has recorded base c and size 32, c+32<=t.next; E includes d.
     phase 2: index p+2, CODECOPY ci [a;z;32] []; same source s.
       eval a=n2w c, eval z=n2w (off+code boundary), source offset bound
       prevents code-address wrap. Scratch disjointness/taint masks retained.
     phase 3: index p+3, MLOAD mi [a] [out]; same source s.
       Scratch now contains the 32 bytes read by source DLOAD; its read
       access is below frontier even before proving output equality.
     successor: source executes d OK s', target executes MLOAD OK t';
       compare successor indices and step_taint/provenance at phase 0.
   For DLOADBYTES [dst;off;n]:
     phase 0: p, ADD [off;Label code_end] [z], witness before source d.
     phase 1: p+1, CODECOPY [dst;z;n], same source s, computed z bound;
       dst is translated by selected identity or is fixed-region scalar;
       source access_ok supplies destination site containment when needed.
     successor: source DLOADBYTES OK s', target CODECOPY OK t', phase 0.
   Other instructions: phase 0 only. Malformed expansion envelopes are
   unchanged by supply, but context shape should exclude them; do not infer
   shape solely from the opcode. Structural origin uses C1.1 facts.

   Prefix induction required by mem_inv_raw_reachable is raw_reachable_ind
   in contextRawReachable, instantiated at the TARGET context and vs0.
   Its four rules are entry, next (including atomic successful INVOKE),
   block, and callee. A next rule with INVOKE steps an entire callee run,
   so stack-phase reasoning alone is insufficient: successful callee-run
   preservation must be a separate boundary, typically by fuel induction.
   Alternative: establish frame_reachable target coverage then prove its
   erasure covers raw_reachable, including that atomic INVOKE-next rule.
   Source-to-target terminating simulation does not imply either route.
   At every phase, prove raw_mem_ok at the active state even if its next
   step errors; an Error has no successor but the current access still
   belongs to raw_reachable. A matched source error cannot justify skipping
   target active-state safety. For source progress at the final phase need
   operand agreement/definedness, not merely successful target execution.

   Outstanding precise boundary: simultaneous target fuel/run coverage
   and prefix induction with explicit caller restoration, plus general
   active-stack order/charge preservation. No such theorem is asserted by
   this finite phase and arithmetic diagnostic.
*)
