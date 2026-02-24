(*
 * FCG Analysis Correctness Statements
 *
 * Theorem statements characterizing soundness and completeness
 * of the FCG analysis, with cheated proofs as scaffolding.
 *
 * TOP-LEVEL definitions:
 *   ctx_fn_names          - convenience: function names in context
 *   wf_fn_names           - well-formedness: distinct names, entry valid
 *   wf_invoke_targets     - well-formedness: INVOKE targets are valid
 *   fn_directly_calls     - semantic direct-call relation
 *   fcg_path              - reachability via RTC of direct calls
 *
 * TOP-LEVEL theorems (all cheated):
 *   fn_directly_calls_scan               - bridge to get_invoke_targets
 *   fcg_analyze_reachable_in_context     - reachable => in context
 *   fcg_analyze_callees_in_context       - callees => in context
 *   fcg_analyze_reachable_distinct       - reachable list is distinct
 *   fcg_analyze_callees_sound            - callees => fn_directly_calls
 *   fcg_analyze_callees_complete         - fn_directly_calls => callees
 *   fcg_analyze_callees_distinct         - callee lists are distinct
 *   fcg_analyze_call_sites_sound         - recorded => real INVOKE
 *   fcg_analyze_call_sites_complete      - real INVOKE => recorded
 *   fcg_analyze_reachable_sound          - reachable => fcg_path
 *   fcg_analyze_reachable_complete       - fcg_path => reachable
 *   fcg_analyze_no_entry                 - NONE entry => nothing reachable
 *   fcg_analyze_no_entry_callees         - NONE entry => callees empty
 *   fcg_analyze_no_entry_call_sites      - NONE entry => call sites empty
 *   fcg_analyze_no_entry_unreachable     - NONE entry => all unreachable
 *   fcg_analyze_unreachable_correct      - unreachable = complement
 *)

Theory fcgAnalysisCorrectness
Ancestors
  fcgAnalysis relation

(* ==========================================================================
   Section 0: Convenience Helper
   ========================================================================== *)

Definition ctx_fn_names_def:
  ctx_fn_names ctx = MAP (\f. f.fn_name) ctx.ctx_functions
End

(* ==========================================================================
   Section 1: Well-Formedness Predicates

   Most theorems assume only wf_fn_names (distinct names, valid entry).
   wf_invoke_targets is stronger and only needed by
   fcg_analyze_callees_in_context, which must know that INVOKE targets
   name real functions in the context. Each theorem uses the minimal
   precondition it actually requires.
   ========================================================================== *)

Definition wf_fn_names_def:
  wf_fn_names ctx <=>
    ALL_DISTINCT (ctx_fn_names ctx) /\
    (!entry_name. ctx.ctx_entry = SOME entry_name ==>
       MEM entry_name (ctx_fn_names ctx))
End

Definition wf_invoke_targets_def:
  wf_invoke_targets ctx <=>
    (!func inst.
       MEM func ctx.ctx_functions /\
       MEM inst (fn_insts func) /\
       inst.inst_opcode = INVOKE ==>
       ?lbl rest. inst.inst_operands = Label lbl :: rest /\
                  MEM lbl (ctx_fn_names ctx))
End

(* ==========================================================================
   Section 2: Semantic Relation via RTC
   ========================================================================== *)

(* Direct call edge: fn_a has an INVOKE instruction targeting fn_b.
   Defined purely from instruction structure — no analysis functions. *)
Definition fn_directly_calls_def:
  fn_directly_calls ctx fn_a fn_b <=>
    ?func inst rest.
      lookup_function fn_a ctx.ctx_functions = SOME func /\
      MEM inst (fn_insts func) /\
      inst.inst_opcode = INVOKE /\
      inst.inst_operands = Label fn_b :: rest
End

(* Reachability = reflexive-transitive closure of direct calls *)
Definition fcg_path_def:
  fcg_path ctx = RTC (fn_directly_calls ctx)
End

(* ==========================================================================
   Section 3: Bridge Lemma — connects semantic spec to analysis impl
   ========================================================================== *)

(* Key equivalence: the raw-instruction definition of fn_directly_calls
   is equivalent to the analysis's fcg_scan_function / get_invoke_targets.
   This is the only place that bridges semantics to implementation. *)
Theorem fn_directly_calls_scan:
  fn_directly_calls ctx fn_a fn_b <=>
  ?func. lookup_function fn_a ctx.ctx_functions = SOME func /\
         MEM fn_b (MAP FST (fcg_scan_function func))
Proof
  cheat
QED

(* ==========================================================================
   Section 4: Domain Invariants
   ========================================================================== *)

Theorem fcg_analyze_reachable_in_context:
  wf_fn_names ctx /\
  fcg_is_reachable (fcg_analyze ctx) fn_name ==>
  MEM fn_name (ctx_fn_names ctx)
Proof
  cheat
QED

Theorem fcg_analyze_callees_in_context:
  wf_fn_names ctx /\
  wf_invoke_targets ctx /\
  MEM callee (fcg_get_callees (fcg_analyze ctx) fn_name) ==>
  MEM callee (ctx_fn_names ctx)
Proof
  cheat
QED

Theorem fcg_analyze_reachable_distinct:
  wf_fn_names ctx ==>
  ALL_DISTINCT (fcg_analyze ctx).fcg_reachable
Proof
  cheat
QED

(* ==========================================================================
   Section 5: Callees Correctness
   ========================================================================== *)

(* Soundness: recorded callee => semantic direct call *)
Theorem fcg_analyze_callees_sound:
  wf_fn_names ctx /\
  MEM callee (fcg_get_callees (fcg_analyze ctx) fn_name) ==>
  fn_directly_calls ctx fn_name callee
Proof
  cheat
QED

(* Completeness: reachable + direct call => recorded callee *)
Theorem fcg_analyze_callees_complete:
  wf_fn_names ctx /\
  fcg_is_reachable (fcg_analyze ctx) fn_name /\
  fn_directly_calls ctx fn_name callee ==>
  MEM callee (fcg_get_callees (fcg_analyze ctx) fn_name)
Proof
  cheat
QED

(* Distinctness: callee lists have no duplicates *)
Theorem fcg_analyze_callees_distinct:
  wf_fn_names ctx ==>
  ALL_DISTINCT (fcg_get_callees (fcg_analyze ctx) fn_name)
Proof
  cheat
QED

(* ==========================================================================
   Section 6: Call Sites Correctness
   ========================================================================== *)

(* Soundness: recorded call site is a real INVOKE from a reachable caller *)
Theorem fcg_analyze_call_sites_sound:
  wf_fn_names ctx /\
  MEM inst (fcg_get_call_sites (fcg_analyze ctx) callee) ==>
  ?caller func.
    fcg_is_reachable (fcg_analyze ctx) caller /\
    lookup_function caller ctx.ctx_functions = SOME func /\
    MEM inst (fn_insts func) /\
    inst.inst_opcode = INVOKE /\
    ?rest. inst.inst_operands = Label callee :: rest
Proof
  cheat
QED

(* Completeness: every INVOKE targeting callee from a reachable caller is recorded *)
Theorem fcg_analyze_call_sites_complete:
  wf_fn_names ctx /\
  fcg_is_reachable (fcg_analyze ctx) caller /\
  lookup_function caller ctx.ctx_functions = SOME func /\
  MEM inst (fn_insts func) /\
  inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label callee :: rest ==>
  MEM inst (fcg_get_call_sites (fcg_analyze ctx) callee)
Proof
  cheat
QED

(* ==========================================================================
   Section 7: Reachability Correctness
   ========================================================================== *)

(* Soundness: analysis says reachable => semantic path from entry *)
Theorem fcg_analyze_reachable_sound:
  wf_fn_names ctx /\
  ctx.ctx_entry = SOME entry_name /\
  fcg_is_reachable (fcg_analyze ctx) fn_name ==>
  fcg_path ctx entry_name fn_name
Proof
  cheat
QED

(* Completeness: semantic path + in context => analysis says reachable *)
Theorem fcg_analyze_reachable_complete:
  wf_fn_names ctx /\
  ctx.ctx_entry = SOME entry_name /\
  fcg_path ctx entry_name fn_name /\
  MEM fn_name (ctx_fn_names ctx) ==>
  fcg_is_reachable (fcg_analyze ctx) fn_name
Proof
  cheat
QED

(* ==========================================================================
   Section 8: No-Entry Edge Cases
   ========================================================================== *)

Theorem fcg_analyze_no_entry:
  ctx.ctx_entry = NONE ==>
  ~fcg_is_reachable (fcg_analyze ctx) fn_name
Proof
  cheat
QED

Theorem fcg_analyze_no_entry_callees:
  ctx.ctx_entry = NONE ==>
  fcg_get_callees (fcg_analyze ctx) fn_name = []
Proof
  cheat
QED

Theorem fcg_analyze_no_entry_call_sites:
  ctx.ctx_entry = NONE ==>
  fcg_get_call_sites (fcg_analyze ctx) fn_name = []
Proof
  cheat
QED

Theorem fcg_analyze_no_entry_unreachable:
  ctx.ctx_entry = NONE ==>
  fcg_get_unreachable ctx (fcg_analyze ctx) = ctx.ctx_functions
Proof
  cheat
QED

(* ==========================================================================
   Section 9: Unreachable Correctness
   ========================================================================== *)

(* Unreachable = complement of reachable within context functions *)
Theorem fcg_analyze_unreachable_correct:
  wf_fn_names ctx ==>
  (MEM func (fcg_get_unreachable ctx (fcg_analyze ctx)) <=>
   MEM func ctx.ctx_functions /\
   ~fcg_is_reachable (fcg_analyze ctx) func.fn_name)
Proof
  cheat
QED

val _ = export_theory();
