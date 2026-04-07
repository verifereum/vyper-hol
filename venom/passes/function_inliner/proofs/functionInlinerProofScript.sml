(*
 * Function Inliner Pass — Correctness Proof
 *
 * PROOF STRUCTURE:
 *   1. lift_result (state_equiv inline_vars) shared_globals_np is refl/trans
 *   2. Per-round: inline + remove preserves the relation (round_correct)
 *   3. Loop: induction + transitivity
 *   4. Top-level: unfold function_inliner_ctx, apply loop
 *
 * WEAKENING JUSTIFICATION:
 *   The terminal relation is shared_globals_np (not execution_equiv) because
 *   when execution terminates (Halt/Abort), only observable effects matter
 *   (memory, storage, logs, account state). Local variables are dead after
 *   termination. The callee's internal state (from original INVOKE) and the
 *   clone's state (inlined code) have irreconcilable variable environments
 *   but identical observable effects via shared_globals_np.
 *)

Theory functionInlinerProof
Ancestors
  functionInlinerCtxSim functionInlinerCallSim functionInlinerDefs
  functionInlinerSim
  stateEquiv stateEquivProps
  venomExecSemantics venomInst venomWf cfgTransform
  fcgCorrectnessProof

open listTheory stringTheory relationTheory indexedListsTheory rich_listTheory
     functionInlinerCtxSimTheory functionInlinerCallSimTheory
open functionInlinerSimTheory functionInlinerCalleeSimTheory
     functionInlinerFreshTheory functionInlinerCallSimHelpersTheory
     functionInlinerRenumberTheory functionInlinerInvokeCloneHelpersTheory
     functionInlinerLabelOpsTheory
     stateEquivTheory venomWfTheory
     fcgCorrectnessProofTheory fcgDefsTheory

(* ===== Definitions ===== *)

(* is_inline_var and inline_vars are defined in functionInlinerFreshTheory *)

Definition ctx_no_inline_vars_def:
  ctx_no_inline_vars ctx <=>
    EVERY (\fn.
      EVERY (\bb.
        EVERY (\inst.
          EVERY (\v. ~is_inline_var v) inst.inst_outputs /\
          EVERY (\op. case op of Var v => ~is_inline_var v | _ => T)
                inst.inst_operands)
        bb.bb_instructions)
      fn.fn_blocks)
    ctx.ctx_functions
End

(* ===== Call graph DAG invariant ===== *)

(* One-step call relation on function names within a context *)
Definition ctx_calls_def:
  ctx_calls fns f_name g_name <=>
    ?f. MEM f fns /\ f.fn_name = f_name /\ ~fn_no_invoke g_name f
End

(* The call graph is a DAG: no function is reachable from itself.
   This implies fn_no_invoke self for every function and prevents
   mutual recursion of any depth. Vyper does not support recursion. *)
Definition ctx_call_dag_def:
  ctx_call_dag fns <=> !name. ~(ctx_calls fns)^+ name name
End

(* ===== Inliner result equivalence ===== *)

(* The inliner relation: state_equiv for OK, shared_globals_np for terminal.
   This is the tightest provable relation: OK continuations get full state
   equivalence (modulo inline vars), terminal results get global state matching. *)
Definition inliner_result_equiv_def:
  inliner_result_equiv vars =
    lift_result (state_equiv vars) shared_globals_np
End

Theorem inliner_result_equiv_refl:
  !r. inliner_result_equiv inline_vars r r
Proof
  Cases >>
  simp[inliner_result_equiv_def, lift_result_def,
       state_equiv_refl, shared_globals_np_def]
QED

Triviality shared_globals_np_trans_local:
  !s1 s2 s3.
    shared_globals_np s1 s2 /\ shared_globals_np s2 s3 ==>
    shared_globals_np s1 s3
Proof
  rw[shared_globals_np_def]
QED

Theorem inliner_result_equiv_trans:
  !r1 r2 r3.
    inliner_result_equiv inline_vars r1 r2 /\
    inliner_result_equiv inline_vars r2 r3 ==>
    inliner_result_equiv inline_vars r1 r3
Proof
  Cases >> Cases >> Cases >>
  simp[inliner_result_equiv_def, lift_result_def] >>
  metis_tac[state_equiv_trans, shared_globals_np_trans_local]
QED

(* ===== DAG helpers ===== *)

(* ctx_call_dag implies fn_no_invoke self for every function *)
Triviality ctx_call_dag_no_self_invoke:
  !fns f. ctx_call_dag fns /\ MEM f fns ==>
    fn_no_invoke f.fn_name f
Proof
  rpt strip_tac >>
  spose_not_then assume_tac >>
  gvs[ctx_call_dag_def] >>
  first_x_assum (qspec_then `f.fn_name` mp_tac) >> simp[] >>
  irule TC_SUBSET >>
  simp[ctx_calls_def] >> metis_tac[]
QED

(* ctx_call_dag implies: if f calls g, then g doesn't call f *)
Triviality ctx_call_dag_no_mutual:
  !fns f g. ctx_call_dag fns /\ MEM f fns /\ MEM g fns /\
    ~fn_no_invoke g.fn_name f ==>
    fn_no_invoke f.fn_name g
Proof
  rpt strip_tac >>
  spose_not_then assume_tac >>
  gvs[ctx_call_dag_def] >>
  first_x_assum (qspec_then `f.fn_name` mp_tac) >> simp[] >>
  irule (cj 2 TC_RULES) >>
  qexists_tac `g.fn_name` >>
  conj_tac >> irule TC_SUBSET >>
  simp[ctx_calls_def] >> metis_tac[]
QED

(* FILTER preserves ctx_call_dag (removing functions only removes edges) *)
Triviality ctx_call_dag_filter:
  !P fns. ctx_call_dag fns ==> ctx_call_dag (FILTER P fns)
Proof
  rw[ctx_call_dag_def] >>
  spose_not_then strip_assume_tac >>
  first_x_assum (qspec_then `name` mp_tac) >> simp[] >>
  `!a b. ctx_calls (FILTER P fns) a b ==> ctx_calls fns a b` by
    (simp[ctx_calls_def, MEM_FILTER] >> metis_tac[]) >>
  imp_res_tac TC_MONOTONE
QED

(* ===== Structural preservation ===== *)

(* Re-exported from functionInlinerSim *)
Theorem inline_call_site_fn_name =
  functionInlinerSimTheory.inline_call_site_fn_name;
Theorem fix_inline_phis_fn_name =
  functionInlinerSimTheory.fix_inline_phis_fn_name;
Theorem inline_one_site_fn_name =
  functionInlinerSimTheory.inline_one_site_fn_name;
Theorem inline_at_sites_fn_name =
  functionInlinerSimTheory.inline_at_sites_fn_name;

Theorem inline_candidate_entry_preserved:
  !ctx callee ist ctx' ist'.
    inline_candidate ctx callee ist = (ctx', ist') ==>
    ctx'.ctx_entry = ctx.ctx_entry
Proof
  rw[inline_candidate_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem inline_candidate_fn_names:
  !ctx callee ist ctx' ist'.
    inline_candidate ctx callee ist = (ctx', ist') ==>
    MAP (\f. f.fn_name) ctx'.ctx_functions =
    MAP (\f. f.fn_name) ctx.ctx_functions
Proof
  rw[inline_candidate_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_abbrev_tac `fns = ctx.ctx_functions` >>
  `!acc ist0 fns0 result ist1.
     FOLDL (\(fns_acc, st) caller_fn.
       let max_sites = LENGTH (fn_insts caller_fn) in
       let (caller', st') = inline_at_sites max_sites caller_fn callee st in
       (SNOC caller' fns_acc, st'))
       (acc, ist0) fns0 = (result, ist1) ==>
     MAP (\f. f.fn_name) result =
     MAP (\f. f.fn_name) acc ++ MAP (\f. f.fn_name) fns0` suffices_by
    (disch_then (qspecl_then [`[]`, `ist`, `fns`] mp_tac) >>
     simp[]) >>
  Induct_on `fns0` >- simp[] >>
  rpt strip_tac >>
  gvs[LET_THM] >> pairarg_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  imp_res_tac inline_at_sites_fn_name >>
  gvs[listTheory.MAP_SNOC, listTheory.SNOC_APPEND]
QED

Theorem remove_function_entry:
  !name ctx. (remove_function name ctx).ctx_entry = ctx.ctx_entry
Proof
  rw[remove_function_def]
QED

(* ===== Inliner well-formedness predicate ===== *)

(* Per-function well-formedness for inlining. Bundles exactly the conditions
   that inline_candidate_correct needs from each function.
   NOTE: We use the 3 specific parts of wf_function that are actually needed
   (ALL_DISTINCT fn_labels, fn_has_entry, EVERY bb_well_formed) rather than
   wf_function itself, because fn_succs_closed and fn_inst_ids_distinct are
   NOT used by inline_candidate_correct and are expensive to preserve. *)
Definition inliner_fn_wf_def:
  inliner_fn_wf f <=>
    ALL_DISTINCT (fn_labels f) /\
    fn_has_entry f /\
    EVERY bb_well_formed f.fn_blocks /\
    fn_no_invoke f.fn_name f /\
    invoke_targets_extern f /\
    labels_no_inline_return f /\
    fn_no_alloca f /\
    label_ops_closed f /\
    EVERY (\bb. params_sequential bb.bb_instructions 0) f.fn_blocks /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> PARAM) bb.bb_instructions)
      (TL f.fn_blocks)
End

(* Context well-formedness for inlining. Bundles per-function WF
   plus the freshness/compatibility conditions that inline_candidate_correct
   needs across the whole context. *)
Definition inliner_ctx_wf_def:
  inliner_ctx_wf ctx ist <=>
    ctx_wf ctx /\
    EVERY inliner_fn_wf ctx.ctx_functions /\
    EVERY (\f. labels_fresh_above ist.is_inline_count f) ctx.ctx_functions /\
    EVERY (\f. vars_fresh_above ist.is_inline_count f) ctx.ctx_functions /\
    (* Entry function is not invoked by any function in the context.
       This is a natural pipeline invariant: the entry is the external API. *)
    (!name. ctx.ctx_entry = SOME name ==>
      EVERY (fn_no_invoke name) ctx.ctx_functions) /\
    (* Caller-callee compatibility: for every callee in the context,
       every INVOKE targeting it is well-formed. *)
    (!callee_name callee.
      lookup_function callee_name ctx.ctx_functions = SOME callee ==>
      EVERY (\f. EVERY (\bb. EVERY (\inst.
        inst_targets callee_name inst ==>
        callee_ret_arity_le (LENGTH inst.inst_outputs) callee /\
        EVERY (\blk. count_params blk.bb_instructions <=
                     LENGTH (TL inst.inst_operands)) callee.fn_blocks /\
        ALL_DISTINCT inst.inst_outputs /\
        EVERY (\op. !v. op = Var v ==> ~MEM v inst.inst_outputs)
          (TL inst.inst_operands))
        bb.bb_instructions) f.fn_blocks) ctx.ctx_functions) /\
    (* Function names don't look like inline labels.
       Ensures fresh inline labels never collide with function names.
       Natural invariant: inline prefixes are generated, never user-visible. *)
    EVERY (\name. !k. ~isPREFIX (inline_prefix k) name) (ctx_fn_names ctx) /\
    (* Call graph is a DAG: no function is reachable from itself via
       invoke edges. Vyper does not support recursion. This implies
       fn_no_invoke self and prevents mutual recursion of any depth.
       Essential for preserving fn_no_invoke self through inlining. *)
    ctx_call_dag ctx.ctx_functions /\
    (* Block labels don't collide with function names. Natural invariant:
       block labels and function names are in separate namespaces.
       Essential for preserving invoke_targets_extern through inlining:
       clone code's INVOKE targets (function names) must not be in the
       caller's block labels (which include original labels). *)
    EVERY (\f. EVERY (\l. ~MEM l (ctx_fn_names ctx)) (fn_labels f))
      ctx.ctx_functions
End

(* ===== Candidate ≠ entry ===== *)

(* If no function invokes name, the FCG records no call sites for name.
   Follows from FCG soundness by contrapositive. *)
Triviality fn_no_invoke_fn_insts_blocks:
  !name bbs inst.
    EVERY (\bb. EVERY (\i. ~inst_targets name i) bb.bb_instructions) bbs /\
    MEM inst (fn_insts_blocks bbs) ==>
    ~inst_targets name inst
Proof
  Induct_on `bbs` >> simp[fn_insts_blocks_def] >>
  rw[MEM_APPEND]
  >- (gvs[EVERY_MEM])
  >- (first_x_assum irule >> gvs[])
QED

Triviality fn_no_invoke_fn_insts:
  !name fn inst.
    fn_no_invoke name fn /\ MEM inst (fn_insts fn) ==>
    ~inst_targets name inst
Proof
  rw[fn_no_invoke_def, fn_insts_def] >>
  irule fn_no_invoke_fn_insts_blocks >>
  metis_tac[]
QED

Triviality no_invoke_no_call_sites:
  !ctx name.
    ctx_wf ctx /\
    EVERY (fn_no_invoke name) ctx.ctx_functions ==>
    fcg_get_call_sites (fcg_analyze ctx) name = []
Proof
  rpt strip_tac >>
  Cases_on `fcg_get_call_sites (fcg_analyze ctx) name` >> simp[] >>
  (* h is a call site — apply soundness *)
  mp_tac (Q.SPECL [`ctx`, `name`, `h`] fcg_analyze_call_sites_sound_proof) >>
  (impl_tac >- simp[]) >> strip_tac >>
  (* soundness gives: lookup_function caller fns = SOME func,
     MEM h (fn_insts func), inst_opcode = INVOKE, operands = Label name::rest *)
  imp_res_tac lookup_function_MEM >>
  `fn_no_invoke name func` by gvs[EVERY_MEM] >>
  drule_all fn_no_invoke_fn_insts >>
  simp[inst_targets_def]
QED

(* select_inline_candidate only picks functions with ≥ 1 call site *)
Triviality select_inline_candidate_has_call_sites:
  !ctx fcg threshold walk name.
    select_inline_candidate ctx fcg threshold walk = SOME name ==>
    LENGTH (fcg_get_call_sites fcg name) >= 1
Proof
  Induct_on `walk` >> simp[select_inline_candidate_def, LET_THM] >>
  rpt gen_tac >> rpt IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
  TRY (Cases_on `fcg_get_call_sites fcg h` >> gvs[]) >>
  first_x_assum irule >> metis_tac[]
QED

(* The candidate selected for inlining is never the entry function. *)
Triviality select_inline_candidate_not_entry:
  !ctx fcg threshold walk name.
    select_inline_candidate ctx fcg threshold walk = SOME name /\
    ctx_wf ctx /\
    (!entry_name. ctx.ctx_entry = SOME entry_name ==>
      EVERY (fn_no_invoke entry_name) ctx.ctx_functions) /\
    fcg = fcg_analyze ctx ==>
    ctx.ctx_entry <> SOME name
Proof
  rpt strip_tac >> gvs[] >>
  imp_res_tac no_invoke_no_call_sites >>
  imp_res_tac select_inline_candidate_has_call_sites >>
  gvs[]
QED

(* select_inline_candidate returns a member of the walk *)
Triviality lookup_function_fn_name:
  !name fns fn.
    lookup_function name fns = SOME fn ==> fn.fn_name = name
Proof
  rw[lookup_function_def] >>
  Induct_on `fns` >> simp[listTheory.FIND_thm] >>
  rpt gen_tac >> Cases_on `h.fn_name = name` >> gvs[]
QED

Triviality select_inline_candidate_MEM:
  !ctx fcg threshold walk name.
    select_inline_candidate ctx fcg threshold walk = SOME name ==>
    MEM name walk
Proof
  Induct_on `walk` >> simp[select_inline_candidate_def, LET_THM] >>
  rpt gen_tac >> rpt IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Triviality every_inliner_fn_wf_extract:
  EVERY inliner_fn_wf fns ==>
  EVERY (\f. ALL_DISTINCT (fn_labels f)) fns /\
  EVERY fn_no_alloca fns /\
  EVERY (\f. EVERY bb_well_formed f.fn_blocks) fns /\
  EVERY label_ops_closed fns /\
  EVERY fn_has_entry fns
Proof
  rw[EVERY_MEM, inliner_fn_wf_def] >> res_tac
QED

(* Split a bundled caller-callee compatibility EVERY into its 4 components.
   This is the form that exists in inliner_ctx_wf_def after specialization,
   and inline_candidate_correct needs them separated. *)
Triviality callee_compat_split:
  EVERY (\f. EVERY (\bb. EVERY (\inst.
    inst_targets name inst ==>
    callee_ret_arity_le (LENGTH inst.inst_outputs) callee /\
    EVERY (\blk. count_params blk.bb_instructions <=
                 LENGTH (TL inst.inst_operands)) callee.fn_blocks /\
    ALL_DISTINCT inst.inst_outputs /\
    EVERY (\op. !v. op = Var v ==> ~MEM v inst.inst_outputs)
      (TL inst.inst_operands))
    bb.bb_instructions) f.fn_blocks) fns ==>
  EVERY (\f. EVERY (\bb. EVERY (\inst.
    inst_targets name inst ==>
    callee_ret_arity_le (LENGTH inst.inst_outputs) callee)
    bb.bb_instructions) f.fn_blocks) fns /\
  EVERY (\f. EVERY (\bb. EVERY (\inst.
    inst_targets name inst ==>
    EVERY (\blk. count_params blk.bb_instructions <=
                 LENGTH (TL inst.inst_operands)) callee.fn_blocks)
    bb.bb_instructions) f.fn_blocks) fns /\
  EVERY (\f. EVERY (\bb. EVERY (\inst.
    inst_targets name inst ==>
    ALL_DISTINCT inst.inst_outputs)
    bb.bb_instructions) f.fn_blocks) fns /\
  EVERY (\f. EVERY (\bb. EVERY (\inst.
    inst_targets name inst ==>
    EVERY (\op. !v. op = Var v ==> ~MEM v inst.inst_outputs)
      (TL inst.inst_operands))
    bb.bb_instructions) f.fn_blocks) fns
Proof
  rw[EVERY_MEM] >> metis_tac[]
QED

(* ===== Per-round correctness ===== *)

(* Wrapper: derive inline_candidate_correct conclusion from inliner_ctx_wf.
   Isolates the 25-precondition matching from the main round proof. *)
(* Extract the parts of wf_function that inline_candidate_correct needs,
   in exactly the syntactic forms ICC expects. *)
Triviality inline_candidate_correct_from_ctx_wf:
  !ctx callee ist ctx' ist' fuel s.
    inliner_ctx_wf ctx ist /\
    lookup_function callee.fn_name ctx.ctx_functions = SOME callee /\
    inline_candidate ctx callee ist = (ctx', ist') /\
    FDOM s.vs_labels = {} /\ ~s.vs_halted ==>
    ?fuel'.
      lift_result (state_equiv inline_vars) shared_globals_np
        (run_context fuel ctx s) (run_context fuel' ctx' s)
Proof
  rpt strip_tac >>
  qpat_x_assum `inliner_ctx_wf _ _`
    (strip_assume_tac o PURE_REWRITE_RULE[inliner_ctx_wf_def]) >>
  imp_res_tac lookup_function_MEM >>
  `inliner_fn_wf callee` by gvs[EVERY_MEM] >>
  pop_assum (strip_assume_tac o PURE_REWRITE_RULE[inliner_fn_wf_def]) >>
  imp_res_tac every_inliner_fn_wf_extract >>
  first_x_assum (qspecl_then [`callee.fn_name`, `callee`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  imp_res_tac callee_compat_split >>
  mp_tac (SRULE [LET_THM, SF ETA_ss] inline_candidate_correct) >>
  disch_then (qspecl_then [`ctx`, `callee`, `ist`, `ctx'`, `ist'`,
    `fuel`, `s`] mp_tac) >>
  gvs[SF ETA_ss]
QED

(* Wrapper: derive inline_candidate_no_invoke from inliner_ctx_wf. *)
Triviality inline_candidate_no_invoke_from_ctx_wf:
  !ctx callee ist ctx' ist'.
    inliner_ctx_wf ctx ist /\
    lookup_function callee.fn_name ctx.ctx_functions = SOME callee /\
    inline_candidate ctx callee ist = (ctx', ist') ==>
    ctx_no_invoke callee.fn_name ctx'
Proof
  rpt strip_tac >>
  qpat_x_assum `inliner_ctx_wf _ _`
    (strip_assume_tac o PURE_REWRITE_RULE[inliner_ctx_wf_def]) >>
  imp_res_tac lookup_function_MEM >>
  `inliner_fn_wf callee` by gvs[EVERY_MEM] >>
  pop_assum (strip_assume_tac o PURE_REWRITE_RULE[inliner_fn_wf_def]) >>
  imp_res_tac every_inliner_fn_wf_extract >>
  mp_tac inline_candidate_no_invoke >>
  disch_then (qspecl_then [`ctx`, `callee`, `ist`, `ctx'`, `ist'`] mp_tac) >>
  gvs[SF ETA_ss]
QED

(* The round composes inline_candidate + remove_function.
   Uses inliner_ctx_wf for ctx-wide conditions. *)
Theorem function_inliner_round_correct[local]:
  !ctx walk threshold ist ctx' walk' ist' s fuel.
    function_inliner_round ctx walk threshold ist =
      SOME (ctx', walk', ist') /\
    inliner_ctx_wf ctx ist /\
    FDOM s.vs_labels = {} /\
    ~s.vs_halted ==>
    ?fuel'.
      inliner_result_equiv inline_vars
        (run_context fuel ctx s)
        (run_context fuel' ctx' s)
Proof
  rw[function_inliner_round_def, LET_THM] >>
  Cases_on `select_inline_candidate ctx (fcg_analyze ctx) threshold walk` >>
  gvs[] >>
  Cases_on `lookup_function x ctx.ctx_functions` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  imp_res_tac lookup_function_fn_name >>
  (* Unify x = x'.fn_name everywhere *)
  qpat_x_assum `x'.fn_name = x` (SUBST_ALL_TAC o GSYM) >>
  (* candidate ≠ entry: derived from inliner_ctx_wf entry-no-invoke + FCG *)
  `ctx.ctx_entry <> SOME x'.fn_name` by (
    mp_tac select_inline_candidate_not_entry >>
    disch_then (qspecl_then [`ctx`, `fcg_analyze ctx`, `threshold`,
      `walk`, `x'.fn_name`] mp_tac) >>
    simp[] >>
    qpat_x_assum `inliner_ctx_wf _ _`
      (strip_assume_tac o PURE_REWRITE_RULE[inliner_ctx_wf_def]) >>
    simp[]) >>
  (* Apply inline_candidate_correct via wrapper *)
  drule_all inline_candidate_correct_from_ctx_wf >>
  disch_then (qspecl_then [`fuel`] strip_assume_tac) >>
  (* Apply inline_candidate_no_invoke via wrapper *)
  drule_all inline_candidate_no_invoke_from_ctx_wf >> strip_tac >>
  gvs[ctx_no_invoke_def] >>
  (* inline_candidate preserves entry *)
  imp_res_tac inline_candidate_entry_preserved >>
  (* remove_function_correct gives exact equality *)
  mp_tac remove_function_correct >>
  disch_then (qspecl_then [`x'.fn_name`, `ctx''`, `fuel'`, `s`] mp_tac) >>
  (impl_tac >- simp[]) >>
  strip_tac >>
  (* Compose *)
  qexists_tac `fuel'` >>
  simp[inliner_result_equiv_def]
QED

(* ===== Preservation lemmas (needed for loop induction) ===== *)

(* inline_one_site increments is_inline_count by 1 *)
Triviality inline_one_site_ist_count:
  !caller callee ist fn' ist'.
    inline_one_site caller callee ist = SOME (fn', ist') ==>
    ist'.is_inline_count = ist.is_inline_count + 1
Proof
  rw[inline_one_site_def] >> gvs[AllCaseEqs(), LET_THM]
QED

Triviality inline_at_sites_ist_count:
  !n fn callee ist fn' ist'.
    inline_at_sites n fn callee ist = (fn', ist') ==>
    ist.is_inline_count <= ist'.is_inline_count
Proof
  Induct >> simp[inline_at_sites_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac inline_one_site_ist_count >>
  first_x_assum drule >> simp[]
QED

(* Combined ALL_DISTINCT + labels_fresh_above for inline_at_sites.
   Uses inline_one_site_preserves_preconds which bundles both. *)
Triviality inline_at_sites_preserves_preconds:
  !n fn callee ist fn' ist'.
    inline_at_sites n fn callee ist = (fn', ist') /\
    ALL_DISTINCT (fn_labels fn) /\
    ALL_DISTINCT (fn_labels callee) /\
    labels_no_inline_return callee /\
    labels_fresh_above ist.is_inline_count fn ==>
    ALL_DISTINCT (fn_labels fn') /\
    labels_fresh_above ist'.is_inline_count fn'
Proof
  Induct >> simp[inline_at_sites_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  `ALL_DISTINCT (fn_labels caller') /\
   labels_fresh_above ist''.is_inline_count caller'`
    suffices_by (
      strip_tac >>
      first_x_assum (qspecl_then [`caller'`, `callee`, `ist''`,
        `fn'`, `ist'`] mp_tac) >> simp[]) >>
  qspecl_then [`fn`, `callee`, `ist`, `caller'`, `ist''`]
    mp_tac inline_one_site_preserves_preconds >> simp[]
QED

(* find_invoke_idx returns an index where inst_targets holds.
   Proof: find_invoke_idx checks inst_targets (same condition). *)
Triviality find_invoke_idx_inst_targets:
  !callee_name insts n idx.
    find_invoke_idx callee_name insts n = SOME idx ==>
    inst_targets callee_name (EL (idx - n) insts)
Proof
  Induct_on `insts` >> simp[find_invoke_idx_def] >>
  rpt gen_tac >>
  reverse IF_CASES_TAC >> simp[]
  >- (strip_tac >> first_x_assum drule >> strip_tac >>
      imp_res_tac find_invoke_idx_bound >>
      `idx - n = SUC (idx - (n + 1))` by simp[] >> simp[])
  >- (strip_tac >> gvs[inst_targets_def])
QED

(* find_invoke_site returns a site where inst_targets holds *)
Triviality find_invoke_site_inst_targets:
  !callee_name bbs lbl idx bb.
    find_invoke_site callee_name bbs = SOME (lbl, idx) /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
    lookup_block lbl bbs = SOME bb ==>
    inst_targets callee_name (EL idx bb.bb_instructions)
Proof
  Induct_on `bbs` >> simp[find_invoke_site_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `find_invoke_idx callee_name h.bb_instructions 0` >> gvs[]
  >- (
    (* NONE — result from recursive call on bbs *)
    `h.bb_label <> lbl` by (
      CCONTR_TAC >> gvs[] >>
      drule find_invoke_site_label_mem >> simp[MEM_MAP] >>
      metis_tac[]) >>
    `lookup_block lbl bbs = SOME bb` by (
      gvs[lookup_block_def, FIND_thm]) >>
    first_x_assum irule >> simp[])
  >- (
    (* SOME x — found in h: lbl = h.bb_label, idx = x, bb = h *)
    `bb = h` by gvs[lookup_block_def, FIND_thm] >>
    gvs[] >> drule find_invoke_idx_inst_targets >> simp[])
QED

(* replace_block preserves EVERY — moved here for use by inline_call_site *)
Triviality every_replace_block:
  !P lbl bb' bbs.
    P bb' /\ EVERY P bbs ==> EVERY P (replace_block lbl bb' bbs)
Proof
  rw[replace_block_def, EVERY_MEM, MEM_MAP] >>
  rpt strip_tac >> gvs[] >> rw[]
QED

(* inline_call_site_preserves_arity, inline_one_site_preserves_arity,
   vars_fresh_above_inline_at_sites: moved after fn_no_invoke block below *)

(* remove_function preserves EVERY *)
Triviality every_remove_function:
  !P name ctx.
    EVERY P ctx.ctx_functions ==>
    EVERY P (remove_function name ctx).ctx_functions
Proof
  rw[remove_function_def] >> irule EVERY_FILTER_IMP >> simp[]
QED

(* Generic FOLDL lifting: if inline_at_sites preserves P for a single
   function, then inline_candidate preserves EVERY P for the whole context.
   The step precondition Q(callee, ist) is threaded unchanged. *)
Triviality inline_candidate_every_lift:
  !P ctx callee ist ctx' ist'.
    (!n fn ist0 fn' ist0'.
       inline_at_sites n fn callee ist0 = (fn', ist0') /\
       P fn ==> P fn') /\
    EVERY P ctx.ctx_functions /\
    inline_candidate ctx callee ist = (ctx', ist') ==>
    EVERY P ctx'.ctx_functions
Proof
  rpt strip_tac >>
  gvs[inline_candidate_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  `!acc ist0 fns0 result ist1.
     EVERY P fns0 /\ EVERY P acc /\

     FOLDL (\(fns_acc, st) caller_fn.
       let max_sites = LENGTH (fn_insts caller_fn) in
       let (caller', st') = inline_at_sites max_sites caller_fn callee st in
       (SNOC caller' fns_acc, st'))
       (acc, ist0) fns0 = (result, ist1) ==>
     EVERY P result` suffices_by
    (disch_then (qspecl_then [`[]`, `ist`, `ctx.ctx_functions`] mp_tac) >>
     simp[]) >>
  Induct_on `fns0` >- (rw[] >> gvs[]) >>
  rpt strip_tac >> gvs[LET_THM] >>
  pairarg_tac >> gvs[] >>
  `P caller'` by (first_x_assum irule >> metis_tac[]) >>
  first_x_assum irule >>
  qexistsl [`SNOC caller' acc`, `st'`, `ist1`] >>
  simp[EVERY_SNOC]
QED

(* labels_fresh_above + ALL_DISTINCT through inline_candidate.
   Threads the inline_state monotonically through the FOLDL. *)
Triviality inline_candidate_labels_fresh:
  !ctx callee ist ctx' ist'.
    ALL_DISTINCT (fn_labels callee) /\
    labels_no_inline_return callee /\
    EVERY (\f. ALL_DISTINCT (fn_labels f) /\
               labels_fresh_above ist.is_inline_count f) ctx.ctx_functions /\
    inline_candidate ctx callee ist = (ctx', ist') ==>
    EVERY (\f. ALL_DISTINCT (fn_labels f) /\
               labels_fresh_above ist'.is_inline_count f) ctx'.ctx_functions
Proof
  rpt strip_tac >>
  gvs[inline_candidate_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  `!acc ist0 fns0 result ist1.
     EVERY (\f. ALL_DISTINCT (fn_labels f) /\
                labels_fresh_above ist0.is_inline_count f) fns0 /\
     EVERY (\f. ALL_DISTINCT (fn_labels f) /\
                labels_fresh_above ist0.is_inline_count f) acc /\
     FOLDL (\(fns_acc, st) caller_fn.
       let max_sites = LENGTH (fn_insts caller_fn) in
       let (caller', st') = inline_at_sites max_sites caller_fn callee st in
       (SNOC caller' fns_acc, st'))
       (acc, ist0) fns0 = (result, ist1) ==>
     EVERY (\f. ALL_DISTINCT (fn_labels f) /\
                labels_fresh_above ist1.is_inline_count f) result`
    suffices_by
    (disch_then (qspecl_then [`[]`, `ist`, `ctx.ctx_functions`] mp_tac) >>
     simp[]) >>
  Induct_on `fns0` >- (rw[] >> gvs[] >>
    irule EVERY_MONOTONIC >> rpt strip_tac >> gvs[] >>
    irule labels_fresh_above_mono >>
    imp_res_tac inline_at_sites_ist_count >> metis_tac[]) >>
  rpt strip_tac >> gvs[LET_THM] >>
  pairarg_tac >> gvs[] >>
  `ALL_DISTINCT (fn_labels caller') /\
   labels_fresh_above st'.is_inline_count caller'` by (
    irule inline_at_sites_preserves_preconds >>
    metis_tac[]) >>
  imp_res_tac inline_at_sites_ist_count >>
  (* Upgrade acc and fns0 to st' freshness via monotonicity *)
  `EVERY (\f. ALL_DISTINCT (fn_labels f) /\
              labels_fresh_above st'.is_inline_count f) acc` by (
    irule EVERY_MONOTONIC >>
    qexists `\f. ALL_DISTINCT (fn_labels f) /\
                 labels_fresh_above ist0.is_inline_count f` >>
    simp[] >> rpt strip_tac >>
    irule labels_fresh_above_mono >> metis_tac[]) >>
  `EVERY (\f. ALL_DISTINCT (fn_labels f) /\
              labels_fresh_above st'.is_inline_count f) fns0` by (
    irule EVERY_MONOTONIC >>
    qexists `\f. ALL_DISTINCT (fn_labels f) /\
                 labels_fresh_above ist0.is_inline_count f` >>
    simp[] >> rpt strip_tac >>
    irule labels_fresh_above_mono >> metis_tac[]) >>
  first_x_assum irule >>
  qexistsl [`SNOC caller' acc`, `st'`] >>
  simp[EVERY_SNOC]
QED

(* inline_candidate preserves fn_names — already proven above as
   inline_candidate_fn_names, re-export for local use *)
Triviality inline_candidate_fn_names_map =
  inline_candidate_fn_names;

(* inline_candidate preserves ctx_entry *)
Triviality inline_candidate_ctx_entry:
  !ctx callee ist ctx' ist'.
    inline_candidate ctx callee ist = (ctx', ist') ==>
    ctx'.ctx_entry = ctx.ctx_entry
Proof
  rw[inline_candidate_def, LET_THM] >>
  pairarg_tac >> gvs[]
QED

(* ALL_DISTINCT for MAP over FILTER *)
Triviality all_distinct_map_filter:
  !f P l. ALL_DISTINCT (MAP f l) ==> ALL_DISTINCT (MAP f (FILTER P l))
Proof
  gen_tac >> gen_tac >> Induct >> simp[] >>
  rpt strip_tac >> rw[MEM_MAP, MEM_FILTER] >>
  gvs[MEM_MAP] >> metis_tac[]
QED

(* ctx_wf through inline_candidate + remove_function *)
Triviality ctx_wf_inline_remove:
  !ctx callee ist ctx_mid ist' name.
    ctx_wf ctx /\
    ctx.ctx_entry <> SOME name /\
    inline_candidate ctx callee ist = (ctx_mid, ist') ==>
    ctx_wf (remove_function name ctx_mid)
Proof
  rw[ctx_wf_def, ctx_distinct_fn_names_def, ctx_has_entry_def,
     ctx_fn_names_def, remove_function_def] >>
  imp_res_tac inline_candidate_fn_names >>
  imp_res_tac inline_candidate_entry_preserved
  >- (gvs[] >> irule all_distinct_map_filter >> gvs[])
  >- (qexists `entry_name` >> gvs[] >>
      simp[MEM_MAP, MEM_FILTER] >>
      `MEM entry_name (MAP (\f. f.fn_name) ctx_mid.ctx_functions)` by
        gvs[] >>
      gvs[MEM_MAP] >>
      rename1 `MEM g ctx_mid.ctx_functions` >>
      qexists `g` >> gvs[])
QED


(* ===== fn_no_invoke preservation for arbitrary name ===== *)

(* inst_targets only depends on opcode and operands *)
Triviality inst_targets_proj:
  !name i. inst_targets name i <=>
    i.inst_opcode = INVOKE /\
    case i.inst_operands of Label l :: _ => l = name | _ => F
Proof
  rw[inst_targets_def]
QED

(* inst_targets is unchanged when only inst_id changes *)
Triviality inst_targets_update_id:
  !name inst id. inst_targets name (inst with inst_id := id) <=>
    inst_targets name inst
Proof
  simp[inst_targets_def]
QED

(* fn_no_invoke + lookup_block → block-level EVERY *)
Triviality fn_no_invoke_block:
  !name f lbl bb.
    fn_no_invoke name f /\
    lookup_block lbl f.fn_blocks = SOME bb ==>
    EVERY (\i. ~inst_targets name i) bb.bb_instructions
Proof
  rw[fn_no_invoke_def] >>
  imp_res_tac lookup_block_MEM >>
  fs[EVERY_MEM] >> first_x_assum drule >> simp[]
QED

(* Helper: renumber_block_inst_ids preserves EVERY (~inst_targets) *)
Triviality renumber_block_no_invoke:
  !n bb name.
    EVERY (\i. ~inst_targets name i) bb.bb_instructions ==>
    EVERY (\i. ~inst_targets name i)
      (SND (renumber_block_inst_ids n bb)).bb_instructions
Proof
  rw[renumber_block_inst_ids_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  (* FOLDL adds inst with inst_id := id. Need to show EVERY is preserved. *)
  `!insts n0 acc.
     EVERY (\i. ~inst_targets name i) insts /\
     EVERY (\i. ~inst_targets name i) acc ==>
     EVERY (\i. ~inst_targets name i)
       (SND (FOLDL (\(id,acc) inst. (id+1, acc ++ [inst with inst_id := id]))
              (n0, acc) insts))` suffices_by
    (disch_then (qspecl_then [`bb.bb_instructions`, `n`, `[]`] mp_tac) >>
     simp[]) >>
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[EVERY_APPEND, inst_targets_update_id]
QED

(* renumber preserves fn_no_invoke (forward direction only — sufficient
   since we always go fn → renumber(fn), never the reverse).
   Proof: inst_targets only depends on opcode+operands, which renumber preserves. *)
Triviality fn_no_invoke_renumber:
  !name f. fn_no_invoke name f ==>
    fn_no_invoke name (renumber_fn_inst_ids f)
Proof
  rw[fn_no_invoke_def, renumber_fn_inst_ids_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  `!bbs n0 acc result n1.
     FOLDL (\(n,acc) bb. let (n',bb') = renumber_block_inst_ids n bb in
                         (n', acc ++ [bb'])) (n0, acc) bbs = (n1, result) /\
     EVERY (\bb. EVERY (\i. ~inst_targets name i) bb.bb_instructions) acc /\
     EVERY (\bb. EVERY (\i. ~inst_targets name i) bb.bb_instructions) bbs ==>
     EVERY (\bb. EVERY (\i. ~inst_targets name i) bb.bb_instructions) result`
    suffices_by (disch_then (qspecl_then [`f.fn_blocks`, `0`, `[]`] mp_tac) >>
      simp[]) >>
  Induct >> simp[] >> rpt strip_tac >>
  gvs[LET_THM] >> pairarg_tac >> gvs[] >>
  first_x_assum (qspecl_then [`n'`, `acc ++ [bb']`, `result`, `n1`] mp_tac) >>
  simp[EVERY_APPEND] >>
  disch_then irule >>
  mp_tac (Q.SPECL [`n0`, `h`, `name`] renumber_block_no_invoke) >>
  simp[]
QED

(* fix_inline_phis preserves fn_no_invoke: only modifies PHI instructions,
   and PHI <> INVOKE so inst_targets is unaffected. *)
Triviality fix_inline_phis_fn_no_invoke:
  !orig new_lbl ret_bb f name.
    fn_no_invoke name f ==>
    fn_no_invoke name (fix_inline_phis orig new_lbl ret_bb f)
Proof
  rw[fn_no_invoke_def, fix_inline_phis_def, LET_THM, EVERY_MEM] >>
  rpt strip_tac >> gvs[MEM_MAP] >>
  rw[EVERY_MEM] >> rpt strip_tac >>
  Cases_on `MEM bb'.bb_label (bb_succs ret_bb)` >> gvs[]
  >- (
    (* Modified block: inst in MAP over bb'.bb_instructions *)
    gvs[MEM_MAP] >> rename1 `MEM orig_i bb'.bb_instructions` >>
    first_x_assum drule >> disch_then drule >>
    Cases_on `orig_i.inst_opcode <> PHI` >>
    gvs[inst_targets_proj, subst_label_inst_def])
  >- metis_tac[]
QED

(* rewrite_inline_inst output never contains INVOKE targeting name.
   PARAM → ASSIGN, RET → ASSIGNs+JMP, other → unchanged. *)
Triviality rewrite_inline_inst_no_invoke:
  !ops outs ret inst pi insts pi' name.
    rewrite_inline_inst ops outs ret inst pi = (insts, pi') /\
    ~inst_targets name inst ==>
    EVERY (\i. ~inst_targets name i) insts
Proof
  rpt gen_tac >> strip_tac >>
  gvs[rewrite_inline_inst_def, LET_THM, AllCaseEqs()] >>
  simp[inst_targets_def, EVERY_MEM, MEM_MAPi, PULL_EXISTS]
QED

(* rewrite_inline_insts preserves ~inst_targets for all instructions *)
Triviality rewrite_inline_insts_no_invoke:
  !insts ops outs ret pi result pi' name.
    rewrite_inline_insts ops outs ret insts pi = (result, pi') /\
    EVERY (\i. ~inst_targets name i) insts ==>
    EVERY (\i. ~inst_targets name i) result
Proof
  Induct >> simp[rewrite_inline_insts_def] >>
  rpt gen_tac >> simp[LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[EVERY_APPEND] >>
  metis_tac[rewrite_inline_inst_no_invoke]
QED

(* rewrite_inline_blocks preserves EVERY (~inst_targets) *)
Triviality rewrite_inline_blocks_no_invoke:
  !bbs ops outs ret pi result pi' name.
    rewrite_inline_blocks ops outs ret bbs pi = (result, pi') /\
    EVERY (\bb. EVERY (\i. ~inst_targets name i) bb.bb_instructions) bbs ==>
    EVERY (\bb. EVERY (\i. ~inst_targets name i) bb.bb_instructions) result
Proof
  Induct >> simp[rewrite_inline_blocks_def] >>
  rpt gen_tac >> simp[LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[rewrite_inline_block_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[rewrite_inline_insts_no_invoke]
QED

(* inline_call_site preserves fn_no_invoke for arbitrary name.
   WHY: fn_blocks becomes replace_block(truncated) ++ [return_bb] ++ rewritten.
   - truncated: TAKE of original + JMP (JMP <> INVOKE)
   - return_bb: DROP of original (subset of fn's instructions)
   - rewritten: from clone+rewrite of callee; callee has fn_no_invoke name
     and invoke_targets_extern, so clone preserves ~inst_targets, and
     rewrite only modifies PARAM/RET (neither is INVOKE). *)
Triviality inline_call_site_fn_no_invoke:
  !prefix ret_lbl f callee bb_lbl idx name.
    fn_no_invoke name f /\
    fn_no_invoke name callee /\
    invoke_targets_extern callee ==>
    fn_no_invoke name (inline_call_site prefix ret_lbl f callee bb_lbl idx)
Proof
  rpt strip_tac >>
  simp[inline_call_site_def] >>
  Cases_on `lookup_block bb_lbl f.fn_blocks` >> simp[] >>
  simp[LET_THM] >> pairarg_tac >> simp[] >>
  (* Now goal: fn_no_invoke name (f with fn_blocks := newblocks) *)
  simp[fn_no_invoke_def, EVERY_APPEND] >> rpt conj_tac
  >- suspend "replace_block"
  >- suspend "drop"
  >> suspend "rewritten"
QED

Resume inline_call_site_fn_no_invoke[replace_block]:
  ho_match_mp_tac every_replace_block >> reverse conj_tac
  >- gvs[fn_no_invoke_def]
  >> drule_all fn_no_invoke_block >>
  simp[EVERY_APPEND, inst_targets_def] >>
  metis_tac[EVERY_TAKE]
QED

Resume inline_call_site_fn_no_invoke[drop]:
  drule_all fn_no_invoke_block >>
  metis_tac[EVERY_DROP]
QED

Triviality MEM_fn_insts_blocks:
  !bbs bb inst.
    MEM bb bbs /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts_blocks bbs)
Proof
  Induct >> simp[fn_insts_blocks_def, MEM_APPEND] >> metis_tac[]
QED

Triviality MEM_fn_insts:
  !bb fn inst.
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts fn)
Proof
  rw[fn_insts_def] >> irule MEM_fn_insts_blocks >> metis_tac[]
QED

Triviality clone_function_no_invoke:
  !prefix callee name.
    fn_no_invoke name callee /\
    invoke_targets_extern callee ==>
    EVERY (\bb. EVERY (\inst. ~inst_targets name inst) bb.bb_instructions)
      (clone_function prefix callee).fn_blocks
Proof
  rw[fn_no_invoke_def, clone_function_def, LET_THM, EVERY_MAP,
      EVERY_MEM] >>
  gvs[MEM_MAP, clone_basic_block_def] >>
  rename1 `MEM orig_bb callee.fn_blocks` >>
  gvs[MEM_MAP] >>
  rename1 `MEM orig_inst orig_bb.bb_instructions` >>
  simp[clone_instruction_def, inst_targets_def] >>
  Cases_on `orig_inst.inst_opcode = INVOKE` >> simp[] >>
  (* orig is INVOKE — fn_no_invoke says ~inst_targets for orig *)
  `~inst_targets name orig_inst` by (
    first_x_assum drule >> disch_then drule >> simp[]) >>
  gvs[inst_targets_def] >>
  Cases_on `orig_inst.inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[] >>
  (* h = Label l where l ≠ name *)
  simp[clone_operand_def] >>
  (* invoke_targets_extern: INVOKE target l ∉ fn_labels callee *)
  `~MEM s (fn_labels callee)` by (
    fs[invoke_targets_extern_def, EVERY_MEM] >>
    first_x_assum (qspec_then `orig_inst` mp_tac) >>
    (impl_tac >- (irule MEM_fn_insts >> metis_tac[])) >>
    simp[]) >>
  simp[]
QED

Resume inline_call_site_fn_no_invoke[rewritten]:
  irule rewrite_inline_blocks_no_invoke >>
  drule_all clone_function_no_invoke >>
  strip_tac >> metis_tac[]
QED

Finalise inline_call_site_fn_no_invoke

(* ===== Arity preservation (moved here — depends on fn_no_invoke block) ===== *)

(* inline_call_site preserves EVERY arity condition.
   Key insight: new blocks either come from original (TAKE/DROP preserves)
   or from callee clone (fn_no_invoke ⇒ no inst_targets ⇒ vacuous). *)
Triviality no_invoke_imp_arity_vacuous:
  !name callee bbs.
    EVERY (\bb. EVERY (\i. ~inst_targets name i) bb.bb_instructions) bbs ==>
    EVERY (\bb. EVERY (\inst.
      inst_targets name inst ==>
      callee_ret_arity_le (LENGTH inst.inst_outputs) callee)
      bb.bb_instructions) bbs
Proof
  rpt strip_tac >>
  irule EVERY_MONOTONIC >>
  qexists `\bb. EVERY (\i. ~inst_targets name i) bb.bb_instructions` >>
  simp[] >> rpt strip_tac >>
  irule EVERY_MONOTONIC >>
  qexists `\i. ~inst_targets name i` >> simp[]
QED

Triviality inline_call_site_preserves_arity:
  !prefix ret_lbl fn callee bb_lbl idx.
    fn_no_invoke callee.fn_name callee /\
    invoke_targets_extern callee /\
    EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      callee_ret_arity_le (LENGTH inst.inst_outputs) callee)
      bb.bb_instructions) fn.fn_blocks ==>
    EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      callee_ret_arity_le (LENGTH inst.inst_outputs) callee)
      bb.bb_instructions)
      (inline_call_site prefix ret_lbl fn callee bb_lbl idx).fn_blocks
Proof
  rpt strip_tac >>
  simp[inline_call_site_def] >>
  Cases_on `lookup_block bb_lbl fn.fn_blocks` >> simp[] >>
  simp[LET_THM] >> pairarg_tac >> simp[] >>
  simp[EVERY_APPEND] >> rpt conj_tac
  >- suspend "replace_block"
  >- suspend "return_bb"
  >> suspend "rewritten"
QED

Resume inline_call_site_preserves_arity[replace_block]:
  (* replace_block: TAKE of original + JMP *)
  irule every_replace_block >> simp[] >>
  simp[EVERY_APPEND, inst_targets_def] >>
  imp_res_tac lookup_block_MEM >>
  qpat_x_assum `EVERY _ fn.fn_blocks` mp_tac >>
  simp[EVERY_MEM] >> disch_then drule >> strip_tac >>
  rpt strip_tac >> imp_res_tac MEM_TAKE >>
  first_x_assum drule >> simp[inst_targets_def]
QED

Resume inline_call_site_preserves_arity[return_bb]:
  (* return_bb: DROP of original after invoke *)
  imp_res_tac lookup_block_MEM >>
  qpat_x_assum `EVERY _ fn.fn_blocks` mp_tac >>
  simp[EVERY_MEM] >> disch_then drule >> strip_tac >>
  rpt strip_tac >> imp_res_tac MEM_DROP_IMP >>
  first_x_assum drule >> simp[inst_targets_def]
QED

Resume inline_call_site_preserves_arity[rewritten]:
  (* rewritten_blocks: from clone, fn_no_invoke => vacuous *)
  irule no_invoke_imp_arity_vacuous >>
  irule rewrite_inline_blocks_no_invoke >>
  drule_all clone_function_no_invoke >> strip_tac >>
  first_x_assum (qspec_then `prefix` assume_tac) >>
  qpat_x_assum `rewrite_inline_blocks _ _ _ _ _ = _`
    (irule_at Any) >> simp[]
QED

Finalise inline_call_site_preserves_arity

(* renumber_block preserves inst_targets-guarded predicates:
   inst_targets depends on opcode+operands which renumber doesn't touch.
   The guarded predicate Q must be invariant under inst_id change. *)
Triviality renumber_block_preserves_targets_imp:
  !n bb name Q.
    (!i id. Q (i with inst_id := id) = Q i) ==>
    EVERY (\i. inst_targets name i ==> Q i) bb.bb_instructions ==>
    EVERY (\i. inst_targets name i ==> Q i)
      (SND (renumber_block_inst_ids n bb)).bb_instructions
Proof
  rw[renumber_block_inst_ids_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  `!insts n0 acc.
     EVERY (\i. inst_targets name i ==> Q i) insts /\
     EVERY (\i. inst_targets name i ==> Q i) acc ==>
     EVERY (\i. inst_targets name i ==> Q i)
       (SND (FOLDL (\(id,acc) inst. (id+1, acc ++ [inst with inst_id := id]))
              (n0, acc) insts))` suffices_by
    (disch_then (qspecl_then [`bb.bb_instructions`, `n`, `[]`] mp_tac) >>
     simp[]) >>
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[EVERY_APPEND, inst_targets_update_id]
QED

(* renumber_fn preserves inst_targets-guarded predicates *)
Triviality fn_renumber_preserves_targets_imp:
  !name Q f.
    (!i id. Q (i with inst_id := id) = Q i) ==>
    EVERY (\bb. EVERY (\i. inst_targets name i ==> Q i)
                       bb.bb_instructions) f.fn_blocks ==>
    EVERY (\bb. EVERY (\i. inst_targets name i ==> Q i)
                       bb.bb_instructions)
          (renumber_fn_inst_ids f).fn_blocks
Proof
  rw[renumber_fn_inst_ids_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  `!bbs n0 acc result n1.
     FOLDL (\(n,acc) bb. let (n',bb') = renumber_block_inst_ids n bb in
                         (n', acc ++ [bb'])) (n0, acc) bbs = (n1, result) /\
     EVERY (\bb. EVERY (\i. inst_targets name i ==> Q i)
                        bb.bb_instructions) acc /\
     EVERY (\bb. EVERY (\i. inst_targets name i ==> Q i)
                        bb.bb_instructions) bbs ==>
     EVERY (\bb. EVERY (\i. inst_targets name i ==> Q i)
                        bb.bb_instructions) result`
    suffices_by (disch_then (qspecl_then [`f.fn_blocks`, `0`, `[]`] mp_tac) >>
      simp[]) >>
  Induct >> simp[] >> rpt strip_tac >>
  gvs[LET_THM] >> pairarg_tac >> gvs[] >>
  first_x_assum (qspecl_then [`n'`, `acc ++ [bb']`, `result`, `n1`] mp_tac) >>
  simp[EVERY_APPEND] >>
  disch_then irule >>
  mp_tac (Q.SPECL [`n0`, `h`, `name`, `Q`] renumber_block_preserves_targets_imp) >>
  simp[]
QED

(* fix_inline_phis preserves inst_targets-guarded predicates:
   only modifies PHI instructions, and PHI <> INVOKE so inst_targets is false
   on all modified instructions, making the implication vacuous. *)
Triviality fix_inline_phis_preserves_targets_imp:
  !orig new_lbl ret_bb f name Q.
    EVERY (\bb. EVERY (\i. inst_targets name i ==> Q i)
                       bb.bb_instructions) f.fn_blocks ==>
    EVERY (\bb. EVERY (\i. inst_targets name i ==> Q i)
                       bb.bb_instructions)
          (fix_inline_phis orig new_lbl ret_bb f).fn_blocks
Proof
  rw[fix_inline_phis_def, LET_THM, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >>
  Cases_on `MEM bb'.bb_label (bb_succs ret_bb)` >> gvs[]
  >- (
    (* Modified block: i ∈ MAP over instructions *)
    gvs[MEM_MAP] >> rename1 `MEM orig_i bb'.bb_instructions` >>
    first_x_assum drule >> disch_then (mp_tac o SIMP_RULE std_ss [EVERY_MEM]) >>
    disch_then drule >> strip_tac >>
    Cases_on `orig_i.inst_opcode <> PHI` >> gvs[inst_targets_proj, subst_label_inst_def])
  >- metis_tac[]
QED

(* inline_one_site preserves EVERY arity condition *)
Triviality inline_one_site_preserves_arity:
  !fn callee ist fn' ist'.
    inline_one_site fn callee ist = SOME (fn', ist') /\
    fn_no_invoke callee.fn_name callee /\
    invoke_targets_extern callee /\
    EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      callee_ret_arity_le (LENGTH inst.inst_outputs) callee)
      bb.bb_instructions) fn.fn_blocks ==>
    EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      callee_ret_arity_le (LENGTH inst.inst_outputs) callee)
      bb.bb_instructions) fn'.fn_blocks
Proof
  rw[inline_one_site_def] >>
  gvs[AllCaseEqs(), LET_THM] >>
  qmatch_goalsub_abbrev_tac `renumber_fn_inst_ids caller''` >>
  `EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      callee_ret_arity_le (LENGTH inst.inst_outputs) callee)
      bb.bb_instructions) caller''.fn_blocks` suffices_by (
    strip_tac >>
    mp_tac (Q.SPECL [`callee.fn_name`,
      `\inst. callee_ret_arity_le (LENGTH inst.inst_outputs) callee`,
      `caller''`] fn_renumber_preserves_targets_imp) >>
    simp[]) >>
  qunabbrev_tac `caller''` >> CASE_TAC >> gvs[]
  >- (irule inline_call_site_preserves_arity >> simp[])
  >- (ho_match_mp_tac fix_inline_phis_preserves_targets_imp >>
      irule inline_call_site_preserves_arity >> simp[])
QED

(* Discharge pointwise arity from EVERY arity + find_invoke_site *)
Triviality every_arity_to_site_arity:
  !callee fn bb_lbl idx call_bb.
    ALL_DISTINCT (fn_labels fn) /\
    EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      callee_ret_arity_le (LENGTH inst.inst_outputs) callee)
      bb.bb_instructions) fn.fn_blocks /\
    find_invoke_site callee.fn_name fn.fn_blocks = SOME (bb_lbl, idx) /\
    lookup_block bb_lbl fn.fn_blocks = SOME call_bb ==>
    callee_ret_arity_le
      (LENGTH (EL idx call_bb.bb_instructions).inst_outputs) callee
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    gvs[fn_labels_def] >>
  drule_all find_invoke_site_inst_targets >> strip_tac >>
  imp_res_tac lookup_block_MEM >>
  qpat_x_assum `EVERY _ fn.fn_blocks` mp_tac >>
  simp[EVERY_MEM] >> disch_then drule >> strip_tac >>
  imp_res_tac find_invoke_site_idx_bound >>
  first_x_assum (qspec_then `EL idx call_bb.bb_instructions` mp_tac) >>
  simp[MEM_EL] >> metis_tac[]
QED

(* vars_fresh_above through inline_at_sites *)
Triviality vars_fresh_above_inline_at_sites:
  !n fn callee ist fn' ist'.
    inline_at_sites n fn callee ist = (fn', ist') /\
    ALL_DISTINCT (fn_labels fn) /\
    ALL_DISTINCT (fn_labels callee) /\
    labels_no_inline_return callee /\
    fn_no_invoke callee.fn_name callee /\
    invoke_targets_extern callee /\
    vars_fresh_above ist.is_inline_count fn /\
    labels_fresh_above ist.is_inline_count fn /\
    EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      callee_ret_arity_le (LENGTH inst.inst_outputs) callee)
      bb.bb_instructions) fn.fn_blocks ==>
    vars_fresh_above ist'.is_inline_count fn'
Proof
  Induct >> simp[inline_at_sites_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  (* Establish step results *)
  imp_res_tac inline_one_site_ist_count >>
  qspecl_then [`fn`, `callee`, `ist`, `caller'`, `ist''`]
    strip_assume_tac inline_one_site_preserves_preconds >> gvs[] >>
  qspecl_then [`fn`, `callee`, `ist`, `caller'`, `ist''`]
    strip_assume_tac inline_one_site_preserves_arity >> gvs[] >>
  qspecl_then [`fn`, `callee`, `ist`, `caller'`, `ist''`]
    mp_tac vars_fresh_above_inline_one_site >>
  (impl_tac >- (simp[] >> metis_tac[every_arity_to_site_arity])) >>
  strip_tac >>
  first_x_assum irule >>
  qexistsl [`callee`, `caller'`, `ist''`] >> gvs[]
QED

(* ===== End of arity preservation block ===== *)

(* inline_one_site preserves fn_no_invoke for arbitrary name *)
Triviality inline_one_site_fn_no_invoke_any:
  !fn callee ist fn' ist' name.
    inline_one_site fn callee ist = SOME (fn', ist') /\
    fn_no_invoke name fn /\
    fn_no_invoke name callee /\
    invoke_targets_extern callee ==>
    fn_no_invoke name fn'
Proof
  rw[inline_one_site_def] >>
  gvs[AllCaseEqs(), LET_THM] >>
  qmatch_abbrev_tac `fn_no_invoke name (renumber_fn_inst_ids caller'')` >>
  `fn_no_invoke name caller''` suffices_by metis_tac[fn_no_invoke_renumber] >>
  qunabbrev_tac `caller''` >> CASE_TAC >> simp[]
  >- (irule inline_call_site_fn_no_invoke >> simp[])
  >- (irule fix_inline_phis_fn_no_invoke >>
      irule inline_call_site_fn_no_invoke >> simp[])
QED

(* inline_at_sites preserves fn_no_invoke for arbitrary name *)
Triviality inline_at_sites_fn_no_invoke_any:
  !n fn callee ist fn' ist' name.
    inline_at_sites n fn callee ist = (fn', ist') /\
    fn_no_invoke name fn /\
    fn_no_invoke name callee /\
    invoke_targets_extern callee ==>
    fn_no_invoke name fn'
Proof
  Induct >> simp[inline_at_sites_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  first_x_assum irule >>
  qexistsl [`callee`, `caller'`, `ist''`, `ist'`] >> simp[] >>
  irule inline_one_site_fn_no_invoke_any >> metis_tac[]
QED

(* inline_candidate preserves EVERY (fn_no_invoke name) for arbitrary name *)
Triviality inline_candidate_fn_no_invoke_any:
  !ctx callee ist ctx' ist' name.
    fn_no_invoke name callee /\
    invoke_targets_extern callee /\
    EVERY (fn_no_invoke name) ctx.ctx_functions /\
    inline_candidate ctx callee ist = (ctx', ist') ==>
    EVERY (fn_no_invoke name) ctx'.ctx_functions
Proof
  rw[inline_candidate_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  (* FOLDL induction — use ctx.ctx_functions directly *)
  `!acc ist0 fns0 result ist1.
     EVERY (fn_no_invoke name) fns0 /\
     EVERY (fn_no_invoke name) acc /\
     FOLDL (\(fns_acc, st) caller_fn.
       let max_sites = LENGTH (fn_insts caller_fn) in
       let (caller', st') = inline_at_sites max_sites caller_fn callee st in
       (SNOC caller' fns_acc, st'))
       (acc, ist0) fns0 = (result, ist1) ==>
     EVERY (fn_no_invoke name) result` suffices_by
    (disch_then (qspecl_then [`[]`, `ist`, `ctx.ctx_functions`] mp_tac) >>
     simp[]) >>
  Induct_on `fns0` >- (rw[] >> gvs[]) >>
  rpt strip_tac >> gvs[LET_THM] >>
  pairarg_tac >> gvs[] >>
  `fn_no_invoke name caller'` by
    (irule inline_at_sites_fn_no_invoke_any >>
     metis_tac[]) >>
  first_x_assum irule >>
  qexistsl [`SNOC caller' acc`, `st'`, `ist1`] >>
  simp[EVERY_SNOC]
QED

(* entry-no-invoke through one round *)
Triviality entry_no_invoke_round:
  !ctx callee ist ctx_mid ist' name threshold walk.
    inliner_ctx_wf ctx ist /\
    lookup_function name ctx.ctx_functions = SOME callee /\
    select_inline_candidate ctx (fcg_analyze ctx) threshold
      walk = SOME name /\
    inline_candidate ctx callee ist = (ctx_mid, ist') ==>
    (!entry_name. (remove_function name ctx_mid).ctx_entry = SOME entry_name ==>
      EVERY (fn_no_invoke entry_name)
        (remove_function name ctx_mid).ctx_functions)
Proof
  rpt strip_tac >>
  (* Extract from inliner_ctx_wf *)
  qpat_x_assum `inliner_ctx_wf _ _`
    (assume_tac o PURE_REWRITE_RULE[inliner_ctx_wf_def]) >> gvs[] >>
  (* Derive ctx.ctx_entry = SOME entry_name *)
  imp_res_tac inline_candidate_ctx_entry >>
  gvs[remove_function_def] >>
  (* Apply the entry_no_invoke assumption *)
  first_x_assum (qspec_then `entry_name` mp_tac) >> simp[] >> strip_tac >>
  irule EVERY_FILTER_IMP >>
  (* Get callee properties *)
  imp_res_tac lookup_function_MEM >>
  `invoke_targets_extern callee` by (
    qpat_x_assum `EVERY inliner_fn_wf _` mp_tac >>
    simp[EVERY_MEM, inliner_fn_wf_def] >> metis_tac[]) >>
  `fn_no_invoke entry_name callee` by (
    qpat_x_assum `EVERY (fn_no_invoke _) _` mp_tac >>
    simp[EVERY_MEM]) >>
  irule inline_candidate_fn_no_invoke_any >>
  metis_tac[]
QED

(* Preservation of inliner_ctx_wf through one round *)
Theorem inliner_ctx_wf_round_preserved[local]:
  !ctx walk threshold ist ctx' walk' ist'.
    function_inliner_round ctx walk threshold ist = SOME (ctx', walk', ist') /\
    inliner_ctx_wf ctx ist ==> inliner_ctx_wf ctx' ist'
Proof
  rw[function_inliner_round_def, LET_THM] >>
  Cases_on `select_inline_candidate ctx (fcg_analyze ctx) threshold walk` >>
  gvs[] >>
  Cases_on `lookup_function x ctx.ctx_functions` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  imp_res_tac lookup_function_fn_name >>
  qpat_x_assum `x'.fn_name = x` (SUBST_ALL_TAC o GSYM) >>
  (* Derive candidate ≠ entry *)
  `ctx.ctx_entry <> SOME x'.fn_name` by (
    irule select_inline_candidate_not_entry >>
    qpat_x_assum `inliner_ctx_wf _ _`
      (assume_tac o PURE_REWRITE_RULE[inliner_ctx_wf_def]) >>
    gvs[] >> metis_tac[]) >>
  (* Expand ctx_wf goal, keeping inliner_ctx_wf in assumptions *)
  rewrite_tac[inliner_ctx_wf_def] >> rpt conj_tac
  >- suspend "rp_ctx_wf"
  >- suspend "rp_fn_wf"
  >- suspend "rp_labels_fresh"
  >- suspend "rp_vars_fresh"
  >- suspend "rp_entry_no_invoke"
  >- suspend "rp_callee_compat"
  >- suspend "rp_fn_names_prefix"
  >- suspend "rp_call_dag"
  >> suspend "rp_labels_disjoint"
QED

(* --- Resume blocks for each conjunct --- *)

(* C1: ctx_wf preserved *)
Resume inliner_ctx_wf_round_preserved[rp_ctx_wf]:
  irule ctx_wf_inline_remove >>
  qpat_x_assum `inliner_ctx_wf _ _`
    (assume_tac o PURE_REWRITE_RULE[inliner_ctx_wf_def]) >>
  gvs[] >> metis_tac[]
QED

(* Helper: EVERY on fn_name-based predicate transfers via MAP fn_name eq *)
Triviality every_fn_name_transfer:
  !P l1 l2.
    MAP (\f. f.fn_name) l1 = MAP (\f. f.fn_name) l2 /\
    EVERY (\f. P f.fn_name) l1 ==>
    EVERY (\f. P f.fn_name) l2
Proof
  gen_tac >> Induct >> simp[] >>
  Cases_on `l2` >> simp[] >> metis_tac[]
QED

(* C7: fn_names_no_inline_prefix *)
Resume inliner_ctx_wf_round_preserved[rp_fn_names_prefix]:
  qpat_x_assum `inliner_ctx_wf _ _`
    (assume_tac o PURE_REWRITE_RULE[inliner_ctx_wf_def]) >>
  gvs[] >>
  drule_all inline_candidate_fn_names >> strip_tac >>
  simp[remove_function_def, ctx_fn_names_def, EVERY_MAP] >>
  irule EVERY_FILTER_IMP >>
  ho_match_mp_tac every_fn_name_transfer >>
  qexists `ctx.ctx_functions` >>
  gvs[ctx_fn_names_def, EVERY_MAP]
QED

(* --- fn_has_entry preservation --- *)

Triviality fn_has_entry_renumber:
  !f. fn_has_entry (renumber_fn_inst_ids f) = fn_has_entry f
Proof
  rw[fn_has_entry_def, renumber_fn_inst_ids_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  `!bbs n0 acc result n1.
     FOLDL (\(n,acc) bb. let (n',bb') = renumber_block_inst_ids n bb in
                         (n', acc ++ [bb'])) (n0, acc) bbs = (n1, result) ==>
     (result = []) = (acc = [] /\ bbs = [])` suffices_by
    (disch_then (qspecl_then [`f.fn_blocks`, `0`, `[]`] mp_tac) >> simp[]) >>
  Induct >> simp[] >> rpt strip_tac >>
  gvs[LET_THM] >> pairarg_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Triviality fn_has_entry_fix_inline_phis:
  !a b c f. fn_has_entry (fix_inline_phis a b c f) = fn_has_entry f
Proof
  rw[fn_has_entry_def, fix_inline_phis_def, LET_THM] >>
  Cases_on `f.fn_blocks` >> simp[]
QED

Triviality inline_call_site_fn_has_entry:
  !prefix ret_lbl f callee bb_lbl idx.
    fn_has_entry f ==>
    fn_has_entry (inline_call_site prefix ret_lbl f callee bb_lbl idx)
Proof
  rw[inline_call_site_def] >>
  Cases_on `lookup_block bb_lbl f.fn_blocks` >> gvs[] >>
  simp[fn_has_entry_def, LET_THM] >> pairarg_tac >> simp[]
QED

Triviality inline_one_site_fn_has_entry:
  !fn callee ist fn' ist'.
    inline_one_site fn callee ist = SOME (fn', ist') /\
    fn_has_entry fn ==>
    fn_has_entry fn'
Proof
  rw[inline_one_site_def] >> gvs[AllCaseEqs(), LET_THM] >>
  simp[fn_has_entry_renumber, fn_has_entry_fix_inline_phis,
       inline_call_site_fn_has_entry] >>
  CASE_TAC >> simp[fn_has_entry_fix_inline_phis, inline_call_site_fn_has_entry]
QED

(* --- rewrite_inline removes PARAMs when input has no PARAMs --- *)

Triviality rewrite_inline_inst_no_param:
  !ops outs ret inst pi result pi'.
    rewrite_inline_inst ops outs ret inst pi = (result, pi') /\
    inst.inst_opcode <> PARAM ==>
    EVERY (\i. i.inst_opcode <> PARAM) result
Proof
  rpt gen_tac >> simp[rewrite_inline_inst_def, LET_THM] >>
  rpt (CASE_TAC >> simp[]) >>
  rpt strip_tac >> gvs[] >>
  simp[EVERY_MEM, MEM_MAPi, PULL_EXISTS]
QED

Triviality rewrite_inline_insts_no_param:
  !insts ops outs ret pi result pi'.
    rewrite_inline_insts ops outs ret insts pi = (result, pi') /\
    EVERY (\i. i.inst_opcode <> PARAM) insts ==>
    EVERY (\i. i.inst_opcode <> PARAM) result
Proof
  Induct >> simp[rewrite_inline_insts_def] >>
  rpt gen_tac >> simp[LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[EVERY_APPEND] >>
  metis_tac[rewrite_inline_inst_no_param]
QED

Triviality rewrite_inline_blocks_no_param:
  !bbs ops outs ret pi result pi'.
    rewrite_inline_blocks ops outs ret bbs pi = (result, pi') /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> PARAM) bb.bb_instructions) bbs ==>
    EVERY (\bb. EVERY (\i. i.inst_opcode <> PARAM) bb.bb_instructions) result
Proof
  Induct >> simp[rewrite_inline_blocks_def] >>
  rpt gen_tac >> simp[LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[rewrite_inline_block_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[rewrite_inline_insts_no_param]
QED

(* --- params_sequential preservation --- *)

Triviality params_sequential_no_param:
  !insts n. EVERY (\i. i.inst_opcode <> PARAM) insts ==>
            params_sequential insts n
Proof
  Induct >> simp[params_sequential_def] >>
  rpt strip_tac >> gvs[]
QED

Triviality params_sequential_take:
  !insts n k. params_sequential insts n ==>
              params_sequential (TAKE k insts) n
Proof
  Induct >> simp[params_sequential_def] >>
  rpt gen_tac >> Cases_on `k` >> simp[params_sequential_def] >>
  strip_tac >> CASE_TAC >> gvs[] >> metis_tac[]
QED

(* params_sequential only depends on inst_opcode and inst_operands.
   renumber_block_inst_ids_map shows renumber preserves those. *)
Triviality params_sequential_opcode_operands:
  !l1 l2 start.
    MAP (\i. (i.inst_opcode, i.inst_operands)) l1 =
    MAP (\i. (i.inst_opcode, i.inst_operands)) l2 ==>
    (params_sequential l1 start <=> params_sequential l2 start)
Proof
  Induct >> Cases_on `l2` >> simp[params_sequential_def] >>
  rpt strip_tac >> gvs[] >>
  CASE_TAC >> gvs[] >> metis_tac[]
QED

Triviality map_triple_imp_pair:
  !l1 l2.
    MAP (\i. (i.inst_opcode, i.inst_operands, i.inst_outputs)) l1 =
    MAP (\i. (i.inst_opcode, i.inst_operands, i.inst_outputs)) l2 ==>
    MAP (\i. (i.inst_opcode, i.inst_operands)) l1 =
    MAP (\i. (i.inst_opcode, i.inst_operands)) l2
Proof
  Induct >> Cases_on `l2` >> simp[] >> rpt strip_tac >> gvs[] >>
  first_x_assum irule >> simp[]
QED

Triviality params_sequential_renumber_block:
  !n0 bb start.
    params_sequential (SND (renumber_block_inst_ids n0 bb)).bb_instructions start
    <=> params_sequential bb.bb_instructions start
Proof
  rpt gen_tac >> irule params_sequential_opcode_operands >>
  irule map_triple_imp_pair >> simp[renumber_block_inst_ids_map]
QED

(* --- no_param_in_tl preservation ---
   After inline_call_site, TL blocks have no PARAMs because:
   - Original non-call blocks: unchanged, no PARAMs (from no_param_in_tl)
   - Truncated call block (if not HD): TAKE + [JMP], both have no PARAMs in TL
   - return_bb: DROP of call block after INVOKE — no PARAMs
   - Rewritten clone blocks: all PARAMs became ASSIGNs *)

Triviality map_opcode_from_triple:
  !l1 l2.
    MAP (\i. (i.inst_opcode, i.inst_operands, i.inst_outputs)) l1 =
    MAP (\i. (i.inst_opcode, i.inst_operands, i.inst_outputs)) l2 ==>
    MAP (\i. i.inst_opcode) l1 = MAP (\i. i.inst_opcode) l2
Proof
  Induct >> Cases_on `l2` >> simp[] >> rpt strip_tac >> gvs[]
QED

Triviality renumber_block_opcodes:
  !n bb. MAP (\i. i.inst_opcode) (SND (renumber_block_inst_ids n bb)).bb_instructions =
         MAP (\i. i.inst_opcode) bb.bb_instructions
Proof
  rpt gen_tac >> irule map_opcode_from_triple >> simp[renumber_block_inst_ids_map]
QED

Triviality renumber_foldl_opcodes:
  !bbs n0 acc result n1.
    FOLDL (\(n,acc) bb. let (n',bb') = renumber_block_inst_ids n bb in
                       (n', acc ++ [bb'])) (n0, acc) bbs = (n1, result) ==>
    MAP (\bb. MAP (\i. i.inst_opcode) bb.bb_instructions) result =
    MAP (\bb. MAP (\i. i.inst_opcode) bb.bb_instructions) (acc ++ bbs)
Proof
  Induct >> simp[] >> rpt gen_tac >>
  simp[LET_THM] >> pairarg_tac >> gvs[] >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  `bb' = SND (renumber_block_inst_ids n0 h)` by simp[] >>
  gvs[renumber_block_opcodes]
QED

Triviality renumber_fn_opcodes:
  !f. MAP (\bb. MAP (\i. i.inst_opcode) bb.bb_instructions)
        (renumber_fn_inst_ids f).fn_blocks =
      MAP (\bb. MAP (\i. i.inst_opcode) bb.bb_instructions) f.fn_blocks
Proof
  gen_tac >> simp[renumber_fn_inst_ids_def] >>
  pairarg_tac >> gvs[] >>
  drule (SRULE [LET_THM] renumber_foldl_opcodes) >> simp[]
QED

Triviality every_opcode_transfer:
  !l1 l2 P.
    MAP (\bb. MAP (\i. i.inst_opcode) bb.bb_instructions) l1 =
    MAP (\bb. MAP (\i. i.inst_opcode) bb.bb_instructions) l2 /\
    EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions) l2 ==>
    EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions) l1
Proof
  Induct >> Cases_on `l2` >> simp[] >> rpt strip_tac >>
  gvs[EVERY_MEM, MEM_MAP]
  >- metis_tac[MEM_MAP]
  >- (first_x_assum (qspecl_then [`t`, `P`] mp_tac) >> simp[] >>
      metis_tac[])
QED

Triviality no_param_in_tl_renumber_fn:
  !f. EVERY (\bb. EVERY (\i. i.inst_opcode <> PARAM) bb.bb_instructions) (TL f.fn_blocks)
      ==>
      EVERY (\bb. EVERY (\i. i.inst_opcode <> PARAM) bb.bb_instructions)
        (TL (renumber_fn_inst_ids f).fn_blocks)
Proof
  gen_tac >> strip_tac >>
  ho_match_mp_tac every_opcode_transfer >>
  qexists `TL f.fn_blocks` >> simp[] >>
  once_rewrite_tac[MAP_TL] >> simp[renumber_fn_opcodes]
QED

Triviality no_param_after_invoke:
  !insts k.
    EVERY (\i. i.inst_opcode <> PARAM) insts /\
    k < LENGTH insts ==>
    EVERY (\i. i.inst_opcode <> PARAM) (DROP (k + 1) insts)
Proof
  rpt strip_tac >> irule EVERY_DROP >> simp[]
QED

(* --- KEY INSIGHT: label_ops_closed implies invoke_targets_extern ---
   label_ops_closed says all Label operands are block labels.
   invoke_targets_extern says INVOKE's Label targets are NOT block labels.
   For an INVOKE with Label l first operand, these contradict.
   So label_ops_closed implies no INVOKE has Label first operand,
   making invoke_targets_extern vacuously true. *)

Triviality MEM_fn_insts_blocks_rev:
  !bbs inst. MEM inst (fn_insts_blocks bbs) ==>
    ?bb. MEM bb bbs /\ MEM inst bb.bb_instructions
Proof
  Induct >> simp[fn_insts_blocks_def, MEM_APPEND] >> metis_tac[]
QED

(* KEY LEMMA: inliner_fn_wf implies no INVOKE with Label first operand.
   Uses both label_ops_closed (Label ops → block labels) and
   invoke_targets_extern (INVOKE Label targets ∉ block labels) to derive
   a contradiction for any INVOKE with Label first operand. *)
Triviality inliner_fn_wf_no_inst_targets:
  !fn bb inst name.
    label_ops_closed fn /\ invoke_targets_extern fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
    ~inst_targets name inst
Proof
  rw[label_ops_closed_def, invoke_targets_extern_def,
     inst_targets_def, EVERY_MEM] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[] >>
  (* Label s :: _: label_ops_closed gives MEM s (fn_labels fn),
     invoke_targets_extern gives ¬MEM s (fn_labels fn) *)
  `MEM inst (fn_insts fn)` by metis_tac[MEM_fn_insts] >>
  first_x_assum drule >> simp[] >>
  first_x_assum (qspecl_then [`bb`, `inst`, `name`] mp_tac) >>
  simp[]
QED

(* COROLLARY: no INVOKE with Label first operand means
   invoke_targets_extern is vacuously true for any fn_labels *)
Triviality no_label_invoke_imp_invoke_targets_extern:
  !fn.
    (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      inst.inst_opcode = INVOKE ==>
      case inst.inst_operands of Label l :: _ => F | _ => T) ==>
    invoke_targets_extern fn
Proof
  rpt strip_tac >>
  simp[invoke_targets_extern_def, EVERY_MEM, fn_insts_def] >>
  rpt strip_tac >>
  drule MEM_fn_insts_blocks_rev >> strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[] >>
  first_x_assum (qspecl_then [`bb`, `inst`] mp_tac) >> gvs[]
QED

(* label_ops_closed + invoke_targets_extern implies fn_no_invoke for ALL names *)
Triviality label_ops_invoke_imp_all_fn_no_invoke:
  !fn. label_ops_closed fn /\ invoke_targets_extern fn ==>
    !b. fn_no_invoke b fn
Proof
  rpt strip_tac >>
  simp[fn_no_invoke_def, EVERY_MEM] >> rpt strip_tac >>
  metis_tac[inliner_fn_wf_no_inst_targets]
QED

(* fn_no_invoke for ALL names implies invoke_targets_extern *)
Triviality all_fn_no_invoke_imp_invoke_targets_extern:
  !fn. (!b. fn_no_invoke b fn) ==> invoke_targets_extern fn
Proof
  simp[invoke_targets_extern_def, EVERY_MEM, fn_insts_def,
       fn_no_invoke_def, inst_targets_def] >>
  rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[] >>
  drule MEM_fn_insts_blocks_rev >> strip_tac >>
  first_x_assum (qspec_then `s` mp_tac) >>
  simp[EVERY_MEM] >>
  disch_then drule >> disch_then drule >> simp[]
QED

(* invoke_targets_extern preserved through inline_one_site.
   Chain: inliner_fn_wf ⇒ all fn_no_invoke ⇒ preserved through
   inline_one_site ⇒ all fn_no_invoke fn' ⇒ invoke_targets_extern fn' *)
Triviality invoke_targets_extern_inline_one_site:
  !fn callee ist fn' ist'.
    inline_one_site fn callee ist = SOME (fn', ist') /\
    label_ops_closed fn /\ invoke_targets_extern fn /\
    label_ops_closed callee /\ invoke_targets_extern callee /\
    fn_no_invoke callee.fn_name callee ==>
    invoke_targets_extern fn'
Proof
  rpt strip_tac >>
  irule all_fn_no_invoke_imp_invoke_targets_extern >>
  gen_tac >>
  irule inline_one_site_fn_no_invoke_any >>
  qexistsl [`callee`, `fn`, `ist`, `ist'`] >> simp[] >>
  metis_tac[label_ops_invoke_imp_all_fn_no_invoke]
QED

(* --- Combined inline_at_sites_preserves_fn_wf --- *)

(* KEY INSIGHT: inliner_fn_wf fn implies no INVOKE with Label first operand
   exists in fn (via label_ops_closed + invoke_targets_extern contradiction).
   So find_invoke_site always returns NONE, inline_one_site returns NONE,
   and inline_at_sites is the identity. *)
Triviality inliner_fn_wf_no_invoke_site:
  !fn name. inliner_fn_wf fn ==>
    find_invoke_site name fn.fn_blocks = NONE
Proof
  rw[inliner_fn_wf_def, find_invoke_site_none, EVERY_MEM,
     fn_no_invoke_def] >> rpt strip_tac >>
  metis_tac[inliner_fn_wf_no_inst_targets]
QED

Triviality inline_at_sites_preserves_fn_wf:
  !n fn callee ist fn' ist'.
    inline_at_sites n fn callee ist = (fn', ist') /\
    inliner_fn_wf fn /\
    inliner_fn_wf callee /\
    fn_no_invoke callee.fn_name callee /\
    invoke_targets_extern callee /\
    labels_fresh_above ist.is_inline_count fn /\
    vars_fresh_above ist.is_inline_count fn /\
    ALL_DISTINCT (fn_labels callee) /\
    labels_no_inline_return callee ==>
    inliner_fn_wf fn'
Proof
  Induct >> rpt strip_tac
  >- gvs[inline_at_sites_def]
  >> gvs[inline_at_sites_def] >>
  `find_invoke_site callee.fn_name fn.fn_blocks = NONE`
    by metis_tac[inliner_fn_wf_no_invoke_site] >>
  gvs[inline_one_site_def]
QED

(* --- fn_wf through inline_candidate FOLDL --- *)

Triviality fn_wf_foldl:
  !fns0 acc callee ist result ist1.
    FOLDL (\(fns, ist) fn.
      let (fn', ist') = inline_at_sites (LENGTH (fn_insts fn)) fn callee ist in
      (SNOC fn' fns, ist')) (acc, ist) fns0 = (result, ist1) /\
    EVERY inliner_fn_wf acc /\
    EVERY inliner_fn_wf fns0 /\
    inliner_fn_wf callee /\
    fn_no_invoke callee.fn_name callee /\
    invoke_targets_extern callee /\
    ALL_DISTINCT (fn_labels callee) /\
    labels_no_inline_return callee /\
    EVERY (\f. labels_fresh_above ist.is_inline_count f) fns0 /\
    EVERY (\f. vars_fresh_above ist.is_inline_count f) fns0 ==>
    EVERY inliner_fn_wf result
Proof
  Induct >> simp[] >> rpt gen_tac >> simp[LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac inline_at_sites_ist_count >>
  first_x_assum (qspecl_then [`SNOC fn' acc`, `callee`, `ist'`,
    `result`, `ist1`] mp_tac) >>
  simp[EVERY_SNOC] >> disch_then irule >> rpt conj_tac
  >- (mp_tac inline_at_sites_preserves_fn_wf >>
      disch_then (qspecl_then [`LENGTH (fn_insts h)`, `h`, `callee`,
        `ist`, `fn'`, `ist'`] mp_tac) >>
      gvs[inliner_fn_wf_def])
  >- (gvs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
      strip_tac >> imp_res_tac inline_at_sites_ist_count >>
      irule labels_fresh_above_mono >> qexists `ist.is_inline_count` >> simp[])
  >- (gvs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
      strip_tac >> imp_res_tac inline_at_sites_ist_count >>
      irule vars_fresh_above_mono >> qexists `ist.is_inline_count` >> simp[])
QED

Triviality fn_wf_round:
  !ctx callee ist ctx' ist'.
    EVERY inliner_fn_wf ctx.ctx_functions /\
    inliner_fn_wf callee /\
    EVERY (\f. labels_fresh_above ist.is_inline_count f) ctx.ctx_functions /\
    EVERY (\f. vars_fresh_above ist.is_inline_count f) ctx.ctx_functions /\
    inline_candidate ctx callee ist = (ctx', ist') ==>
    EVERY inliner_fn_wf ctx'.ctx_functions
Proof
  rpt strip_tac >>
  gvs[SRULE [LET_THM] inline_candidate_def] >>
  pairarg_tac >> gvs[] >>
  irule fn_wf_foldl >>
  qexistsl [`[]`, `callee`, `ctx.ctx_functions`, `ist`, `ist'`] >>
  simp[] >>
  imp_res_tac lookup_function_MEM >>
  `inliner_fn_wf callee` by gvs[EVERY_MEM] >>
  gvs[inliner_fn_wf_def]
QED

(* C2: EVERY inliner_fn_wf *)
Resume inliner_ctx_wf_round_preserved[rp_fn_wf]:
  qpat_x_assum `inliner_ctx_wf _ _`
    (assume_tac o PURE_REWRITE_RULE[inliner_ctx_wf_def]) >> gvs[] >>
  imp_res_tac lookup_function_MEM >>
  `inliner_fn_wf x'` by gvs[EVERY_MEM] >>
  simp[remove_function_def] >> irule EVERY_FILTER_IMP >>
  irule fn_wf_round >>
  qexistsl [`x'`, `ctx`, `ist`, `ist'`] >> gvs[inliner_fn_wf_def]
QED

(* C3: labels_fresh_above — helper to avoid by-block in rich context *)
Triviality labels_fresh_above_round:
  !ctx callee ist ctx' ist'.
    EVERY inliner_fn_wf ctx.ctx_functions /\
    inliner_fn_wf callee /\
    EVERY (\f. labels_fresh_above ist.is_inline_count f) ctx.ctx_functions /\
    inline_candidate ctx callee ist = (ctx', ist') ==>
    EVERY (\f. labels_fresh_above ist'.is_inline_count f) ctx'.ctx_functions
Proof
  rpt strip_tac >>
  `EVERY (\f. ALL_DISTINCT (fn_labels f) /\
              labels_fresh_above ist'.is_inline_count f)
     ctx'.ctx_functions` suffices_by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  irule inline_candidate_labels_fresh >>
  gvs[inliner_fn_wf_def] >>
  qexistsl [`callee`, `ctx`, `ist`] >> simp[] >>
  gvs[EVERY_MEM] >> rpt strip_tac >> gvs[inliner_fn_wf_def]
QED

Resume inliner_ctx_wf_round_preserved[rp_labels_fresh]:
  qpat_x_assum `inliner_ctx_wf _ _`
    (assume_tac o PURE_REWRITE_RULE[inliner_ctx_wf_def]) >> gvs[] >>
  simp[remove_function_def] >>
  irule EVERY_FILTER_IMP >>
  imp_res_tac lookup_function_MEM >>
  irule labels_fresh_above_round >>
  `inliner_fn_wf x'` by (gvs[EVERY_MEM]) >>
  metis_tac[]
QED

(* C4: FOLDL step for vars_fresh_above — concrete, no higher-order tricks *)
Triviality vars_fresh_above_foldl:
  !callee fns0 acc ist0 result ist1.
    inliner_fn_wf callee /\
    EVERY (\f. ALL_DISTINCT (fn_labels f) /\
               labels_fresh_above ist0.is_inline_count f /\
               vars_fresh_above ist0.is_inline_count f /\
               EVERY (\bb. EVERY (\inst.
                 inst_targets callee.fn_name inst ==>
                 callee_ret_arity_le (LENGTH inst.inst_outputs) callee)
                 bb.bb_instructions) f.fn_blocks) fns0 /\
    EVERY (\f. vars_fresh_above ist0.is_inline_count f) acc /\
    FOLDL (\(fns, st) caller_fn.
      (\(caller', st'). (SNOC caller' fns, st'))
        (inline_at_sites (LENGTH (fn_insts caller_fn))
                         caller_fn callee st))
      (acc, ist0) fns0 = (result, ist1) ==>
    EVERY (\f. vars_fresh_above ist1.is_inline_count f) result
Proof
  gen_tac >>
  Induct_on `fns0` >- (rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[LET_THM] >>
  pairarg_tac >> gvs[] >>
  imp_res_tac inline_at_sites_ist_count >>
  first_x_assum (qspecl_then [`SNOC caller' acc`, `st'`,
    `result`, `ist1`] mp_tac) >>
  simp[EVERY_SNOC] >>
  disch_then irule >> rpt conj_tac
  >- ( (* subgoal 1: EVERY (4-conjunct) fns0 — monotonicity *)
    irule EVERY_MONOTONIC >>
    qexists `\f. ALL_DISTINCT (fn_labels f) /\
                 labels_fresh_above ist0.is_inline_count f /\
                 vars_fresh_above ist0.is_inline_count f /\
                 EVERY (\bb. EVERY (\inst.
                   inst_targets callee.fn_name inst ==>
                   callee_ret_arity_le (LENGTH inst.inst_outputs) callee)
                   bb.bb_instructions) f.fn_blocks` >>
    simp[] >> rpt strip_tac >>
    metis_tac[vars_fresh_above_mono, labels_fresh_above_mono])
  >- ( (* subgoal 2: EVERY vars_fresh acc — monotonicity *)
    irule EVERY_MONOTONIC >>
    qexists `\f. vars_fresh_above ist0.is_inline_count f` >>
    simp[] >> rpt strip_tac >>
    irule vars_fresh_above_mono >> metis_tac[])
  >> ( (* subgoal 3: vars_fresh caller' — step lemma *)
    irule vars_fresh_above_inline_at_sites >>
    qexistsl [`callee`, `h`, `ist0`, `LENGTH (fn_insts h)`] >> gvs[] >>
    gvs[inliner_fn_wf_def])
QED

Triviality vars_fresh_above_round:
  !ctx callee ist ctx' ist'.
    EVERY inliner_fn_wf ctx.ctx_functions /\
    inliner_fn_wf callee /\
    EVERY (\f. labels_fresh_above ist.is_inline_count f) ctx.ctx_functions /\
    EVERY (\f. vars_fresh_above ist.is_inline_count f) ctx.ctx_functions /\
    EVERY (\f. EVERY (\bb. EVERY (\inst.
      inst_targets callee.fn_name inst ==>
      callee_ret_arity_le (LENGTH inst.inst_outputs) callee)
      bb.bb_instructions) f.fn_blocks) ctx.ctx_functions /\
    inline_candidate ctx callee ist = (ctx', ist') ==>
    EVERY (\f. vars_fresh_above ist'.is_inline_count f) ctx'.ctx_functions
Proof
  rpt strip_tac >>
  gvs[SRULE [LET_THM] inline_candidate_def] >>
  pairarg_tac >> gvs[] >>
  irule vars_fresh_above_foldl >>
  qexistsl [`[]`, `callee`, `ctx.ctx_functions`, `ist`] >> simp[] >>
  simp[EVERY_CONJ] >> rpt strip_tac >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!e. MEM e _ ==> inliner_fn_wf _` drule >>
  simp[inliner_fn_wf_def]
QED

Resume inliner_ctx_wf_round_preserved[rp_vars_fresh]:
  qpat_x_assum `inliner_ctx_wf _ _`
    (assume_tac o PURE_REWRITE_RULE[inliner_ctx_wf_def]) >> gvs[] >>
  simp[remove_function_def] >>
  irule EVERY_FILTER_IMP >>
  imp_res_tac lookup_function_MEM >>
  `inliner_fn_wf x'` by (gvs[EVERY_MEM]) >>
  (* Extract callee_compat for the specific callee *)
  first_x_assum (qspecl_then [`x'.fn_name`, `x'`] mp_tac) >>
  simp[] >> strip_tac >>
  irule vars_fresh_above_round >>
  qexistsl [`x'`, `ctx`, `ist`] >> simp[] >>
  (* Weaken 4-conjunct callee_compat to just callee_ret_arity_le *)
  gvs[EVERY_MEM] >> metis_tac[]
QED



(* C5: entry-no-invoke *)
Resume inliner_ctx_wf_round_preserved[rp_entry_no_invoke]:
  rpt strip_tac >>
  irule (SRULE [] entry_no_invoke_round) >>
  metis_tac[]
QED

(* callee_compat is vacuously true when all functions satisfy inliner_fn_wf,
   because inliner_fn_wf implies ~inst_targets for all instructions *)
Triviality inliner_fn_wf_callee_compat_vacuous:
  !fns callee_name callee.
    EVERY inliner_fn_wf fns ==>
    EVERY (\f. EVERY (\bb. EVERY (\inst.
      inst_targets callee_name inst ==>
      callee_ret_arity_le (LENGTH inst.inst_outputs) callee /\
      EVERY (\blk. count_params blk.bb_instructions <=
                   LENGTH (TL inst.inst_operands)) callee.fn_blocks /\
      ALL_DISTINCT inst.inst_outputs /\
      EVERY (\op. !v. op = Var v ==> ~MEM v inst.inst_outputs)
        (TL inst.inst_operands))
      bb.bb_instructions) f.fn_blocks) fns
Proof
  rpt strip_tac >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  `label_ops_closed f /\ invoke_targets_extern f` by
    gvs[inliner_fn_wf_def] >>
  metis_tac[inliner_fn_wf_no_inst_targets]
QED

(* C6: callee_compat *)
Resume inliner_ctx_wf_round_preserved[rp_callee_compat]:
  rpt strip_tac >>
  irule inliner_fn_wf_callee_compat_vacuous >>
  simp[remove_function_def] >> irule EVERY_FILTER_IMP >>
  (* Derive EVERY inliner_fn_wf ctx''.ctx_functions from fn_wf_round *)
  qpat_x_assum `inliner_ctx_wf _ _`
    (assume_tac o PURE_REWRITE_RULE[inliner_ctx_wf_def]) >> gvs[] >>
  imp_res_tac lookup_function_MEM >>
  `inliner_fn_wf x'` by gvs[EVERY_MEM] >>
  irule fn_wf_round >>
  qexistsl [`x'`, `ctx`, `ist`, `ist'`] >> gvs[inliner_fn_wf_def]
QED

(* C8: ctx_call_dag — helper lemmas *)

(* inline_one_site SOME implies fn invokes callee *)
Triviality inline_one_site_some_fn_invokes:
  !fn callee ist r.
    inline_one_site fn callee ist = SOME r ==>
    ~fn_no_invoke callee.fn_name fn
Proof
  rw[inline_one_site_def, fn_no_invoke_def, GSYM find_invoke_site_none] >>
  gvs[AllCaseEqs()]
QED

(* Strengthened contrapositive: if fn' invokes b after inlining,
   then either fn already invoked b, or fn invoked callee AND callee invokes b *)
Triviality inline_at_sites_invoke_source:
  !n fn callee ist fn' ist' b.
    inline_at_sites n fn callee ist = (fn', ist') /\
    fn_no_invoke callee.fn_name callee /\
    invoke_targets_extern callee /\
    ~fn_no_invoke b fn' ==>
    ~fn_no_invoke b fn \/
    (~fn_no_invoke callee.fn_name fn /\ ~fn_no_invoke b callee)
Proof
  Induct
  >- simp[inline_at_sites_def]
  >> simp[inline_at_sites_def] >> rpt gen_tac >> strip_tac >>
     gvs[AllCaseEqs()] >>
     imp_res_tac inline_one_site_some_fn_invokes >>
     first_x_assum drule_all >> strip_tac >> gvs[]
  >> (* Both IH cases *)
     Cases_on `fn_no_invoke b fn` >> simp[] >>
     imp_res_tac inline_one_site_fn_no_invoke_any >> gvs[]
QED

(* FOLDL MEM correspondence: every fn in result came from acc or inline_at_sites *)
Triviality inline_foldl_mem_source:
  !fns0 acc ist0 callee result ist1 f.
    FOLDL (\(fns, st) caller_fn.
       (\(caller', st'). (SNOC caller' fns, st'))
         (inline_at_sites (LENGTH (fn_insts caller_fn)) caller_fn callee st))
       (acc, ist0) fns0 = (result, ist1) /\
    MEM f result ==>
    MEM f acc \/
    ?g ist2 ist3.
      MEM g fns0 /\
      inline_at_sites (LENGTH (fn_insts g)) g callee ist2 = (f, ist3)
Proof
  Induct >- (rw[] >> gvs[])
  >> rpt strip_tac >> gvs[Once FOLDL] >>
     pairarg_tac >> gvs[] >>
     first_x_assum (qspecl_then
       [`SNOC caller' acc`, `st'`, `callee`, `result`, `ist1`, `f`] mp_tac) >>
     simp[] >> strip_tac
  >- (gvs[MEM_SNOC] >- metis_tac[MEM] >> simp[])
  >> metis_tac[MEM]
QED

(* Lift to inline_candidate level *)
Triviality inline_candidate_mem_source:
  !ctx callee ist ctx' ist' f.
    inline_candidate ctx callee ist = (ctx', ist') /\
    MEM f ctx'.ctx_functions ==>
    ?g ist2 ist3.
      MEM g ctx.ctx_functions /\
      inline_at_sites (LENGTH (fn_insts g)) g callee ist2 = (f, ist3)
Proof
  rpt strip_tac >>
  gvs[SRULE [LET_THM] inline_candidate_def] >>
  pairarg_tac >> gvs[] >>
  drule inline_foldl_mem_source >> disch_then drule >> simp[]
QED

(* FOLDL correspondence: new call edges are in TC of original *)
Triviality inline_candidate_calls_in_tc:
  !ctx callee ist ctx' ist'.
    inline_candidate ctx callee ist = (ctx', ist') /\
    fn_no_invoke callee.fn_name callee /\
    invoke_targets_extern callee /\
    MEM callee ctx.ctx_functions ==>
    !a b. ctx_calls ctx'.ctx_functions a b ==>
          (ctx_calls ctx.ctx_functions)^+ a b
Proof
  rpt strip_tac >>
  gvs[ctx_calls_def] >>
  drule_all inline_candidate_mem_source >> strip_tac >>
  drule_all inline_at_sites_invoke_source >> strip_tac >>
  drule inline_at_sites_fn_name >> strip_tac >> gvs[]
  >- (
    irule (CONJUNCT1 (SPEC_ALL TC_RULES)) >>
    simp[ctx_calls_def] >> metis_tac[])
  >> irule (CONJUNCT2 (SPEC_ALL TC_RULES)) >>
     qexists `callee.fn_name` >>
     conj_tac >>
     irule (CONJUNCT1 (SPEC_ALL TC_RULES)) >>
     simp[ctx_calls_def] >> metis_tac[]
QED

Resume inliner_ctx_wf_round_preserved[rp_call_dag]:
  qpat_x_assum `inliner_ctx_wf _ _`
    (assume_tac o PURE_REWRITE_RULE[inliner_ctx_wf_def]) >> gvs[] >>
  imp_res_tac lookup_function_MEM >>
  `inliner_fn_wf x'` by (gvs[EVERY_MEM]) >>
  (* Step 1: remove_function preserves ctx_call_dag *)
  simp[remove_function_def] >>
  irule ctx_call_dag_filter >>
  (* Step 2: inline_candidate preserves acyclicity via TC subsumption *)
  simp[ctx_call_dag_def] >> rpt strip_tac >>
  spose_not_then assume_tac >>
  (* TC of ctx_calls ctx'' ⊆ TC of ctx_calls ctx, by TC_MONOTONE + TC_IDEM *)
  `(ctx_calls ctx.ctx_functions)^+ name name` suffices_by
    metis_tac[ctx_call_dag_def] >>
  `((ctx_calls ctx.ctx_functions)^+)^+ name name` suffices_by
    metis_tac[TC_IDEM] >>
  irule TC_MONOTONE >>
  qexists `ctx_calls ctx''.ctx_functions` >> simp[] >>
  rpt strip_tac >>
  irule inline_candidate_calls_in_tc >>
  qexistsl [`x'`, `ctx''`, `ist`, `ist'`] >> simp[] >>
  gvs[inliner_fn_wf_def]
QED

(* Helper: fn_labels through case-on-lookup + fix_inline_phis *)
Triviality fn_labels_case_fix_inline_phis:
  !lbl fn ics a b.
    fn_labels (case lookup_block lbl ics.fn_blocks of
      NONE => ics | SOME ret_bb => fix_inline_phis a b ret_bb ics) =
    fn_labels ics
Proof
  rpt gen_tac >> Cases_on `lookup_block lbl ics.fn_blocks` >>
  simp[fn_labels_fix_inline_phis]
QED

(* Helper: inline_one_site labels are original or inline-prefixed.
   No ALL_DISTINCT needed — uses MEM containment directly. *)
Triviality inline_one_site_labels_mem_or_prefixed:
  !fn callee ist fn' ist'.
    inline_one_site fn callee ist = SOME (fn', ist') ==>
    !l. MEM l (fn_labels fn') ==>
      MEM l (fn_labels fn) \/ (?k. inline_prefix k ≼ l)
Proof
  rw[inline_one_site_def] >> gvs[AllCaseEqs(), LET_THM] >>
  rpt strip_tac >>
  imp_res_tac find_invoke_site_lookup >> gvs[] >>
  gvs[renumber_fn_inst_ids_fn_labels, fn_labels_case_fix_inline_phis] >>
  drule inline_call_site_fn_labels >>
  disch_then (qspecl_then [`inline_prefix ist.is_inline_count`,
    `return_block_label (inline_prefix ist.is_inline_count)
       ist.is_label_counter`, `callee`, `idx`] mp_tac) >>
  simp[] >> strip_tac >> gvs[MEM_APPEND, MEM_MAP] >>
  disj2_tac >> qexists `ist.is_inline_count` >>
  simp[return_block_label_def, inline_prefix_def, isPREFIX_STRCAT]
QED

(* Helper: inline_at_sites labels are original or inline-prefixed.
   Needs ALL_DISTINCT + labels_fresh_above + callee properties for
   induction through inline_one_site_all_distinct. *)
Triviality inline_at_sites_labels_mem_or_prefixed:
  !n fn callee ist fn' ist'.
    inline_at_sites n fn callee ist = (fn', ist') /\
    ALL_DISTINCT (fn_labels fn) /\
    ALL_DISTINCT (fn_labels callee) /\
    labels_fresh_above ist.is_inline_count fn /\
    labels_no_inline_return callee ==>
    !l. MEM l (fn_labels fn') ==>
      MEM l (fn_labels fn) \/ (?k. inline_prefix k ≼ l)
Proof
  Induct >- (rw[inline_at_sites_def]) >>
  rw[inline_at_sites_def] >> gvs[AllCaseEqs()] >>
  imp_res_tac inline_one_site_ist_count >>
  `~MEM (return_block_label (inline_prefix ist.is_inline_count)
           ist.is_label_counter)
        (MAP (STRCAT (inline_prefix ist.is_inline_count))
           (fn_labels callee))` by
    (irule ret_lbl_not_in_mapped_callee_weak >> simp[]) >>
  `ALL_DISTINCT (fn_labels caller')` by
    (irule inline_one_site_all_distinct >> metis_tac[]) >>
  drule_all labels_fresh_above_inline_one_site >> strip_tac >>
  (* Apply IH — labels_fresh_above (ist.is_inline_count + 1) = ist''.is_inline_count *)
  first_x_assum (qspecl_then [`caller'`, `callee`, `ist''`, `fn'`, `ist'`] mp_tac) >>
  gvs[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  metis_tac[inline_one_site_labels_mem_or_prefixed]
QED

(* Helper: labels-disjoint-from-names preserved through inline_at_sites *)
Triviality inline_at_sites_labels_disjoint_names:
  !n fn callee ist fn' ist' names.
    inline_at_sites n fn callee ist = (fn', ist') /\
    ALL_DISTINCT (fn_labels fn) /\
    ALL_DISTINCT (fn_labels callee) /\
    labels_fresh_above ist.is_inline_count fn /\
    labels_no_inline_return callee /\
    EVERY (\l. ~MEM l names) (fn_labels fn) /\
    EVERY (\name. !k. ~(inline_prefix k ≼ name)) names ==>
    EVERY (\l. ~MEM l names) (fn_labels fn')
Proof
  rpt strip_tac >>
  mp_tac inline_at_sites_labels_mem_or_prefixed >> simp[] >>
  disch_then drule >> simp[] >> strip_tac >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac
  >- (gvs[EVERY_MEM])
  >- (gvs[EVERY_MEM] >> metis_tac[])
QED

(* Helper: labels-disjoint-from-names preserved through inline_candidate.
   Threads ALL_DISTINCT + labels_fresh_above through FOLDL alongside
   the disjoint property, using concrete predicates (no higher-order P). *)
Triviality labels_disjoint_names_foldl:
  !fns0 acc ist0 callee result ist1 names.
    FOLDL (\(fns_acc, st) caller_fn.
      let max_sites = LENGTH (fn_insts caller_fn) in
      let (caller', st') = inline_at_sites max_sites caller_fn callee st in
      (SNOC caller' fns_acc, st'))
      (acc, ist0) fns0 = (result, ist1) /\
    ALL_DISTINCT (fn_labels callee) /\
    labels_no_inline_return callee /\
    EVERY (\name. !k. ~(inline_prefix k ≼ name)) names /\
    EVERY (\f. ALL_DISTINCT (fn_labels f) /\
               labels_fresh_above ist0.is_inline_count f /\
               EVERY (\l. ~MEM l names) (fn_labels f)) fns0 /\
    EVERY (\f. EVERY (\l. ~MEM l names) (fn_labels f)) acc ==>
    EVERY (\f. EVERY (\l. ~MEM l names) (fn_labels f)) result
Proof
  Induct >- (rw[] >> gvs[]) >>
  rpt strip_tac >> gvs[LET_THM] >>
  pairarg_tac >> gvs[] >>
  imp_res_tac inline_at_sites_ist_count >>
  first_x_assum (qspecl_then [`SNOC caller' acc`, `st'`, `callee`,
    `result`, `ist1`, `names`] mp_tac) >>
  simp[EVERY_SNOC] >> disch_then irule >> reverse (rpt conj_tac)
  >- (
    (* caller' has disjoint labels *)
    mp_tac inline_at_sites_labels_disjoint_names >> simp[] >>
    disch_then (qspecl_then [`LENGTH (fn_insts h)`, `h`, `callee`,
      `ist0`, `caller'`, `st'`, `names`] mp_tac) >> simp[])
  >- (
    (* EVERY 3-conjunct for rest of fns0 — bump labels_fresh_above *)
    irule EVERY_MONOTONIC >>
    qpat_x_assum `EVERY _ fns0` (irule_at Any) >>
    simp[] >> rpt strip_tac >>
    irule labels_fresh_above_mono >>
    qexists `ist0.is_inline_count` >> simp[])
QED

Triviality labels_disjoint_names_round:
  !ctx callee ist ctx' ist' names.
    inline_candidate ctx callee ist = (ctx', ist') /\
    ALL_DISTINCT (fn_labels callee) /\
    labels_no_inline_return callee /\
    EVERY (\name. !k. ~(inline_prefix k ≼ name)) names /\
    EVERY (\f. ALL_DISTINCT (fn_labels f) /\
               labels_fresh_above ist.is_inline_count f /\
               EVERY (\l. ~MEM l names) (fn_labels f))
      ctx.ctx_functions ==>
    EVERY (\f. EVERY (\l. ~MEM l names) (fn_labels f)) ctx'.ctx_functions
Proof
  rpt strip_tac >>
  gvs[SRULE [LET_THM] inline_candidate_def] >>
  pairarg_tac >> gvs[] >>
  irule labels_disjoint_names_foldl >>
  conj_tac
  >- (qexistsl [`[]`, `callee`, `ctx.ctx_functions`, `ist`, `ist'`] >> simp[])
  >- simp[]
QED

(* C9: fn_labels_disjoint_fn_names *)
Resume inliner_ctx_wf_round_preserved[rp_labels_disjoint]:
  qpat_x_assum `inliner_ctx_wf _ _`
    (assume_tac o PURE_REWRITE_RULE[inliner_ctx_wf_def]) >> gvs[] >>
  imp_res_tac lookup_function_MEM >>
  `inliner_fn_wf x'` by (gvs[EVERY_MEM]) >>
  (* Step 1: labels of ctx'' functions are disjoint from ctx_fn_names ctx *)
  mp_tac labels_disjoint_names_round >>
  disch_then (qspecl_then [`ctx`, `x'`, `ist`, `ctx''`, `ist'`,
    `ctx_fn_names ctx`] mp_tac) >> simp[] >>
  (impl_tac >- (
    gvs[inliner_fn_wf_def] >> simp[EVERY_CONJ] >>
    gvs[EVERY_MEM] >> rpt strip_tac >>
    first_x_assum drule >> gvs[inliner_fn_wf_def])) >>
  strip_tac >>
  (* fn_names of remove_function ⊆ fn_names of ctx'' = fn_names of ctx *)
  drule_all inline_candidate_fn_names >> strip_tac >>
  simp[remove_function_def] >> irule EVERY_FILTER_IMP >>
  simp[ctx_fn_names_def] >>
  qpat_x_assum `EVERY _ ctx''.ctx_functions` mp_tac >>
  PURE_REWRITE_TAC[ctx_fn_names_def] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  qpat_x_assum `MEM l (MAP _ (FILTER _ _))` mp_tac >>
  simp[MEM_MAP, MEM_FILTER] >> rpt strip_tac >> gvs[] >>
  metis_tac[MEM_MAP]
QED

Finalise inliner_ctx_wf_round_preserved

(* ===== Loop correctness ===== *)

Theorem function_inliner_loop_correct[local]:
  !n ctx walk threshold ist s fuel.
    inliner_ctx_wf ctx ist /\
    FDOM s.vs_labels = {} /\
    ~s.vs_halted ==>
    let ctx' = function_inliner_loop n ctx walk threshold ist in
    ?fuel'.
      inliner_result_equiv inline_vars
        (run_context fuel ctx s)
        (run_context fuel' ctx' s)
Proof
  Induct >- (
    rw[function_inliner_loop_def] >>
    qexists_tac `fuel` >> simp[inliner_result_equiv_refl]
  ) >>
  rw[function_inliner_loop_def, LET_THM] >>
  CASE_TAC >- (
    qexists_tac `fuel` >> simp[inliner_result_equiv_refl]
  ) >>
  PairCases_on `x` >> gvs[] >>
  (* Apply round_correct *)
  drule function_inliner_round_correct >>
  disch_then (qspecl_then [`s`, `fuel`] mp_tac) >> simp[] >>
  strip_tac >>
  (* Derive preservation for IH *)
  `inliner_ctx_wf x0 x2` by (
    imp_res_tac inliner_ctx_wf_round_preserved) >>
  (* Apply IH *)
  first_x_assum (qspecl_then [`x0`, `x1`, `threshold`, `x2`, `s`, `fuel'`]
    mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `fuel''` >>
  irule inliner_result_equiv_trans >>
  qexists_tac `run_context fuel' x0 s` >>
  simp[]
QED

(* ===== Main theorem ===== *)

Theorem function_inliner_correct:
  !ctx s fuel threshold.
    inliner_ctx_wf ctx <| is_inline_count := 0; is_label_counter := 0 |> /\
    FDOM s.vs_labels = {} /\
    ~s.vs_halted ==>
    let ctx' = function_inliner_ctx threshold ctx in
    ?fuel'.
      inliner_result_equiv inline_vars
        (run_context fuel ctx s)
        (run_context fuel' ctx' s)
Proof
  rw[function_inliner_ctx_def, LET_THM] >>
  Cases_on `ctx.ctx_entry` >- (
    mp_tac (SIMP_RULE (srw_ss()) [LET_THM] function_inliner_loop_correct) >>
    disch_then (qspecl_then [`LENGTH ctx.ctx_functions`,
      `ctx`, `[]`, `threshold`,
      `<| is_inline_count := 0; is_label_counter := 0 |>`,
      `s`, `fuel`] mp_tac) >>
    simp[]
  ) >>
  mp_tac (SIMP_RULE (srw_ss()) [LET_THM] function_inliner_loop_correct) >>
  disch_then (qspecl_then [`LENGTH ctx.ctx_functions`,
    `ctx`, `build_call_walk (fcg_analyze ctx) x`, `threshold`,
    `<| is_inline_count := 0; is_label_counter := 0 |>`,
    `s`, `fuel`] mp_tac) >>
  simp[]
QED

val _ = export_theory();
