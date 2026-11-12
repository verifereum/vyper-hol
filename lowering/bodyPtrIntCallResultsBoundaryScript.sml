Theory bodyPtrIntCallResultsBoundary
Ancestors bodyPtrPreds vyperInterpreter vyperState exprLowering
  context compileEnv fragGasPathPtr bodyPtrIntCallEntryContracts
  bodyPtrIntCallConfinement stmtFragPtr exprSimWordArgs gasCount
  bodyPtrDefs gasSummary venomState

Theorem intcall_successful_results_ptr_children:
  !es cx s raws t.
    body_results_ptr_ok cx es /\
    eval_expr_results cx es s = (INL raws,t) ==>
    EVERY (body_expr_ptr_ok cx) es
Proof
  Induct_on `es` >> simp[body_results_ptr_ok_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  metis_tac[]
QED

(* Both empty argument phases leave the compiler and the counted runtime
   state untouched.  This is also the base case when flags/types are empty. *)
Theorem intcall_empty_argument_phases:
  ~s.vs_halted ==>
  compile_multi_vvs compile_expr ce [] sa = ([],sa) /\
  compile_stage_intcall_args ce [] flags tys sa = ([],sa) /\
  eval_expr_results cx [] es = (INL [],es) /\
  gas_path_ptr D lo ctx fn PG G tn s 0 G tn (OK s)
Proof
  simp[compile_multi_vvs_def, compile_stage_intcall_args_def,
       comp_return_def, Once evaluate_def, return_def] >>
  strip_tac >> irule (cj 1 gas_path_ptr_rules) >> simp[]
QED

Theorem intcall_empty_results_ptr_outcome:
  stmt_state_rel ctx fn ce cx es s /\ ghost_inv d ce cx es G tn s /\
  ~s.vs_halted ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
    (eval_expr_results cx []) (es,s,G,tn)
    (\res ee H un t.
      res = INL [] /\ ee = es with gas_obs := [] /\
      H = G /\ un = tn /\ t = s /\
      stmt_state_rel ctx fn ce cx ee t /\ ghost_inv d ce cx ee H un t /\
      ghost_kept ce es sa G tn s H un /\ pure_frame ce fn es sa s t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid site. FLOOKUP s.vs_allocas aid = SOME site ==>
                  FLOOKUP t.vs_allocas aid = SOME site))
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> simp[gas_outcome_ptr_def] >> qexists_tac `[]` >>
  disj1_tac >> simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL []`, `es`, `G`, `tn`, `OK s`] >>
  simp[Once evaluate_def, return_def, gas_explicit_def,
       ghost_inv_gas_obs, ghost_kept_def] >>
  irule (cj 1 gas_path_ptr_rules) >> simp[]
QED

Theorem intcall_empty_staging_ptr_frame:
  compile_stage_intcall_args ce [] flags tys sa = (ops,sb) /\
  stmt_state_rel ctx fn ce cx ee s /\ ghost_inv d ce cx ee G tn s /\
  ~s.vs_halted ==>
  ?H un t argv.
    gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 H un (OK t) /\
    sb = sa /\ t = s /\ H = G /\ un = tn /\ ops = [] /\ argv = [] /\
    eval_operands ops t = SOME argv /\
    stmt_state_rel ctx fn ce cx ee t /\ ghost_inv d ce cx ee H un t /\
    ghost_kept ce ee sa G tn s H un /\ pure_frame ce fn ee sa s t /\
    intcall_owned_sites 0 sa.cs_next_id ops H t /\
    EVERY (\op. !site. op_prov H op = SOME site ==>
      intcall_site_outside (intcall_protected ce ee sa s) site) ops
Proof
  simp[compile_stage_intcall_args_def, comp_return_def] >> strip_tac >>
  simp[eval_operands_def, ghost_kept_def, intcall_owned_sites_def] >>
  irule (cj 1 gas_path_ptr_rules) >> simp[]
QED

(* AUDIT ONLY.  The following quotations are parsed/typechecked contracts,
   not theorem claims.  In particular they do not supply either runner.
   Keeping them here checks all argument orders without introducing an
   admission or a predicate which conceals an unproved run.

   Evaluation interface: css retains the ORIGINAL interval of every operand.
   The observation-closure premise below is deliberately explicit: its
   body-pre/admissibility producer must be proved before publishing a runner.
   post_value_type equality is also retained, not inferred from purity alone.
   The list admissibility test handles exceptions separately from INL raws. *)
val _ = ``
  body_inv tops ctx ce cx /\ body_results_ptr_ok cx args /\
  EVERY (supported_expr tops) args /\
  EVERY (\e. ~expr_has_effect e) args /\
  EVERY (\e. post_value_type ce e = expr_type e) args /\
  (!e ee. MEM e args /\ ee.scopes = es.scopes /\
     ee.accounts = es.accounts /\ ee.tStorage = es.tStorage /\
     ee.immutables = es.immutables ==>
     expr_body_pre ce cx env e ee /\
     gas_admissible (eval_expr cx e) expr_vv_res_ok ee) /\
  gas_admissible (eval_expr_results cx args)
    (\res. case res of INL raws => LENGTH raws = LENGTH args
            | INR exc => expr_vv_res_ok (INR exc)) es /\
  compile_multi_vvs compile_expr ce args sa = (vvs,sb) /\
  LENGTH css = SUC (LENGTH args) /\ HD css = sa /\ LAST css = sb /\
  LENGTH vvs = LENGTH args /\
  (!i. i < LENGTH args ==>
    compile_expr ce (expr_type (EL i args)) (EL i args) (EL i css) =
      (EL i vvs, EL (SUC i) css)) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx fn ce cx es s /\ ghost_inv d ce cx es G tn s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
    (eval_expr_results cx args) (es,s,G,tn)
    (\res ee H un t. ?raws.
      res = INL raws /\ LENGTH raws = LENGTH args /\
      stmt_state_rel ctx fn ce cx ee t /\ ghost_inv d ce cx ee H un t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ee.scopes = es.scopes /\ ee.accounts = es.accounts /\
      ee.tStorage = es.tStorage /\ ee.immutables = es.immutables /\
      ghost_kept ce es sa G tn s H un /\ pure_frame ce fn es sa s t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid site. FLOOKUP s.vs_allocas aid = SOME site ==>
        FLOOKUP t.vs_allocas aid = SOME site) /\
      (!i. i < LENGTH args ==>
        vv_holds ce cx (expr_type (EL i args)) (EL i raws) (EL i vvs) ee t /\
        vv_at ce cx (expr_type (EL i args)) (EL i css) (EL (SUC i) css)
          ee (EL i raws) (EL i vvs) t /\
        vv_storage_live cx (EL i vvs) ee t /\
        ptr_vv_ok cx (expr_type (EL i args)) (EL i raws) (EL i vvs) ee H un t /\
        (!ty op. EL i vvs = StackValue ty op /\
          ~is_word_type (expr_type (EL i args)) ==> ptr_buf_ok ce (EL i args) op H t) /\
        (!ty p. EL i vvs = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok ce (EL i args) p.ptr_operand H t)))
    (\res ee gt r. expr_exit res r)
``;

(* Staging interface: no independently existential semantic entry state.
   It consumes delayed-read facts at precisely ee,s.  Stack parameters are
   words; memory parameters have capacity for the callee's declared type.
   Source physical annotations vv_type and destination tys remain distinct. *)
val _ = ``
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env ee /\
  compile_stage_intcall_args ce vvs flags tys sa = (ops,sb) /\
  LENGTH args = LENGTH vvs /\ LENGTH raws = LENGTH vvs /\
  LENGTH vs = LENGTH vvs /\ LENGTH flags = LENGTH vvs /\
  LENGTH tys = LENGTH vvs /\ LENGTH css = SUC (LENGTH vvs) /\
  read_results cx raws ee = (INL vs,ee) /\
  (!i. i < LENGTH vvs ==>
    vv_holds ce cx (expr_type (EL i args)) (EL i raws) (EL i vvs) ee s /\
    vv_at ce cx (expr_type (EL i args)) (EL i css) (EL (SUC i) css)
      ee (EL i raws) (EL i vvs) s /\
    vv_storage_live cx (EL i vvs) ee s /\
    ptr_vv_ok cx (expr_type (EL i args)) (EL i raws) (EL i vvs) ee G tn s /\
    (!ty op. EL i vvs = StackValue ty op /\
      ~is_word_type (expr_type (EL i args)) ==> ptr_buf_ok ce (EL i args) op G s) /\
    (!ty p. EL i vvs = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce (EL i args) p.ptr_operand G s) /\
    (EL i css).cs_next_id <= sa.cs_next_id /\
    (EL (SUC i) css).cs_next_id <= sa.cs_next_id /\
    (EL (SUC i) css).cs_next_var <= sa.cs_next_var /\
    vv_type (EL i vvs) = expr_type (EL i args) /\
    arg_type_fits (vv_type (EL i vvs)) (EL i tys) /\
    MAX 32 (type_memory_bytes ce (EL i tys)) < dimword (:256) /\
    (?stv dtv. evaluate_type (get_tenv cx) (vv_type (EL i vvs)) = SOME stv /\
      evaluate_type (get_tenv cx) (EL i tys) = SOME dtv /\
      val_wf stv (EL i vs) /\ val_wf dtv (EL i vs)) /\
    (EL i flags ==> is_word_type (EL i tys))) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  stmt_state_rel ctx fn ce cx ee s /\ ghost_inv d ce cx ee G tn s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?marks H un t argv.
    gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s (LENGTH marks) H un (OK t) /\
    EVERY (\b. b = F) marks /\
    LENGTH ops = LENGTH vvs /\ eval_operands ops t = SOME argv /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx fn ce cx ee t /\ ghost_inv d ce cx ee H un t /\
    ghost_kept ce ee sa G tn s H un /\ pure_frame ce fn ee sa s t /\
    (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
      lookup_var x t = SOME w) /\
    (!aid site. FLOOKUP s.vs_allocas aid = SOME site ==>
      FLOOKUP t.vs_allocas aid = SOME site) /\
    intcall_owned_sites 0 sa.cs_next_id ops H t /\
    EVERY (\op. !site. op_prov H op = SOME site ==>
      intcall_site_outside (intcall_protected ce ee sa s) site) ops /\
    (!i. i < LENGTH vvs ==>
      op_taint un (EL i ops) = {} /\
      if EL i flags then
        op_prov H (EL i ops) = NONE /\
        EL i argv = val_to_w256 (EL i vs)
      else
        ptr_mem_ok cx (EL i tys) (EL i vs) (EL i ops) H un t /\
        ?b n. op_prov H (EL i ops) = SOME (b,n) /\
          b <= w2n (EL i argv) /\
          w2n (EL i argv) + MAX 32 (type_memory_bytes ce (EL i tys)) <= b+n)
``;

(* Conjunct/producer ledger for the audited contracts (NOT proof credit).

   EVALUATION INPUTS
   - body_results_ptr_ok: the frozen third IH; on a successful whole list,
     intcall_successful_results_ptr_children exposes EVERY body_expr_ptr_ok.
     For exceptions retain body_results_ptr_ok's conditional tail clause:
     its existential success guard is supplied only after the head succeeds.
   - Effect freedom: intcall_body_pre_effect_free_args. Supported children,
     child expr_body_pre and gas_admissible closure: residual producer from
     the outer expr_body_pre/gas_admissible, NOT assumed proved here.
     gas_admissible_def quantifies all gas streams. The INL list predicate
     above is not expr_vv_res_ok applied to a list; INR uses the exception
     branch of that predicate. Exception composition must preserve expr_exit.
   - post_value_type equality: post_value_type_no_calls suffices after an
     effect-free supported expression is shown to have no internal calls;
     that traversal implication remains a residual producer. Purity by itself
     is not a rewrite of post_value_type. Keep equality until it is proved.
   - css intervals: compile_multi_vvs_def exposes compile_expr head/tail;
     compile_expr_extends (or compile_expr_grows) gives cs_extends and both
     monotone counters on EACH equation. Transitivity supplies all staging
     inequalities. No final-interval substitution in vv_at is valid here.
   - Initial code/layout/ghost/cursor assumptions are precisely those of
     expr_vv_sim_ptr_def. fn_has_code_split and compiler extension must
     transport them to each child, a remaining list-runner obligation.

   EVALUATION OUTPUTS
   - Each child's vv_post_def gives vv_holds, vv_at, vv_storage_live, old
     SOME lookups, old allocation entries, locals_kept and pure_frame.
     expr_vv_sim_ptr_def separately gives ptr_vv_ok, BOTH ptr_buf_ok clauses,
     ghost_inv, ghost_kept and its counted gas_outcome_ptr (not an S1 run).
   - intcall_effect_free_results_observations supplies all four source
     observations, on both success and exception. Delayed read_result and
     read_results transport: intcall_effect_free_results_delayed_read(s).
   - These facts do NOT yet prove delayed vv_at/ptr_vv_ok/ptr_buf_ok/vv_holds.
     Residual transport must combine unchanged pure_frame bytes, old operand
     values/provenance, ghost_kept taint non-growth and delayed source reads.
     Located footprint separation uses intcall_located_footprint_separation;
     writes use intcall_located_ptr_confined_write. Stack memory and storage
     variants and the whole-list pure/ghost frame composition remain work.
   - nil: intcall_empty_results_ptr_outcome proves the exact gas outcome and
     frame. All per-element conjuncts are vacuous; css=[sa], sb=sa, vvs=[]
     come from intcall_empty_argument_phases. Cursor equations then follow
     from its unchanged runtime state and the input cursor equations.

   STAGING INPUTS/OUTPUTS
   - The common ee,s inputs are evaluation outputs, NOT an S1 existential.
     read_results success is the actual source read phase. Source physical
     vv_type equality needs compile_expr result-tag facts (StageArgument);
     no equality of destination tys with source types is asserted.
   - arg_type_fits (vv_type vv) dst_ty is the source/destination relation of
     the counted typed-copy interfaces. Both evaluated semantic types and
     val_wf are retained. Residual producer: source call typing/bind_arguments
     plus coherent expr_sim_inv metadata. This is not proved by pointer facts.
   - Destination size bound: residual call-layout/alloc_limits producer.
     The required callee layout bridge is: for each bound parameter entry
     at MemLoc off sz, type_memory_size entry.type <= sz and sz no larger
     than MAX 32 (type_memory_bytes caller_ce declared_arg_ty). Inputs are
     build_compile_env's parameter layout, bind_arguments and evaluated
     declared argument types, plus struct-metadata agreement. internal_args_rel
     alone supplies no provenance/capacity evidence. Prologue's
     intcall_entry_captured_pending consumes this bridge and staged robustness.
   - ALLOCA: exec_alloca_def has reused and new-site branches. Size/capacity
     and upper endpoint require stmt_state_rel's allocation invariants and
     code/layout matching; old address >= s.vs_alloca_next is NOT required.
     Residual allocation runner must publish the actual instruction ID >=
     sa.cs_next_id, its table entry, capacity, and whole-site separation from
     old sites/locals. intcall_separated_site_outside then proves separation
     from intcall_protected; intcall_owned_sites_def uses lo=0. Combined INVOKE
     ownership must start BEFORE the separate return-buffer allocation.
   - unwrap_value execution, ALLOCA, store sequencing, list induction and
     ghost/pure frame preservation remain staging-runner obligations. Its
     counted path must end at the actual INVOKE operands, not at a replacement
     entry. Scalar operands have no provenance; memory operands have robust
     values, full destination capacity, instruction-site ownership and explicit
     protected-set separation, independently of one another.
   - nil: intcall_empty_staging_ptr_frame proves all non-vacuous frame,
     operand-evaluation and ownership conclusions. Choose marks=[]; remaining
     cursor conclusions are the unchanged-state/input-cursor equalities.

   STORE DISPATCH AND REMAINING RECURSION
   - compile_store_memory_def: word MSTORE; bytes/string runtime copy;
     different annotations use compile_store_memory_typed; equal annotations
     use compile_copy_memory. Staging has its own word/bytes dispatch first.
   - Word child: intcall_store_word_counted; primitive load/store path:
     emit_word_copy_counted. Fixed copy: compile_copy_memory_robust_counted.
     Static-array fast path: intcall_static_array_fast_counted, with its
     stride equality/non-ABI-dynamic premises, NOT arbitrary array execution.
   - Tuple/struct: intcall_tuple_fields_conditional and
     intcall_struct_fields_conditional. These discharge offset execution,
     not recursive child stores. intcall_typed_fields_counted_traversal and
     intcall_struct_fields_counted_traversal likewise retain child callbacks.
   - General dynamic arrays, static slow loops, dynamic-copy integration,
     and all child callback discharge are UNPROVED here. The actual recursion
     is contextScript's mutually recursive compile_store_memory_typed family:
     destination type_rank under acyclic_struct_metadata, with phase offsets;
     field phases use SUM of destination ranks, array phases element rank.
     Source type and capacity are NOT recursion parameters. Recursive child
     statements need arg_type_fits source_child destination_child, coherent
     evaluated types, source robustness, destination capacity/disjointness
     and strict endpoints; these must be transported to each child.

   Classification: all residual entries above are internal helper/runner
   proof obligations. No omitted external premise of the frozen theorem or
   admitted seams has been established. Neither quotation is a proved seam.
*)
