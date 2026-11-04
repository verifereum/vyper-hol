(* Bounded reverse-provenance diagnostics, not stage counterexamples. *)
Theory concretizeAnalysisReverseProbe
Ancestors
  ptrDiscipline pointerConfinedDefs pointerClosure venomWf venomInst
  venomState venomExecSemantics concretizeMemLocDefs finite_map pred_set list While sum
Libs wordsLib

Definition reverse_probe_phi_def:
  reverse_probe_phi = mk_inst 3 PHI
    [Label "left"; Var "a"; Label "right"; Var "p"] ["q"]
End

Definition reverse_probe_fn_def:
  reverse_probe_fn = mk_raw_function "reverse_probe"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 1 ALLOCA [Lit 32w] ["a"];
       mk_inst 2 PARAM [Lit 0w] ["p"];
       reverse_probe_phi;
       mk_inst 4 MSTORE [Var "q"; Lit 7w] [];
       mk_inst 5 STOP [] []] |>]
End

Theorem reverse_probe_selected_provenance:
  phi_prov (SOME "right") (FEMPTY |+ ("a",(64,32))) reverse_probe_phi = NONE /\
  phi_prov (SOME "left") (FEMPTY |+ ("a",(64,32))) reverse_probe_phi = SOME (64,32) /\
  phi_prov (SOME "right")
    (FEMPTY |+ ("a",(64,32)) |+ ("p",(96,32))) reverse_probe_phi = SOME (96,32)
Proof
  EVAL_TAC
QED

Theorem reverse_probe_alloca_closure:
  pointer_derived_vars reverse_probe_fn {"a"} = {"a"; "q"} /\
  pointer_derived_vars reverse_probe_fn {"p"} = {"p"; "q"}
Proof
  simp[pointer_derived_vars_def, SET_TO_LIST_SING] >>
  simp[pointer_use_vars_def] >>
  ntac 3 (once_rewrite_tac[OWHILE_THM] >>
    simp[ISL, OUTL, pointer_use_step_step_def, pointer_use_step_def,
         reverse_probe_fn_def, reverse_probe_phi_def, mk_raw_function_def,
         mk_inst_def, is_pointer_preserving_op_def]) >>
  simp[EXTENSION] >> metis_tac[]
QED

Theorem reverse_probe_nonpointer_phi_rejected:
  ~phi_pv_all_var reverse_probe_fn {"a"}
Proof
  simp[phi_pv_all_var_def, reverse_probe_alloca_closure,
       reverse_probe_fn_def, reverse_probe_phi_def, mk_raw_function_def,
       mk_inst_def] >>
  qexists_tac `reverse_probe_phi` >> EVAL_TAC >>
  conj_tac >- (qexists_tac `"a"` >> EVAL_TAC) >>
  disj1_tac >> qexists_tac `"p"` >> EVAL_TAC
QED

Theorem reverse_probe_mixed_write_excluded:
  "q" IN pointer_derived_vars reverse_probe_fn {"a"} /\
  "q" IN pointer_derived_vars reverse_probe_fn {"p"} /\
  mem_write_ops (mk_inst 4 MSTORE [Var "q"; Lit 7w] []) =
    SOME <| iao_ofst := Var "q"; iao_size := SOME (Lit 32w);
            iao_max_size := SOME (Lit 32w) |>
Proof
  simp[reverse_probe_alloca_closure] >> EVAL_TAC
QED

(* Existing diamond has two local ALLOCA sources; reuse it instead of
   introducing a second same-shaped CFG fixture. *)

Theorem reverse_probe_pointer_param_may_be_absent:
  out_prov [NONE] FEMPTY (mk_inst 2 PARAM [Lit 0w] ["p"])
    (init_venom_state "entry") = NONE
Proof
  EVAL_TAC
QED

Theorem reverse_probe_cached_repeat:
  exec_alloca (mk_inst 1 ALLOCA [Lit 32w] ["a"])
    ((init_venom_state "entry") with vs_allocas := FEMPTY |+ (1,(64,32))) 32w =
  OK (update_var "a" 64w
    ((init_venom_state "entry") with vs_allocas := FEMPTY |+ (1,(64,32)))) /\
  get_alloca_size reverse_probe_fn (Allocation 1) = 32 /\
  inst_alloca_size (mk_inst 1 ALLOCA [Lit 32w] ["a"]) = SOME 32
Proof
  EVAL_TAC
QED

Definition reverse_probe_prepop_def:
  reverse_probe_prepop = mk_raw_function "prepop"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 10 MSTORE [Var "a"; Lit 7w] [];
       mk_inst 11 ALLOCA [Lit 32w] ["a"];
       mk_inst 12 STOP [] []] |>]
End

Theorem reverse_probe_prepop_unavailable:
  ~def_on_all_paths reverse_probe_prepop
    (HD reverse_probe_prepop.fn_blocks)
    (SOME (mk_inst 10 MSTORE [Var "a"; Lit 7w] [])) "a"
Proof
  simp[def_on_all_paths_def] >> qexists_tac `["entry"]` >>
  EVAL_TAC >> simp[] >>
  rpt gen_tac >> Cases_on `i < 3` >> simp[] >>
  `i = 0 \/ i = 1 \/ i = 2` by decide_tac >> gvs[] >>
  gen_tac >> Cases_on `j < 3` >> simp[] >>
  `j = 0 \/ j = 1 \/ j = 2` by decide_tac >> gvs[]
QED

Theorem reverse_probe_pointer_phi_admitted:
  phi_pv_all_var reverse_probe_fn {"a"; "p"}
Proof
  `{"a"; "p"} SUBSET pointer_derived_vars reverse_probe_fn {"a"; "p"}` by
    (irule pointer_derived_vars_roots >> simp[]) >>
  gvs[SUBSET_DEF] >>
  simp[phi_pv_all_var_def, reverse_probe_fn_def, reverse_probe_phi_def,
       mk_raw_function_def, mk_inst_def] >> rpt strip_tac >>
  gvs[reverse_probe_fn_def, reverse_probe_phi_def, mk_raw_function_def, mk_inst_def]
QED

(* Proposed interfaces -- NOT proved by these finite diagnostics.

   reverse_write_lookup:
     origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
     o1_run_state_ok vs0 /\ o1_ctx_shape ctx /\ EVERY wf_function ctx.ctx_functions /\
     EVERY (fn_ptr_ok P) ctx.ctx_functions /\
     EVERY ssa_form ctx.ctx_functions /\
     EVERY fn_defs_reach_uses ctx.ctx_functions /\
     EVERY all_reachable ctx.ctx_functions /\ ~ctx_has_dalloca ctx /\
     ctx_inst_ids_distinct ctx /\
     mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
     find_base_allocas_opt
       (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
       (inst_write_op inst) = [Allocation a] /\
     step_inst fuel ctx inst s = OK s'
     ==> ?site. FLOOKUP G v = SOME site

   current_cache_size:
     origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
     o1_run_state_ok vs0 /\ o1_ctx_shape ctx /\ EVERY wf_function ctx.ctx_functions /\
     ctx_inst_ids_distinct ctx /\ ~ctx_has_dalloca ctx /\
     FLOOKUP s.vs_allocas a = SOME (b,sz)
     ==> get_alloca_size fn (Allocation a) = sz

   Both hypotheses are drawn from the task's reachability/static shape
   interface (origin_frame_reachable is the existing instrumentation), not
   new assumed reverse soundness.  They are proposals requiring review,
   not claims that these hypotheses suffice.  In particular the second
   uses o1_run_state_ok vs0: o1_initial_state_ok requires
   vs0.vs_allocas = FEMPTY (unitTransformDefsScript.sml:98-102).
   setup_callee_def resets the callee cache; merge_callee_state_def keeps
   the caller cache. An arbitrary prepopulated initial cache is not sufficient.

   Production-size bridge is SEPARATE: context_mem_livesets uses
   if context_alloca_size fn (imported_mems_used ctx fn) a = 0 then NONE
   else SOME (context_alloca_size fn (imported_mems_used ctx fn) a).
   A local site requires exclusion of an imported same-id entry (context
   distinct ids plus actual metadata ownership), before get_alloca_size
   can replace context_alloca_size.  Zero-size caches have no protected
   byte and need not give SOME 0 in that production lookup.

   Induction dependency audit:
   * Ordinary uses: fn_defs_reach_uses_ordinary and
     def_on_all_paths_first_visit in concretizeAnalysisPathDefinitions
     supply static earlier definitions, NOT chronological execution.
     frame_history_current_completed / saved_completed in
     frameHistoryCompleted supply completed blocks.  Their composition
     with current-prefix execution is still needed.
   * ALLOCA: out_prov_def reads the resulting cache; exec_alloca_def
     creates (vs_alloca_next,w2n literal) once and reuses it thereafter.
     ssa and distinct instruction ids identify the same literal on repeat.
   * ASSIGN/ADD/SUB: first_prov_def; affine_pointer_ops excludes two
     full-root pointers, while closure must propagate non-alloca root
     membership to exclude an incoming source. No offset soundness needed.
   * PHI: phi_prov_def resolves a predecessor using OLD G0 (parallel).
     phi_pv_all_var is for full roots. If selected value is outside A,
     full-root membership must force N membership, then closure puts its
     output in N, contradicting allocation-exclusive write membership.
     Needed static closure decomposition A UNION N = full closure and
     chronological selected-definition induction remain unproved.
   * PARAM: pointer root is not provenance (checked NONE example).
     PARAM-only roots lie in N and cannot feed an exclusive write.
   * INVOKE: step_prov clears outputs; ptr_use_ok must exclude a source
     allocation-derived return output masquerading as an ordinary derived
     definition. Saved caller G/cache restoration, not callee cache, is
     required. Existing origin/cache identity facts are only one-way.
   * Prepopulated values: definite assignment is code/path based, not a
     lookup_var check. The checked late-definition fixture is rejected at
     the store even if a runtime map happens to contain "a".

   Finite tests are not universal invariants. Existing two-ALLOCA fixture
   ptr_sem_diamond in concretizePtrSemanticProbe already checks its
   full-root PHI restriction and both static bases; the selected local
   lookup here checks the same phi_prov operation without cloning its CFG.
   Reads seed demand BEFORE same-step writes. Suspended caller demand
   needs saved activation/cache identity. No future-demand definition or
   stage proof is introduced here.
*)
