(*
 * Venom Pipeline Correctness
 *
 * General composition theorem: sequential application of
 * semantics-preserving context transforms preserves semantics.
 * Instantiated for each optimization level.
 *
 * TOP-LEVEL:
 *   pass_correct_trans             -- binary transitivity
 *   compose_passes_correct         -- FOLDL of any correct pass list
 *   apply_ctx_fn_transform_correct -- lift function-level to context-level
 *   venom_pipeline_correct         -- parameterized pipeline instantiation
 *)

Theory venomPipelineCorrect
Ancestors
  venomPipeline
  passSimulationDefs
  stateEquiv stateEquivProps
  allocaSafety
  venomExecSemantics

(* ===== Context-Level Pass Correctness ===== *)

(* A context-level pass: transforms a context, preserves semantics.
   fresh = set of vars that may differ between original and transformed. *)
Definition ctx_pass_correct_def:
  ctx_pass_correct (p : venom_context -> venom_context) fresh ctx s <=>
    pass_correct fresh
      (\fuel. run_context fuel ctx s)
      (\fuel. run_context fuel (p ctx) s)
End

(* ===== Composition Infrastructure ===== *)

(* pass_correct is transitive (fresh vars accumulate via union).
   Proof sketch: terminates iff chains by transitivity of iff;
   result_equiv chains via result_equiv_trans + subset monotonicity. *)
Theorem pass_correct_trans:
  !fresh1 fresh2 exec1 exec2 exec3.
    pass_correct fresh1 exec1 exec2 /\
    pass_correct fresh2 exec2 exec3 ==>
    pass_correct (fresh1 UNION fresh2) exec1 exec3
Proof
  cheat
QED

(* Sequential composition of context transforms.
   Each pass is correct when applied to the context produced
   by all preceding passes (FOLDL-indexed precondition). *)
Theorem compose_passes_correct:
  !passes fresh_sets ctx s.
    LENGTH fresh_sets = LENGTH passes /\
    (!i. i < LENGTH passes ==>
      let ctx_i = FOLDL (\c p. p c) ctx (TAKE i passes) in
      ctx_pass_correct (EL i passes) (EL i fresh_sets) ctx_i s)
  ==>
    pass_correct (BIGUNION (set fresh_sets))
      (\fuel. run_context fuel ctx s)
      (\fuel. run_context fuel (FOLDL (\c p. p c) ctx passes) s)
Proof
  cheat
QED

(* ===== Lifting Infrastructure ===== *)

(* Lift function-level correctness to context level.
   If every function in the context is correctly transformed by f,
   then apply_ctx_fn_transform f is a correct context transform. *)
Theorem apply_ctx_fn_transform_correct:
  !f ctx s fresh.
    (!fn. MEM fn ctx.ctx_functions ==>
      !fuel s'.
        s'.vs_inst_idx = 0 ==>
        pass_correct fresh
          (\fuel. run_function fuel ctx fn s')
          (\fuel. run_function fuel ctx (f fn) s'))
  ==>
    ctx_pass_correct (apply_ctx_fn_transform f) fresh ctx s
Proof
  cheat
QED

(* Lift lift_result to pass_correct *)
Theorem lift_result_to_pass_correct:
  !vars fn fn' ctx s.
    (!fuel.
      s.vs_inst_idx = 0 ==>
      lift_result (state_equiv vars) (execution_equiv vars)
        (run_function fuel ctx fn s)
        (run_function fuel ctx fn' s))
  ==>
    pass_correct vars
      (\fuel. run_function fuel ctx fn s)
      (\fuel. run_function fuel ctx fn' s)
Proof
  cheat
QED

(* ===== Pipeline Correctness ===== *)

(* The full pipeline preserves semantics, parameterized by the
   per-function pass sequence. Each phase's correctness is a
   precondition; the theorem composes them. *)
Theorem venom_pipeline_correct:
  !ircf_global ricf_global threshold fn_pipeline ctx s
    fresh_cfg fresh_ircf fresh_ricf fresh_inl fresh_fn.
    (* Alloca safety: pointers don't escape to observable channels.
     * Precondition on initial context; consumed by passes that
     * change alloca layout (remove_unused, function_inliner). *)
    EVERY alloca_safe_fn ctx.ctx_functions /\
    ctx_pass_correct (apply_ctx_fn_transform simplify_cfg_fn)
                     fresh_cfg ctx s /\
    (let ctx1 = apply_ctx_fn_transform simplify_cfg_fn ctx in
     ctx_pass_correct (apply_ctx_fn_transform ircf_global)
                      fresh_ircf ctx1 s) /\
    (let ctx2 = apply_ctx_fn_transform ircf_global
                  (apply_ctx_fn_transform simplify_cfg_fn ctx) in
     ctx_pass_correct (apply_ctx_fn_transform ricf_global)
                      fresh_ricf ctx2 s) /\
    (let ctx3 = apply_ctx_fn_transform ricf_global
                  (apply_ctx_fn_transform ircf_global
                    (apply_ctx_fn_transform simplify_cfg_fn ctx)) in
     ctx_pass_correct (function_inliner_ctx threshold)
                      fresh_inl ctx3 s) /\
    (let ctx4 = function_inliner_ctx threshold
                  (apply_ctx_fn_transform ricf_global
                    (apply_ctx_fn_transform ircf_global
                      (apply_ctx_fn_transform simplify_cfg_fn ctx))) in
     ctx_pass_correct (apply_ctx_fn_transform fn_pipeline)
                      fresh_fn ctx4 s)
  ==>
    ctx_pass_correct
      (venom_pipeline ircf_global ricf_global threshold fn_pipeline)
      (fresh_cfg UNION fresh_ircf UNION fresh_ricf UNION
       fresh_inl UNION fresh_fn)
      ctx s
Proof
  cheat
QED

(* pass_correct implies observable equivalence of terminal results *)
Theorem pass_correct_implies_observable:
  !fresh exec1 exec2 fuel fuel'.
    pass_correct fresh exec1 exec2 /\
    terminates (exec1 fuel) /\ terminates (exec2 fuel') ==>
    observable_result_equiv (exec1 fuel) (exec2 fuel')
Proof
  rw[pass_correct_def] >>
  metis_tac[result_equiv_implies_observable_result]
QED
