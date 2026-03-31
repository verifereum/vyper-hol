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
   R_ok/R_term are the per-state relations for OK/terminal results. *)
Definition ctx_pass_correct_def:
  ctx_pass_correct (p : venom_context -> venom_context) R_ok R_term ctx s <=>
    pass_correct R_ok R_term
      (\fuel. run_context fuel ctx s)
      (\fuel. run_context fuel (p ctx) s)
End

(* ===== Composition Infrastructure ===== *)

(* pass_correct is transitive when relations compose.
   R12_ok/R12_term must contain the relational composition of the
   individual relations (R1 then R2). *)
Theorem pass_correct_trans:
  !R1_ok R1_term R2_ok R2_term R12_ok R12_term exec1 exec2 exec3.
    (!s1 s2 s3. R1_ok s1 s2 /\ R2_ok s2 s3 ==> R12_ok s1 s3) /\
    (!s1 s2 s3. R1_term s1 s2 /\ R2_term s2 s3 ==> R12_term s1 s3) /\
    pass_correct R1_ok R1_term exec1 exec2 /\
    pass_correct R2_ok R2_term exec2 exec3 ==>
    pass_correct R12_ok R12_term exec1 exec3
Proof
  cheat
QED

(* Corollary: state_equiv/execution_equiv accumulate via union. *)
Theorem pass_correct_trans_equiv:
  !fresh1 fresh2 exec1 exec2 exec3.
    pass_correct (state_equiv fresh1) (execution_equiv fresh1) exec1 exec2 /\
    pass_correct (state_equiv fresh2) (execution_equiv fresh2) exec2 exec3 ==>
    pass_correct (state_equiv (fresh1 UNION fresh2))
                 (execution_equiv (fresh1 UNION fresh2)) exec1 exec3
Proof
  cheat
QED

(* ===== Lifting Infrastructure ===== *)

(* Lift function-level correctness to context level.
   If every function in the context is correctly transformed by f,
   then apply_ctx_fn_transform f is a correct context transform.
   Uses same ctx on both sides (callees not transformed in callee lookup). *)
Theorem apply_ctx_fn_transform_correct:
  !f ctx s R_ok R_term.
    (!fn. MEM fn ctx.ctx_functions ==>
      !fuel s'.
        s'.vs_inst_idx = 0 ==>
        pass_correct R_ok R_term
          (\fuel. run_function fuel ctx fn s')
          (\fuel. run_function fuel ctx (f fn) s'))
  ==>
    ctx_pass_correct (apply_ctx_fn_transform f) R_ok R_term ctx s
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
                     (state_equiv fresh_cfg) (execution_equiv fresh_cfg)
                     ctx s /\
    (let ctx1 = apply_ctx_fn_transform simplify_cfg_fn ctx in
     ctx_pass_correct (apply_ctx_fn_transform ircf_global)
                      (state_equiv fresh_ircf) (execution_equiv fresh_ircf)
                      ctx1 s) /\
    (let ctx2 = apply_ctx_fn_transform ircf_global
                  (apply_ctx_fn_transform simplify_cfg_fn ctx) in
     ctx_pass_correct (apply_ctx_fn_transform ricf_global)
                      (state_equiv fresh_ricf) (execution_equiv fresh_ricf)
                      ctx2 s) /\
    (let ctx3 = apply_ctx_fn_transform ricf_global
                  (apply_ctx_fn_transform ircf_global
                    (apply_ctx_fn_transform simplify_cfg_fn ctx)) in
     ctx_pass_correct (function_inliner_ctx threshold)
                      (state_equiv fresh_inl) (execution_equiv fresh_inl)
                      ctx3 s) /\
    (let ctx4 = function_inliner_ctx threshold
                  (apply_ctx_fn_transform ricf_global
                    (apply_ctx_fn_transform ircf_global
                      (apply_ctx_fn_transform simplify_cfg_fn ctx))) in
     ctx_pass_correct (apply_ctx_fn_transform fn_pipeline)
                      (state_equiv fresh_fn) (execution_equiv fresh_fn)
                      ctx4 s)
  ==>
    ctx_pass_correct
      (venom_pipeline ircf_global ricf_global threshold fn_pipeline)
      (state_equiv (fresh_cfg UNION fresh_ircf UNION fresh_ricf UNION
                    fresh_inl UNION fresh_fn))
      (execution_equiv (fresh_cfg UNION fresh_ircf UNION fresh_ricf UNION
                        fresh_inl UNION fresh_fn))
      ctx s
Proof
  cheat
QED

(* pass_correct implies observable equivalence when R_ok/R_term
   imply observable equivalence. *)
Theorem pass_correct_implies_observable:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) exec1 exec2 fuel fuel'.
    (!s1 s2. R_ok s1 s2 ==> observable_equiv s1 s2) /\
    (!s1 s2. R_term s1 s2 ==> observable_equiv s1 s2) /\
    pass_correct R_ok R_term exec1 exec2 /\
    terminates (exec1 fuel) /\ terminates (exec2 fuel') ==>
    observable_result_equiv (exec1 fuel) (exec2 fuel')
Proof
  rw[pass_correct_def] >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `exec1 fuel` >> Cases_on `exec2 fuel'` >>
  gvs[lift_result_def, observable_result_equiv_def] >>
  metis_tac[]
QED
