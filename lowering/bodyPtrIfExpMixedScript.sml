Theory bodyPtrIfExpMixed
Ancestors
  bodyPtrDefs bodyPtrIfExpSource gasExemptCert fragGasPathPtr
  exprLowering compileEnv context vyperInterpreter vyperState

Theorem forced_exempt_raw_source:
  gas_exempt_cert memory tops (ctx,fn)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,finstate) ==>
  !tail. ignore_bind (eval_expr cx e) (return ())
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INR (Error err),ee with gas_obs := tail)
Proof
  strip_tac >> drule gas_exempt_cert_execution >> strip_tac >> gen_tac >>
  irule gas_source_unforce_result >> simp[] >> goal_assum drule >> simp[]
QED

(* Mixed-judgment diagnostic (not a normal arm theorem):
   Specializing expr_sim_ptr and expr_vv_sim_ptr at the same entry is
   possible by drule_all after compile_expr/unwrap_value establish the
   lower_value equation. The outcomes choose independent forced_marks and
   raw_marks. Both raw-certificate branches close by
   ifexp_arm_exempt_transport, choosing raw_marks in the desired outcome.
   A forced normal summary still needs conditional_result source transport
   and the typed post. The crossed forced-certificate/raw-summary branch
   has no counted unwrap suffix at sb. forced_exempt_raw_source gives the
   raw source's exempt equation under forced_marks only, not raw_marks and
   not a raw certificate. gas_exempt_cert_execution also gives a focus
   path, not a gas_path_ptr with the desired normal ghost post. This
   shortcut therefore needs a separate mark/trace compatibility theorem
   or the located counted suffix; neither is established by this audit. *)
