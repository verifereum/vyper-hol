Theory bodyIntCallExemptReturn
Ancestors
  gasExemptCert fragGasFocus vyperState vyperInterpreter
Libs
  monadsyntax

(* Keep the callee's concrete exempt origin through arbitrary value-returning
   bodies, scope cleanup, and the caller's result continuation. *)
Theorem gas_exempt_cert_value_cleanup:
  !memory tops ctx callee f es entered marks err ee leaf finish func s prev cx view k.
  gas_exempt_cert memory tops (ctx,callee)
    (ignore_bind (f : evaluation_state -> value evaluation_result) (return ()))
    (es,entered) marks (err,ee) (leaf,finish) /\
  gas_invoke_entry (ctx,func) s callee entered ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind
      (bind (finally f (do pop_function prev; unlock_if_nr cx F view od)) k)
      (return ()))
    (es,s) marks (err,ee with scopes := prev) (leaf,finish)
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_value >>
  rewrite_tac[GSYM ignore_bind_def, ignore_bind_finally_unit] >>
  irule gas_exempt_cert_cleanup >> qexists_tac `ee` >> reverse conj_tac
  >- (irule gas_exempt_cert_invoke >> goal_assum (drule_at Any) >> simp[]) >>
  simp[pop_function_def, unlock_if_nr_def, set_scopes_def,
       ignore_bind_def, bind_def, return_def]
QED
