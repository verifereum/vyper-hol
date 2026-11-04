(* Exempt errors retain a concrete origin through actual source sequencing
   and completed target prefixes, including prefixes inside INVOKE. *)
Theory gasExemptCert
Ancestors
  gasExemptOrigin gasSummary gasSummaryCompose fragGasFocus fragGasPathMem
  vyperState vyperInterpreter vyperValue venomState list arithmetic

Inductive gas_exempt_cert:
[~origin:]
  (!memory tops ctx func source es s0 marks err ee t.
     gas_exempt_origin memory tops (ctx, func) source (es, s0)
       marks (err, ee) t ==>
     gas_exempt_cert memory tops (ctx, func) source (es, s0)
       marks (err, ee) (func, t))

[~bind_unit:]
  (!memory tops ctx func (a : evaluation_state -> (unit) evaluation_result)
      k es s0 left v mid t right err ee leaf finish.
     gas_marked_exec (ctx, func) a (es, s0) left (INL v) mid (OK t) /\
     gas_exempt_cert memory tops (ctx, func) (k v)
       (mid with gas_obs := [], t) right (err, ee) (leaf, finish) ==>
     gas_exempt_cert memory tops (ctx, func) (bind a k) (es, s0)
       (left ++ right) (err, ee) (leaf, finish))

[~error_unit:]
  (!memory tops ctx func (a : evaluation_state -> (unit) evaluation_result)
      k es s0 marks err ee leaf finish.
     gas_exempt_cert memory tops (ctx, func)
       (ignore_bind a (return ())) (es, s0)
       marks (err, ee) (leaf, finish) ==>
     gas_exempt_cert memory tops (ctx, func) (bind a k) (es, s0)
       marks (err, ee) (leaf, finish))

[~bind_bool:]
  (!memory tops ctx func (a : evaluation_state -> (bool) evaluation_result)
      k es s0 left v mid t right err ee leaf finish.
     gas_marked_exec (ctx, func) a (es, s0) left (INL v) mid (OK t) /\
     gas_exempt_cert memory tops (ctx, func) (k v)
       (mid with gas_obs := [], t) right (err, ee) (leaf, finish) ==>
     gas_exempt_cert memory tops (ctx, func) (bind a k) (es, s0)
       (left ++ right) (err, ee) (leaf, finish))

[~error_bool:]
  (!memory tops ctx func (a : evaluation_state -> (bool) evaluation_result)
      k es s0 marks err ee leaf finish.
     gas_exempt_cert memory tops (ctx, func)
       (ignore_bind a (return ())) (es, s0)
       marks (err, ee) (leaf, finish) ==>
     gas_exempt_cert memory tops (ctx, func) (bind a k) (es, s0)
       marks (err, ee) (leaf, finish))

[~bind_result:]
  (!memory tops ctx func (a : evaluation_state -> (eval_result) evaluation_result)
      k es s0 left v mid t right err ee leaf finish.
     gas_marked_exec (ctx, func) a (es, s0) left (INL v) mid (OK t) /\
     gas_exempt_cert memory tops (ctx, func) (k v)
       (mid with gas_obs := [], t) right (err, ee) (leaf, finish) ==>
     gas_exempt_cert memory tops (ctx, func) (bind a k) (es, s0)
       (left ++ right) (err, ee) (leaf, finish))

[~error_result:]
  (!memory tops ctx func (a : evaluation_state -> (eval_result) evaluation_result)
      k es s0 marks err ee leaf finish.
     gas_exempt_cert memory tops (ctx, func)
       (ignore_bind a (return ())) (es, s0)
       marks (err, ee) (leaf, finish) ==>
     gas_exempt_cert memory tops (ctx, func) (bind a k) (es, s0)
       marks (err, ee) (leaf, finish))

[~bind_value:]
  (!memory tops ctx func (a : evaluation_state -> (value) evaluation_result)
      k es s0 left v mid t right err ee leaf finish.
     gas_marked_exec (ctx, func) a (es, s0) left (INL v) mid (OK t) /\
     gas_exempt_cert memory tops (ctx, func) (k v)
       (mid with gas_obs := [], t) right (err, ee) (leaf, finish) ==>
     gas_exempt_cert memory tops (ctx, func) (bind a k) (es, s0)
       (left ++ right) (err, ee) (leaf, finish))

[~error_value:]
  (!memory tops ctx func (a : evaluation_state -> (value) evaluation_result)
      k es s0 marks err ee leaf finish.
     gas_exempt_cert memory tops (ctx, func)
       (ignore_bind a (return ())) (es, s0)
       marks (err, ee) (leaf, finish) ==>
     gas_exempt_cert memory tops (ctx, func) (bind a k) (es, s0)
       marks (err, ee) (leaf, finish))

[~bind_place:]
  (!memory tops ctx func (a : evaluation_state -> (place) evaluation_result)
      k es s0 left v mid t right err ee leaf finish.
     gas_marked_exec (ctx, func) a (es, s0) left (INL v) mid (OK t) /\
     gas_exempt_cert memory tops (ctx, func) (k v)
       (mid with gas_obs := [], t) right (err, ee) (leaf, finish) ==>
     gas_exempt_cert memory tops (ctx, func) (bind a k) (es, s0)
       (left ++ right) (err, ee) (leaf, finish))

[~error_place:]
  (!memory tops ctx func (a : evaluation_state -> (place) evaluation_result)
      k es s0 marks err ee leaf finish.
     gas_exempt_cert memory tops (ctx, func)
       (ignore_bind a (return ())) (es, s0)
       marks (err, ee) (leaf, finish) ==>
     gas_exempt_cert memory tops (ctx, func) (bind a k) (es, s0)
       marks (err, ee) (leaf, finish))

[~bind_values:]
  (!memory tops ctx func (a : evaluation_state -> (value list) evaluation_result)
      k es s0 left v mid t right err ee leaf finish.
     gas_marked_exec (ctx, func) a (es, s0) left (INL v) mid (OK t) /\
     gas_exempt_cert memory tops (ctx, func) (k v)
       (mid with gas_obs := [], t) right (err, ee) (leaf, finish) ==>
     gas_exempt_cert memory tops (ctx, func) (bind a k) (es, s0)
       (left ++ right) (err, ee) (leaf, finish))

[~error_values:]
  (!memory tops ctx func (a : evaluation_state -> (value list) evaluation_result)
      k es s0 marks err ee leaf finish.
     gas_exempt_cert memory tops (ctx, func)
       (ignore_bind a (return ())) (es, s0)
       marks (err, ee) (leaf, finish) ==>
     gas_exempt_cert memory tops (ctx, func) (bind a k) (es, s0)
       marks (err, ee) (leaf, finish))

[~bind_results:]
  (!memory tops ctx func (a : evaluation_state -> (eval_result list) evaluation_result)
      k es s0 left v mid t right err ee leaf finish.
     gas_marked_exec (ctx, func) a (es, s0) left (INL v) mid (OK t) /\
     gas_exempt_cert memory tops (ctx, func) (k v)
       (mid with gas_obs := [], t) right (err, ee) (leaf, finish) ==>
     gas_exempt_cert memory tops (ctx, func) (bind a k) (es, s0)
       (left ++ right) (err, ee) (leaf, finish))

[~error_results:]
  (!memory tops ctx func (a : evaluation_state -> (eval_result list) evaluation_result)
      k es s0 marks err ee leaf finish.
     gas_exempt_cert memory tops (ctx, func)
       (ignore_bind a (return ())) (es, s0)
       marks (err, ee) (leaf, finish) ==>
     gas_exempt_cert memory tops (ctx, func) (bind a k) (es, s0)
       marks (err, ee) (leaf, finish))

[~cleanup:]
  (!memory tops ctx func source cleanup es s0 marks err mid ee leaf finish.
     gas_exempt_cert memory tops (ctx, func) source (es, s0)
       marks (err, mid) (leaf, finish) /\
     (!tail. cleanup ((mid with gas_obs := []) with gas_obs := tail) =
       (INL (), ee with gas_obs := tail)) ==>
     gas_exempt_cert memory tops (ctx, func) (finally source cleanup)
       (es, s0) marks (err, ee) (leaf, finish))

[~handler:]
  (!memory tops ctx func source handler es s0 marks err mid ee leaf finish.
     gas_exempt_cert memory tops (ctx, func) source (es, s0)
       marks (err, mid) (leaf, finish) /\
     (!tail. handler (Error err)
       ((mid with gas_obs := []) with gas_obs := tail) =
       (INR (Error err), ee with gas_obs := tail)) ==>
     gas_exempt_cert memory tops (ctx, func) (try source handler)
       (es, s0) marks (err, ee) (leaf, finish))

[~invoke:]
  (!memory tops ctx func s callee entered source es marks err ee leaf finish.
     gas_invoke_entry (ctx, func) s callee entered /\
     gas_exempt_cert memory tops (ctx, callee) source (es, entered)
       marks (err, ee) (leaf, finish) ==>
     gas_exempt_cert memory tops (ctx, func) source (es, s)
       marks (err, ee) (leaf, finish))
End

(* The endpoint of the concrete child remains separate from the source
   endpoint after enclosing cleanup. Entering a call is not completing it. *)
Theorem gas_exempt_cert_execution:
  !memory tops ctx func source es s0 marks err ee leaf finish.
    gas_exempt_cert memory tops (ctx, func) source (es, s0)
      marks (err, ee) (leaf, finish) ==>
    (!tail. source
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INR (Error err), ee with gas_obs := tail)) /\
    gas_focus_path (ctx, func) s0 (LENGTH marks) (leaf, finish) /\
    unspecified_behaviour_exempt tops err
Proof
  (* New frozen theorem, awaiting the independent prover. *)
  cheat
QED

