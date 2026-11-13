(* Cleanup interface probe.  The callee exit certificate is indexed by the
   pre-unlock source state; physical restoration must use its existential
   post-unlock state instead.  A halt restores scopes but skips unlock. *)
Theory bodyIntCallNRCleanupProbe
Ancestors
  bodyIntCallNRSource bodyIntCallSeamDefs
  vyperInterpreter vyperState

Theorem intcall_cleanup_terminal:
  f es = (res,ee) /\
  unlock_if_nr cx nr view ee = (INL (),ue) ==>
  finally_unless_halt
    (finally (f : evaluation_state -> value evaluation_result)
       (pop_function prev)) (unlock_if_nr cx nr view) es =
  (res, if res = INR HaltException then ee with scopes := prev
        else ue with scopes := prev)
Proof
  strip_tac >> Cases_on `res`
  >- simp[finally_def, finally_unless_halt_def, pop_function_def,
          set_scopes_def, ignore_bind_def, bind_def, return_def,
          intcall_unlock_scopes, Excl "unlock_if_nr_def"] >>
  rename1 `f es = (INR ex,ee)` >> Cases_on `ex` >>
  simp[finally_def, finally_unless_halt_def, pop_function_def,
       set_scopes_def, ignore_bind_def, bind_def, return_def, raise_def,
       intcall_unlock_scopes, Excl "unlock_if_nr_def"]
QED

(* Candidate replacement for invoke_cleanup_outcome (audit, not a theorem):

   Inputs: gas_invoke_entry (ctx,func) t callee entered;
   gas_admissible (intcall_rest cx name mut nr ss prev rtv)
     expr_vv_res_ok es;
   gas_outcome F tops (ctx,callee) (intcall_callee_src cx name mut nr ss)
     (es,entered) (\res ee r. F)
     (intcall_callee_exit func ce cx mut nr rtv rc rb n m t).

   Physical continuation, universally over marks, v, ee, ir, cs, ue:
   gas_marked_exec for that callee source ending (INL v,ee,IntRet ir cs),
   its exit certificate at (ee with gas_obs := []),
   unlock_if_nr cx nr (is_view_mut mut) (ee with gas_obs := []) =
     (INL (),ue), and value_has_type rtv v imply
     ?k out. gas_path ctx func t (LENGTH marks + k) (OK out) /\
       Q (INL (Value v)) (ue with scopes := prev) out.
   Conclusion: gas_outcome for intcall_rest at (es,t), normal post Q,
   exceptional post expr_exit.  Instantiate Q with vv_post, final compiler
   position, nonhalting, frontier monotonicity, intcall_expr_res and the
   return-buffer allocation/size/bound witness (as in the frozen consumer).

   Source cases, for each gas-observation tail separately:
   - lock failure: rest equals the failed lock, with NO pop and NO unlock;
   - successful lock and normal body result: pop, unlock, then safe_cast;
   - successful lock and ordinary exception: pop, unlock, propagate;
   - successful lock and HaltException: pop, NO unlock, propagate halt.
   handle_function turns ReturnException into a normal result, preserves
   Error/AssertException/HaltException, rejects other escapes as TypeError.
   The normal exit certificate already supplies ue; do not unlock cs again.

   Decoded physical inputs, independent of argument-history compilation:
   st3 and its position at t; decoded INVOKE label/operands and evaluated
   argv; emission of void INVOKE or multi INVOKE plus store_multi_results;
   fn_has_code and fresh output bounds; return-buffer ALLOCA at sa.next_id,
   address, size and range; return-count/type metadata; incoming caller
   stmt_state_rel, wb_frame, protected regions and local-region transport.
   These are projections of intcall_entry plus compiler monotonicity.

   Legal physical boundaries: return_successor_frame, invoke_return_frame,
   multi_outputs_return_state, compiled_return_buffer_geometry,
   stack_buffer_run_owned, intcall_store_results_resources,
   intcall_store_run_counted_resources, intcall_return_buffer_prepare and
   intcall_bound_return_buffer.  Use the existential post-unlock source
   state in return_successor_frame's state_rel premise.  Rebuild the held
   stack/zero dispatch from these inputs, never from old compile_multi_vvs.

   Resource endpoint: intcall_expr_res_metadata_frame is proved/exported;
   it additionally needs expr_sim_inv at ue with caller scopes, immutable
   metadata preservation, reserved/old variables, protected memory,
   allocas_above, frontier monotonicity and reverse local-region transport.
   Existing source dynamic/invariant wrappers are F-only and need new nr
   boundaries; state_rel alone does not supply these facts.  No missing
   external premise was identified by this audit.
*)
