Theory bodyFullIntCallArgsTrace
Ancestors vyperStorageTrace vyperInterpreter vyperState vyperValueOperation

Theorem intcall_after_defaults_storage_trace_frame:
  (!v. storage_trace_frame (f v)) ==>
  storage_trace_frame
    (bind
      (bind (lift_option_type (bind_arguments (get_tenv cx) args (vs ++ dvs))
                "IntCall bind_arguments") (\penv.
       bind (lift_option_type (evaluate_type (get_tenv cx) ret)
                "IntCall eval ret") (\rtv.
       ignore_bind (lock_if_nr cx nr (is_view_mut mut))
         (bind (push_function (src,name) penv cx) (\cxf.
          bind (finally_unless_halt
            (finally
              (try (ignore_bind (eval_stmts cxf ss) (return NoneV)) handle_function)
              (pop_function prev))
            (unlock_if_nr cx nr (is_view_mut mut))) (\rv.
          bind (lift_option_type (safe_cast rtv rv) "IntCall cast ret")
               (\crv. return (Value crv)))))))) f)
Proof
  strip_tac >>
  irule storage_trace_frame_bind_all >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule storage_trace_frame_bind_all >>
  simp_tac bool_ss [storage_trace_frame_lifts] >> gen_tac >>
  irule storage_trace_frame_bind_all >>
  simp_tac bool_ss [storage_trace_frame_lifts] >> gen_tac >>
  irule storage_trace_frame_ignore_bind >>
  simp_tac bool_ss [storage_trace_frame_optional_locks] >>
  irule storage_trace_frame_bind_all >>
  simp_tac bool_ss [storage_trace_frame_function_stack] >> gen_tac >>
  irule storage_trace_frame_bind_all >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp_tac bool_ss [storage_trace_frame_lifts, storage_trace_frame_return]) >>
  irule storage_trace_frame_finally_unless_halt >>
  simp_tac bool_ss [storage_trace_frame_optional_locks] >>
  irule storage_trace_frame_finally >>
  simp_tac bool_ss [storage_trace_frame_function_stack] >>
  irule storage_trace_frame_try >>
  simp_tac bool_ss [storage_trace_frame_function_handler] >>
  irule storage_trace_frame_ignore_bind >>
  simp_tac bool_ss [evaluate_storage_trace_frame, storage_trace_frame_return]
QED
