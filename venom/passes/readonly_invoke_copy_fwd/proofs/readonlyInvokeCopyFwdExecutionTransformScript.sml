(* The actual transformed context uses the same raw midpoint at every call. *)
Theory readonlyInvokeCopyFwdExecutionTransform
Ancestors
  readonlyInvokeCopyFwdExecutionBoundary readonlyInvokeCopyFwdPlan
  readonlyInvokeCopyFwdDefs o1ScheduleDecompHelpers o1PassContract
  passSharedProps venomWf venomInst list option

Theorem ricf_execution_transform_midpoints:
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  EVERY ricf_full_alloca_copies C.ctx_functions /\
  EVERY ricf_no_derived_mutable_sibling C.ctx_functions /\
  EVERY ricf_src_alloca C.ctx_functions ==>
  ?mid_of log_of. !fn. MEM fn C.ctx_functions ==>
    ricf_function_trace (icf_build_ctx fn_meta C.ctx_functions rma fn)
      fn (mid_of fn) /\
    ricf_logged_function_trace (icf_build_ctx fn_meta C.ctx_functions rma fn)
      fn (log_of fn) (mid_of fn) /\
    ricf_function_edit fn (mid_of fn) /\
    LIST_REL ricf_outputs_edit (fn_insts fn) (fn_insts (mid_of fn)) /\
    ricf_transform_function fn_meta C.ctx_functions rma fn =
      (if (mid_of fn).fn_blocks <> fn.fn_blocks
       then clear_nops_function (mid_of fn) else mid_of fn) /\
    lookup_function fn.fn_name (ricf_transform_ctx fn_meta rma C).ctx_functions =
      SOME (if (mid_of fn).fn_blocks <> fn.fn_blocks
            then clear_nops_function (mid_of fn) else mid_of fn) /\
    fn_entry_label
      (if (mid_of fn).fn_blocks <> fn.fn_blocks
       then clear_nops_function (mid_of fn) else mid_of fn) = fn_entry_label fn
Proof
  strip_tac >> drule_all ricf_context_midpoints >>
  disch_then (qspecl_then [`rma`,`fn_meta`] strip_assume_tac) >>
  qexistsl_tac [`mid_of`,`log_of`] >> gen_tac >> strip_tac >>
  qpat_x_assum `!fn. MEM fn _ ==> _` (qspec_then `fn` mp_tac) >>
  simp[] >> strip_tac >> simp[] >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions)` by
    fs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def] >>
  `lookup_function fn.fn_name C.ctx_functions = SOME fn` by
    simp[lookup_function_member_iff] >>
  conj_tac
  >- simp[ricf_transform_ctx_def, lookup_function_map,
          ricf_transform_function_fn_name] >>
  Cases_on `(mid_of fn).fn_blocks <> fn.fn_blocks` >>
  simp[clear_nops_preserves_entry_label] >>
  drule ricf_function_trace_structure >> strip_tac >>
  Cases_on `fn.fn_blocks` >> Cases_on `(mid_of fn).fn_blocks` >>
  gvs[fn_entry_label_def, entry_block_def]
QED
