Theory concretizeStageLookup
Ancestors
  o1PassContract venomInst list

(* First-match lookup commutes with a pointwise name-preserving relation,
   even when names are repeated: the paired heads match simultaneously. *)
Theorem list_rel_lookup_function:
  !xs ys.
    LIST_REL R xs ys /\
    (!f g. R f g ==> g.fn_name = f.fn_name) /\
    lookup_function name xs = SOME f ==>
    ?g. lookup_function name ys = SOME g /\ R f g
Proof
  Induct >> Cases_on `ys` >> simp[] >> rpt strip_tac >>
  gvs[lookup_function_def, FIND_thm] >>
  Cases_on `h.fn_name = name` >> gvs[] >> metis_tac[]
QED

Theorem ctx_pass_stage_lookup:
  ctx_pass_stage rpolicy pass view C C' /\
  lookup_function name C.ctx_functions = SOME fn ==>
  ?fn' observed s out.
    lookup_function name C'.ctx_functions = SOME fn' /\
    fn_pass_step rpolicy pass observed s fn out /\
    out.fpo_function = fn' /\ fn'.fn_name = fn.fn_name /\
    observed.cu_context.ctx_entry = C.ctx_entry /\
    observed.cu_context.ctx_global_reserved = C.ctx_global_reserved /\
    ctx_fn_names observed.cu_context = ctx_fn_names C /\
    view C' fn observed
Proof
  strip_tac >>
  gvs[ctx_pass_stage_def] >>
  drule list_rel_lookup_function >>
  disch_then (qspecl_then [`name`, `fn`] mp_tac) >>
  (impl_tac >- (conj_tac >- (rpt strip_tac >> gvs[fn_pass_step_def]) >> simp[])) >>
  strip_tac >> metis_tac[fn_pass_step_def]
QED
