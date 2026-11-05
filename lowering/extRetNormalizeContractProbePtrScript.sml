Theory extRetNormalizeContractProbePtr
Ancestors
  extRetNormalizeInputsPtr extRetNormalizeWindowPtr exprLowering
  stmtLowering vyperTypeSystem compileEnv finite_map bodyMemoryDefs exprLoweringProps

(* Integration audit (not a theorem asserting a new source invariant).
   Producer: bodyPtrDefs.expr_sim_ptr_def:234-241 gives expr_post at
   expr_type e, ptr_val_ok at expr_type e, conditional ptr_buf_ok at the
   lowered type, ghost_inv and ghost_kept. expr_post provides state_rel,
   expr_val_rel/expr_val_at at the annotation and old-state framing.
   Consumer: stmtLowering Return:1055-1072 selects lowered_value_type e as
   source type of compile_store_memory_typed. The S1 normalization boundary
   stmtSimReturnWiden.compile_return_normalize_frag additionally requires
   source val_in_memory at that type, a strict source endpoint, and concrete
   allocation-or-local placement of its full declared extent.
   Existing return_lowered_runtime_layout proves runtime typing/layout,
   not a memory representation conversion. return_equal_lowered_robust
   already discharges robust representation when the types are equal.
   The probe below checks that the unequal internal-call case cannot be
   dismissed by a blanket claim that nested bound widening keeps strides.
   It does not assert the full expression simulation premises for a run.
*)
Theorem normalize_nested_call_layout_probe:
  !ce.
    let sty = ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 1)) (Fixed 2) in
    let aty = ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 2)) (Fixed 2) in
    let e = Call aty (IntCall (NONE,"f")) [] NONE in
    ce.ce_func_return_type "f" = sty ==>
      lowered_value_type ce e = sty /\ expr_type e = aty /\
      type_widens_to FEMPTY sty aty /\
      ~is_word_type aty /\
      ~(is_bytestring_type aty /\ is_bytestring_type sty) /\
      sty <> aty /\
      type_memory_bytes ce sty = 128 /\ type_memory_bytes ce aty = 192
Proof
  simp[lowered_value_type_def, nsid_to_string_def,
       type_widens_to_def, arg_type_fits_def, well_formed_type_def,
       is_word_type_def, is_bytestring_type_def, type_memory_bytes_def] >> EVAL_TAC >> simp[wordsTheory.dimword_def] >> EVAL_TAC >> simp[]
QED

(* The type system permits this call annotation; these are precisely the
   empty-argument signature premises, not expression execution premises. *)
Theorem normalize_nested_call_typing_probe:
  !env sig.
    let sty = ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 1)) (Fixed 2) in
    let aty = ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 2)) (Fixed 2) in
    env.type_defs = FEMPTY /\
    FLOOKUP env.fn_sigs (NONE,"f") = SOME sig /\
    sig.ret_ty = sty /\ sig.param_types = [] /\ sig.num_defaults = 0 ==>
    well_typed_expr env (Call aty (IntCall (NONE,"f")) [] NONE)
Proof
  rpt gen_tac >> pure_rewrite_tac [LET_THM] >> BETA_TAC >> strip_tac >>
  simp[well_typed_expr_def, type_widens_to_def, arg_type_fits_def,
       well_formed_type_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def] >> EVAL_TAC >> simp[]
QED

(* Local placement is sufficient for the strict endpoint: state_rel gives
   the local frontier bound, and alloca_room bounds that frontier. *)
Theorem normalize_local_region_end_bound:
  stmt_state_rel ctx func ce cx es s /\
  local_region ce es.scopes s name b sz ==>
  b + sz < dimword (:256)
Proof
  rpt strip_tac >> drule_all body_local_region_frontier >>
  gvs[stmt_state_rel_def, alloca_room_def] >> decide_tac
QED

(* Audit conclusion: allocated and local source-placement alternatives both
   imply strict endpoints (allocated_footprint_window_bound and the theorem
   above). ptr_buf_ok alone supplies neither alternative. For unequal
   internal-call annotations, the checked probes show different nested
   strides are permitted by well_typed_expr. Thus return_lowered_runtime_layout
   cannot substitute for a robust val_in_memory at the lowered source type.
   The missing consumer implication is specifically:
     expr_post /\ ghost_inv /\ ptr_val_ok at expr_type e /\ ptr_buf_ok
       ==> robust val_in_memory at lowered_value_type ce e,
           plus allocation-or-local containment of the copied extent.
   No theorem here asserts that implication or a counterexample to the
   frozen external_frame_ret_ok_ptr. Integration must justify it using
   additional expression-specific information, or avoid that interface. *)
