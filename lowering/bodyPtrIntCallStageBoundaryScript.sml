Theory bodyPtrIntCallStageBoundary
Ancestors bodyPtrDefs bodyPtrIntCallConfinement exprLowering compileEnv
  ptrDiscipline finite_map pred_set list

Theorem intcall_stage_stack_singleton:
  compile_stage_intcall_args cenv [StackValue ty op] [T] [aty] sa =
  ([op],sa)
Proof
  simp[compile_stage_intcall_args_def, unwrap_value_def,
       comp_bind_def, comp_return_def]
QED

Theorem intcall_ptr_val_word:
  is_word_type ty ==>
  (ptr_val_ok cx ty v op G tn s <=> op_taint tn op = {})
Proof
  simp[ptr_val_ok_def]
QED

(* A clean scalar may retain an old site's provenance. This refutes only
   the proposed all-parameter whole-site exclusion interface, not the
   frozen internal-call theorem. *)
Theorem intcall_word_site_overlap:
  is_word_type ty ==>
  ptr_val_ok cx ty v (Var x) (FEMPTY |+ (x,(0,32)))
    (tn with t_var := FEMPTY) s /\
  ~intcall_prov_outside {0}
    [op_prov (FEMPTY |+ (x,(0,32))) (Var x)] FEMPTY
Proof
  simp[intcall_ptr_val_word, op_taint_def, op_prov_def,
       FLOOKUP_UPDATE, intcall_prov_outside_def,
       intcall_site_outside_def, DISJOINT_DEF, EXTENSION] >>
  qexists_tac `0` >> simp[]
QED
