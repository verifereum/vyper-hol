(* Diagnostic probes only: these do not assert reachability from a source RHS. *)
Theory augAssignPtrProvenanceProbe
Ancestors
  augAssignPtrInterfaces bodyPtrDefs ptrDiscipline venomInst finite_map

Theorem comparison_one_provenance_fails:
  FLOOKUP G r = SOME site /\ FLOOKUP G l = NONE ==>
  ~access_ok lo G fn (mk_inst id LT [Var r; Var l] [out]) s
Proof
  strip_tac >> strip_tac >>
  qpat_x_assum `access_ok _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [access_ok_def, mk_inst_def, instruction_accessors]) >>
  qpat_x_assum `!u w. _` (qspecl_then [`r`, `l`] mp_tac) >>
  fs[FLOOKUP_DEF]
QED

Theorem word_ptr_val_ok_allows_provenance:
  is_word_type ty /\ op_taint tn op = {} ==>
  ptr_val_ok cx ty v op G tn s
Proof
  simp[ptr_val_ok_def]
QED

Theorem clean_add_guard_obstruction:
  FLOOKUP G left = NONE /\ FLOOKUP G right = SOME site /\ result <> left ==>
  ~access_ok lo
    (step_prov PG G (mk_inst addid ADD [Var left; Var right] [result]) u)
    fn (mk_inst guardid LT [Var result; Var left] [out]) s
Proof
  strip_tac >> irule comparison_one_provenance_fails >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_UPDATE] >> metis_tac[]
QED
