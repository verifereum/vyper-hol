(* A source dispatcher without a fallback has no compiled fallback package. *)
Theory linkedFallbackAbsent
Ancestors
  calldataNoneFallbackJoint compileUnit list pair

Theorem linked_classified_fallback_absent:
  classify_functions_unit mods exps = (exts,ints,fb,ctor,imp_ctors) /\
  ~list$EXISTS is_default_decl (main_module mods) /\
  exported_fallback mods exps = NONE ==>
  fb = NONE
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac absent_default_fold >>
  qpat_x_assum `classify_functions_unit _ _ = _` mp_tac >>
  simp[classify_functions_unit_def] >>
  pairarg_tac >> fs[]
QED
