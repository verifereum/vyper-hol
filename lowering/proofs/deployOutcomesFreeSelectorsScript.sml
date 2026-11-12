Theory deployOutcomesFreeSelectors
Ancestors
  vyperTypeSystem list

(* Diagnostic boundary: a real typing premise supplies the indices used by
   binary lowering. P can carry both exclusion and recursive selector safety. *)
Theorem outcomes_free_binary_selectors:
  well_typed_builtin_app ty (Bop op) (MAP expr_type args) /\
  EVERY P args ==>
  P (HD args) /\ P (HD (TL args)) /\
  MEM (HD args) args /\ MEM (HD (TL args)) args
Proof
  simp[well_typed_builtin_app_def] >> strip_tac >>
  Cases_on `args` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[]
QED
