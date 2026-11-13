(* Lowered bytestring types at backend assignment boundaries. *)
Theory assignPlaceBytestringBackendTypes
Ancestors
  assignPlaceBackendContinuationMem exprSimConvertBytes vyperTypeSystem compileEnv

Theorem assign_bytestring_backend_types:
  is_bytestring_type lt /\ is_bytestring_type et /\ is_bytestring_type dty /\
  evaluate_type tenv lt = SOME stv /\ evaluate_type tenv et = SOME etv /\
  arg_type_fits lt et /\ type_widens_to tenv et dty ==>
  assignable_type tenv lt /\ type_widens_to tenv lt dty
Proof
  rw[bytestring_type_cases] >>
  gvs[arg_type_fits_def, type_widens_to_def, assignable_type_def,
      well_formed_type_def] >> decide_tac
QED
