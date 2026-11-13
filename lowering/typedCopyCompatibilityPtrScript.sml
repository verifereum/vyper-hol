(* Separate evaluated layouts for implicit-bound normalization. *)
Theory typedCopyCompatibilityPtr
Ancestors vyperTypeArgFits vyperTypeValues vyperTypeSystem list

Theorem arg_type_fits_array_layouts:
  !tenv t u b c tv tu.
    arg_type_fits (ArrayT t b) (ArrayT u c) /\
    evaluate_type tenv (ArrayT t b) = SOME tv /\
    evaluate_type tenv (ArrayT u c) = SOME tu ==>
    ?et eu. tv = ArrayTV et b /\ tu = ArrayTV eu c /\
      evaluate_type tenv t = SOME et /\ evaluate_type tenv u = SOME eu /\
      arg_type_fits t u /\
      ((?n m. b = Dynamic n /\ c = Dynamic m /\ n <= m) \/
       (?n. b = Fixed n /\ c = Fixed n))
Proof
  rpt strip_tac >>
  imp_res_tac evaluate_type_ArrayT_cases >> gvs[] >>
  Cases_on `b` >> Cases_on `c` >> gvs[arg_type_fits_def]
QED

Theorem arg_types_fit_index[local]:
  !ts us. arg_types_fit ts us ==>
    LENGTH ts = LENGTH us /\
    !i. i < LENGTH ts ==> arg_type_fits (EL i ts) (EL i us)
Proof
  Induct >> Cases_on `us` >> simp[arg_type_fits_def] >>
  rpt strip_tac >> Cases_on `i` >> gvs[]
QED

Theorem arg_type_fits_tuple_layouts:
  !tenv ts us tv tu.
    arg_type_fits (TupleT ts) (TupleT us) /\
    evaluate_type tenv (TupleT ts) = SOME tv /\
    evaluate_type tenv (TupleT us) = SOME tu ==>
    ?tvs tus. tv = TupleTV tvs /\ tu = TupleTV tus /\
      LENGTH ts = LENGTH us /\ LENGTH tvs = LENGTH ts /\ LENGTH tus = LENGTH us /\
      (!i. i < LENGTH ts ==>
        arg_type_fits (EL i ts) (EL i us) /\
        evaluate_type tenv (EL i ts) = SOME (EL i tvs) /\
        evaluate_type tenv (EL i us) = SOME (EL i tus))
Proof
  rpt strip_tac >> imp_res_tac evaluate_type_TupleT_cases >>
  gvs[arg_type_fits_def, LIST_REL_EL_EQN] >>
  drule arg_types_fit_index >> strip_tac >> simp[]
QED
