(* Source-side resolution and induction-hypothesis boundaries for custom
   errors.  These facts are shared by the value, memory and pointer towers. *)
Theory bodyCustomErrorSource
Ancestors
  bodySim vyperAST vyperTypeContract vyperTypeSystem vyperEvent
  compileEnv list

Theorem custom_error_ordered_exprs:
  order_custom_error_args params err = SOME es ==>
  es = custom_error_exprs err
Proof
  Cases_on `err` >> rw[order_custom_error_args_def, custom_error_exprs_def] >>
  imp_res_tac order_custom_error_kwargs_SOME >> gvs[NULL_EQ]
QED

Theorem custom_error_resolved_source:
  custom_error_resolved [(NONE,tops)] (CustomError id positional kwargs) ==>
  FST id = NONE /\
  ?params.
    lookup_custom_error_args_in (SND id) tops = SOME params /\
    order_custom_error_args params (CustomError id positional kwargs) =
      SOME (custom_error_exprs (CustomError id positional kwargs)) /\
    MAP expr_type (custom_error_exprs (CustomError id positional kwargs)) =
      MAP SND params
Proof
  PairCases_on `id` >>
  simp[custom_error_resolved_def] >>
  Cases_on `id0 = NONE` >> simp[] >>
  strip_tac >>
  Cases_on `lookup_custom_error_args_in id1 tops` >> gvs[] >>
  Cases_on `order_custom_error_args x (CustomError (NONE,id1) positional kwargs)` >>
  gvs[] >> metis_tac[custom_error_ordered_exprs]
QED

Theorem custom_error_body_resolution:
  body_inv tops ctx ce cx /\
  custom_error_resolved [(NONE,tops)] (CustomError id positional kwargs) ==>
  ?params.
    FST id = NONE /\
    get_module_code cx (FST id) = SOME tops /\
    lookup_custom_error_args_in (SND id) tops = SOME params /\
    ce.ce_error_info (nsid_to_string id) = SOME params /\
    order_custom_error_args params (CustomError id positional kwargs) =
      SOME (custom_error_exprs (CustomError id positional kwargs)) /\
    MAP expr_type (custom_error_exprs (CustomError id positional kwargs)) =
      MAP SND params
Proof
  strip_tac >> drule custom_error_resolved_source >> strip_tac >>
  PairCases_on `id` >> gvs[] >>
  fs[body_inv_def, cenv_module_pins_def, nsid_to_string_def] >>
  metis_tac[]
QED

(* The assertion IH becomes available only after evaluating the condition. *)
Theorem custom_error_raise_args_ready:
  (!id positional kwargs decls params args.
    err = CustomError id positional kwargs /\
    get_module_code cx (FST id) = SOME decls /\
    lookup_custom_error_args_in (SND id) decls = SOME params /\
    order_custom_error_args params err = SOME args ==>
    body_exprs_ok cx args) /\
  body_inv tops ctx ce cx /\ custom_error_resolved [(NONE,tops)] err ==>
  body_exprs_ok cx (custom_error_exprs err)
Proof
  Cases_on `err` >> strip_tac >>
  drule_all custom_error_body_resolution >> strip_tac >> metis_tac[]
QED

Theorem custom_error_assert_args_ready:
  (!s0 tv s1 id positional kwargs decls params args.
    eval_expr cx e s0 = (INL tv,s1) /\
    err = CustomError id positional kwargs /\
    get_module_code cx (FST id) = SOME decls /\
    lookup_custom_error_args_in (SND id) decls = SOME params /\
    order_custom_error_args params err = SOME args ==>
    body_exprs_ok cx args) /\
  eval_expr cx e es = (INL tv,es1) /\
  body_inv tops ctx ce cx /\ custom_error_resolved [(NONE,tops)] err ==>
  body_exprs_ok cx (custom_error_exprs err)
Proof
  Cases_on `err` >> strip_tac >>
  drule_all custom_error_body_resolution >> strip_tac >> metis_tac[]
QED
