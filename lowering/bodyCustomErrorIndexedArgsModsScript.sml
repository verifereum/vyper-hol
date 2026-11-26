(* Index the linked positional rows at the common successful exit. *)
Theory bodyCustomErrorIndexedArgsMods
Ancestors
  bodyExtPosSavedRowMods vyperTypeArgFits vyperTypeSystem vyperABI
  vyperInterpreter list pair

Theorem custom_error_indexed_args_mods:
  LENGTH args = LENGTH saved_vals /\ LENGTH args = LENGTH vs /\
  MAP expr_type args = MAP SND params /\
  (!i. i < LENGTH args ==>
    ?e sv v tv param_tv.
      e = EL i args /\ sv = EL i saved_vals /\ v = EL i vs /\
      ext_pos_saved_row_mods lo cenv cx [] sa sb H e sv v ee G tn t /\
      arg_type_fits (lowered_value_type cenv e)
        (EL i (MAP SND params)) /\
      evaluate_type (get_tenv cx) (EL i (MAP SND params)) = SOME param_tv /\
      value_has_type param_tv v /\
      evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
      value_has_type tv v) ==>
  !i. i < LENGTH args ==>
    ?tv param_tv.
      ext_pos_saved_row_mods lo cenv cx [] sa sb H
        (EL i args) (EL i saved_vals) (EL i vs) ee G tn t /\
      arg_type_fits (lowered_value_type cenv (EL i args))
        (EL i (MAP SND params)) /\
      evaluate_type (get_tenv cx) (EL i (MAP SND params)) = SOME param_tv /\
      value_has_type param_tv (EL i vs) /\
      evaluate_type (get_tenv cx) (lowered_value_type cenv (EL i args)) = SOME tv /\
      value_has_type tv (EL i vs)
Proof
  strip_tac >> gen_tac >> disch_tac >>
  qpat_assum `!i. i < LENGTH args ==> ?e sv v tv param_tv. _`
    (qspec_then `i` (drule_then
      (qx_choosel_then [`e`,`sv`,`v`,`tv`,`param_tv`]
        (MAP_EVERY assume_tac o CONJUNCTS)))) >>
  qpat_assum `e = EL i args` (fn th => SUBST_ALL_TAC th) >>
  qpat_assum `sv = EL i saved_vals` (fn th => SUBST_ALL_TAC th) >>
  qpat_assum `v = EL i vs` (fn th => SUBST_ALL_TAC th) >>
  qexistsl [`tv`,`param_tv`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
