(* Zero-sized well-formed widening cannot change its type syntax. *)
Theory wideningZeroLayout
Ancestors
  exprSimAggregateChildren exprSimFieldLayout
  vyperTypeSystem vyperValue valueEncoding

Theorem arg_fits_zero_layout[local]:
  (!sty dty. !stv dtv.
    arg_type_fits sty dty /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv dty = SOME dtv /\
    type_memory_size stv = 0 ==> sty = dty) /\
  (!stys dtys. !stvs dtvs.
    arg_types_fit stys dtys /\
    OPT_MMAP (evaluate_type tenv) stys = SOME stvs /\
    OPT_MMAP (evaluate_type tenv) dtys = SOME dtvs /\
    type_memory_size_list stvs = 0 ==> stys = dtys)
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  rw[arg_type_fits_def, vyperValueTheory.evaluate_type_def,
     AllCaseEqs(), type_memory_size_def, evaluate_types_OPT_MMAP] >>
  gvs[vyperValueTheory.evaluate_type_def, evaluate_types_OPT_MMAP,
      type_memory_size_def]
QED

Theorem type_widens_to_zero_layout:
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv dty = SOME dtv /\
  type_memory_size stv = 0 ==> sty = dty
Proof
  rw[type_widens_to_def] >> gvs[] >>
  metis_tac[cj 1 arg_fits_zero_layout]
QED
