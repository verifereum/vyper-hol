Theory assignPlaceLayout
Ancestors
  exprSimAggregateChildren compileEnv

Theorem widening_source_memory_size_pos:
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv dty = SOME dtv /\
  0 < type_memory_size dtv ==>
  0 < type_memory_size stv
Proof
  simp[vyperTypeSystemTheory.type_widens_to_def] >> rpt strip_tac >> gvs[] >>
  drule_all (cj 1 arg_fits_zero_memory_size) >> simp[]
QED
