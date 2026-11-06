Theory placeMemoryTypeInterfaces
Ancestors
  vyperTypeArgFits vyperTypeValues valueEncodingProps vyperTypeSystem vyperValue

(* Evaluation may forget nominal names, but not along an implicit widening. *)
Theorem arg_type_fits_evaluate_equal:
  (!t u tv.
     arg_type_fits t u /\ evaluate_type tenv t = SOME tv /\
     evaluate_type tenv u = SOME tv ==> t = u) /\
  (!ts us tvs.
     arg_types_fit ts us /\
     LIST_REL (\t tv. evaluate_type tenv t = SOME tv) ts tvs /\
     LIST_REL (\t tv. evaluate_type tenv t = SOME tv) us tvs ==> ts = us)
Proof
  ho_match_mp_tac arg_type_fits_ind >> rw[arg_type_fits_def] >>
  imp_res_tac evaluate_type_ArrayT_cases >>
  imp_res_tac evaluate_type_TupleT_cases >>
  gvs[evaluate_type_def] >>
  metis_tac[]
QED

Theorem type_widens_to_evaluate_equal:
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME tv /\
  evaluate_type tenv dty = SOME tv ==> sty = dty
Proof
  simp[type_widens_to_def] >> metis_tac[arg_type_fits_evaluate_equal]
QED

(* Zero-sized evaluated sources have zero-sized destinations even when the
   syntactic types differ. This is a layout fact, not permission to omit
   the destination value obligation. *)
Theorem arg_type_fits_zero_slots:
  (!t u tv tu.
     arg_type_fits t u /\ evaluate_type tenv t = SOME tv /\
     evaluate_type tenv u = SOME tu ==>
     (type_slot_size tv = 0 <=> type_slot_size tu = 0)) /\
  (!ts us tvs tus.
     arg_types_fit ts us /\
     LIST_REL (\t tv. evaluate_type tenv t = SOME tv) ts tvs /\
     LIST_REL (\t tv. evaluate_type tenv t = SOME tv) us tus ==>
     (type_slot_size_list tvs = 0 <=> type_slot_size_list tus = 0))
Proof
  ho_match_mp_tac arg_type_fits_ind >> rw[arg_type_fits_def] >>
  imp_res_tac evaluate_type_ArrayT_cases >>
  imp_res_tac evaluate_type_TupleT_cases >>
  gvs[evaluate_type_def, type_slot_size_def] >>
  metis_tac[]
QED

Theorem type_widens_to_zero_memory_size:
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv dty = SOME dtv ==>
  (type_memory_size stv = 0 <=> type_memory_size dtv = 0)
Proof
  rw[type_widens_to_def, type_memory_size_slots] >>
  gvs[] >> metis_tac[cj 1 arg_type_fits_zero_slots]
QED

(* The two exceptional overlap disjuncts of the assignment theorem cannot
   reach a genuinely widening typed copy with a positive destination. *)
Theorem widening_typed_copy_separation:
  type_widens_to tenv sty dty /\ sty <> dty /\
  evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv dty = SOME dtv /\ 0 < type_slot_size dtv /\
  (type_memory_size stv = 0 \/
   src + type_memory_size stv <= dst \/
   dst + type_memory_size dtv <= src \/ stv = dtv) ==>
  src + type_memory_size stv <= dst \/
  dst + type_memory_size dtv <= src
Proof
  strip_tac >>
  `stv <> dtv` by metis_tac[type_widens_to_evaluate_equal] >>
  `type_memory_size stv <> 0` by
    (drule_all type_widens_to_zero_memory_size >>
     simp[type_memory_size_slots]) >>
  metis_tac[]
QED
