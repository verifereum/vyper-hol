Theory bodyPtrIfExpDefaults
Ancestors
  vyperTypeArgFits

(* The arg_type_fits boundary already exists in vyperTypeArgFits;
   only its implicit-widening corollary is needed here. *)
Theorem ifexp_type_widens_default_value:
  !tenv st dt sv dv.
    type_widens_to tenv st dt /\ evaluate_type tenv st = SOME sv /\
    evaluate_type tenv dt = SOME dv ==>
    default_value sv = default_value dv
Proof
  rw[vyperTypeSystemTheory.type_widens_to_def]
  >- gvs[] >>
  drule_all (cj 1 arg_type_fits_default_value) >> simp[]
QED
