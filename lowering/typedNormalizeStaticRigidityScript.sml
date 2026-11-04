(* ABI-static destinations admit no nontrivial implicit widening. *)
Theory typedNormalizeStaticRigidity
Ancestors
  typedNormalizeWidening compileEnv vyperTypeSystem list

Theorem arg_type_fits_static_identity_joint[local]:
  (!s d. arg_type_fits s d ==>
     !(sf : (string, (string # type # num) list) fmap). ~is_abi_dynamic sf d ==> s = d) /\
  (!ss ds. arg_types_fit ss ds ==>
     !(sf : (string, (string # type # num) list) fmap). ~EXISTS (is_abi_dynamic sf) ds ==> ss = ds)
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  rw[arg_type_fits_def, is_abi_dynamic_def] >>
  first_x_assum drule >> disch_then (qspec_then `sf` mp_tac) >> gvs[EVERY_MEM, combinTheory.o_DEF] >> metis_tac[]
QED

Theorem arg_type_fits_static_identity:
  !s d (sf : (string, (string # type # num) list) fmap). arg_type_fits s d /\ ~is_abi_dynamic sf d ==> s = d
Proof
  metis_tac[arg_type_fits_static_identity_joint]
QED

Theorem type_widens_to_static_identity:
  type_widens_to tenv s d /\ ~is_abi_dynamic (sf : (string, (string # type # num) list) fmap) d ==> s = d
Proof
  rw[type_widens_to_def] >> metis_tac[arg_type_fits_static_identity]
QED
