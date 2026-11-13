(* ABI-static destinations admit no nontrivial implicit widening. *)
Theory typedNormalizeStaticRigidity
Ancestors
  typedNormalizeWidening typedNormalizeFastRepresentation
  valueEncoding valueEncodingDefs vyperValue compileEnv vyperTypeSystem list

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

Theorem typed_static_fast_evaluated_identity:
  type_widens_to tenv s d /\
  ~is_abi_dynamic cenv.ce_struct_fields d /\
  evaluate_type tenv s = SOME sv /\ evaluate_type tenv d = SOME dv ==>
  sv = dv
Proof
  strip_tac >> drule_all type_widens_to_static_identity >> strip_tac >> gvs[]
QED

(* Validate all hypotheses needed by the dense/sparse lifting interface. *)
Theorem typed_static_fast_representation[local]:
  type_widens_to tenv s d /\
  ~is_abi_dynamic cenv.ce_struct_fields d /\
  evaluate_type tenv s = SOME sv /\ evaluate_type tenv d = SOME dv ==>
  type_memory_size sv = type_memory_size dv /\
  (!v p mem. val_in_memory sv v p mem ==> val_in_memory dv v p mem) /\
  (!p mem. val_in_memory sv (default_value sv) p mem ==>
           val_in_memory dv (default_value dv) p mem)
Proof
  strip_tac >> drule_all typed_static_fast_evaluated_identity >> simp[]
QED

(* The actual dynamic shortcut tests identical element syntax. Only the
   outer capacity differs, not the represented live elements. *)
Theorem typed_dynamic_fast_representation[local]:
  s = d /\ evaluate_type tenv s = SOME sv /\
  evaluate_type tenv d = SOME dv ==>
  (val_in_memory (ArrayTV sv (Dynamic n)) (ArrayV (DynArrayV vs)) b mem <=>
   val_in_memory (ArrayTV dv (Dynamic m)) (ArrayV (DynArrayV vs)) b mem)
Proof
  strip_tac >> gvs[] >> simp[dynarray_in_memory_capacity_irrelevant]
QED
