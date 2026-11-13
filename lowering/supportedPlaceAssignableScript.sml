(* Child typing interfaces for recursive supported place types. *)
Theory supportedPlaceAssignable
Ancestors
  retAbiPlanProps vyperTypeSystem vyperValue vyperMisc finite_map list option
  supportedTypes

Theorem well_formed_array_element:
  well_formed_type tenv (ArrayT ty bd) ==> well_formed_type tenv ty
Proof
  Cases_on `evaluate_type tenv ty` >>
  Cases_on `bd` >> simp[well_formed_type_def, evaluate_type_def]
QED

Theorem well_formed_tuple_elements:
  well_formed_type tenv (TupleT tys) ==>
  EVERY (well_formed_type tenv) tys
Proof
  simp[well_formed_type_def, evaluate_type_def, evaluate_types_OPT_MMAP,
       IS_SOME_EXISTS] >> strip_tac >>
  gvs[AllCaseEqs(), OPT_MMAP_SOME_IFF, EVERY_MEM, MEM_MAP, PULL_EXISTS,
      well_formed_type_def, IS_SOME_EXISTS] >>
  metis_tac[]
QED

Theorem well_formed_struct_fields_deleted:
  well_formed_type tenv (StructT id) /\
  FLOOKUP tenv id = SOME (StructArgs fields) ==>
  EVERY (well_formed_type (tenv \\ id) o SND) fields
Proof
  simp[well_formed_type_def, evaluate_type_def, evaluate_types_OPT_MMAP,
       IS_SOME_EXISTS] >> strip_tac >>
  gvs[AllCaseEqs(), OPT_MMAP_SOME_IFF, EVERY_MEM, MEM_MAP, PULL_EXISTS,
      well_formed_type_def]
QED

Theorem supported_struct_submap_lookup:
  tenv SUBMAP type_env tops /\ well_formed_type tenv (StructT id) /\
  supported_struct_fields tops id = SOME fields ==>
  FLOOKUP tenv id = SOME (StructArgs fields)
Proof
  strip_tac >> drule supported_struct_fields_type_env >> strip_tac >>
  Cases_on `FLOOKUP tenv id` >>
  gvs[well_formed_type_def, evaluate_type_def] >>
  rename1 `FLOOKUP tenv id = SOME desc` >> Cases_on `desc` >> gvs[] >>
  drule_all FLOOKUP_SUBMAP >> simp[]
QED

