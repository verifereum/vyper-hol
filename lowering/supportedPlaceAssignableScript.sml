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

Theorem supported_nested_type_assignable:
  !fuel tops ty.
    !tenv. supported_nested_type supported_scalar_type fuel tops ty /\
    tenv SUBMAP type_env tops /\ well_formed_type tenv ty ==>
    assignable_type tenv ty
Proof
  completeInduct_on `fuel` >> gen_tac >>
  measureInduct_on `type_size ty` >> rpt strip_tac >>
  Cases_on `supported_scalar_type ty`
  >- metis_tac[supported_scalar_type_assignable] >>
  qpat_x_assum `supported_nested_type _ _ _ _` mp_tac >>
  simp[Once supported_nested_type_def] >>
  Cases_on `ty` >> gvs[]
  >~ [`TupleT tys`]
  >- (strip_tac >> drule well_formed_tuple_elements >> strip_tac >>
      simp[assignable_type_def] >> gvs[EVERY_MEM] >> rpt strip_tac >>
      first_x_assum irule >> simp[] >>
      `!xs t. MEM t xs ==> type_size t < list_size type_size xs` by
        (Induct >> simp[list_size_def] >> rpt strip_tac >> gvs[] >>
         res_tac >> simp[]) >>
      first_x_assum drule >> simp[])
  >~ [`ArrayT elem bd`]
  >- (Cases_on `bd` >> simp[] >> strip_tac >>
      drule well_formed_array_element >> strip_tac >>
      simp[assignable_type_def] >> first_x_assum irule >> simp[]) >>
  strip_tac >> Cases_on `supported_struct_fields tops p` >> gvs[] >>
  drule_all supported_struct_submap_lookup >> strip_tac >>
  drule_all well_formed_struct_fields_deleted >> strip_tac >>
  simp[assignable_type_def] >> gvs[EVERY_MEM] >> rpt strip_tac >>
  gvs[] >>
  qpat_x_assum `!m. m < fuel ==> _` (qspec_then `fuel - 1` mp_tac) >>
  simp[] >> disch_then irule >> simp[] >>
  qexists `tops` >> simp[] >>
  fs[SUBMAP_DEF, DRESTRICT_DEF, DOMSUB_FAPPLY_THM]
QED

Theorem supported_place_type_assignable:
  supported_place_type tops ty /\ well_formed_type (type_env tops) ty ==>
  assignable_type (type_env tops) ty
Proof
  rw[supported_place_type_def] >>
  irule supported_nested_type_assignable >> simp[] >>
  qexistsl [`LENGTH tops`, `tops`] >> simp[]
QED
