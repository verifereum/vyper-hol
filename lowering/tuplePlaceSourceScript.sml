(* Source-side and paired-layout interfaces for tuple place assignment. *)
Theory tuplePlaceSource
Ancestors
  typedCopyCompatibilityPtr vyperTypeArgFits vyperTypeSystem
  targetPlaceSimCases targetPlaceSimCasesBase targetPlaceSim
  exprSimHypsDefs vyperPlaceWriteSoundness vyperPlaceTyping
  vyperPlaceStoragePreservation stmtPoppedKeys vyperPlaceFrames
  vyperTypeStoragePreservation vyperStorageBackend
  list

Theorem tuple_place_type_facts:
  !tenv tys ltys tvs ltvs.
    assignable_type tenv (TupleT tys) /\ arg_types_fit ltys tys /\
    evaluate_type tenv (TupleT tys) = SOME (TupleTV tvs) /\
    evaluate_type tenv (TupleT ltys) = SOME (TupleTV ltvs) ==>
    LENGTH ltys = LENGTH tys /\ LENGTH tvs = LENGTH tys /\
    LENGTH ltvs = LENGTH tys /\
    !i. i < LENGTH tys ==>
      evaluate_type tenv (EL i tys) = SOME (EL i tvs) /\
      evaluate_type tenv (EL i ltys) = SOME (EL i ltvs) /\
      assignable_type tenv (EL i tys) /\
      type_widens_to tenv (EL i ltys) (EL i tys) /\
      0 < type_slot_size (EL i tvs)
Proof
  rpt gen_tac >> strip_tac >>
  `arg_type_fits (TupleT ltys) (TupleT tys)` by
    simp[arg_type_fits_def] >>
  drule_all arg_type_fits_tuple_layouts >> strip_tac >> gvs[] >>
  rpt strip_tac >>
  `assignable_type tenv (EL i tys)` by
    gvs[assignable_type_def, EVERY_EL] >>
  `well_formed_type tenv (EL i tys)` by
    metis_tac[assignable_type_well_formed] >>
  gvs[type_widens_to_def] >>
  metis_tac[assignable_type_slot_size_pos]
QED

Theorem tuple_place_target_ready:
  target_case F ctx func cenv cx bt /\
  ~immutable_root cx bt /\ target_indices_pre cenv cx env bt /\
  expr_sim_inv cenv cx env es ==>
  target_pre cenv cx env bt es /\ target_sim ctx func cenv cx env bt es
Proof
  simp[target_case_def, target_pre_def] >> metis_tac[]
QED
