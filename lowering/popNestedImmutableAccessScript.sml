(* Source interfaces for immutable roots across nested-target indices.
   These bounded clauses do not assert the full evaluator access frame. *)
Theory popNestedImmutableAccess
Ancestors
  targetOverlapAccess popNestedImmutableTransport vyperTypeConstantCells
  vyperTypeInitialState vyperSubscriptOverlap vyperTypeContract list
  vyperState vyperMisc vyperAST finite_map alist

Theorem constant_decl_member[local]:
  !id ts. constant_decl id ts ==>
    ?vis e ty init. MEM (VariableDecl vis (Constant e) id ty init) ts
Proof
  Induct_on `ts` >- simp[constant_decl_def] >>
  Cases_on `h` >> simp[constant_decl_def] >>
  rpt gen_tac >> simp[] >>
  qmatch_goalsub_rename_tac `constant_decl id (VariableDecl vis0 mut id0 ty0 init0::ts)` >>
  Cases_on `mut` >> gvs[constant_decl_def] >> metis_tac[]
QED

Theorem immutable_decl_not_constant_decl:
  !src ts vis id ty init.
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts)) /\
    MEM (VariableDecl vis Immutable id ty init) ts ==>
    ~constant_decl id ts
Proof
  rpt strip_tac >> drule constant_decl_member >> strip_tac >>
  drule_all module_immutable_constant_names_distinct >> simp[]
QED

Theorem set_immutable_unwritten_lookup:
  set_immutable cx src' id' tv v st = (res,st') /\
  (src <> src' \/ id <> id') ==>
  FLOOKUP (case ALOOKUP st'.immutables cx.txn.target of
             NONE => FEMPTY | SOME imms => get_source_immutables src imms) id =
  FLOOKUP (case ALOOKUP st.immutables cx.txn.target of
             NONE => FEMPTY | SOME imms => get_source_immutables src imms) id
Proof
  simp[set_immutable_def, get_address_immutables_def,
       set_address_immutables_def, bind_def, return_def,
       lift_option_type_def, lift_option_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> Cases_on `src = src'` >>
  gvs[get_source_immutables_set_same, get_source_immutables_set_other,
      FLOOKUP_UPDATE] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  gvs[return_def, raise_def]
QED
