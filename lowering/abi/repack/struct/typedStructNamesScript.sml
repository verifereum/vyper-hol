(* TOP-LEVEL: every actual checked struct metadata list has distinct
   field names. Size resolution retains the source declaration's names. *)
Theory typedStructNames
Ancestors
  typedCopyMetadata structLayoutProps compileVyper compileEnv vyperTypeContract
  vyperAST finite_map list pair combin

Theorem built_struct_field_names:
  !tenv args. MAP FST (build_struct_fields_one tenv args) = MAP FST args
Proof
  simp[build_struct_fields_one_def, MAP_MAP_o, o_DEF] >> rpt gen_tac >>
  irule MAP_CONG >> simp[FORALL_PROD]
QED

Theorem built_struct_fields_name_origin:
  !tops tenv sf name fields.
    FLOOKUP (build_struct_fields_map tenv tops sf) name = SOME fields ==>
    FLOOKUP sf name = SOME fields \/
    ?args. MEM (StructDecl name args) tops /\ MAP FST fields = MAP FST args
Proof
  Induct_on `tops` >- simp[build_struct_fields_map_def] >>
  rpt gen_tac >> qmatch_goalsub_rename_tac `build_struct_fields_map _ (top_decl::rest_tops) _` >>
  Cases_on `top_decl` >> simp[build_struct_fields_map_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[FLOOKUP_UPDATE, AllCaseEqs(), built_struct_field_names] >> metis_tac[]
QED

Theorem make_struct_fields_name_origin:
  !tops name fields.
    FLOOKUP (make_struct_fields_map tops) name = SOME fields ==>
    ?args. MEM (StructDecl name args) tops /\ MAP FST fields = MAP FST args
Proof
  rpt gen_tac >> simp[make_struct_fields_map_def] >>
  rpt strip_tac >> drule built_struct_fields_name_origin >> simp[]
QED

Theorem checked_struct_metadata_names_distinct:
  !tops in_deploy layouts addr art name fields.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    FLOOKUP (make_struct_fields_map tops) name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields)
Proof
  rpt gen_tac >> strip_tac >> drule make_struct_fields_name_origin >>
  disch_then (qx_choose_then `args` strip_assume_tac) >>
  mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `src` |-> `NONE`, `tls` |-> `tops`,
    `id` |-> `name`, `fields` |-> `args`] check_contract_struct_fields_distinct) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]) >> simp[]
QED
