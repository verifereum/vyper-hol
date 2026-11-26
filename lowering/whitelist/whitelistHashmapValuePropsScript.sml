Theory whitelistHashmapValueProps
Ancestors
  vyperAST vyperImportRefs vyperTypeContract supportedTypes

Theorem checked_hashmap_value_supported:
  (!ty. well_formed_type tenv ty /\ hashmap_key_type ty ==>
        supported_hashmap_key_type ty) /\
  (!ty. assignable_type tenv ty /\ (imported_only ==> imported_type_refs_ok ty) ==>
        supported_place_type tops ty) ==>
  !vt. check_value_type tenv vt /\ (imported_only ==> imported_value_type_refs_ok vt) ==>
       supported_hashmap_value tops vt
Proof
  strip_tac >> Induct >>
  simp[check_value_type_def, supported_hashmap_value_def,
       supported_storage_type_def, GSYM supported_place_type_def,
       imported_value_type_refs_ok_def] >>
  metis_tac[]
QED
