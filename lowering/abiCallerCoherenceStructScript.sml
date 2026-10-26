(* Struct coherence descends through both maps. The compiler field sizes
   still refer to the complete environment, as the real builder does. *)
Theory abiCallerCoherenceStruct
Ancestors
  abiCallerCoherenceNodes abiCallerMetadata abiCallerStructMap
  abiDecoderCoherence compileEnv vyperTypeSystem vyperTypeABI vyperValue
  finite_map list pair combin

Theorem abi_caller_struct_coherent:
  abi_caller_metadata ce root /\ env SUBMAP root /\
  sf SUBMAP ce.ce_struct_fields /\ abi_caller_struct_map sf env /\
  assignable_type env (StructT nsid) /\
  evaluate_type env (StructT nsid) = SOME tv /\
  (!args tvs child_sf.
    FLOOKUP env nsid = SOME (StructArgs args) /\
    LIST_REL (\ty tv. evaluate_type (env \\ nsid) ty = SOME tv) (MAP SND args) tvs /\
    EVERY (assignable_type (env \\ nsid)) (MAP SND args) /\
    env \\ nsid SUBMAP root /\ child_sf SUBMAP ce.ce_struct_fields /\
    abi_caller_struct_map child_sf (env \\ nsid) ==>
    LIST_REL (abi_decoder_coherent ce (env \\ nsid) child_sf) (MAP SND args) tvs) ==>
  abi_decoder_coherent ce env sf (StructT nsid) tv
Proof
  strip_tac >>
  qpat_assum `evaluate_type _ (StructT _) = SOME _`
    (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >> gvs[AllCaseEqs()] >>
  drule_all abi_caller_struct_map_namespace >> strip_tac >>
  Cases_on `nsid` >> gvs[] >>
  rename1 `FLOOKUP env (NONE,struct_name) = SOME (StructArgs source_fields)` >>
  rename1 `evaluate_types _ _ [] = SOME field_tvs` >>
  drule_all abi_caller_struct_map_lookup >> strip_tac >>
  rename1 `FLOOKUP sf _ = SOME field_rows` >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [nsid_to_string_def]) >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  qpat_x_assum `assignable_type env (StructT _)` mp_tac >>
  asm_simp_tac (srw_ss()) [Once assignable_type_def] >> strip_tac >>
  `env \\ (NONE,struct_name) SUBMAP root` by
    (irule SUBMAP_TRANS >> qexists_tac `env` >> simp[]) >>
  `sf \\ struct_name SUBMAP ce.ce_struct_fields` by
    (irule SUBMAP_TRANS >> qexists_tac `sf` >> simp[]) >>
  `abi_caller_struct_map (sf \\ struct_name) (env \\ (NONE,struct_name))` by
    (irule abi_caller_struct_map_delete >> simp[]) >>
  `LIST_REL (abi_decoder_coherent ce (env \\ (NONE,struct_name)) (sf \\ struct_name))
      (MAP SND source_fields) field_tvs` by
    (qpat_x_assum `!tvs child_sf. _ ==> LIST_REL _ _ _` irule >>
     fs[EVERY_MAP, o_DEF]) >>
  qpat_assum `abi_caller_metadata ce root`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_caller_metadata_def]) >>
  `EVERY (\(name,ty,sz). sz = type_memory_bytes ce ty) field_rows` by
    (qpat_x_assum `!env sf name args fields tvs. _ ==> EVERY _ fields`
       (fn th => drule_all th) >> simp[]) >>
  `abi_decoder_header ce env (StructT (NONE,struct_name))
      (StructTV (ZIP (MAP FST source_fields,field_tvs)))` by
    (qpat_x_assum `!env ty tv. _ ==> abi_decoder_header ce env ty tv` irule >> simp[]) >>
  simp[abi_decoder_coherent_struct_iff] >>
  qexistsl_tac [`field_rows`, `field_tvs`] >> simp[nsid_to_string_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_CALLER_COHERENCE_STRUCT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI caller struct coherence not kernel closed: " ^ n)
  end) (DB.thms "abiCallerCoherenceStruct");
