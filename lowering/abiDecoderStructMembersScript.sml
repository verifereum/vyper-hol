(* Recover the positional child view from semantic struct conversion.
   TOP-LEVEL: abi_decoder_struct_members.
   Helper: successful list conversion preserves all three lengths. *)
Theory abiDecoderStructMembers
Ancestors
  abiDecoderMembers abiDecoderCoherence abiDecoderTypedContract
  vyperABI vyperValue vyperTyping vyperTypeDefaults contractABI
  compileEnv valueEncoding finite_map list

Theorem abi_to_vyper_list_lengths:
  !tys avs vs. abi_to_vyper_list env tys avs = SOME vs ==>
    LENGTH tys = LENGTH avs /\ LENGTH avs = LENGTH vs
Proof
  Induct_on `tys` >> rpt gen_tac >> Cases_on `avs` >>
  simp[Once abi_to_vyper_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> first_x_assum drule_all >> simp[]
QED

Theorem abi_decoder_struct_abi_types:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  has_type (vyper_to_abi_type env (StructT nsid)) (ListV avs) ==>
  has_types (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args)) avs
Proof
  strip_tac >> gvs[vyper_to_abi_type_def, has_type_def, vyper_to_abi_types_MAP]
QED

Theorem abi_decoder_struct_conversion:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  abi_to_vyper env (StructT nsid) (ListV avs) = SOME (StructV fields) ==>
  abi_to_vyper_list (env \\ nsid) (MAP SND args) avs = SOME (MAP SND fields)
Proof
  strip_tac >>
  qpat_x_assum `abi_to_vyper _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [Once abi_to_vyper_def, AllCaseEqs()] >> strip_tac >>
  drule_all abi_to_vyper_list_lengths >> strip_tac >> gvs[MAP_ZIP]
QED

Theorem abi_decoder_struct_members:
  abi_decoder_coherent ce env sf (StructT nsid) tv /\
  FLOOKUP env nsid = SOME (StructArgs args) /\
  abi_decoder_metadata ce env (StructT nsid) tv di (ListV avs) (StructV fields) ==>
  ?tvs. tv = StructTV (ZIP (MAP FST args,tvs)) /\
    abi_decoder_members ce (env \\ nsid) (sf \\ nsid_to_string nsid)
      (MAP SND args) tvs avs (MAP SND fields)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_decoder_coherent _ _ _ _ _` mp_tac >>
  asm_simp_tac bool_ss [abi_decoder_coherent_struct_iff] >> strip_tac >>
  qpat_x_assum `SOME (StructArgs args) = _`
    (SUBST_ALL_TAC o SYM o SIMP_RULE (srw_ss()) []) >>
  rename1 `LIST_REL (abi_decoder_coherent ce (env \\ nsid)
    (sf \\ nsid_to_string nsid)) (MAP SND args) tvs` >>
  qpat_x_assum `tv = StructTV _` SUBST_ALL_TAC >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  `has_types (MAP (vyper_to_abi_type (env \\ nsid)) (MAP SND args)) avs` by
    metis_tac[abi_decoder_struct_abi_types] >>
  drule_all abi_decoder_struct_conversion >> strip_tac >>
  `LENGTH tvs = LENGTH args` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  `LIST_REL value_has_type tvs (MAP SND fields)` by
    (qpat_assum `value_has_type (StructTV _) (StructV _)` mp_tac >>
     simp_tac bool_ss [Once value_has_type_def] >> strip_tac >>
     drule struct_has_type_values_have_types >> simp[MAP_ZIP, values_have_types_LIST_REL]) >>
  qexists_tac `tvs` >> asm_simp_tac bool_ss [] >>
  irule abi_decoder_members_intro >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_STRUCT_MEMBERS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI struct members not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderStructMembers");
