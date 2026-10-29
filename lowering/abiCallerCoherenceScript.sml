Theory abiCallerCoherence
Ancestors
  abiCallerMetadata abiCallerStructMap abiDecoderConstructors abiDecoderCoherence
  abiDecoderPrimitiveCaller compileEnv vyperValue vyperABI vyperTypeABI finite_map list pair
  vyperTypeSystem combin compileVyper vyperContext

(* ===== Nodes ===== *)

(* Source evaluator inversions for recursive coherence. These constructors
   reuse the existing array/tuple interfaces and the checked metadata header. *)

Theorem abi_caller_array_coherent:
  evaluate_type env (ArrayT ty bound) = SOME atv /\
  (!tv. evaluate_type env ty = SOME tv ==>
    abi_decoder_coherent ce env sf ty tv) ==>
  abi_decoder_coherent ce env sf (ArrayT ty bound) atv
Proof
  strip_tac >>
  qpat_assum `evaluate_type _ (ArrayT _ _) = SOME _`
    (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >> gvs[AllCaseEqs()] >>
  drule_all decoder_caller_array >> simp[]
QED

Theorem abi_caller_tuple_coherent:
  evaluate_type env (TupleT tys) = SOME tv /\
  (!tvs. LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs ==>
    LIST_REL (abi_decoder_coherent ce env sf) tys tvs) ==>
  abi_decoder_coherent ce env sf (TupleT tys) tv
Proof
  strip_tac >>
  qpat_assum `evaluate_type _ (TupleT _) = SOME _`
    (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >> gvs[AllCaseEqs()] >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  irule decoder_caller_tuple >> simp[] >> first_x_assum irule >> simp[]
QED

Theorem abi_caller_flag_metadata_coherent:
  abi_caller_metadata ce root /\ env SUBMAP root /\
  evaluate_type env (FlagT nsid) = SOME tv ==>
  abi_decoder_coherent ce env sf (FlagT nsid) tv
Proof
  strip_tac >>
  qpat_assum `evaluate_type _ (FlagT _) = SOME _`
    (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `FLOOKUP env nsid = SOME (FlagArgs members)` >>
  fs[abi_caller_metadata_def] >>
  `ce.ce_flag_n_members (nsid_to_string nsid) = members` by
    (qpat_x_assum `!env nsid n. _ ==> ce.ce_flag_n_members _ = n` irule >>
     qexists_tac `env` >> simp[]) >>
  `abi_decoder_header ce env (FlagT nsid) (FlagTV members)` by
    (qpat_x_assum `!env ty tv. _ ==> abi_decoder_header ce env ty tv` irule >> simp[]) >>
  simp[abi_decoder_coherent_flag_iff]
QED

Theorem abi_caller_struct_map_namespace:
  abi_caller_struct_map sf env /\
  FLOOKUP env nsid = SOME (StructArgs args) ==>
  FST nsid = NONE
Proof
  simp[abi_caller_struct_map_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[]
QED

(* ===== Struct ===== *)

(* Struct coherence descends through both maps. The compiler field sizes
   still refer to the complete environment, as the real builder does. *)

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

(* ===== Caller Coherence ===== *)

(* Recursive caller coherence from actual checked construction. The general
   induction carries semantic/compiler submaps through struct descent. The
   public constructed theorem assumes only namespaces, assignability and
   successful source type evaluation. *)

Theorem abi_caller_coherent_from_metadata:
  abi_caller_metadata ce root ==>
  (!env ty. !tv sf.
    evaluate_type env ty = SOME tv /\ assignable_type env ty /\
    env SUBMAP root /\ sf SUBMAP ce.ce_struct_fields /\
    abi_caller_struct_map sf env ==>
    abi_decoder_coherent ce env sf ty tv) /\
  (!env tys. !tvs sf.
    LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs /\
    EVERY (assignable_type env) tys /\
    env SUBMAP root /\ sf SUBMAP ce.ce_struct_fields /\
    abi_caller_struct_map sf env ==>
    LIST_REL (abi_decoder_coherent ce env sf) tys tvs)
Proof
  strip_tac >> ho_match_mp_tac vyper_to_abi_type_ind >>
  conj_tac >- simp[abi_decoder_base_caller_coherent] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[Once assignable_type_def] >>
      RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
      irule abi_caller_tuple_coherent >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[Once assignable_type_def] >>
      irule abi_caller_array_coherent >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[Once assignable_type_def] >>
      irule abi_caller_array_coherent >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      irule abi_caller_struct_coherent >> simp[] >>
      qexists_tac `root` >> simp[] >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `!args. FLOOKUP _ _ = SOME (StructArgs args) ==> _`
        (fn ih => drule_all ih) >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all abi_caller_flag_metadata_coherent >> simp[]) >>
  conj_tac >- simp[assignable_type_def] >>
  conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> map_every qx_gen_tac [`tvs`, `sf`] >>
  Cases_on `tvs` >> simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem abi_caller_coherent:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  assignable_type (type_env tops) ty /\ evaluate_type (type_env tops) ty = SOME tv ==>
  abi_decoder_coherent
    (build_compile_env tops vis mut func_name fargs ret_type
      (code_stmts:stmt list) use_trans) (type_env tops)
    (build_compile_env tops vis mut func_name fargs ret_type
      code_stmts use_trans).ce_struct_fields ty tv
Proof
  strip_tac >>
  `abi_caller_metadata
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans)
    (type_env tops)` by
    (irule abi_caller_constructed_metadata >> qexists_tac `in_deploy` >> simp[]) >>
  `abi_caller_struct_map
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans).
      ce_struct_fields (type_env tops)` by
    (irule abi_caller_constructed_struct_map >> qexists_tac `in_deploy` >> simp[]) >>
  drule abi_caller_coherent_from_metadata >> strip_tac >>
  first_x_assum irule >> simp[]
QED
