Theory abiCallerBuiltinInput
Ancestors
  abiCallerMetadata abiCallerStructMap abiDecoderConstructors abiDecoderCoherence
  abiDecoderPrimitiveCaller compileEnv vyperValue vyperABI vyperTypeABI finite_map list pair
  vyperTypeSystem combin compileVyper vyperContext abiCallerAbiShape abiValidAggregateHeads
  abiValidMembers abiDecodeRanges vyperABIValid contractABI arithmetic abiBuiltinPrefixSource
  abiBuiltinPrefixInput abiValidPrefixSource abiBuiltinSource abiBuiltinDecodeEffect
  abiDecoderContract abiDecoderLoop abiDecoderReentry valueEncoding abiEncoder builtinAbi
  fragExec venomState words abiBuiltinCanonicalPre

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

(* Source validity supplies the actual compiler minimum-length guard.
   Dynamic member offsets use validity's head extents, including empty fixed arrays. *)
Theorem abi_caller_embedded_head:
  abi_caller_abi_shape sf env ty ==>
  abi_embedded_static_size sf ty = abi_member_head_size (vyper_to_abi_type env ty)
Proof
  Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
  simp[abi_caller_abi_shape_def, abi_embedded_static_size_def, abi_member_head_size_def]
QED

Theorem abi_caller_members_head:
  !tys. EVERY (abi_caller_abi_shape sf env) tys ==>
  MAP (\ty. if is_abi_dynamic sf ty then 32 else abi_static_size sf ty) tys =
    MAP abi_member_head_size (vyper_to_abi_types env tys)
Proof
  Induct_on `tys` >> simp[vyper_to_abi_type_def] >>
  qx_gen_tac `elem_ty` >> strip_tac >>
  `abi_embedded_static_size sf elem_ty =
    abi_member_head_size (vyper_to_abi_type env elem_ty)` by
    (irule abi_caller_embedded_head >> simp[]) >>
  fs[abi_embedded_static_size_def]
QED

Theorem abi_caller_decode_minimum_fixed:
  abi_caller_abi_shape sf env ty /\
  valid_enc (vyper_to_abi_type env (ArrayT ty (Fixed n))) bs ==>
  abi_static_size sf (ArrayT ty (Fixed n)) <= LENGTH bs
Proof
  strip_tac >> drule abi_caller_embedded_head >> strip_tac >>
  qpat_x_assum `valid_enc _ _` mp_tac >>
  simp_tac bool_ss [Once vyper_to_abi_type_def, Once valid_enc_def, LET_THM] >>
  strip_tac >> drule abi_valid_array_heads >> strip_tac >>
  asm_simp_tac bool_ss [Once abi_static_size_def, GSYM abi_embedded_static_size_def]
QED

Theorem abi_caller_decode_minimum_tuple:
  EVERY (abi_caller_abi_shape sf env) tys /\
  valid_enc (vyper_to_abi_type env (TupleT tys)) bs ==>
  abi_static_size sf (TupleT tys) <= LENGTH bs
Proof
  strip_tac >> drule abi_caller_members_head >> strip_tac >>
  `valid_enc (Tuple (vyper_to_abi_types env tys)) bs` by
    fs[Once vyper_to_abi_type_def] >>
  drule abi_valid_tuple_view >> strip_tac >>
  asm_simp_tac bool_ss [Once abi_static_size_def]
QED

Theorem abi_caller_decode_minimum_struct:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
  MAP (\(name,ty,sz). (name,ty)) fields = args /\
  EVERY (abi_caller_abi_shape (sf \\ nsid_to_string nsid) (env \\ nsid))
    (MAP SND args) /\
  valid_enc (vyper_to_abi_type env (StructT nsid)) bs ==>
  abi_static_size sf (StructT nsid) <= LENGTH bs
Proof
  strip_tac >> drule_all abi_caller_struct_map_field_types >> strip_tac >>
  drule abi_caller_members_head >> strip_tac >>
  `valid_enc (Tuple (vyper_to_abi_types (env \\ nsid) (MAP SND args))) bs` by
    (qpat_assum `valid_enc (vyper_to_abi_type env (StructT nsid)) bs`
       (mp_tac o ONCE_REWRITE_RULE [vyper_to_abi_type_def]) >>
     asm_simp_tac (srw_ss()) [Excl "valid_enc_def", Excl "dec_def"]) >>
  drule abi_valid_tuple_view >> strip_tac >>
  asm_simp_tac (srw_ss()) [Once abi_static_size_def, LET_THM]
QED

Theorem abi_caller_decode_minimum_array_eval:
  evaluate_type env (ArrayT ty bound) = SOME tv /\
  abi_caller_struct_map sf env /\
  valid_enc (vyper_to_abi_type env (ArrayT ty bound)) bs ==>
  abi_static_size sf (ArrayT ty bound) <= LENGTH bs
Proof
  strip_tac >> Cases_on `bound`
  >- (qpat_x_assum `evaluate_type _ _ = _` mp_tac >>
      simp_tac bool_ss [Once evaluate_type_def, LET_THM] >> strip_tac >>
      gvs[AllCaseEqs(), Excl "valid_enc_def", Excl "dec_def", Excl "vyper_to_abi_type_def"] >>
      drule_all (cj 1 abi_caller_abi_shape_induction) >> strip_tac >>
      drule_all abi_caller_decode_minimum_fixed >> simp[]) >>
  simp[abi_static_size_def]
QED

Theorem abi_caller_decode_minimum_tuple_eval:
  evaluate_type env (TupleT tys) = SOME tv /\ abi_caller_struct_map sf env /\
  valid_enc (vyper_to_abi_type env (TupleT tys)) bs ==>
  abi_static_size sf (TupleT tys) <= LENGTH bs
Proof
  strip_tac >> qpat_x_assum `evaluate_type _ _ = _` mp_tac >>
  simp_tac bool_ss [Once evaluate_type_def, LET_THM] >> strip_tac >>
  gvs[AllCaseEqs(), Excl "valid_enc_def", Excl "dec_def", Excl "vyper_to_abi_type_def"] >>
  drule_all (cj 2 abi_caller_abi_shape_induction) >> strip_tac >>
  drule_all abi_caller_decode_minimum_tuple >> simp[]
QED

Theorem abi_caller_decode_minimum_struct_eval:
  evaluate_type env (StructT nsid) = SOME tv /\ abi_caller_struct_map sf env /\
  valid_enc (vyper_to_abi_type env (StructT nsid)) bs ==>
  abi_static_size sf (StructT nsid) <= LENGTH bs
Proof
  strip_tac >> qpat_x_assum `evaluate_type _ _ = _` mp_tac >>
  simp_tac bool_ss [Once evaluate_type_def, LET_THM] >> strip_tac >>
  gvs[AllCaseEqs(), Excl "valid_enc_def", Excl "dec_def", Excl "vyper_to_abi_type_def"] >>
  rename1 `FLOOKUP env nsid = SOME (StructArgs args)` >>
  drule_all abi_caller_struct_map_namespace >> strip_tac >>
  `abi_caller_struct_map (sf \\ nsid_to_string nsid) (env \\ nsid)` by
    (Cases_on `nsid` >> gvs[nsid_to_string_def] >>
     irule abi_caller_struct_map_delete >> simp[]) >>
  drule_all (cj 2 abi_caller_abi_shape_induction) >> strip_tac >>
  drule_all abi_caller_struct_map_lookup >> strip_tac >>
  drule_all abi_caller_decode_minimum_struct >> simp[]
QED

Theorem abi_caller_decode_minimum_base:
  static_length (vyper_to_abi_type env (BaseT bt)) <= LENGTH bs ==>
  abi_static_size (sf:string |-> (string # vyperAST$type # num) list) (BaseT bt) <= LENGTH bs
Proof
  Cases_on `bt` >>
  FIRST [rename1 `BytesT bound` >> Cases_on `bound`, all_tac] >>
  simp[abi_static_size_def, vyper_base_to_abi_type_def, vyper_to_abi_type_def]
QED

Theorem abi_caller_decode_minimum:
  evaluate_type env ty = SOME tv /\ abi_caller_struct_map sf env /\
  vyper_valid_enc env ty bs ==>
  abi_static_size sf ty <= LENGTH bs
Proof
  strip_tac >> drule vyper_valid_enc_valid_enc >> strip_tac >>
  drule vyper_valid_enc_length_lower >> strip_tac >>
  Cases_on `ty` >>
  FIRST [drule_all abi_caller_decode_minimum_array_eval >> simp[],
    drule_all abi_caller_decode_minimum_tuple_eval >> simp[],
    drule_all abi_caller_decode_minimum_struct_eval >> simp[],
    drule_all abi_caller_decode_minimum_base >>
      disch_then (qspec_then `sf` ACCEPT_TAC),
    fs[abi_static_size_def]]
QED

Theorem abi_caller_source_decode_minimum:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  evaluate_type (type_env tops) ty = SOME tv /\
  evaluate_abi_decode (type_env tops) ty bs = INL v ==>
  abi_static_size
    (build_compile_env tops vis mut func_name fargs ret_type
      (code_stmts:stmt list) use_trans).ce_struct_fields ty <= LENGTH bs
Proof
  strip_tac >> drule evaluate_abi_decode_vyper_valid_enc >> strip_tac >>
  `abi_caller_struct_map
    (build_compile_env tops vis mut func_name fargs ret_type
      code_stmts use_trans).ce_struct_fields (type_env tops)` by
    (irule abi_caller_constructed_struct_map >>
     qexists_tac `in_deploy` >> asm_simp_tac bool_ss []) >>
  drule_all abi_caller_decode_minimum >> simp[]
QED

(* Checked environment construction establishes the metadata of prefix-consuming
   decoding. Source validity supplies the prefix, with numeric resources separate. *)
Theorem abi_caller_prefix_pre:
  let ce = build_compile_env tops vis mut func_name fargs ret_type
    (code_stmts:stmt list) use_trans in
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  assignable_type (type_env tops) ty /\ evaluate_type (type_env tops) ty = SOME tv /\
  evaluate_abi_decode (type_env tops) ty bs = INL v /\
  (~is_dynamic (vyper_to_abi_type (type_env tops) ty) \/
    ?elem. vyper_to_abi_type (type_env tops) ty = Array NONE elem /\ ~is_dynamic elem) /\
  val_in_memory (BaseTV (BytesT (Dynamic input_bound))) (vyperValue$BytesV bs) p s.vs_memory /\
  eval_operand data s = SOME (n2w p) /\ abi_decoder_operand_live st.cs_next_var data /\
  abi_builtin_decode_resources st first last min_size max_size (type_memory_bytes ce ty)
    (LENGTH bs) p d b cap s ==>
  abi_builtin_prefix_pre ce (type_env tops) ce.ce_struct_fields ty tv bs
    (dec (vyper_to_abi_type (type_env tops) ty) bs) v st
    first last data min_size max_size p d b cap s
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans)
    (type_env tops)
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans).ce_struct_fields
    ty tv` by
    (irule abi_caller_coherent >> asm_simp_tac bool_ss [] >>
     qexists_tac `in_deploy` >> asm_simp_tac bool_ss []) >>
  drule_all abi_builtin_prefix_pre_valid_source >> simp[]
QED

Theorem lower_abi_decode_checked_prefix_source:
  let ce = build_compile_env tops vis mut func_name fargs ret_type
    (code_stmts:stmt list) use_trans in
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  assignable_type (type_env tops) ty /\ evaluate_type (type_env tops) ty = SOME tv /\
  evaluate_abi_decode (type_env tops) ty bs = INL v /\
  (~is_dynamic (vyper_to_abi_type (type_env tops) ty) \/
    ?elem. vyper_to_abi_type (type_env tops) ty = Array NONE elem /\ ~is_dynamic elem) /\
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty) min_size max_size
    (type_memory_bytes ce ty) start = (out,final) /\ fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  val_in_memory (BaseTV (BytesT (Dynamic input_bound))) (vyperValue$BytesV bs) src_base initial.vs_memory /\
  eval_operand data initial = SOME (n2w src_base) /\ abi_decoder_operand_live start.cs_next_var data /\
  abi_builtin_decode_resources start first last min_size max_size (type_memory_bytes ce ty)
    (LENGTH bs) src_base d b cap initial /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w d) /\ val_in_memory tv v d actual.vs_memory /\
    abi_builtin_decode_effect first last start final limit_st d (type_memory_bytes ce ty)
      b cap initial actual /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all (SIMP_RULE bool_ss [LET_THM] abi_caller_prefix_pre) >> strip_tac >>
  drule_all lower_abi_decode_prefix >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* Establish the existing builtin decoder input contract from actual checked
   construction. Canonical bytes and numerical allocator resources remain
   explicit until the separate resource-history proof establishes them. *)
Theorem abi_caller_source_metadata:
  let ce = build_compile_env tops vis mut func_name fargs ret_type
    (code_stmts:stmt list) use_trans in
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  assignable_type (type_env tops) ty /\ evaluate_type (type_env tops) ty = SOME tv /\
  evaluate_abi_decode (type_env tops) ty bs = INL v ==>
  abi_decoder_metadata ce (type_env tops) ty tv
    (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (dec (vyper_to_abi_type (type_env tops) ty) bs) v
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `abi_decoder_coherent
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans)
    (type_env tops)
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans).
      ce_struct_fields ty tv` by
    (irule abi_caller_coherent >> simp[] >> qexists_tac `in_deploy` >> simp[]) >>
  drule_all abi_builtin_source_metadata >> simp[]
QED

Theorem abi_caller_canonical_pre:
  let ce = build_compile_env tops vis mut func_name fargs ret_type
    (code_stmts:stmt list) use_trans in
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  assignable_type (type_env tops) ty /\ evaluate_type (type_env tops) ty = SOME tv /\
  evaluate_abi_decode (type_env tops) ty bs = INL v /\
  bs = enc (vyper_to_abi_type (type_env tops) ty)
    (dec (vyper_to_abi_type (type_env tops) ty) bs) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) p s.vs_memory /\
  eval_operand data s = SOME (n2w p) /\ abi_decoder_operand_live st.cs_next_var data /\
  abi_builtin_decode_resources st first last min_size max_size (type_memory_bytes ce ty)
    (LENGTH bs) p d b cap s ==>
  abi_builtin_canonical_pre ce (type_env tops) ce.ce_struct_fields ty tv
    (dec (vyper_to_abi_type (type_env tops) ty) bs) v st
    first last data min_size max_size p d b cap s
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `abi_decoder_coherent
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans)
    (type_env tops)
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans).
      ce_struct_fields ty tv` by
    (irule abi_caller_coherent >> simp[] >> qexists_tac `in_deploy` >> simp[]) >>
  drule_all abi_builtin_canonical_pre_from_source >> simp[]
QED
