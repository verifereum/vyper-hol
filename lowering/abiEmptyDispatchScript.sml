Theory abiEmptyDispatch
Ancestors
  valueEncodingTyping abiEmptyAggregateInput abiDecoderCoherence abiDecoderMembers
  abiDecoderMemberInfos abiDecoderStruct abiEncoderInput compileEnv exprLowering valueEncoding
  vyperABI contractABI finite_map words list rich_list pair combin arithmetic abiEmptyAllocate
  abiEmptySize abiEmptyEffect abiBuiltinAllocation abiCallerBuiltinInput builtinSimple
  exprLoweringProps compileVyper vyperTypeSystem vyperValue vyperContext venomState
  venomExecSemantics abiDecoderReentry context

(* Default struct input follows both deleted maps through recursive members. *)
Theorem abi_empty_struct_default_value:
  LENGTH args = LENGTH tvs ==>
  default_to_abi (StructTV (ZIP (MAP FST args,tvs))) = ListV (default_to_abi_list tvs)
Proof
  simp[default_to_abi_def, default_to_abi_fields_MAP, default_to_abi_list_MAP,
    MAP_MAP_o, MAP_ZIP]
QED

Theorem abi_empty_struct_memory_size:
  abi_decoder_header ce env (StructT nsid) (StructTV (ZIP (MAP FST args,tvs))) /\
  LIST_REL (abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid))
    (MAP SND args) tvs ==>
  type_memory_bytes ce (StructT nsid) = type_memory_bytes ce (TupleT (MAP SND args))
Proof
  strip_tac >> drule abi_decoder_member_infos_layout >> strip_tac >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    (imp_res_tac LIST_REL_LENGTH >> fs[]) >>
  fs[abi_decoder_header_def, type_memory_size_def, type_memory_size_fields_zip] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [type_memory_bytes_def])) >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  asm_rewrite_tac[]
QED

Theorem abi_empty_struct_descriptor:
  is_abi_dynamic ce.ce_struct_fields (StructT nsid) /\
  FLOOKUP sf (nsid_to_string nsid) = SOME fields ==>
  type_to_abi_enc_info sf ce (StructT nsid) =
    AbiComplex (MAP (\ty.
      (type_to_abi_enc_info (sf \\ nsid_to_string nsid) ce ty,
       abi_embedded_static_size ce.ce_struct_fields ty, type_memory_bytes ce ty,
       is_abi_dynamic ce.ce_struct_fields ty)) (MAP (FST o SND) fields))
Proof
  strip_tac >> asm_simp_tac (srw_ss())
    [Once type_to_abi_enc_info_def, LET_THM, MAP_MAP_o] >>
  irule MAP_CONG >> simp[FORALL_PROD, o_DEF]
QED

Theorem abi_empty_struct_default_input:
  FLOOKUP env nsid = SOME (StructArgs args) /\
  FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
  MAP (\(name,ty,sz). (name,ty)) fields = args /\
  EVERY (\(name,ty,sz). sz = type_memory_bytes ce ty) fields /\
  LIST_REL (\ty tv.
    abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid) ty tv /\
    (has_type (vyper_to_abi_type (env \\ nsid) ty) (default_to_abi tv) ==>
      abi_encoder_input (type_to_abi_enc_info (sf \\ nsid_to_string nsid) ce ty)
        (vyper_to_abi_type (env \\ nsid) ty) (default_to_abi tv)
        0 (type_memory_bytes ce ty) [])) (MAP SND args) tvs /\
  abi_decoder_header ce env (StructT nsid) (StructTV (ZIP (MAP FST args,tvs))) /\
  has_type (vyper_to_abi_type env (StructT nsid))
    (default_to_abi (StructTV (ZIP (MAP FST args,tvs)))) ==>
  abi_encoder_input (type_to_abi_enc_info sf ce (StructT nsid))
    (vyper_to_abi_type env (StructT nsid))
    (default_to_abi (StructTV (ZIP (MAP FST args,tvs))))
    0 (type_memory_bytes ce (StructT nsid)) []
Proof
  simp_tac bool_ss [LIST_REL_CONJ] >> strip_tac >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  `abi_decoder_coherent ce env sf (StructT nsid)
     (StructTV (ZIP (MAP FST args,tvs)))` by
    (irule struct_case >> asm_rewrite_tac[] >>
     qexists_tac `fields` >> asm_rewrite_tac[]) >>
  Cases_on `is_dynamic (vyper_to_abi_type env (StructT nsid))`
  >- (`is_abi_dynamic ce.ce_struct_fields (StructT nsid)` by fs[abi_decoder_header_def] >>
      `LENGTH args = LENGTH tvs` by (imp_res_tac LIST_REL_LENGTH >> fs[]) >>
      drule_all abi_empty_struct_default_value >> strip_tac >>
      drule_all abi_empty_struct_memory_size >> strip_tac >>
      drule_all abi_decoder_struct_field_types >> strip_tac >>
      `MAP (FST o SND) fields = MAP SND args` by gvs[] >>
      drule_all abi_empty_struct_descriptor >> strip_tac >>
      asm_simp_tac bool_ss [vyper_to_abi_type_def] >>
      mp_tac (Q.INST [`tys` |-> `MAP SND (args:(string # vyperAST$type) list)`,
        `tvs` |-> `tvs`,
        `env` |-> `env \\ nsid`, `sf` |-> `sf \\ nsid_to_string nsid`,
        `at` |-> `Tuple (vyper_to_abi_types (env \\ nsid)
          (MAP SND (args:(string # vyperAST$type) list)))`, `p` |-> `0`]
        abi_empty_members_zero) >>
      impl_tac
      >- (fs[abi_encoder_tuple_type_def, LIST_REL_CONJ, vyper_to_abi_type_def] >>
          CONV_TAC (DEPTH_CONV ETA_CONV) >> gvs[has_type_def]) >> simp[]) >>
  irule abi_empty_coherent_static_input >> simp[abi_empty_memory_observation]
QED

(* Complete default encoder inputs for every recursively coherent source type.
   Child ABI typing is required only when that child occurs in the value. *)
Theorem abi_empty_base_default_input:
  abi_decoder_coherent ce env sf (BaseT bt) (BaseTV bt) /\
  has_type (vyper_to_abi_type env (BaseT bt)) (default_to_abi (BaseTV bt)) ==>
  abi_encoder_input (type_to_abi_enc_info sf ce (BaseT bt))
    (vyper_to_abi_type env (BaseT bt)) (default_to_abi (BaseTV bt))
    0 (type_memory_bytes ce (BaseT bt)) []
Proof
  strip_tac >> Cases_on `is_dynamic (vyper_to_abi_type env (BaseT bt))`
  >- (Cases_on `bt` >> gvs[vyper_to_abi_type_def, is_dynamic_def] >>
      FIRST [irule (SIMP_RULE (srw_ss()) [vyper_to_abi_type_def]
          (cj 2 abi_empty_bytestring_inputs)) >> simp[abi_empty_memory_observation],
        rename1 `BytesT bound` >> Cases_on `bound` >> gvs[is_dynamic_def] >>
        irule (SIMP_RULE (srw_ss()) [vyper_to_abi_type_def]
          (cj 1 abi_empty_bytestring_inputs)) >> simp[abi_empty_memory_observation]]) >>
  irule abi_empty_coherent_static_input >> simp[abi_empty_memory_observation]
QED

Theorem abi_empty_flag_default_input:
  abi_decoder_coherent ce env sf (FlagT nsid) (FlagTV n) /\
  has_type (vyper_to_abi_type env (FlagT nsid)) (default_to_abi (FlagTV n)) ==>
  abi_encoder_input (type_to_abi_enc_info sf ce (FlagT nsid))
    (vyper_to_abi_type env (FlagT nsid)) (default_to_abi (FlagTV n))
    0 (type_memory_bytes ce (FlagT nsid)) []
Proof
  strip_tac >> irule abi_empty_coherent_static_input >>
  simp[abi_empty_memory_observation] >>
  fs[abi_decoder_coherent_flag_iff, vyper_to_abi_type_def, is_dynamic_def]
QED

Theorem abi_empty_array_default_input:
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_header ce env (ArrayT ty bound) (ArrayTV tv bound) /\
  (has_type (vyper_to_abi_type env ty) (default_to_abi tv) ==>
    abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
      (default_to_abi tv) 0 (type_memory_bytes ce ty) []) /\
  has_type (vyper_to_abi_type env (ArrayT ty bound)) (default_to_abi (ArrayTV tv bound)) ==>
  abi_encoder_input (type_to_abi_enc_info sf ce (ArrayT ty bound))
    (vyper_to_abi_type env (ArrayT ty bound)) (default_to_abi (ArrayTV tv bound))
    0 (type_memory_bytes ce (ArrayT ty bound)) []
Proof
  strip_tac >> Cases_on `bound`
  >- (irule abi_empty_fixed_default_input >> simp[abi_decoder_coherent_array_iff]) >>
  irule abi_empty_dynamic_array_input >> simp[abi_empty_memory_observation] >>
  drule abi_decoder_coherent_header >> simp[]
QED

Theorem abi_empty_recursive_default_input:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
  has_type (vyper_to_abi_type env ty) (default_to_abi tv) ==>
  abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
    (default_to_abi tv) 0 (type_memory_bytes ce ty) []
Proof
  ho_match_mp_tac abi_decoder_coherent_strongind >> rpt conj_tac
  >- (rpt strip_tac >> irule abi_empty_base_default_input >>
      simp[abi_decoder_coherent_base_iff])
  >- (rpt strip_tac >> irule abi_empty_flag_default_input >>
      simp[abi_decoder_coherent_flag_iff])
  >- (rpt strip_tac >> irule abi_empty_array_default_input >> simp[])
  >- (rpt strip_tac >> irule abi_empty_tuple_default_input >>
      fs[abi_decoder_coherent_tuple_iff, LIST_REL_CONJ] >>
      RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  rpt strip_tac >> irule abi_empty_struct_default_input >>
  asm_rewrite_tac[] >> qexists_tac `fields` >> simp[]
QED

Theorem abi_empty_default_initialized_input:
  abi_decoder_coherent ce env sf ty tv /\
  has_type (vyper_to_abi_type env ty) (default_to_abi tv) /\
  mem_bytes_at p (type_memory_bytes ce ty) mem = REPLICATE (type_memory_bytes ce ty) 0w ==>
  abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
    (default_to_abi tv) p (type_memory_bytes ce ty) mem
Proof
  strip_tac >> drule_all abi_empty_recursive_default_input >> strip_tac >>
  irule abi_empty_input_relocate >> simp[]
QED

(* Actual Empty execution establishes the recursive ABI source input.
   Count-only roots require only their initialized count word. *)
Theorem abi_empty_count_default_input:
  abi_decoder_coherent ce env sf ty tv /\
  (is_bytestring_type ty \/ (case ty of ArrayT _ (Dynamic _) => T | _ => F)) /\
  mem_bytes_at p 32 mem = REPLICATE 32 0w ==>
  abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
    (default_to_abi tv) p (type_memory_bytes ce ty) mem
Proof
  strip_tac >> Cases_on `ty` >> gvs[is_bytestring_type_def]
  >- (rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def] >>
      FIRST [gvs[abi_decoder_coherent_string_iff] >>
          irule (SIMP_RULE (srw_ss()) [vyper_to_abi_type_def]
            (cj 2 abi_empty_bytestring_inputs)) >> simp[],
        rename1 `BytesT bound` >> Cases_on `bound` >> gvs[is_bytestring_type_def] >>
        gvs[abi_decoder_coherent_bytes_iff] >>
        irule (SIMP_RULE (srw_ss()) [vyper_to_abi_type_def]
          (cj 1 abi_empty_bytestring_inputs)) >> simp[]]) >>
  rename1 `ArrayT child bound` >> Cases_on `bound` >> gvs[] >>
  gvs[abi_decoder_coherent_array_iff] >>
  irule (SIMP_RULE (srw_ss()) [vyper_to_abi_type_def]
    abi_empty_dynamic_array_input) >> simp[] >>
  drule abi_decoder_coherent_header >> simp[]
QED

Theorem abi_empty_default_producer:
  abi_decoder_coherent ce env sf ty tv /\
  has_type (vyper_to_abi_type env ty) (default_to_abi tv) /\
  length_only = (is_bytestring_type ty \/
    (case ty of ArrayT _ (Dynamic _) => T | _ => F)) /\
  compile_builtin_empty_complex (type_memory_bytes ce ty) length_only st = (buf,final) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,type_memory_bytes ce ty)) /\
  type_memory_bytes ce ty < dimword (:256) /\
  p+abi_empty_initialized_bytes (type_memory_bytes ce ty) length_only < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\
    eval_operand buf.buf_operand actual = SOME (n2w p) /\
    buf.buf_size = type_memory_bytes ce ty /\
    abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
      (default_to_abi tv) p (type_memory_bytes ce ty) actual.vs_memory /\
    abi_empty_effect st.cs_next_var p
      (abi_empty_initialized_bytes (type_memory_bytes ce ty) length_only) limit_st
      (abi_builtin_allocate_state st.cs_next_id (type_memory_bytes ce ty) initial) actual /\
    inst_extends st final
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_empty_complex_execute >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK actual` >>
  `abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
     (default_to_abi tv) p (type_memory_bytes ce ty) actual.vs_memory` by
    (Cases_on `length_only`
     >- (irule abi_empty_count_default_input >> fs[abi_empty_initialized_bytes_def]) >>
     drule abi_empty_round_coherent >> strip_tac >>
     irule abi_empty_default_initialized_input >> fs[]) >>
  qexists_tac `actual` >> asm_rewrite_tac[]
QED

(* The actual complex Empty dispatcher produces a complete recursive ABI input.
   Source memory contents are established by execution, not assumed. *)
Theorem abi_empty_dispatch_code:
  ~is_word_type ret_ty /\
  compile_type_builtin_dispatch_body cfn ce vv_ty src_ty Empty ret_ty args st = (vv,final) ==>
  ?buf. compile_builtin_empty_complex (type_memory_bytes ce ret_ty)
    (is_bytestring_type ret_ty \/ (case ret_ty of ArrayT _ (Dynamic _) => T | _ => F))
    st = (buf,final) /\ vv = LocatedValue vv_ty (base_ptr buf)
Proof
  simp_tac bool_ss [Once compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt strip_tac >>
  Cases_on `compile_builtin_empty_complex (type_memory_bytes ce ret_ty)
    (is_bytestring_type ret_ty \/ (case ret_ty of ArrayT _ (Dynamic _) => T | _ => F)) st` >>
  gvs[AllCaseEqs()]
QED

Theorem abi_empty_dispatch_input:
  let length_only = (is_bytestring_type ret_ty \/
    (case ret_ty of ArrayT _ (Dynamic _) => T | _ => F)) in
  abi_decoder_coherent ce env sf ret_ty tv /\
  has_type (vyper_to_abi_type env ret_ty) (default_to_abi tv) /\ ~is_word_type ret_ty /\
  compile_type_builtin_dispatch_body cfn ce vv_ty src_ty Empty ret_ty args st = (vv,final) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,type_memory_bytes ce ret_ty)) /\
  type_memory_bytes ce ret_ty < dimword (:256) /\
  p+abi_empty_initialized_bytes (type_memory_bytes ce ret_ty) length_only < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\
    vv_location vv = SOME LocMemory /\ eval_operand (vv_operand vv) actual = SOME (n2w p) /\
    abi_decoder_operand_live final.cs_next_var (vv_operand vv) /\
    abi_encoder_input (type_to_abi_enc_info sf ce ret_ty) (vyper_to_abi_type env ret_ty)
      (default_to_abi tv) p (type_memory_bytes ce ret_ty) actual.vs_memory /\
    abi_empty_effect st.cs_next_var p
      (abi_empty_initialized_bytes (type_memory_bytes ce ret_ty) length_only) limit_st
      (abi_builtin_allocate_state st.cs_next_id (type_memory_bytes ce ret_ty) initial) actual /\
    inst_extends st final
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_empty_dispatch_code >> strip_tac >>
  drule abi_empty_producer_operand_live >> strip_tac >>
  mp_tac (Q.INST [`ty` |-> `ret_ty`, `length_only` |->
    `is_bytestring_type ret_ty \/ (case ret_ty of ArrayT _ (Dynamic _) => T | _ => F)`]
    abi_empty_default_producer) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  qexists_tac `actual` >> gvs[vv_operand_def, vv_location_def, base_ptr_def]
QED

Theorem abi_empty_checked_dispatch_input:
  let ce = build_compile_env tops vis mut func_name fargs ret_type
    (code_stmts:stmt list) use_trans in
  let length_only = (is_bytestring_type ret_ty \/
    (case ret_ty of ArrayT _ (Dynamic _) => T | _ => F)) in
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  assignable_type (type_env tops) ret_ty /\ evaluate_type (type_env tops) ret_ty = SOME tv /\
  has_type (vyper_to_abi_type (type_env tops) ret_ty) (default_to_abi tv) /\
  ~is_word_type ret_ty /\
  compile_type_builtin_dispatch_body cfn ce vv_ty src_ty Empty ret_ty args st = (vv,final) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,type_memory_bytes ce ret_ty)) /\
  type_memory_bytes ce ret_ty < dimword (:256) /\
  p+abi_empty_initialized_bytes (type_memory_bytes ce ret_ty) length_only < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\
    vv_location vv = SOME LocMemory /\ eval_operand (vv_operand vv) actual = SOME (n2w p) /\
    abi_decoder_operand_live final.cs_next_var (vv_operand vv) /\
    abi_encoder_input (type_to_abi_enc_info ce.ce_struct_fields ce ret_ty)
      (vyper_to_abi_type (type_env tops) ret_ty) (default_to_abi tv)
      p (type_memory_bytes ce ret_ty) actual.vs_memory /\
    abi_empty_effect st.cs_next_var p
      (abi_empty_initialized_bytes (type_memory_bytes ce ret_ty) length_only) limit_st
      (abi_builtin_allocate_state st.cs_next_id (type_memory_bytes ce ret_ty) initial) actual /\
    inst_extends st final
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent
     (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans)
     (type_env tops)
     (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans).
       ce_struct_fields ret_ty tv` by
    (irule abi_caller_coherent >> asm_rewrite_tac[] >>
     qexists_tac `in_deploy` >> asm_rewrite_tac[]) >>
  drule_all (SIMP_RULE bool_ss [LET_THM] abi_empty_dispatch_input) >> simp[]
QED
