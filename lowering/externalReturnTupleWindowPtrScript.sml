(* Compiler plan coherence for normalized bytes/string tuple windows. *)
Theory externalReturnTupleWindowPtr
Ancestors abiEncoderTupleWindowSource returnMetadataPtr abiDecoderMembers


Theorem bytestring_abi_plans_members[local]:
  !ts infos tvs.
  EVERY (\t. (?k. t = BaseT (BytesT (Dynamic k))) \/
             (?k. t = BaseT (StringT k))) ts /\
  LIST_REL (\t tv. evaluate_type env t = SOME tv) ts tvs /\
  abi_enc_plans env ts infos ==>
  LENGTH infos = LENGTH ts /\ LENGTH tvs = LENGTH ts /\
  (!i. i < LENGTH ts ==>
    (?k. EL i ts = BaseT (BytesT (Dynamic k)) /\
      vyper_to_abi_type env (EL i ts) = Bytes NONE /\
      EL i infos = (AbiBytestring k,32,type_memory_size (EL i tvs),T)) \/
    (?k. EL i ts = BaseT (StringT k) /\
      vyper_to_abi_type env (EL i ts) = String /\
      EL i infos = (AbiBytestring k,32,type_memory_size (EL i tvs),T)))
Proof
  Induct >> rpt gen_tac >>
  simp[Once abiEncoderPropsTheory.abi_enc_plan_cases] >> strip_tac >> gvs[] >>
  qpat_x_assum `abi_enc_plan _ _ _` mp_tac >>
  simp[Once abiEncoderPropsTheory.abi_enc_plan_cases,
    compileEnvTheory.is_word_type_def, vyperABITheory.vyper_to_abi_type_def,
    contractABITheory.is_dynamic_def] >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >> simp[contractABITheory.is_dynamic_def] >>
  Cases_on `i` >> gvs[]
QED

Theorem abi_plan_tuple_bytes_robust_window:
  ts <> [] /\
  EVERY (\t. (?k. t = BaseT (BytesT (Dynamic k))) \/
             (?k. t = BaseT (StringT k))) ts /\
  evaluate_type env (TupleT ts) = SOME (TupleTV tvs) /\
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
  abi_enc_plan env (TupleT ts) ei /\ vyper_to_abi_list env ts vs = SOME avs /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) b mem) ==>
  !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_window_input ei (vyper_to_abi_type env (TupleT ts)) (ListV avs)
      b (SUM (MAP type_memory_size tvs)) mem
Proof
  strip_tac >>
  `is_dynamic (vyper_to_abi_type env (TupleT ts))` by
    (Cases_on `ts` >> gvs[] >>
     simp[vyperABITheory.vyper_to_abi_type_def, contractABITheory.is_dynamic_def] >>
     gvs[vyperABITheory.vyper_to_abi_type_def, contractABITheory.is_dynamic_def]) >>
  qpat_x_assum `abi_enc_plan _ _ _` mp_tac >>
  simp[Once abiEncoderPropsTheory.abi_enc_plan_cases, compileEnvTheory.is_word_type_def] >>
  strip_tac >> gvs[] >>
  drule vyperTypeValuesTheory.evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
  drule_all bytestring_abi_plans_members >> strip_tac >>
  rpt strip_tac >>
  irule (SRULE [] abi_encoder_tuple_bytes_robust_window_source) >>
  qexistsl_tac [`env`, `s`, `tn`, `ts`, `vs`] >>
  simp[vyperABITheory.vyper_to_abi_type_def,
    abiDecoderMembersTheory.vyper_to_abi_types_MAP] >>
  `LENGTH vs = LENGTH ts /\
   (!i. i < LENGTH ts ==> value_has_type (EL i tvs) (EL i vs))` by
    fs[vyperTypingTheory.value_has_type_def,
      abiTupleValueEncodingTheory.abi_values_have_types, listTheory.LIST_REL_EL_EQN] >>
  simp[] >> rpt strip_tac >>
  fs[listTheory.LIST_REL_EL_EQN] >>
  qpat_x_assum `!i. i < LENGTH ts ==> (_ \/ _)` (qspec_then `i` mp_tac) >>
  simp[listTheory.EL_MAP]
QED

Theorem abi_window_singleton_wrap[local]:
  abi_encoder_window_input ei at av b cap mem /\ cap <= memsz ==>
  abi_encoder_window_input
    (AbiComplex [(ei,abi_member_head_size at,memsz,is_dynamic at)])
    (Tuple [at]) (ListV [av]) b cap mem
Proof
  strip_tac >>
  simp[abiEncoderWindowTheory.abi_encoder_window_complex_iff,
    abiEncoderInputTheory.abi_encoder_tuple_type_def] >>
  qexists_tac `cap` >> simp[abiEncoderInputTheory.abi_encoder_member_span_def]
QED

Theorem abi_plan_tuple_bytes_external_window:
  ts <> [] /\
  EVERY (\t. (?k. t = BaseT (BytesT (Dynamic k))) \/
             (?k. t = BaseT (StringT k))) ts /\
  evaluate_type env (TupleT ts) = SOME (TupleTV tvs) /\
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
  abi_enc_plan env
    (if needs_external_call_wrap (TupleT ts) then TupleT [TupleT ts] else TupleT ts) ei /\
  vyper_to_abi_list env ts vs = SOME avs /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) b mem) ==>
  !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_window_input ei
      (if needs_external_call_wrap (TupleT ts) then Tuple [vyper_to_abi_type env (TupleT ts)]
       else vyper_to_abi_type env (TupleT ts))
      (if needs_external_call_wrap (TupleT ts) then ListV [ListV avs] else ListV avs)
      b (SUM (MAP type_memory_size tvs)) mem
Proof
  strip_tac >>
  Cases_on `needs_external_call_wrap (TupleT ts)` >> gvs[]
  >- suspend "wrapped" >>
  rpt strip_tac >> drule_all abi_plan_tuple_bytes_robust_window >> simp[]
QED

Resume abi_plan_tuple_bytes_external_window[wrapped]:
  `is_dynamic (vyper_to_abi_type env (TupleT ts))` by
    (Cases_on `ts` >> gvs[] >>
     gvs[vyperABITheory.vyper_to_abi_type_def, contractABITheory.is_dynamic_def]) >>
  qpat_x_assum `abi_enc_plan _ _ _` mp_tac >>
  simp[Once abiEncoderPropsTheory.abi_enc_plan_cases, compileEnvTheory.is_word_type_def,
    vyperABITheory.vyper_to_abi_type_def, contractABITheory.is_dynamic_def] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `abi_enc_plans _ _ _` mp_tac >>
  simp[Once abiEncoderPropsTheory.abi_enc_plan_cases] >> strip_tac >> gvs[] >>
  qpat_x_assum `abi_enc_plans _ [] _` mp_tac >>
  simp[Once abiEncoderPropsTheory.abi_enc_plan_cases] >> strip_tac >> gvs[] >>
  rpt strip_tac >>
  `abi_encoder_window_input ei (vyper_to_abi_type env (TupleT ts)) (ListV avs)
     b (SUM (MAP type_memory_size tvs)) mem` by
    (drule_all abi_plan_tuple_bytes_robust_window >> simp[]) >>
  `type_memory_size (TupleTV tvs) = SUM (MAP type_memory_size tvs)` by
    simp[valueEncodingTheory.type_memory_size_def,
      valueEncodingProofsTheory.type_memory_size_list_sum] >>
  drule abi_window_singleton_wrap >>
  disch_then (qspec_then `type_memory_size (TupleTV tvs)` mp_tac) >>
  simp[abiDecodeRangesTheory.abi_member_head_size_def,
    vyperABITheory.vyper_to_abi_type_def, contractABITheory.is_dynamic_def]
QED
Finalise abi_plan_tuple_bytes_external_window

Theorem external_frame_tuple_bytes_robust_window:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,defaults,TupleT ts,(fbody:stmt list))) =
      (lbl,cenv0,pos,cds,payable,nr',key,ut,view,body',rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv,sa) /\
  same_frame cenv next /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  assignable_type (type_env tops) (TupleT ts) /\ ts <> [] /\
  EVERY (\t. (?k. t = BaseT (BytesT (Dynamic k))) \/
             (?k. t = BaseT (StringT k))) ts /\
  evaluate_type (type_env tops) (TupleT ts) = SOME (TupleTV tvs) /\
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
  vyper_to_abi_list (type_env tops) ts vs = SOME avs /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) b mem) ==>
  !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_window_input next.ce_ret_enc_info
      (if needs_external_call_wrap (TupleT ts)
       then Tuple [vyper_to_abi_type (type_env tops) (TupleT ts)]
       else vyper_to_abi_type (type_env tops) (TupleT ts))
      (if needs_external_call_wrap (TupleT ts) then ListV [ListV avs] else ListV avs)
      b (SUM (MAP type_memory_size tvs)) mem
Proof
  rpt strip_tac >>
  `TupleT ts <> NoneT` by simp[] >>
  drule_all external_frame_ret_abi_plan >> strip_tac >>
  `is_dynamic (vyper_to_abi_type (type_env tops) (TupleT ts))` by
    (Cases_on `ts` >> gvs[] >>
     gvs[vyperABITheory.vyper_to_abi_type_def, contractABITheory.is_dynamic_def]) >>
  qpat_x_assum `abi_enc_plan _ _ _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all abi_plan_tuple_bytes_external_window >> simp[]
QED
