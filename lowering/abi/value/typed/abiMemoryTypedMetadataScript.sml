(* TOP-LEVEL: evaluated source types determine the actual compiler encoder's
   static dispatcher width. Source environment restriction preserves the
   global metadata correspondence used for strides and ABI dynamic flags. *)
Theory abiMemoryTypedMetadata
Ancestors
  abiMemoryEncoding abiTypeShape typeLayoutProps exprLowering compileEnv
  valueEncoding vyperABI vyperValue vyperTyping vyperTypeValues
  vyperTypeExprSoundness finite_map list pair words

Theorem abi_struct_env_rel_submap:
  !tenv global_env sfields.
    abi_struct_env_rel global_env sfields /\ tenv SUBMAP global_env ==>
    abi_struct_env_rel tenv sfields
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [abi_struct_env_rel_def] >>
  MAP_EVERY qx_gen_tac [`nsid`, `args`] >> DISCH_TAC >>
  `FLOOKUP global_env nsid = SOME (StructArgs args)` by
    (drule_all FLOOKUP_SUBMAP >> simp[]) >>
  drule_all abi_struct_env_rel_lookup >> simp[]
QED

Definition abi_memory_env_rel_def:
  abi_memory_env_rel tenv cenv <=>
    abi_struct_env_rel tenv cenv.ce_struct_fields /\
    !ty tv. evaluate_type tenv ty = SOME tv ==> type_memory_bytes cenv ty = type_memory_size tv
End

Theorem abi_memory_env_rel_domsub:
  !tenv cenv nsid.
    abi_memory_env_rel tenv cenv ==> abi_memory_env_rel (tenv \\ nsid) cenv
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_memory_env_rel_def] >> strip_tac >> conj_tac
  >- (qspecl_then [`tenv \\ nsid`, `tenv`, `cenv.ce_struct_fields`]
        mp_tac abi_struct_env_rel_submap >> simp[]) >>
  rpt gen_tac >> DISCH_TAC >> drule (CONJUNCT1 evaluate_type_mono) >> DISCH_TAC >>
  first_x_assum drule_all >> simp[]
QED

Theorem abi_memory_env_rel_tops:
  !tops cenv.
    struct_args_unique tops /\ cenv.ce_struct_fields = make_struct_fields_map tops ==>
    abi_memory_env_rel (type_env tops) cenv
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [abi_memory_env_rel_def] >> conj_tac
  >- (drule abi_struct_env_rel_tops >> simp[]) >>
  rpt strip_tac >> drule_all type_memory_bytes_evaluated >> simp[]
QED

Theorem evaluated_static_encoder_info:
  !tenv sfields cenv ty tv.
    abi_struct_env_rel tenv cenv.ce_struct_fields /\ evaluate_type tenv ty = SOME tv /\
    ~is_dynamic (vyper_to_abi_type tenv ty) /\ type_memory_bytes cenv ty = type_memory_size tv ==>
    type_to_abi_enc_info sfields cenv ty =
      (if ty = NoneT then AbiComplex [] else AbiCopy (type_memory_size tv))
Proof
  rpt gen_tac >> strip_tac >> drule_all (CONJUNCT1 abi_type_dynamic_joint) >> DISCH_TAC >>
  Cases_on `ty` >> gvs[Once type_to_abi_enc_info_def] >>
  FIRST [
    rename1 `BaseT bt` >> Cases_on `bt` >>
    gvs[type_to_abi_enc_info_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def] >>
    rename1 `BytesT byte_bound` >> Cases_on `byte_bound` >>
    gvs[type_to_abi_enc_info_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def],
    rename1 `ArrayT elem_ty array_bound` >> Cases_on `array_bound` >>
    gvs[type_to_abi_enc_info_def, is_abi_dynamic_def]]
QED

Theorem evaluated_static_encoder_size:
  !tenv sfields cenv ty tv.
    abi_struct_env_rel tenv cenv.ce_struct_fields /\ evaluate_type tenv ty = SOME tv /\
    ~is_dynamic (vyper_to_abi_type tenv ty) /\ type_memory_bytes cenv ty = type_memory_size tv ==>
    abi_static_encoder_size (type_to_abi_enc_info sfields cenv ty) = type_memory_size tv
Proof
  rpt gen_tac >> strip_tac >> drule_all evaluated_static_encoder_info >> DISCH_TAC >>
  Cases_on `ty = NoneT` >> gvs[abi_static_encoder_size_def, evaluate_type_def, type_memory_size_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed typed ABI memory metadata: " ^ name)
  end) (DB.thms "abiMemoryTypedMetadata")
