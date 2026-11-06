(* Checked probes for zero-footprint sources.  The actual source operand is
   retained, without an endpoint or allocation-frontier bound. *)
Theory exprSimAbiEncodeEmptySource
Ancestors
  exprSimAbiEncodePrefixWindow abiEncoderWindowLeaves
  abiEncoderSourceFootprint abiEncoderWindow abiEncoderProps abiEncoder
  valueEncoding vyperABI loweringPosts fragExec valueCopy emitHelper
  contractABI vyperTypeSystem vyperValue compileEnv emitHelperProps exprLoweringProps
  valueEncodingProofs abiDecoderMembers list rich_list valueEncodingTyping vyperTypeDefaults

Theorem abi_encode_empty_window_shape:
  abi_encoder_window_input ei at av sb 0 mem ==>
  ei = AbiCopy 0 \/ ?infos. ei = AbiComplex infos
Proof
  simp[Once abi_encoder_window_input_cases] >> rpt strip_tac >> simp[]
QED

Theorem abi_encode_empty_tuple_plan_probe:
  abi_enc_plan env (TupleT []) (AbiCopy 0) /\
  evaluate_type env (TupleT []) = SOME (TupleTV []) /\
  val_footprint (TupleTV []) (ArrayV (TupleV [])) = 0
Proof
  conj_tac
  >- (simp[Once abi_enc_plan_cases, vyper_to_abi_type_def, is_dynamic_def,
           evaluate_type_def, type_memory_size_def, type_slot_size_def, is_word_type_def]) >>
  simp[evaluate_type_def, val_footprint_def, type_memory_size_def, type_slot_size_def]
QED

Theorem abi_encode_empty_copy_frag_probe:
  compile_abi_encode_to_buf dst src (AbiCopy 0) sa = (out,sb) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME a ==>
  out = Lit 0w /\
  frag_exec ctx sa sb (\t. t = s)
    (\t. t = ((mcopy (w2n d) (w2n a) 0 s)
                  with vs_inst_idx := LENGTH sb.cs_current_insts)) (\r. F)
Proof
  simp[Once compile_abi_encode_child_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, pairTheory.pair_case_thm] >>
  strip_tac >> pairarg_tac >> gvs[] >>
  drule_all (SRULE [] (Q.INST [`n` |-> `0`] (SPEC_ALL emit_mcopy_run))) >> simp[] >> strip_tac >>
  irule frag_exec_run_inst_seq >> gvs[same_blocks_def] >> simp[]
QED

Theorem abi_encode_empty_complex_body_probe:
  compile_abi_encode_to_buf dst src (AbiComplex []) sa = (Lit 0w,sa)
Proof
  simp[Once compile_abi_encode_child_def, comp_return_def]
QED

(* The obvious ABI-dynamic empty complex plan is not a typed Vyper source:
   evaluate_type excludes fixed zero-length arrays before execution. *)
Theorem abi_encode_zero_array_excluded_probe:
  evaluate_type env (ArrayT ty (Fixed 0)) = NONE
Proof
  simp[evaluate_type_def] >> Cases_on `evaluate_type env ty` >> simp[]
QED

Theorem abi_encode_empty_copy_source_independent:
  mcopy dst src 0 s = mcopy dst other 0 s
Proof
  simp[venomExecSemanticsTheory.mcopy_def]
QED

Theorem abi_encode_nonword_zero_window_shape:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  ~is_word_type (expr_type e) /\
  abi_enc_plan (get_tenv cx) (expr_type e) ei /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
  val_footprint tv v = 0 ==>
  ei = AbiCopy 0 \/ ?infos. ei = AbiComplex infos
Proof
  strip_tac >> drule_all abi_encode_nonword_expr_window >> strip_tac >>
  irule abi_encode_empty_window_shape >> metis_tac[]
QED

Theorem abi_encode_zero_footprint_size:
  val_footprint tv v = 0 ==> type_memory_size tv = 0
Proof
  Cases_on `v` >> simp[val_footprint_def] >>
  Cases_on `tv` >> simp[] >> rename1 `BaseTV bt` >>
  Cases_on `bt` >> simp[] >> rename1 `BytesT bd` >>
  Cases_on `bd` >> simp[]
QED

Theorem abi_encode_zero_size_static_ind:
  (!env ty. !tv. evaluate_type env ty = SOME tv /\
    type_memory_size tv = 0 ==> ~is_dynamic (vyper_to_abi_type env ty)) /\
  (!env tys acc. !tvs. evaluate_types env tys acc = SOME tvs /\
    type_memory_size_list tvs = 0 ==>
    type_memory_size_list acc = 0 /\
    EVERY (\ty. ~is_dynamic (vyper_to_abi_type env ty)) tys)
Proof
  ho_match_mp_tac evaluate_type_ind >>
  conj_tac
  >- (rpt gen_tac >> Cases_on `bt` >>
      simp[evaluate_type_def, type_memory_size_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[type_memory_size_def, AllCaseEqs()] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[evaluate_type_def, type_memory_size_def, AllCaseEqs()]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[Once evaluate_type_def, AllCaseEqs(), type_memory_size_def,
           vyper_to_abi_type_def, is_dynamic_def] >>
      rpt strip_tac >> gvs[type_memory_size_def] >>
      qpat_x_assum `any_dynamic _` mp_tac >>
      simp[any_dynamic_every_static, vyper_to_abi_types_MAP, EVERY_MAP]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      Cases_on `bd` >>
      gvs[Once evaluate_type_def, AllCaseEqs(), type_memory_size_def,
          vyper_to_abi_type_def, is_dynamic_def] >>
      rpt strip_tac >> gvs[type_memory_size_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_type_def, AllCaseEqs(), type_memory_size_def] >>
      `LENGTH (MAP FST args) = LENGTH tvs` by
        (drule evaluate_types_length >> simp[]) >>
      gvs[type_memory_size_fields_zip] >>
      simp[any_dynamic_every_static, vyper_to_abi_types_MAP, EVERY_MAP]) >>
  conj_tac
  >- (simp[evaluate_type_def, AllCaseEqs(), type_memory_size_def]) >>
  conj_tac >- simp[evaluate_type_def, vyper_to_abi_type_def, is_dynamic_def] >>
  conj_tac >- simp[evaluate_type_def, type_memory_size_list_sum, MAP_REVERSE, SUM_REVERSE] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_type_def, AllCaseEqs()] >>
  gvs[type_memory_size_def]
QED

Theorem abi_encode_zero_size_static:
  evaluate_type env ty = SOME tv /\ type_memory_size tv = 0 ==>
  ~is_dynamic (vyper_to_abi_type env ty)
Proof
  metis_tac[cj 1 abi_encode_zero_size_static_ind]
QED

Theorem abi_encode_zero_footprint_plan:
  abi_enc_plan env ty ei /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  val_footprint tv v = 0 ==> ei = AbiCopy 0
Proof
  strip_tac >>
  `type_memory_size tv = 0` by metis_tac[abi_encode_zero_footprint_size] >>
  `~is_dynamic (vyper_to_abi_type env ty)` by
    metis_tac[abi_encode_zero_size_static] >>
  qpat_x_assum `abi_enc_plan _ _ _` mp_tac >>
  simp[Once abi_enc_plan_cases] >> strip_tac >> gvs[] >>
  gvs[evaluate_type_def, type_memory_size_def, AllCaseEqs(), is_word_type_def] >>
  Cases_on `ty` >>
  gvs[is_word_type_def, evaluate_type_def, type_memory_size_def,
      AllCaseEqs(), vyper_to_abi_type_def, is_dynamic_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[evaluate_type_def, type_memory_size_def, AllCaseEqs()] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[evaluate_type_def, type_memory_size_def, AllCaseEqs()]
QED

Theorem abi_encode_nonword_zero_plan:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  ~is_word_type (expr_type e) /\
  abi_enc_plan (get_tenv cx) (expr_type e) ei /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
  val_footprint tv v = 0 ==> ei = AbiCopy 0
Proof
  metis_tac[abi_encode_zero_footprint_plan]
QED
