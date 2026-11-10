(* Forward coverage of encoder ids in a containing function. *)
Theory exprExtRequestEncoderWitness
Ancestors
  exprExtRequestCodeWitness exprExtRequestEncoderCode abiEncoderAppend
  abiEncoder compileEnv emitHelper abiDecoderCode localPtrsProps abiEncoderProps

val witness_simps =
  [extrequest_code_witness_return, extrequest_code_witness_emit_op,
   extrequest_code_witness_emit_void, extrequest_code_witness_emit_inst,
   extrequest_code_witness_fresh_label, extrequest_code_witness_new_block,
   extrequest_code_witness_alloc_buffer, LET_THM];

fun witness_tac extra g =
  (rpt gen_tac >> simp_tac pure_ss [LET_THM] >> BETA_TAC >>
   FIRST [FIRST_PROVE [asm_simp_tac (srw_ss()) (extra @ witness_simps)],
    first_x_assum (fn th => FIRST_PROVE
      [irule (SRULE[] th) >> asm_simp_tac (srw_ss()) []]),
    ho_match_mp_tac extrequest_code_witness_bind >> conj_tac
      >- witness_tac extra >> rpt gen_tac >> witness_tac extra,
    ho_match_mp_tac extrequest_code_witness_ignore_bind >> conj_tac >> witness_tac extra,
    IF_CASES_TAC >> fs[] >> witness_tac extra]) g;

Theorem extrequest_encoder_witness_static:
  !st. extrequest_code_witness st (SND (compile_abi_encode_static dst src st))
Proof
  rewrite_tac[compile_abi_encode_static_def] >> witness_tac []
QED

Theorem extrequest_encoder_witness_static_info:
  !dst src ei st. extrequest_code_witness st
    (SND (compile_abi_encode_static_info dst src ei st))
Proof
  rpt gen_tac >> Cases_on `ei` >>
  rewrite_tac[compile_abi_encode_static_info_def] >>
  witness_tac [extrequest_encoder_witness_static]
QED

Theorem extrequest_encoder_witness_static_loop:
  !st. extrequest_code_witness st
    (SND (compile_abi_encode_dyn_static_loop dst src ei asz msz len st))
Proof
  rewrite_tac[compile_abi_encode_dyn_static_loop_def] >>
  witness_tac [extrequest_encoder_witness_static_info]
QED

Theorem extrequest_encoder_witness_mutual:
  (!dst src ei dyn off ptr st. extrequest_code_witness st
     (SND (compile_abi_encode_child dst src ei dyn off ptr st))) /\
  (!dst src ei st. extrequest_code_witness st
     (SND (compile_abi_encode_to_buf dst src ei st))) /\
  (!dst src infos so ho ptr st. extrequest_code_witness st
     (SND (compile_abi_encode_complex_elems dst src infos so ho ptr st))) /\
  (!dst src ei asz msz len st. extrequest_code_witness st
     (SND (compile_abi_encode_dyn_loop dst src ei asz msz len st)))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt (disch_then strip_assume_tac) >>
  ONCE_REWRITE_TAC[compile_abi_encode_child_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  TRY (drule_all abi_encoder_complex_append_bindings >> strip_tac) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  witness_tac [extrequest_encoder_witness_static,
    extrequest_encoder_witness_static_loop]
QED

Theorem extrequest_encoder_function_alloca_shape:
  compile_abi_encode_to_buf dst src ei st = (len,st') /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_id IN frag_ids st st' /\
  inst.inst_opcode = ALLOCA ==>
  inst.inst_operands = [Lit 32w] /\ ?out. inst.inst_outputs = [out]
Proof
  strip_tac >>
  `extrequest_code_witness st st'` by
    metis_tac[cj 2 extrequest_encoder_witness_mutual, pairTheory.SND] >>
  fs[extrequest_code_witness_def, frag_ids_def] >>
  first_x_assum drule_all >> strip_tac >>
  drule_all fn_inst_ids_distinct_inj >> strip_tac >>
  gvs[abi_decoder_alloc_shape_def]
QED

Theorem extrequest_encoder_function_alloca_output:
  compile_abi_encode_to_buf dst src ei st = (len,en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_id IN frag_ids st en /\
  inst.inst_opcode = ALLOCA ==>
  ?n. inst.inst_outputs = [STRING #"%" (toString n)] /\ st.cs_next_var <= n
Proof
  strip_tac >>
  `extrequest_code_witness st en` by
    metis_tac[cj 2 extrequest_encoder_witness_mutual, pairTheory.SND] >>
  fs[extrequest_code_witness_def, frag_ids_def] >>
  first_x_assum drule_all >> strip_tac >>
  drule_all fn_inst_ids_distinct_inj >> strip_tac >> gvs[]
QED

Theorem extrequest_encoder_function_alloca_not_local:
  compile_abi_encode_to_buf dst src ei st = (len,en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_id IN frag_ids st en /\
  inst.inst_opcode = ALLOCA /\ local_ptrs_reserved cenv st ==>
  ?out. inst.inst_outputs = [out] /\ not_local_ptr cenv scopes out
Proof
  strip_tac >> drule_all extrequest_encoder_function_alloca_output >> strip_tac >>
  qexists `STRING #"%" (toString n)` >> simp[] >>
  irule exprLoweringPropsTheory.local_ptrs_reserved_fresh >> metis_tac[]
QED
