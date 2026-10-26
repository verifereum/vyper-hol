(* TOP-LEVEL: empty complex decoding checks only the inline head position;
   an evaluated zero-length fixed array has its value in every memory. *)
Theory abiDecoderEmpty
Ancestors
  abiDecoderCoherence abiDecoderOffset abiDecoderComplexHead abiDecoderTypedContract abiDecoderContract
  abiEncoder compileEnv emitHelper valueEncoding vyperABI vyperValue
  contractABI venomState venomExecSemantics words list

Theorem abi_decode_empty_complex_phases:
  compile_abi_decode_to_buf dst src opc hi (DecComplex dynamic []) =
    abi_decode_complex_head_guard src hi 0
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [compile_abi_decode_to_buf_def])) >>
  Cases_on `hi = Lit 0w` >>
  simp[FUN_EQ_THM, abi_decode_complex_head_guard_def,
    abiDecoderGuardLETheory.abi_decode_le_guard_def,
    compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_decode_empty_complex_sequence:
  compile_abi_decode_to_buf dst src opc hi (DecComplex dynamic []) st = ((),st') /\
  eval_operand src s = SOME (n2w sb) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi s = SOME (n2w hb) /\
                      sb <= hb /\ hb < dimword (:256)) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  simp_tac bool_ss [abi_decode_empty_complex_phases] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`head_sz` |-> `0:num`] abi_decode_complex_head_guard_sequence) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> simp[]
QED

Theorem abi_decoder_empty_fixed_array_value:
  abi_decoder_coherent ce env sf (ArrayT ty (Fixed 0)) (ArrayTV tv (Fixed 0)) ==>
  type_memory_bytes ce (ArrayT ty (Fixed 0)) = 0 /\
  (!bs. abi_to_vyper env (ArrayT ty (Fixed 0))
    (dec (vyper_to_abi_type env (ArrayT ty (Fixed 0))) bs) =
      SOME (ArrayV (SArrayV []))) /\
  (!d mem. val_in_memory (ArrayTV tv (Fixed 0)) (ArrayV (SArrayV [])) d mem)
Proof
  strip_tac >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  `evaluate_type env ty = SOME tv` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  simp[type_memory_bytes_def, vyper_to_abi_type_def, dec_def, abi_to_vyper_def,
    compatible_bound_def, make_array_value_def, enumerate_static_array_def,
    val_in_memory_def]
QED

Theorem abi_decoder_empty_descriptor_value:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecComplex T [] /\
  abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) = SOME v ==>
  type_memory_bytes ce ty = 0 /\ (!d mem. val_in_memory tv v d mem)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  gvs[abi_decoder_empty_dynamic_translation] >>
  qpat_assum `abi_decoder_coherent _ _ _ _ _`
    (mp_tac o PURE_REWRITE_RULE [abi_decoder_coherent_array_iff]) >>
  strip_tac >> gvs[] >>
  drule abi_decoder_empty_fixed_array_value >> strip_tac >>
  gvs[]
QED

Theorem abi_decoder_empty_metadata_value:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecComplex T [] /\
  abi_decoder_metadata ce env ty tv parent_di av v ==>
  type_memory_bytes ce ty = 0 /\ (!d mem. val_in_memory tv v d mem)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  gvs[abi_decoder_empty_dynamic_translation, abi_decoder_coherent_array_iff] >>
  rename1 `abi_decoder_coherent ce env sf elem elem_tv` >>
  `evaluate_type env elem = SOME elem_tv` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  qpat_x_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  Cases_on `av` >> gvs[vyper_to_abi_type_def, has_type_def, valid_length_def] >>
  gvs[abi_to_vyper_def, compatible_bound_def, make_array_value_def,
    enumerate_static_array_def, type_memory_bytes_def, val_in_memory_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_EMPTY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI empty decoder fact not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderEmpty");
