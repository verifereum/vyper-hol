(* Pure compilation, metadata and pointer premises shared by finite-loop proofs. *)
Theory abiDecoderPrimitiveLoopContext
Ancestors
  abiDecoderPrimitiveLoopInvariant abiDecoderArrayInvariant abiDecoderArrayAdvance
  abiDecoderPrimitiveLoopFragment abiDecoderCoherence abiDecoderTypedContract
  abiDecoderContract abiDecoderReentry abiDecoderExecution fragExec
  exprLoweringProps emitHelperProps compileEnv valueEncoding vyperABI
  venomState contractABI words list arithmetic
Libs
  Omega

Definition abi_decoder_primitive_loop_compiled_def:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc hi clamp
      hdr exit_lbl hid first iv limit_st <=>
    abi_decode_array_element_setup ip src dst opc hi (DecPrimWord clamp) 32 32
      st0 = (ops,middle) /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi (DecPrimWord clamp)
      middle = ((),st1) /\
    abi_decoder_primitive_loop_code fn st0 st1 ops ip src opc hdr exit_lbl hid first iv /\
    st1.cs_next_var < limit_st.cs_next_var
End

Definition abi_decoder_primitive_loop_data_def:
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot fp <=>
    abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
    abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
      (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)))
      (ListV avs) (ArrayV (DynArrayV vs)) /\
    type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\ abi_decode_source_opcode opc /\
    sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
    d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256) /\
    slot < dimword (:256) /\
    (slot + 32 <= d \/ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= slot) /\
    (opc = MLOAD ==>
      (sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <= d \/
        d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= sb) /\
      (sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <= slot \/
        slot + 32 <= sb)) /\
    MEM (d,type_memory_bytes ce (ArrayT ty (Dynamic maxn))) fp /\ MEM (slot,32) fp
End

Definition abi_decoder_loop_inputs_def:
  abi_decoder_loop_inputs first ip src dst sb d slot initial <=>
    abi_decoder_operand_live first ip /\ abi_decoder_operand_live first src /\
    abi_decoder_operand_live first dst /\
    eval_operand ip initial = SOME (n2w slot) /\ eval_operand src initial = SOME (n2w sb) /\
    eval_operand dst initial = SOME (n2w d)
End

Theorem abi_decoder_loop_inputs_eval:
  abi_decoder_loop_inputs first ip src dst sb d slot initial /\
  abi_decoder_loop_rel first limit_st fp initial s ==>
  eval_operand ip s = SOME (n2w slot) /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d)
Proof
  simp_tac bool_ss [abi_decoder_loop_inputs_def] >> metis_tac[abi_decoder_loop_rel_eval]
QED

Theorem abi_decoder_loop_inputs_live:
  abi_decoder_loop_inputs first ip src dst sb d slot initial /\ first <= next ==>
  abi_decoder_operand_live next ip /\ abi_decoder_operand_live next src /\
  abi_decoder_operand_live next dst
Proof
  simp_tac bool_ss [abi_decoder_loop_inputs_def] >> metis_tac[abi_decoder_operand_live_mono]
QED

Theorem abi_decoder_primitive_compiled_facts:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc hi clamp
    hdr exit_lbl hid first iv limit_st /\ abi_decode_source_opcode opc ==>
  first + 4 <= limit_st.cs_next_var /\ first <= st0.cs_next_var /\
  first <= st1.cs_next_var /\ st1.cs_next_var <= limit_st.cs_next_var /\
  st1.cs_current_bb = st0.cs_current_bb /\ fn_has_code st0 st1 fn
Proof
  simp_tac bool_ss [abi_decoder_primitive_loop_compiled_def] >> strip_tac >>
  drule_all abi_decoder_primitive_body_counters >> strip_tac >>
  drule_all abi_decoder_primitive_loop_body_shape >> strip_tac >>
  drule_all abi_decoder_primitive_body_contained >> strip_tac >>
  qpat_assum `abi_decoder_primitive_loop_code _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_primitive_loop_code_def]) >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_decoder_primitive_count_bound:
  !d n bound:num. d + (32 + n * 32) < bound ==> n < bound
Proof
  Omega.OMEGA_TAC
QED

Theorem abi_decoder_primitive_data_facts:
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot fp ==>
  LENGTH avs = LENGTH vs /\ all_have_type tv vs /\ LENGTH vs <= maxn /\
  LENGTH vs < dimword (:256) /\ type_memory_size tv = 32 /\
  type_memory_bytes ce (ArrayT ty (Dynamic maxn)) = 32 + maxn * 32
Proof
  simp_tac bool_ss [abi_decoder_primitive_loop_data_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_dynarray_values >> strip_tac >>
  drule_all abi_decoder_primitive_array_sizes >> strip_tac >>
  `maxn < dimword (:256)` by
    (irule abi_decoder_primitive_count_bound >> qexists_tac `d` >>
     gvs[Excl "enc_def"]) >>
  asm_simp_tac bool_ss [] >> metis_tac[LESS_EQ_LESS_TRANS]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_PRIMITIVE_LOOP_CONTEXT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI primitive loop context not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderPrimitiveLoopContext");
