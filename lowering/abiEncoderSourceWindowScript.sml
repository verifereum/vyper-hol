(* Source-window representatives with a type uniform across array elements. *)
Theory abiEncoderSourceWindow
Ancestors
  abiEncoderStaticRepresentative abiEncoderOpenInput abiCallerStaticMemory
  valueEncodingProps valueEncoding valueEncodingTyping vyperTyping vyperTypeValues
  vyperABI vyperMisc vyperValue contractABI words list arithmetic

Theorem abi_encoder_uniform_block_representative:
  !n. ?at. ~is_dynamic at /\ static_length at = 32*n /\
    !bs. LENGTH bs = 32*n ==>
      ?av. has_type at av /\ enc at av = bs
Proof
  Induct
  >- (qexists_tac `Tuple []` >>
      simp[is_dynamic_def, static_length_def] >> rpt strip_tac >>
      gvs[] >> qexists_tac `ListV []` >>
      simp[has_type_def, valid_length_def, enc_def, REV_DEF]) >>
  pop_assum (qx_choose_then `at` strip_assume_tac) >>
  qexists_tac `Tuple [Bytes (SOME 32); at]` >>
  simp[is_dynamic_def, static_length_def, static_length_Tuple_SUM] >>
  rpt strip_tac >>
  `32 <= LENGTH bs /\ LENGTH (DROP 32 bs) = 32*n` by
    (simp[LENGTH_DROP] >> decide_tac) >>
  first_x_assum (qspec_then `DROP 32 bs` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `av` strip_assume_tac) >>
  `LENGTH (TAKE 32 bs) = 32` by simp[LENGTH_TAKE] >>
  drule abi_encoder_bytes32_representative >> strip_tac >>
  qexists_tac `ListV [BytesV (TAKE 32 bs); av]` >>
  simp[abi_encoder_pair_typing, abi_encoder_static_pair_encoding] >>
  metis_tac[TAKE_DROP]
QED

Theorem abi_encoder_uniform_aligned_representative:
  sz MOD 32 = 0 ==>
  ?at. ~is_dynamic at /\ static_length at = sz /\
    !bs. LENGTH bs = sz ==> ?av. has_type at av /\ enc at av = bs
Proof
  strip_tac >>
  `sz = 32 * (sz DIV 32)` by
    (qspec_then `32` mp_tac arithmeticTheory.DIVISION >> simp[] >>
     disch_then (qspec_then `sz` mp_tac) >> simp[] >> decide_tac) >>
  metis_tac[abi_encoder_uniform_block_representative]
QED

Theorem abi_encoder_uniform_static_source:
  evaluate_type env ty = SOME tv /\
  ~is_dynamic (vyper_to_abi_type env ty) ==>
  ?at. ~is_dynamic at /\ static_length at = type_memory_size tv /\
    !v av sb mem. value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
      val_in_memory tv v sb mem ==>
      ?av'. enc at av' = enc (vyper_to_abi_type env ty) av /\
        abi_encoder_open_input (AbiCopy (type_memory_size tv)) at av' sb
          (type_memory_size tv) mem
Proof
  rpt strip_tac >> drule_all abi_encoder_static_source_alignment >> strip_tac >>
  drule abi_encoder_uniform_aligned_representative >>
  disch_then (qx_choose_then `at` strip_assume_tac) >>
  qexists_tac `at` >> simp[] >> rpt strip_tac >>
  drule_all val_in_memory_static_abi >> strip_tac >>
  first_x_assum (qspec_then `mem_bytes_at sb (type_memory_size tv) mem` mp_tac) >>
  simp[mem_bytes_at_def] >>
  disch_then (qx_choose_then `av'` strip_assume_tac) >>
  qexists_tac `av'` >> conj_tac >- metis_tac[] >>
  irule abiEncoderOpenInputTheory.copy >> simp[mem_bytes_at_def]
QED

Theorem abi_encoder_open_bytes_source:
  evaluate_type env (BaseT (BytesT (Dynamic n))) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi env (BaseT (BytesT (Dynamic n))) v = SOME av /\
  val_in_memory tv v sb mem ==>
  abi_encoder_open_input (AbiBytestring n) (Bytes NONE) av sb
    (type_memory_size tv) mem
Proof
  rpt strip_tac >> drule evaluate_type_well_formed_type_value >> strip_tac >>
  drule (cj 1 value_has_type_val_wf) >> strip_tac >>
  Cases_on `v` >>
  gvs[evaluate_type_def, value_has_type_def, vyper_to_abi_def,
      val_wf_def, val_in_memory_def, type_memory_size_def,
      well_formed_type_value_def] >>
  irule abiEncoderOpenInputTheory.bytes >>
  simp[has_type_def, valid_length_def] >> decide_tac
QED

Theorem abi_encoder_open_string_source:
  evaluate_type env (BaseT (StringT n)) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi env (BaseT (StringT n)) v = SOME av /\
  val_in_memory tv v sb mem ==>
  abi_encoder_open_input (AbiBytestring n) String av sb
    (type_memory_size tv) mem
Proof
  `n2w_o_ORD = (n2w o ORD):char -> word8` by
    simp[FUN_EQ_THM, n2w_o_ORD_def] >>
  rpt strip_tac >> drule evaluate_type_well_formed_type_value >> strip_tac >>
  drule (cj 1 value_has_type_val_wf) >> strip_tac >>
  Cases_on `v` >>
  gvs[evaluate_type_def, value_has_type_def, vyper_to_abi_def,
      val_wf_def, val_in_memory_def, type_memory_size_def,
      well_formed_type_value_def, n2w_o_ORD_def, combinTheory.o_DEF] >>
  irule abiEncoderOpenInputTheory.bytes >>
  simp[has_type_def, valid_length_def, combinTheory.o_DEF] >> decide_tac
QED

(* Retained tags do not reconstruct axiom provenance erased by .dat loading. *)
val _ = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print ("ENCODER_SOURCE_WINDOW_AUDIT_OK " ^ name ^ "\n")
    else raise Fail ("source window admission dependency: " ^ name)
  end)
  [("uniform_block", abi_encoder_uniform_block_representative),
   ("uniform_aligned", abi_encoder_uniform_aligned_representative),
   ("uniform_static", abi_encoder_uniform_static_source),
   ("bytes", abi_encoder_open_bytes_source),
   ("string", abi_encoder_open_string_source)];
