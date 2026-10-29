(* Closed shared array constructor, derived from the shared execution spine. *)
Theory abiEncoderSharedArray
Ancestors
  abiEncoderSharedArrayOuter abiEncoderSharedArrayInput abiEncoderSharedContract
  abiEncoderOpenInput abiEncoderInput abiDecoderReentry abiDecoderContract
  compileEnv valueEncoding contractABI venomState words list

Theorem abi_encoder_shared_array:
  abi_encoder_shared ei /\ (~active ==> abi_encoder_static_leaf ei) ==>
  abi_encoder_shared (AbiDynArray ei asz msz active)
Proof
  strip_tac >> simp_tac bool_ss [abi_encoder_shared_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_shared_input _ _ _ _ _ _`
    (assume_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
  qpat_x_assum `abi_encoder_open_input _ _ _ _ _ _`
    (qx_choose_then `ty` (qx_choose_then `avs` strip_assume_tac) o
      REWRITE_RULE [abi_encoder_open_array_iff]) >>
  qpat_x_assum `at = Array NONE ty` SUBST_ALL_TAC >>
  qpat_x_assum `av = ListV avs` SUBST_ALL_TAC >>
  drule_all abi_encoder_shared_array_outer >>
  disch_then (qspec_then `ctx` (qx_choose_then `actual` strip_assume_tac)) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [abi_encoder_shared_endpoint_def]
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared array constructor admission, axiom or hypothesis"
  end) [abi_encoder_shared_array];
