(* Existing decoder translation headers supply the tuple encoder's numerical
   layout conditions; complete runtime source windows remain separate. *)
Theory abiTupleEncodeSourceLayout
Ancestors
  abiTupleEncodeLayout abiDecoderCoherence compileEnv vyperABI
  valueEncoding contractABI list arithmetic

Theorem abi_tuple_encode_layout_headers:
  !ops tys tvs. LENGTH ops = LENGTH tys /\ LIST_REL (abi_decoder_header ce env) tys tvs ==>
  abi_tuple_encode_layout ce (ZIP (ops,tys)) (vyper_to_abi_types env tys)
Proof
  Induct >- simp[abi_tuple_encode_layout_def] >>
  Cases_on `tys` >> Cases_on `tvs` >>
  simp[abi_tuple_encode_layout_def] >> rpt gen_tac >> strip_tac >>
  fs[abi_decoder_header_def] >>
  rename1 `LIST_REL (abi_decoder_header ce env) tail_tys tail_tvs` >>
  qpat_x_assum `!tys tvs. _` (qspecl_then [`tail_tys`, `tail_tvs`] mp_tac) >>
  asm_simp_tac bool_ss [abi_tuple_encode_layout_def]
QED

Theorem abi_tuple_encode_layout_coherent:
  LENGTH ops = LENGTH tys /\ LIST_REL (abi_decoder_coherent ce env sf) tys tvs ==>
  abi_tuple_encode_layout ce (ZIP (ops,tys)) (vyper_to_abi_types env tys)
Proof
  strip_tac >>
  `LIST_REL (abi_decoder_header ce env) tys tvs` by
    (irule LIST_REL_mono >> qexists_tac `abi_decoder_coherent ce env sf` >>
     asm_simp_tac bool_ss [] >> rpt strip_tac >> drule abi_decoder_coherent_header >> simp[]) >>
  drule_all abi_tuple_encode_layout_headers >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_TUPLE_ENCODE_SOURCE_LAYOUT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI tuple encoder source layout not kernel closed: " ^ n)
  end) (DB.thms "abiTupleEncodeSourceLayout");
