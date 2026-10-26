(* Physical separation suffices for scratch-free decoder adapters.
   A zero-width interval at the current allocation frontier is derived, never assumed. *)
Theory abiScratchDecoderRanges
Ancestors
  abiScratchDecoderContract abiScratchFootprint abiDecoderFootprint abiDecoderAllocation
  abiDecoderTypedContract abiDecoderValidContract abiDecoderFrame abiDecoderContract
  abiDecoderCoherence abiDecoderReentry abiValidStaticAggregate abiValidStaticScalar
  abiDecodeRanges compileEnv valueEncoding vyperABI contractABI
  venomState words list arithmetic

Theorem abi_scratch_frontier_point_disjoint:
  s.vs_alloca_next <= b + cap /\
  abi_footprint_disjoint p n (abi_decoder_child_scratch ids b cap s) ==>
  abi_footprint_disjoint p n [(s.vs_alloca_next,0)]
Proof
  strip_tac >> drule_all abi_scratch_frontier_disjoint >> disch_then assume_tac >>
  simp[abi_footprint_disjoint_def] >> decide_tac
QED

Theorem abi_scratch_decoder_ranges_point:
  abi_scratch_decoder_ranges opc hi src dst sb len d outsz first last b cap s /\
  abi_decoder_budget first last b cap s ==>
  abi_decoder_ranges opc hi src dst sb len d outsz s.vs_alloca_next 0 s
Proof
  simp_tac bool_ss [abi_scratch_decoder_ranges_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_budget_frontier >> strip_tac >>
  `abi_footprint_disjoint d outsz [(s.vs_alloca_next,0)]` by
    (irule abi_scratch_frontier_point_disjoint >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`b`, `cap`, `abi_decoder_ids first last`] >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [abi_decoder_ranges_def] >>
  conj_tac
  >- (qpat_assum `abi_footprint_disjoint d outsz _`
        (mp_tac o PURE_REWRITE_RULE [abi_footprint_disjoint_def]) >> simp[]) >>
  strip_tac >>
  qpat_x_assum `opc = MLOAD ==> _` (fn th => drule_all th) >>
  simp_tac bool_ss [abi_scratch_disjoint_cons] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_footprint_disjoint sb len [(s.vs_alloca_next,0)]` by
    (irule abi_scratch_frontier_point_disjoint >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`b`, `cap`, `abi_decoder_ids first last`] >> asm_simp_tac bool_ss []) >>
  fs[abi_footprint_disjoint_def]
QED

Theorem abi_scratch_decoder_point_reservation:
  abi_decoder_budget first last b cap s ==>
  abi_decoder_reservation st.cs_next_id st.cs_next_id s.vs_alloca_next 0 s
Proof
  strip_tac >> drule abi_decoder_budget_frontier >> strip_tac >>
  `b + cap < dimword (:256)` by fs[abi_decoder_budget_def] >>
  `s.vs_alloca_next < dimword (:256)` by decide_tac >>
  rw[abi_decoder_reservation_def] >> decide_tac
QED

Theorem abi_scratch_decoder_input_point:
  abi_scratch_decoder_input ce env sf ty tv bs v st src dst opc hi sb d first last b cap s /\
  abi_decoder_budget first last b cap s ==>
  abi_decoder_valid_pre ce env sf ty tv bs v st src dst opc hi sb d s.vs_alloca_next 0 s
Proof
  simp_tac bool_ss [abi_scratch_decoder_input_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_ranges_point >> strip_tac >>
  asm_simp_tac bool_ss [abi_decoder_valid_pre_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DECODER_RANGES_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI physical decoder range fact not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDecoderRanges");
