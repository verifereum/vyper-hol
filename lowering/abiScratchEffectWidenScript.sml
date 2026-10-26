(* Enclose precise child effects in larger output and instruction intervals.
   TOP-LEVEL: abi_scratch_effect_widen retains allocation evolution and older
   operands while permitting only the enclosing physical write footprint. *)
Theory abiScratchEffectWiden
Ancestors
  abiScratchEncoderContract abiScratchFrameCompose abiScratchFootprint
  abiDecoderAllocation abiDecoderFootprint abiDecoderFrame abiDecoderReentry
  compileEnv venomState finite_map pred_set list arithmetic

Theorem abi_scratch_effect_widen:
  abi_scratch_effect first last child_lo child_hi child_next limit_st child_d child_sz b cap s t /\
  lo <= child_lo /\ child_hi <= hi /\ next <= child_next /\
  d <= child_d /\ child_d+child_sz <= d+sz ==>
  abi_scratch_effect first last lo hi next limit_st d sz b cap s t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `abi_decoder_ids child_lo child_hi SUBSET abi_decoder_ids lo hi` by
    (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  `abi_decode_footprint_frame
    ([(child_d,child_sz)] ++ abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s) s t` by
    (irule abi_scratch_frame_subset_append >> asm_simp_tac (srw_ss()) [] >>
     qexists_tac `abi_decoder_ids child_lo child_hi` >> simp[]) >>
  `abi_decode_footprint_frame ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s) s t` by
    (irule abi_decode_footprint_frame_weaken >>
     qexists_tac `[(child_d,child_sz)] ++ abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s` >>
     asm_simp_tac bool_ss [] >> simp[] >> qx_genl_tac [`p`, `n`] >> strip_tac >|
     [qexistsl_tac [`d`, `sz`] >> simp[], qexistsl_tac [`p`, `n`] >> simp[]]) >>
  `!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==> eval_operand op t = SOME w` by
    (rpt gen_tac >> strip_tac >>
     `abi_decoder_operand_live child_next op` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
     qpat_x_assum `!op w. _` irule >> simp[]) >>
  `!id. id < lo \/ hi <= id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id` by
    (rpt gen_tac >> strip_tac >> `id < child_lo \/ child_hi <= id` by decide_tac >>
     asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [abi_scratch_effect_def] >> first_assum ACCEPT_TAC
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_EFFECT_WIDEN_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch enclosing effect not kernel closed: " ^ n)
  end) (DB.thms "abiScratchEffectWiden");
