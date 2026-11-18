Theory bodyFullAbiDecodeRuntimeLoopSyntax
Ancestors
  bodyFullAbiDecodeInterface abiDecoderLoopSetup abiEncoder
Libs
  bodyFullAbiDecodeRuntimeLoopSyntaxLib

(* The compiler IH does not track state-monad bind equations. Its only
   guard is the boolean for the dynamic-offset branch. *)
Theorem abi_decode_loop_recursive_call:
  (^loop_ih) /\
  abi_decode_array_element_setup ip src dst opc base_op hi ei asz msz body_st =
    ((idx,child_src,child_dst),child) ==>
  (^guarded_to_buf_motive) child_dst child_src opc base_op hi ei
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> disch_then (mp_tac o CONJUNCT1) >>
  disch_then (qspecl_then [`dec_info_needs_offset ei`, `child_dst`, `child_src`] mp_tac) >>
  rewrite_tac[]
QED

Theorem abi_decode_loop_entry_projection:
  !dst src opc base_op hi ei asz msz ip cnt env sf ty tv live protected start finish
    (s:venom_state) G tn d aid counter cell n j srcbase srcoff h.
  (^repaired_loop_entry) dst src opc base_op hi ei asz msz ip cnt
    env sf ty tv live protected start finish s G tn d aid counter cell n j srcbase srcoff h ==>
  (^old_loop_entry) dst src opc base_op hi ei asz msz ip cnt
    env sf ty tv live protected start finish s G tn d aid counter cell n j srcbase srcoff h /\
  abi_decoder_operand_live start.cs_next_var ip /\ srcbase = w2n input_word
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> rpt gen_tac >> disch_then ACCEPT_TAC
QED
