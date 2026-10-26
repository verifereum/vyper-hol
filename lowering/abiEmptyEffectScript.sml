(* Allocation-preserving output frames for Empty memory initialization. *)
Theory abiEmptyEffect
Ancestors
  abiDecoderFrameCompose abiDecoderContract abiDecoderReentry
  exprLoweringProps compileEnv venomState venomExecSemantics arithmetic

Definition abi_empty_effect_def:
  abi_empty_effect next p sz limit_st s t <=>
    fresh_vars_wrt limit_st t /\ abi_decode_frame p sz s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\
    (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w)
End

Theorem abi_empty_effect_refl:
  fresh_vars_wrt limit_st s ==> abi_empty_effect next p sz limit_st s s
Proof
  simp[abi_empty_effect_def, abi_decode_frame_def]
QED

Theorem abi_empty_effect_operand:
  abi_empty_effect next p sz limit_st s t /\
  abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
  eval_operand op t = SOME w
Proof
  simp[abi_empty_effect_def] >> rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem abi_empty_effect_append:
  abi_empty_effect first p m limit_st s middle /\
  abi_empty_effect next (p+m) n limit_st middle t /\ first <= next ==>
  abi_empty_effect first p (m+n) limit_st s t
Proof
  simp_tac bool_ss [abi_empty_effect_def] >> strip_tac >>
  `abi_decode_frame p (m+n) s t` by
    (drule_all abi_decode_frame_adjacent >> simp[]) >>
  asm_simp_tac bool_ss [] >> rpt gen_tac >> strip_tac >>
  `abi_decoder_operand_live next op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `first` >> simp[]) >>
  qpat_x_assum `!op w. abi_decoder_operand_live next op /\ _ ==> _` irule >>
  asm_simp_tac bool_ss [] >>
  qpat_x_assum `!op w. abi_decoder_operand_live first op /\ _ ==> _` irule >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_EMPTY_EFFECT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI empty effect not kernel closed: " ^ n)
  end) (DB.thms "abiEmptyEffect");

