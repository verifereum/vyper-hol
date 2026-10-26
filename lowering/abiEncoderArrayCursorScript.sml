(* Stable cursor observations at a loop's compiler entry, across recursive bodies. *)
Theory abiEncoderArrayCursor
Ancestors
  abiEncoderMembersDefs abiEncoderDynamicChildCore abiDecoderEffect abiDecoderAllocation abiDecoderProtectedScratch
  abiDecoderReentry abiDecoderContract compileEnv venomState finite_map words arithmetic

Theorem abi_encoder_cursor_bounds:
  abi_encoder_cursor T cursor_op site slot first lo st off s /\
  abi_decoder_budget first last b cap s /\ st.cs_next_id <= last ==>
  first <= site /\ site < last /\ b <= slot /\ slot+32 <= b+cap /\ slot < dimword (:256)
Proof
  simp_tac bool_ss [abi_encoder_cursor_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `site < last` by decide_tac >> `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  qpat_assum `abi_decoder_budget _ _ _ _ _`
    (assume_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_encoder_cursor_mono:
  abi_encoder_cursor active cursor_op site slot first lo st off s /\
  st.cs_next_var <= prepared.cs_next_var /\ st.cs_next_id <= prepared.cs_next_id ==>
  abi_encoder_cursor active cursor_op site slot first lo prepared off s
Proof
  Cases_on `active` >> simp_tac bool_ss [abi_encoder_cursor_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_operand_live prepared.cs_next_var cursor_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_encoder_cursor_effect_registered:
  abi_encoder_cursor active cursor_op site slot first lo st off initial /\
  abi_decoder_effect first last owned_lo owned_hi next limit_st d sz b cap initial actual /\
  st.cs_next_var <= next /\ FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
  mload slot actual = n2w next_off ==>
  abi_encoder_cursor active cursor_op site slot first lo st next_off actual
Proof
  Cases_on `active` >> simp_tac bool_ss [abi_encoder_cursor_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_operand_live next cursor_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand cursor_op actual = SOME (n2w slot)` by
    (imp_res_tac abi_encoder_effect_operand >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_encoder_cursor_effect_protected:
  abi_encoder_cursor active cursor_op site slot first lo st off initial /\
  abi_decoder_effect first last owned_lo owned_hi next limit_st d sz b cap initial actual /\
  st.cs_next_var <= next /\ site < last /\ (site < owned_lo \/ owned_hi <= site) ==>
  abi_encoder_cursor active cursor_op site slot first lo st off actual
Proof
  Cases_on `active` >> simp_tac bool_ss [abi_encoder_cursor_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`lo` |-> `owned_lo:num`, `hi` |-> `owned_hi:num`,
    `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`] abi_decoder_effect_protected_slot) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_decoder_operand_live next cursor_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand cursor_op actual = SOME (n2w slot)` by
    (imp_res_tac abi_encoder_effect_operand >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_CURSOR_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array cursor not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayCursor");
