(* Signed canonical-word arithmetic used by primitive decoder validation. *)
Theory abiDecoderSignedWord
Ancestors
  abiDecoderClamp venomExecSemantics venomState integer_word words arithmetic
Libs
  wordsLib

Theorem abi_signed_dimindex[simp,local]: dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Theorem abi_signed_bit_one[local]:
  bit$BIT i 1 <=> i = 0
Proof
  mp_tac (Q.SPECL [`i`, `0`] bitTheory.BIT_TWO_POW) >>
  simp_tac bool_ss [EXP] >> metis_tac[]
QED

Theorem abi_decoder_sign_extend_cast_bit:
  dimindex (:'a) = 8 * (n + 1) /\ n < 31 ==>
  ((sw2sw (w:'a word) : bytes32) >>> (8 * n + 7)) && 1w =
    if word_msb w then 1w else 0w
Proof
  strip_tac >>
  `8 * n + 7 = dimindex (:'a) - 1 /\ dimindex (:'a) <= 256` by decide_tac >>
  Cases_on `word_msb w` >>
  rw_tac (std_ss ++ fcpLib.FCP_ss ++ numSimps.ARITH_ss)
    [word_and_def, word_lsr_def, sw2sw, word_msb_def, word_index, word_0,
     abi_signed_dimindex, abi_signed_bit_one] >>
  Cases_on `i = 0` >> gvs[sw2sw, word_msb_def] >>
  `8 * (n + 1) - 1 = dimindex (:'a) - 1` by decide_tac >> asm_rewrite_tac[]
QED

Theorem abi_decoder_sign_extend_cast_mask:
  dimindex (:'a) <= 256 ==>
  (if word_msb (w:'a word) then
     (sw2sw w : bytes32) || ~(1w << dimindex (:'a) - 1w)
   else (sw2sw w : bytes32) && (1w << dimindex (:'a) - 1w)) = sw2sw w
Proof
  strip_tac >> Cases_on `word_msb w` >>
  simp_tac bool_ss [] >>
  rw_tac (std_ss ++ fcpLib.FCP_ss ++ numSimps.ARITH_ss)
    [word_and_def, word_or_def, word_1comp_def, sw2sw, SHIFT_1_SUB_1,
     abi_signed_dimindex] >>
  Cases_on `i < dimindex (:'a)` >> gvs[]
QED

Theorem abi_decoder_sign_extend_cast:
  dimindex (:'a) = 8 * (n + 1) /\ n < 32 ==>
  sign_extend (n2w n) (sw2sw (w:'a word) : bytes32) = sw2sw w
Proof
  strip_tac >> `n < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  Cases_on `30 < n`
  >- simp[venomExecSemanticsTheory.sign_extend_def, w2n_n2w] >>
  `n < 31 /\ dimindex (:'a) <= 256 /\ 8 * n + 8 = dimindex (:'a)` by decide_tac >>
  drule_all abi_decoder_sign_extend_cast_bit >> strip_tac >>
  Cases_on `word_msb w` >>
  mp_tac (Q.ISPEC `w:'a word` (GEN_ALL abi_decoder_sign_extend_cast_mask)) >>
  asm_simp_tac (std_ss ++ numSimps.ARITH_ss)
    [venomExecSemanticsTheory.sign_extend_def, w2n_n2w, LET_THM, GREATER_DEF] >> simp[]
QED

Theorem abi_decoder_sign_extend_i2w:
  dimindex (:'a) = 8 * (n + 1) /\ n < 32 /\
  INT_MIN (:'a) <= i /\ i <= INT_MAX (:'a) ==>
  sign_extend (n2w n) (i2w i : bytes32) = i2w i
Proof
  strip_tac >> `dimindex (:'a) <= 256` by decide_tac >>
  `(sw2sw (i2w i : 'a word) : bytes32) = i2w i` by
    (irule sw2sw_i2w >> simp[]) >>
  drule_all abi_decoder_sign_extend_cast >>
  disch_then (qspec_then `i2w i : 'a word` mp_tac) >> simp[]
QED

Theorem abi_decoder_sign_extend_8:
  sign_extend 0w (sw2sw (w:word8) : bytes32) = sw2sw w
Proof
  mp_tac (Q.INST [`n` |-> `0`]
    (INST_TYPE [alpha |-> ``:8``] abi_decoder_sign_extend_cast)) >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_SIGNED_WORD_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI canonical signed word not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderSignedWord");
