(* The emitted low-five-bit mask computes the ABI contractABI$ceil32 length. *)
Theory abiEncoderRounding
Ancestors contractABI words arithmetic
Libs wordsLib

Theorem abi_encoder_round_dimindex[simp,local]: dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Theorem abi_encoder_round_mask:
  (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w:bytes32) && w =
    (w >>> 5) << 5
Proof
  WORD_DECIDE_TAC
QED

Theorem abi_encoder_round_mask_n2w:
  n < dimword (:256) ==>
  (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w:bytes32) && n2w n =
    n2w (32 * (n DIV 32))
Proof
  strip_tac >>
  `(n2w n:bytes32) >>> 5 = n2w (n DIV 32)` by
    (mp_tac (PURE_REWRITE_RULE [w2n_lsr]
       (Q.ISPEC `(n2w n:bytes32) >>> 5` n2w_w2n)) >>
     asm_simp_tac (srw_ss()) [w2n_lsr, w2n_n2w, EQ_SYM_EQ]) >>
  asm_simp_tac (srw_ss()) [abi_encoder_round_mask, WORD_MUL_LSL, word_mul_n2w]
QED

Theorem abi_encoder_round_ceil32:
  cnt + 31 < dimword (:256) ==>
  (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w:bytes32) &&
    (31w + n2w cnt) = n2w (contractABI$ceil32 cnt)
Proof
  strip_tac >>
  `31w + (n2w cnt:bytes32) = n2w (cnt+31)` by simp[word_add_n2w, ADD_COMM] >>
  asm_simp_tac (srw_ss()) [abi_encoder_round_mask_n2w, ceil32_def]
QED

Theorem abi_encoder_ceil32_bounds:
  cnt <= contractABI$ceil32 cnt /\ contractABI$ceil32 cnt < cnt+32
Proof
  simp_tac bool_ss [le_ceil32] >>
  mp_tac (Q.SPEC `cnt+31` (MATCH_MP DIVISION (DECIDE ``0 < 32:num``))) >>
  simp[ceil32_def] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ROUNDING_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder rounding not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderRounding");
