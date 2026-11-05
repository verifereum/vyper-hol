(* Finite loop closure; round execution is an internal interface premise. *)
Theory abiDecoderConditionalLoop
Ancestors
  abiDecoderFiniteControl abiDecoderLoopData abiDecoderExecution relation arithmetic

Theorem decoder_finite_loop_conditional:
  (!j s. R j s ==> j <= n) /\
  (!j s. R j s ==> Dreach ctx fn s (H j s) /\ (j = n ==> Q (H j s))) /\
  (!j s. R j s /\ j < n ==>
    (?a u. Dabort ctx fn (H j s) a u) \/
    (?v. Dreach ctx fn (H j s) v /\ R (SUC j) v)) ==>
  !j s. R j s ==>
    (?a u. Dabort ctx fn s a u) \/ (?u. Dreach ctx fn s u /\ Q u)
Proof
  strip_tac >>
  `!k j s. n-j = k /\ R j s ==>
    (?a u. Dabort ctx fn s a u) \/ (?u. Dreach ctx fn s u /\ Q u)` suffices_by
    metis_tac[] >>
  completeInduct_on `k` >> rpt gen_tac >> strip_tac >>
  `j <= n` by metis_tac[] >>
  `Dreach ctx fn s (H j s) /\ (j = n ==> Q (H j s))` by metis_tac[] >>
  Cases_on `j = n` >- metis_tac[] >>
  `j < n` by decide_tac >>
  `(?a u. Dabort ctx fn (H j s) a u) \/
   (?v. Dreach ctx fn (H j s) v /\ R (SUC j) v)` by metis_tac[]
  >- metis_tac[Dreach_abort] >>
  `n - SUC j < k` by decide_tac >>
  first_x_assum (qspec_then `n - SUC j` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`SUC j`, `v`] mp_tac) >> simp[] >>
  metis_tac[Dreach_trans, Dreach_abort]
QED

Theorem decoder_round_compose:
  Dreach ctx fn h entry /\
  ((?a u. Dabort ctx fn entry a u) \/
   (?v. Dreach ctx fn entry v /\ BodyPost j v)) /\
  (!v. BodyPost j v ==> ?w. Dreach ctx fn v w /\ Ready (SUC j) w) ==>
  (?a u. Dabort ctx fn h a u) \/
  (?w. Dreach ctx fn h w /\ Ready (SUC j) w)
Proof
  metis_tac[Dreach_trans, Dreach_abort]
QED

Theorem Lready_finite_loop:
  (!j s. Lready ctx fn first writes origin idx slot ip src opc base_op B sb n j hdr s ==>
    Dreach ctx fn s
      (jump_to (if j < n then body_lbl else exit_lbl)
        (abi_decode_position_header_state base_op first B sb j n s)) /\
    (j = n ==>
      Q (jump_to (if j < n then body_lbl else exit_lbl)
        (abi_decode_position_header_state base_op first B sb j n s)))) /\
  (!j s. Lready ctx fn first writes origin idx slot ip src opc base_op B sb n j hdr s /\
    j < n ==>
    (?a u. Dabort ctx fn
      (jump_to (if j < n then body_lbl else exit_lbl)
        (abi_decode_position_header_state base_op first B sb j n s)) a u) \/
    (?v. Dreach ctx fn
      (jump_to (if j < n then body_lbl else exit_lbl)
        (abi_decode_position_header_state base_op first B sb j n s)) v /\
      Lready ctx fn first writes origin idx slot ip src opc base_op B sb n (SUC j) hdr v)) ==>
  !j s. Lready ctx fn first writes origin idx slot ip src opc base_op B sb n j hdr s ==>
    (?a u. Dabort ctx fn s a u) \/ (?u. Dreach ctx fn s u /\ Q u)
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST [`H` |->
    `\j s. jump_to (if j < n then body_lbl else exit_lbl)
      (abi_decode_position_header_state base_op first B sb j n s)`]
    decoder_finite_loop_conditional) >>
  simp[] >> conj_tac
  >- simp[Lready_def, Ldata_def] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!j s. _ ==> _ /\ _`
        (qspecl_then [`n`, `s`] mp_tac) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`j`, `s`] mp_tac) >> simp[]
QED
