(*
 * Byte/Keccak length lemmas used by fresh Vyper type soundness proofs.
 *)

Theory vyperTypeBytesCrypto
Ancestors
  list rich_list arithmetic words byte keccak vyperMisc
Libs
  wordsLib

(* Keccak_p_24_w64 preserves length 25 *)
Theorem LENGTH_Keccak_p_24_w64:
  !ws. LENGTH ws = 25 ==> LENGTH (Keccak_p_24_w64 ws) = 25
Proof
  rewrite_tac[Keccak_p_24_w64_def] >>
  qspec_tac (`iota_w64_RCz`, `rcs`) >>
  Induct >> simp[FOLDL] >> rpt strip_tac >>
  first_x_assum match_mp_tac >>
  metis_tac[LENGTH_Rnd_w64]
QED

(* FOLDL with Keccak_p_24_w64 preserves length 25 *)
Theorem LENGTH_FOLDL_Keccak:
  !Pis s. LENGTH s = 25 /\ EVERY (\p. LENGTH p >= 25) Pis ==>
          LENGTH (FOLDL (\Si Pi. Keccak_p_24_w64 (MAP2 $?? Si Pi)) s Pis) = 25
Proof
  Induct >> simp[FOLDL] >> rpt strip_tac >>
  first_x_assum match_mp_tac >> simp[] >>
  irule LENGTH_Keccak_p_24_w64 >> simp[LENGTH_MAP2, MIN_DEF]
QED

(* absorb_w64 returns length 25 when all chunks have length >= 25 *)
Theorem LENGTH_absorb_w64:
  !Pis. EVERY (\p. LENGTH p >= 25) Pis ==>
        LENGTH (absorb_w64 Pis) = 25
Proof
  rpt strip_tac >>
  simp[absorb_w64_def] >>
  irule LENGTH_FOLDL_Keccak >>
  simp[LENGTH_REPLICATE]
QED

(* state_bools_w64 implies word list has length 25 *)
Theorem state_bools_w64_LENGTH:
  state_bools_w64 bls ws ==> LENGTH ws = 25
Proof
  simp[state_bools_w64_def] >> strip_tac >> gvs[] >>
  `divides 64 1600` by (simp[dividesTheory.divides_def] >> qexists_tac `25` >> simp[]) >>
  `~NULL (MAP bool_to_bit bls)` by (Cases_on `bls` >> gvs[]) >>
  simp[LENGTH_chunks, LENGTH_MAP, bool_to_bit_def]
QED

(* LIST_REL state_bools_w64 ==> EVERY length 25 *)
Theorem LIST_REL_state_bools_w64_lengths:
  !bss wss. LIST_REL state_bools_w64 bss wss ==>
            EVERY (\p. LENGTH p >= 25) wss
Proof
  Induct >> simp[LIST_REL_CONS1] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac state_bools_w64_LENGTH >> simp[]
QED

Theorem pad10s1_136_w64_every_len25:
  !bs. EVERY (\p. LENGTH p >= 25)
         (pad10s1_136_w64 eight_zeros_w64 bs [])
Proof
  gen_tac >>
  mp_tac (INST [``bytes:word8 list`` |-> ``bs:word8 list``]
               pad10s1_136_w64_sponge_init) >>
  simp[LET_THM] >>
  `eight_zeros_w64 = REPLICATE (512 DIV 64) (0w:word64)`
    by EVAL_TAC >>
  pop_assum SUBST_ALL_TAC >> strip_tac >>
  irule LIST_REL_state_bools_w64_lengths >>
  qexists_tac `MAP (\Pi. Pi ++ REPLICATE 512 F)
    (chunks 1088 (bytes_to_bools bs ++
       pad10s1 1088 (LENGTH (bytes_to_bools bs))))` >>
  simp[]
QED

Theorem LENGTH_absorb_pad:
  !bs. LENGTH (absorb_w64 (pad10s1_136_w64 eight_zeros_w64 bs [])) = 25
Proof
  gen_tac >> irule LENGTH_absorb_w64 >>
  simp[pad10s1_136_w64_every_len25]
QED

Theorem LENGTH_FLAT_word_to_bytes:
  !ws:word64 list.
    LENGTH (FLAT (MAP (\y. word_to_bytes y F) ws)) = 8 * LENGTH ws
Proof
  Induct >> simp[LENGTH_word_to_bytes]
QED

Theorem LENGTH_Keccak_256_w64:
  !bs. LENGTH (Keccak_256_w64 bs) = 32
Proof
  gen_tac >> rewrite_tac[Keccak_256_w64_def, combinTheory.C_DEF] >>
  BETA_TAC >>
  simp[LENGTH_FLAT_word_to_bytes, LENGTH_TAKE, LENGTH_absorb_pad]
QED
