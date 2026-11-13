(* Interpretation of arbitrary available bytestring suffixes. *)
Theory abiDecoderBytestringSource
Ancestors
  valueEncodingDefs
  abiDecoderSourceFacts abiDecoderBytestringOutcome abiCanonicalHeadSize
  abiDecoderString vyperABI contractABI vyperValue valueEncoding words
  list rich_list arithmetic abiDecoderContract venomState

Theorem abi_decode_bytestring_source_acceptance:
  c = w2n (word_of_bytes T (0w:bytes32) (TAKE 32 bs)) ==>
  ((vyper_decode_valid_enc (Bytes NONE) bs /\
    ?v. abi_to_vyper env (BaseT (BytesT (Dynamic n))) (dec (Bytes NONE) bs) = SOME v) <=>
   32 <= LENGTH bs /\ c <= n /\ c <= LENGTH bs - 32) /\
  ((vyper_decode_valid_enc String bs /\
    ?v. abi_to_vyper env (BaseT (StringT n)) (dec String bs) = SOME v) <=>
   32 <= LENGTH bs /\ c <= n /\ c <= LENGTH bs - 32)
Proof
  strip_tac >> Cases_on `32 <= LENGTH bs`
  >- (drule abi_decode_bytestring_validation >> strip_tac >>
      gvs[abi_to_vyper_def, compatible_bound_def, LENGTH_TAKE, LENGTH_DROP] >>
      Cases_on `w2n (word_of_bytes T (0w:bytes32) (TAKE 32 bs)) <= LENGTH bs - 32` >>
      simp[LENGTH_TAKE, LENGTH_DROP]) >>
  simp[vyper_decode_valid_enc_def, is_num_value_def, dec_def,
       dec_number_def, dest_NumV_def]
QED

Theorem abi_decode_bytestring_suffix_acceptance:
  bs = mem_bytes_at (b+p) (h-p) mem /\
  c = w2n (mem_word_at (b+p) mem) ==>
  ((vyper_decode_valid_enc (Bytes NONE) bs /\
    ?v. abi_to_vyper env (BaseT (BytesT (Dynamic n))) (dec (Bytes NONE) bs) = SOME v) <=>
   p+32 <= h /\ c <= n /\ p+32+c <= h) /\
  ((vyper_decode_valid_enc String bs /\
    ?v. abi_to_vyper env (BaseT (StringT n)) (dec String bs) = SOME v) <=>
   p+32 <= h /\ c <= n /\ p+32+c <= h)
Proof
  strip_tac >> Cases_on `p+32 <= h`
  >- (`TAKE 32 bs = mem_bytes_at (b+p) 32 mem` by
        (gvs[] >>
         `TAKE 32 (DROP 0 (mem_bytes_at (b+p) (h-p) mem)) =
          mem_bytes_at ((b+p)+0) 32 mem` by
            (irule mem_bytes_at_window >> decide_tac) >> gvs[]) >>
      `c = w2n (word_of_bytes T (0w:bytes32) (TAKE 32 bs))` by
        simp[mem_word_at_def, mem_bytes_at_def] >>
      drule abi_decode_bytestring_source_acceptance >>
      disch_then (qspecl_then [`n`,`env`] mp_tac) >>
      simp[] >> decide_tac) >>
  `LENGTH bs < 32` by (simp[mem_bytes_at_def] >> decide_tac) >>
  simp[vyper_decode_valid_enc_def, is_num_value_def, dec_def,
       dec_number_def, dest_NumV_def]
QED

Theorem abi_decode_bytestring_copy_views:
  mem_bytes_at d (32+c) out = mem_bytes_at a (32+c) mem ==>
  mem_word_at d out = mem_word_at a mem /\
  mem_bytes_at (d+32) c out = mem_bytes_at (a+32) c mem
Proof
  strip_tac >>
  `TAKE 32 (DROP 0 (mem_bytes_at d (32+c) out)) =
     mem_bytes_at (d+0) 32 out` by (irule mem_bytes_at_window >> simp[]) >>
  `TAKE 32 (DROP 0 (mem_bytes_at a (32+c) mem)) =
     mem_bytes_at (a+0) 32 mem` by (irule mem_bytes_at_window >> simp[]) >>
  `TAKE c (DROP 32 (mem_bytes_at d (32+c) out)) =
     mem_bytes_at (d+32) c out` by (irule mem_bytes_at_window >> simp[]) >>
  `TAKE c (DROP 32 (mem_bytes_at a (32+c) mem)) =
     mem_bytes_at (a+32) c mem` by (irule mem_bytes_at_window >> simp[]) >>
  gvs[mem_word_at_def, mem_bytes_at_def]
QED

Theorem abi_decode_bytestring_suffix_value:
  bs = mem_bytes_at a len mem /\ 32+c <= len /\
  c = w2n (mem_word_at a mem) /\
  mem_bytes_at d (32+c) out = mem_bytes_at a (32+c) mem ==>
  val_in_memory (BaseTV (BytesT (Dynamic n)))
    (vyperValue$BytesV (TAKE c (DROP 32 bs))) d out /\
  val_in_memory (BaseTV (StringT n))
    (StringV (MAP (CHR o w2n) (TAKE c (DROP 32 bs)))) d out
Proof
  strip_tac >>
  `TAKE c (DROP 32 bs) = mem_bytes_at (a+32) c mem` by
    (gvs[] >> irule mem_bytes_at_window >> simp[]) >>
  drule abi_decode_bytestring_copy_views >> strip_tac >>
  gvs[val_in_memory_def, mem_bytes_at_def, abi_decoder_string_memory]
QED

Theorem abi_decode_bytestring_suffix_conversions:
  bs = mem_bytes_at a len mem /\ 32+c <= len /\
  c = w2n (mem_word_at a mem) /\ c <= n ==>
  abi_to_vyper env (BaseT (BytesT (Dynamic n))) (dec (Bytes NONE) bs) =
    SOME (vyperValue$BytesV (TAKE c (DROP 32 bs))) /\
  abi_to_vyper env (BaseT (StringT n)) (dec String bs) =
    SOME (StringV (MAP (CHR o w2n) (TAKE c (DROP 32 bs))))
Proof
  strip_tac >>
  `32 <= LENGTH bs` by simp[mem_bytes_at_def] >>
  `TAKE 32 bs = mem_bytes_at a 32 mem` by
    (gvs[] >>
     `TAKE 32 (DROP 0 (mem_bytes_at a len mem)) = mem_bytes_at (a+0) 32 mem`
       by (irule mem_bytes_at_window >> decide_tac) >> gvs[]) >>
  `w2n (word_of_bytes T (0w:bytes32) (TAKE 32 bs)) = c` by
    simp[mem_word_at_def, mem_bytes_at_def] >>
  drule abi_decode_bytestring_validation >> strip_tac >>
  gvs[abi_to_vyper_def, compatible_bound_def, LENGTH_TAKE, LENGTH_DROP,
      mem_bytes_at_def]
QED

Theorem abi_decoder_bytestring_source_outcome:
  compile_abi_decode_to_buf dst pos MLOAD base_op hi (DecBytestring n) st = ((),st') /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\
  eval_operand pos s = SOME (n2w p) /\ eval_operand base_op s = SOME (n2w b) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand hi s = SOME (n2w h) /\
  c = w2n (abi_decode_load MLOAD (n2w (b+p):bytes32) s) /\
  p < dimword (:256) /\ b+h < dimword (:256) /\
  d+abi_decode_bytes_copy_size n < dimword (:256) /\
  (b+h <= d \/ d+abi_decode_bytes_copy_size n <= b) /\
  fresh_vars_wrt st s /\ decode_site_resources ctx fn s /\
  {a | d <= a /\ a < d+abi_decode_bytes_copy_size n} SUBSET writes /\
  d+abi_decode_bytes_copy_size n <= s.vs_alloca_next /\
  bs = mem_bytes_at (b+p) (h-p) s.vs_memory /\
  (bt = BytesT (Dynamic n) \/ bt = StringT n) ==>
  ((?t v. run_inst_seq (emitted_insts st st') s = OK t /\
    vyper_decode_valid_enc (vyper_to_abi_type env (BaseT bt)) bs /\
    abi_to_vyper env (BaseT bt) (dec (vyper_to_abi_type env (BaseT bt)) bs) = SOME v /\
    val_in_memory (BaseTV bt) v d t.vs_memory /\ fresh_vars_wrt st' t /\
    mem_bytes_at d (32+c) t.vs_memory = mem_bytes_at (b+p) (32+c) s.vs_memory /\
    mem_bytes_at (d+32+c) (32*((c+31) DIV 32)-c) t.vs_memory =
      REPLICATE (32*((c+31) DIV 32)-c) 0w /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    decode_site_effect ctx fn next writes s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) \/
   (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t /\
    ~(vyper_decode_valid_enc (vyper_to_abi_type env (BaseT bt)) bs /\
      ?v. abi_to_vyper env (BaseT bt)
        (dec (vyper_to_abi_type env (BaseT bt)) bs) = SOME v)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `p+32 <= h ==> c = w2n (mem_word_at (b+p) s.vs_memory)` by
    (strip_tac >> `b+p < dimword (:256)` by decide_tac >>
     simp[abi_decode_load_def, mload_def, mem_word_at_def, w2n_n2w]) >>
  `((vyper_decode_valid_enc (vyper_to_abi_type env (BaseT bt)) bs /\
     ?v. abi_to_vyper env (BaseT bt)
       (dec (vyper_to_abi_type env (BaseT bt)) bs) = SOME v) <=>
     p+32 <= h /\ c <= n /\ p+32+c <= h)` by
    (Cases_on `p+32 <= h`
     >- (`c = w2n (mem_word_at (b+p) s.vs_memory)` by metis_tac[] >>
         drule_all abi_decode_bytestring_suffix_acceptance >>
         disch_then (qspecl_then [`n`,`env`] mp_tac) >>
         Cases_on `bt = BytesT (Dynamic n)` >>
         gvs[vyper_to_abi_type_def, vyper_base_to_abi_type_def]) >>
     `LENGTH bs < 32` by (simp[mem_bytes_at_def] >> decide_tac) >>
     Cases_on `bt = BytesT (Dynamic n)` >>
     gvs[vyper_to_abi_type_def, vyper_base_to_abi_type_def,
         vyper_decode_valid_enc_def, is_num_value_def, dec_def,
         dec_number_def, dest_NumV_def]) >>
  drule_all abi_decoder_bytes_outcome >>
  disch_then (qspec_then `next` mp_tac) >>
  Cases_on `p+32 <= h /\ c <= n /\ p+32+c <= h` >>
  asm_simp_tac bool_ss [] >> strip_tac
  >- (disj1_tac >>
      `32+c <= h-p /\ c <= n /\
       c = w2n (mem_word_at (b+p) s.vs_memory)` by (conj_tac >- decide_tac >> metis_tac[]) >>
      drule_all abi_decode_bytestring_suffix_conversions >>
      disch_then (qspec_then `env` strip_assume_tac) >>
      `mem_bytes_at d (32+c) t'.vs_memory =
       mem_bytes_at (b+p) (32+c) s.vs_memory` by
        (asm_simp_tac bool_ss []) >>
      drule_all abi_decode_bytestring_suffix_value >>
      disch_then (qspec_then `n` strip_assume_tac) >>
      Cases_on `bt = BytesT (Dynamic n)` >>
      gvs[vyper_to_abi_type_def, vyper_base_to_abi_type_def] >> metis_tac[]) >>
  metis_tac[]
QED
