Theory entryZeroWidthCodec
Ancestors contractABI list words

Theorem entry_zero_width_encoding_acc[local]:
  !n hl tl rhds rtls.
    enc_tuple hl tl (REPLICATE n (Tuple []))
      (REPLICATE n (ListV [])) rhds rtls =
    FLAT (REVERSE rhds) ++ FLAT (REVERSE rtls)
Proof
  Induct >> simp[enc_def, is_dynamic_def, static_length_def,
                 REV_REVERSE_LEM, FLAT_APPEND]
QED

Theorem entry_zero_width_encoding[local]:
  !n. enc (Tuple (REPLICATE n (Tuple [])))
        (ListV (REPLICATE n (ListV []))) = []
Proof
  simp[enc_def, entry_zero_width_encoding_acc]
QED

Theorem entry_zero_width_decoding_acc[local]:
  !n suffix off acc.
    dec_tuple (REPLICATE n (Tuple [])) suffix off acc =
    ListV (REVERSE acc ++ REPLICATE n (ListV []))
Proof
  Induct >> simp[dec_def, is_dynamic_def, static_length_def]
QED

Theorem entry_zero_width_decoding[local]:
  !n suffix. dec (Tuple (REPLICATE n (Tuple []))) suffix =
    ListV (REPLICATE n (ListV []))
Proof
  simp[dec_def, entry_zero_width_decoding_acc]
QED

Theorem entry_zero_width_cardinality_boundary[local]:
  let ats = REPLICATE (dimword (:256)) (Tuple []);
      av = ListV (REPLICATE (dimword (:256)) (ListV [])) in
  enc (Tuple ats) av = [] /\
  (!suffix. dec (Tuple ats) suffix = av) /\
  ~has_type (Tuple ats) av
Proof
  simp[entry_zero_width_encoding, entry_zero_width_decoding, has_type_def]
QED

(* Consumer boundary tested, not replaced here:
   entrySourceRegistrationFold.entry_registration_source_endpoint:523 passes
   global has_types through entry_registration_singleton_anchored:129 to
   entrySingletonProducer.entry_registration_singleton_source_endpoint:55.
   That proof invokes entry_canonical_registration_address at line 100 and
   entry_canonical_valid_pre at line 120. The latter supplies the decoder's
   abi_decoder_valid_pre from a canonical member window. These canonical
   address/valid-pre interfaces (and their recursive canonical-member facts)
   must admit the source-realizable input family without demanding global
   ABI cardinality typing before the registration consumer can be generalized.
   This probe supplies only enc/dec equations, not valid_pre, ownership,
   coherence, allocation resources, source provenance or a new endpoint. *)
