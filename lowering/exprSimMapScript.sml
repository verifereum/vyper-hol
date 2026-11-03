(* Mapping read-side simulation: key representation and hash steps. *)
Theory exprSimMap
Ancestors
  exprSimHyps exprSimHash valueEncodingProofs
  vyperTypeSystem compileEnv vyperValue vyperTyping vyperStorage valueEncoding

Theorem encode_hashmap_key_scalar:
  !kt kv tenv tv.
    hashmap_key_type kt /\ ~is_bytestring_type kt /\
    evaluate_type tenv kt = SOME tv /\ value_has_type tv kv ==>
    encode_hashmap_key kt kv = typed_val_to_w256 tv kv
Proof
  Cases_on `kt` >> simp[hashmap_key_type_def] >>
  rpt gen_tac >> strip_tac
  >- (rename1 `BaseT bt` >> Cases_on `bt` >>
      gvs[hashmap_key_type_def, is_bytestring_type_def,
          evaluate_type_def, AllCaseEqs()] >>
      Cases_on `kv` >>
      gvs[value_has_type_def, encode_hashmap_key_def,
          typed_val_to_w256_def, val_to_w256_def, AllCaseEqs()]) >>
  gvs[evaluate_type_def, AllCaseEqs()] >> Cases_on `kv` >>
  gvs[value_has_type_def, encode_hashmap_key_def,
      typed_val_to_w256_def, val_to_w256_def]
QED

Theorem expr_val_rel_hashmap_scalar:
  hashmap_key_type kt /\ ~is_bytestring_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv kv /\
  expr_val_rel cx kt kv op s ==>
  eval_operand op s = SOME (encode_hashmap_key kt kv)
Proof
  strip_tac >>
  `is_word_type kt` by
    (Cases_on `kt` >> gvs[hashmap_key_type_def, is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[hashmap_key_type_def, is_word_type_def, is_bytestring_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, is_word_type_def, evaluate_type_def,
         AllCaseEqs()]) >>
  drule_all encode_hashmap_key_scalar >> strip_tac >>
  gvs[exprSimTheory.expr_val_rel_def] >> res_tac >> gvs[]
QED

Theorem expr_post_hashmap_bytestring:
  expr_post ctx func cenv cx e es sa sm s0 es' kv op s /\
  expr_type e = kt /\ is_bytestring_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv kv ==>
  ?b bs. eval_operand op s = SOME (n2w b) /\
    mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
    b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    encode_hashmap_key kt kv = word_of_bytes_be (Keccak_256_w64 bs)
Proof
  strip_tac >> Cases_on `kt` >> gvs[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[is_bytestring_type_def, evaluate_type_def]
  >- (Cases_on `kv` >> gvs[value_has_type_def] >>
      rename1 `StringV str` >>
      `evaluate_type (get_tenv cx) (expr_type e) =
         SOME (BaseTV (StringT n))` by simp[evaluate_type_def] >>
      drule_all hash_string_post_view >> strip_tac >>
      qexistsl_tac [`b`, `MAP (n2w o ORD) str`] >>
      gvs[encode_hashmap_key_def, vyperMiscTheory.n2w_o_ORD_eq,
          wordsTheory.dimword_def]) >>
  rename1 `BytesT bound` >> Cases_on `bound` >>
  gvs[is_bytestring_type_def, evaluate_type_def] >>
  Cases_on `kv` >> gvs[value_has_type_def] >>
  rename1 `BytesV bs` >> rename1 `Dynamic cap` >>
  `evaluate_type (get_tenv cx) (expr_type e) =
     SOME (BaseTV (BytesT (Dynamic cap)))` by simp[evaluate_type_def] >>
  drule_all hash_dynamic_post_view >> strip_tac >>
  qexistsl_tac [`b`, `bs`] >> gvs[encode_hashmap_key_def, wordsTheory.dimword_def]
QED

(* Computation probes distinguish left-aligned fixed bytes from data hashing. *)
Theorem hashmap_fixed_key_alignment_probe[local]:
  encode_hashmap_key (BaseT (BytesT (Fixed 1))) (BytesV [1w]) =
    (n2w (2 ** 248):bytes32) /\
  encode_hashmap_key (BaseT (BytesT (Fixed 32)))
    (BytesV (1w :: REPLICATE 31 0w)) = (n2w (2 ** 248):bytes32)
Proof
  EVAL_TAC >> wordsLib.WORD_DECIDE_TAC
QED

Theorem hashmap_empty_dynamic_key_probe[local]:
  encode_hashmap_key (BaseT (BytesT (Dynamic 0))) (BytesV []) =
    word_of_bytes_be (Keccak_256_w64 []) /\
  encode_hashmap_key (BaseT (StringT 0)) (StringV "") =
    word_of_bytes_be (Keccak_256_w64 [])
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``Keccak_256_w64``])
QED
