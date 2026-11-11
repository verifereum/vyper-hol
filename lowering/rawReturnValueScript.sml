Theory rawReturnValue
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts
   valueEncoding valueEncodingDefs valueEncodingProps valueCopyBytes valueTypingMemoryProps
  vyperTyping vyperValue venomState

Theorem raw_return_value_layout[local]:
  !tenv ty tv v off mem.
    is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
    value_has_type tv v /\ val_in_memory tv v off mem ==>
    ?bs. raw_return_bytes v = SOME bs /\
         val_footprint tv v = 32 + LENGTH bs /\
         mem_word_at off mem = n2w (LENGTH bs) /\
         mem_bytes_at (off + 32) (LENGTH bs) mem = bs
Proof
  rpt strip_tac >>
  drule_all bytestring_type_value >> strip_tac >>
  Cases_on `v` >>
  gvs[value_has_type_def, val_in_memory_def, val_footprint_def,
      raw_return_bytes_def, string_to_bytes_def]
QED

Theorem raw_return_payload_read[local]:
  !p bs s.
    w2n (p:256 word) + (32 + LENGTH bs) <= dimword (:256) /\
    mem_bytes_at (w2n p + 32) (LENGTH bs) s.vs_memory = bs ==>
    read_memory (w2n (p + 32w)) (LENGTH bs) s = bs
Proof
  rpt strip_tac >>
  Cases_on `bs = []`
  >- gvs[read_memory_def] >>
  `0 < LENGTH bs` by (Cases_on `bs` >> gvs[]) >>
  `w2n p + w2n (32w:256 word) < dimword (:256)` by
    (simp[] >> decide_tac) >>
  drule wordsTheory.w2n_add_2 >> strip_tac >>
  gvs[read_memory_def, mem_bytes_at_def]
QED

(* Use the actual value footprint, including for a short literal at a
   wider declared bytes/string type. The zero-length payload needs no
   nonwrapping payload pointer. *)
Theorem raw_return_value_read:
  !tenv ty tv v p s.
    is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
    value_has_type tv v /\ val_in_memory tv v (w2n p) s.vs_memory /\
    w2n (p : 256 word) + val_footprint tv v <= dimword (:256) ==>
    ?bs. raw_return_bytes v = SOME bs /\
         LENGTH bs < dimword (:256) /\
         mload (w2n p) s = n2w (LENGTH bs) /\
         read_memory (w2n (p + 32w)) (LENGTH bs) s = bs
Proof
  rpt strip_tac >>
  drule_all raw_return_value_layout >> strip_tac >>
  qexists_tac `bs` >>
  `LENGTH bs < dimword (:256)` by decide_tac >>
  gvs[mem_word_at_eq_mload] >>
  irule raw_return_payload_read >> simp[]
QED
