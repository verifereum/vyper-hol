(* Robust represented values cannot taint live encoded storage bytes. *)
Theory assignBasePtrStorageTaint
Ancestors representationCleanPtr storageCopyLive valueEncodingProofs
  bodyPtrDefs compileEnv valueEncoding vyperValue vyperTyping
  venomState list words arithmetic

Theorem robust_mem_word_byte_clean:
  !ta mem a b c.
    b < 32 /\
    (!m. mem_agree_outside ta mem m ==>
      EL b (word_to_bytes (mem_word_at a m) T) = c) ==>
    a+b NOTIN ta
Proof
  rpt strip_tac >>
  `!m. mem_agree_outside ta mem m ==>
       mem_bytes_at (a+b) 1 m = [c]` by
    (rpt strip_tac >> irule LIST_EQ >> simp[EL_mem_bytes_at] >>
     rpt strip_tac >>
     first_x_assum drule >>
     simp[GSYM mem_bytes_at_word, EL_mem_bytes_at]) >>
  drule robust_mem_bytes_at_clean >> simp[] >>
  qexists_tac `a+b` >> simp[]
QED

Theorem robust_memory_taint_dead:
  !tv v writes k st ta mem off j b.
    well_formed_type_value tv /\ value_has_type tv v /\
    encode_value tv v = SOME writes /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    (!m. mem_agree_outside ta mem m ==> val_in_memory tv v off m) /\
    j < type_slot_size tv /\ b < 32 /\ off + 32*j + b IN ta ==>
    dead_bytes (apply_writes k writes st) (w2n k) tv (w2n k+j) b
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `!m. mem_agree_outside ta mem m ==>
    EL b (word_to_bytes (mem_word_at (off+32*j) m) T) =
    EL b (word_to_bytes (lookup_storage (n2w (w2n k+j))
      (apply_writes k writes st)) T)` by
    (rpt strip_tac >> sym_tac >> irule encode_value_memory_live >>
     metis_tac[]) >>
  drule_all robust_mem_word_byte_clean >> simp[]
QED
