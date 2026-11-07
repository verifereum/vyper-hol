(* Meaningful-prefix transfer boundaries for constructor immutables. *)
Theory immutableDeployAssignTransfer
Ancestors
  immutableCopyExecution regularCallEmitSim valueEncoding valueEncodingProofs list rich_list
  venomMemProps venomState words byte codegenRel

Theorem immutable_transfer_read_byte:
  read_byte i (immutable_word_transfer T T a b off s).vs_memory =
  if w2n (b + n2w off) <= i /\ i < w2n (b + n2w off) + 32 then
    read_byte (w2n (a + n2w off) + (i - w2n (b + n2w off))) s.vs_memory
  else read_byte i s.vs_memory
Proof
  simp[immutable_word_transfer_fields, immutable_copy_read_def] >>
  `!p w s. mstore p w s = write_memory_with_expansion p (word_to_bytes w T) s` by
    simp[mstore_def, write_memory_with_expansion_def, LENGTH_word_to_bytes,
         wordsTheory.dimword_def] >>
  simp[read_byte_write_memory_with_expansion, LENGTH_word_to_bytes,
       wordsTheory.dimword_def] >>
  IF_CASES_TAC >> simp[] >>
  simp[mload_def, word_bytes_roundtrip_256, EL_TAKE, EL_APPEND_EQN,
       EL_DROP, EL_REPLICATE, read_byte_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem immutable_transfers_read_byte_frame:
  !n b s i.
    b + 32*n < dimword (:256) /\ (i < b \/ b + 32*n <= i) ==>
    read_byte i (immutable_transfers T T a (n2w b) n 0 s).vs_memory =
      read_byte i s.vs_memory
Proof
  Induct >- simp[immutable_transfers_def] >> rpt gen_tac >> strip_tac >>
  `b + 32*n < dimword (:256) /\ b + 32*n < dimword (:256)` by decide_tac >>
  simp[immutable_transfers_snoc, immutable_transfer_read_byte,
       word_add_n2w, w2n_n2w] >>
  `~(b + 32*n <= i /\ i < b + 32*n + 32)` by decide_tac >>
  simp[] >> first_x_assum irule >> simp[] >> decide_tac
QED

Theorem immutable_transfers_read_byte_prefix:
  !n a b s k i.
    k <= 32*n /\ a+k < dimword (:256) /\ b+32*n < dimword (:256) /\
    (a+k <= b \/ b+32*n <= a) /\ i < k ==>
    read_byte (b+i) (immutable_transfers T T (n2w a) (n2w b) n 0 s).vs_memory =
      read_byte (a+i) s.vs_memory
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >> (
  `b + 32*n < dimword (:256)` by decide_tac >>
  simp[immutable_transfers_snoc, immutable_transfer_read_byte,
       word_add_n2w, w2n_n2w] >>
  Cases_on `i < 32*n`
  >- (simp[] >> first_x_assum irule >> simp[] >> qexists `MIN k (32*n)` >>
      simp[] >> Cases_on `k <= 32*n` >> gvs[arithmeticTheory.MIN_DEF] >> decide_tac) >>
  `a + 32*n < dimword (:256)` by decide_tac >>
  simp[] >>
  `b + i - (b + 32*n) = i - 32*n` by decide_tac >>
  `a + 32*n + (i - 32*n) = a + i` by decide_tac >>
  simp[] >> irule immutable_transfers_read_byte_frame >> simp[] >> decide_tac)
QED

Theorem immutable_mem_bytes_read_byte:
  i < k ==> EL i (mem_bytes_at off k mem) = read_byte (off+i) mem
Proof
  strip_tac >> simp[mem_bytes_at_def, EL_TAKE, EL_APPEND_EQN, EL_DROP,
                   EL_REPLICATE, read_byte_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem immutable_transfers_memory_prefix:
  k <= 32*n /\ a+k < dimword (:256) /\ b+32*n < dimword (:256) /\
  (a+k <= b \/ b+32*n <= a) ==>
  mem_bytes_at b k (immutable_transfers T T (n2w a) (n2w b) n 0 s).vs_memory =
    mem_bytes_at a k s.vs_memory
Proof
  strip_tac >> irule LIST_EQ >> simp[] >> rpt strip_tac >>
  simp[immutable_mem_bytes_read_byte] >>
  irule immutable_transfers_read_byte_prefix >> simp[] >>
  qexists `k` >> simp[]
QED

Theorem immutable_transfers_memory_frame:
  b+32*n < dimword (:256) /\ (p+k <= b \/ b+32*n <= p) ==>
  mem_bytes_at p k (immutable_transfers T T a (n2w b) n 0 s).vs_memory =
    mem_bytes_at p k s.vs_memory
Proof
  strip_tac >> irule LIST_EQ >> simp[] >> rpt strip_tac >>
  simp[immutable_mem_bytes_read_byte] >>
  irule immutable_transfers_read_byte_frame >> simp[] >> decide_tac
QED

Theorem compile_imm_store_words_prefix:
  compile_imm_store_words (SOME region) src dst n 0 st = ((),st') /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  eval_operand region s = SOME 0w /\ fresh_vars_wrt st s /\
  k <= 32*n /\ a+k < dimword (:256) /\ b+32*n < dimword (:256) /\
  (a+k <= b \/ b+32*n <= a) ==>
  ?s'. immutable_execution_frame st s st' s' /\
    mem_bytes_at b k s'.vs_memory = mem_bytes_at a k s.vs_memory /\
    (!p len. p+len <= b \/ b+32*n <= p ==>
       mem_bytes_at p len s'.vs_memory = mem_bytes_at p len s.vs_memory) /\
    s'.vs_immutables = (immutable_transfers T T (n2w a) (n2w b) n 0 s).vs_immutables
Proof
  strip_tac >> (
  drule_all compile_imm_store_words_execution >> strip_tac >>
  qexists `s'` >> simp[] >> conj_tac
  >- (irule immutable_transfers_memory_prefix >> simp[]) >>
  rpt strip_tac >> irule immutable_transfers_memory_frame >> simp[])
QED
