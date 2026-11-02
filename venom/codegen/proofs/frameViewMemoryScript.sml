Theory frameViewMemory
Ancestors
  venomState codegenRel list rich_list arithmetic

Theorem padded_memory_read_bytes:
  !off n (mem:byte list).
  TAKE n (DROP off mem ++ REPLICATE n 0w) =
  GENLIST (\i. read_byte (off + i) mem) n
Proof
  rpt gen_tac >>
  simp[LIST_EQ_REWRITE, LENGTH_TAKE_EQ, LENGTH_GENLIST,
       LENGTH_APPEND, LENGTH_DROP] >> rpt strip_tac >>
  `x < MIN n (LENGTH (DROP off mem) + n)` by simp[MIN_DEF] >>
  simp[EL_TAKE, EL_GENLIST, read_byte_def] >>
  Cases_on `off + x < LENGTH mem`
  >- (`x < LENGTH (DROP off mem)` by (simp[LENGTH_DROP] >> decide_tac) >>
      simp[EL_APPEND1, EL_DROP])
  >> `LENGTH (DROP off mem) <= x` by (simp[LENGTH_DROP] >> decide_tac) >>
     `x - LENGTH (DROP off mem) < n` by decide_tac >>
     simp[EL_APPEND2, EL_REPLICATE]
QED

Theorem padded_memory_read_cong:
  (!i. off <= i /\ i < off + n ==> read_byte i m = read_byte i mem) ==>
  TAKE n (DROP off m ++ REPLICATE n 0w) =
  TAKE n (DROP off mem ++ REPLICATE n 0w)
Proof
  strip_tac >> simp[padded_memory_read_bytes, LIST_EQ_REWRITE] >>
  rpt strip_tac >> simp[EL_GENLIST]
QED

Theorem read_byte_append_zero:
  read_byte i (mem ++ REPLICATE n 0w) = read_byte i mem
Proof
  simp[read_byte_def] >> Cases_on `i < LENGTH mem`
  >- simp[EL_APPEND1]
  >> Cases_on `i < LENGTH mem + n` >> simp[EL_APPEND2, EL_REPLICATE]
QED

Theorem read_byte_splice:
  off + LENGTH bytes <= LENGTH mem ==>
  read_byte i (TAKE off mem ++ bytes ++ DROP (off + LENGTH bytes) mem) =
  if off <= i /\ i < off + LENGTH bytes then EL (i - off) bytes
  else read_byte i mem
Proof
  strip_tac >>
  `LENGTH (TAKE off mem) = off` by simp[LENGTH_TAKE_EQ] >>
  simp[read_byte_def] >> Cases_on `i < LENGTH mem`
  >- (Cases_on `i < off`
      >- simp[EL_APPEND1, EL_TAKE]
      >> Cases_on `i < off + LENGTH bytes`
      >- simp[EL_APPEND2, EL_APPEND1]
      >> simp[EL_APPEND2, EL_DROP])
  >> simp[]
QED

Theorem read_byte_write_memory_with_expansion:
  read_byte i (write_memory_with_expansion off bytes s).vs_memory =
  if off <= i /\ i < off + LENGTH bytes then EL (i - off) bytes
  else read_byte i s.vs_memory
Proof
  simp[write_memory_with_expansion_def] >>
  IF_CASES_TAC >> simp[read_byte_splice, read_byte_append_zero]
QED

Theorem write_memory_byte_agreement:
  read_byte i s.vs_memory = read_byte i t.vs_memory ==>
  read_byte i (write_memory_with_expansion off bytes s).vs_memory =
  read_byte i (write_memory_with_expansion off bytes t).vs_memory
Proof
  simp[read_byte_write_memory_with_expansion]
QED

Theorem write_memory_byte_outside:
  ~(off <= i /\ i < off + LENGTH bytes) ==>
  read_byte i (write_memory_with_expansion off bytes s).vs_memory =
  read_byte i s.vs_memory
Proof
  simp[read_byte_write_memory_with_expansion]
QED

Theorem write_memory_byte_frame:
  LENGTH bytes <= n /\ ~(off <= i /\ i < off + n) ==>
  read_byte i (write_memory_with_expansion off bytes s).vs_memory =
  read_byte i s.vs_memory
Proof
  strip_tac >> irule write_memory_byte_outside >> decide_tac
QED
