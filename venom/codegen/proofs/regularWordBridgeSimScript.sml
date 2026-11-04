Theory regularWordBridgeSim
Ancestors
  words byte list rich_list venomExecSemantics vfmExecution
Libs
  wordsLib

Theorem byte_widen_narrow_mask[local]:
  (w2w ((w2w (y:bytes32)):word8):bytes32) = y && 255w
Proof
  wordsLib.WORD_DECIDE_TAC
QED

Theorem asm_byte_eq_evm_byte:
  (if w2n (n:bytes32) < 32 then w2w (get_byte n (x:bytes32) T) else 0w) =
  evm_byte n x
Proof
  Cases_on `w2n n < 32` >>
  simp[evm_byte_def, byteTheory.get_byte_def, byteTheory.byte_index_def,
       byte_widen_narrow_mask]
QED

Theorem asm_sign_extend_large[local]:
  31 < w2n (n:bytes32) ==>
  vfmExecution$sign_extend n x = venomExecSemantics$sign_extend n x
Proof
  strip_tac >> `31 - w2n n = 0` by decide_tac >>
  simp[vfmExecutionTheory.sign_extend_def,
       venomExecSemanticsTheory.sign_extend_def, WORD_GREATER,
       word_lo_def, word_of_bytes_word_to_bytes]
QED

Theorem asm_sign_extend_full_width[local]:
  w2n (n:bytes32) = 31 ==>
  vfmExecution$sign_extend n x = venomExecSemantics$sign_extend n x
Proof
  strip_tac >>
  simp[vfmExecutionTheory.sign_extend_def,
       venomExecSemanticsTheory.sign_extend_def, word_of_bytes_word_to_bytes]
QED

Theorem first_byte_at_contiguous[local]:
  !bs a j. a + LENGTH bs <= 32 /\ a <= j /\ j < a + LENGTH bs ==>
  first_byte_at 32 j (n2w a:bytes32) bs = EL (j-a) bs
Proof
  Induct >> simp[] >> rpt strip_tac >>
  simp[Once first_byte_at_def] >>
  Cases_on `j = a` >- gvs[] >>
  `a < 32` by decide_tac >>
  `j - a = SUC (j - (a+1))` by decide_tac >>
  simp[word_add_n2w, EL] >>
  first_x_assum irule >> decide_tac
QED

Theorem get_byte_word_of_bytes_32[local]:
  LENGTH bs = 32 /\ j < 32 ==>
  get_byte (n2w j) (word_of_bytes T 0w bs:bytes32) T = EL j bs
Proof
  strip_tac >>
  simp[get_byte_word_of_bytes_be] >>
  qspec_then `bs` (qspec_then `0` mp_tac) first_byte_at_contiguous >>
  simp[]
QED

Theorem sign_extend_bytes_get_byte[local]:
  k < 31 /\ j < 32 ==>
  get_byte (n2w j)
    (word_of_bytes T 0w
      (REPLICATE (31-k) b ++ DROP (31-k) (word_to_bytes (x:bytes32) T)):bytes32) T =
  if j < 31-k then b else get_byte (n2w j) x T
Proof
  strip_tac >>
  `LENGTH (REPLICATE (31-k) b ++ DROP (31-k) (word_to_bytes x T)) = 32`
    by simp[] >>
  simp[get_byte_word_of_bytes_32] >>
  Cases_on `j < 31-k`
  >- simp[EL_APPEND1, EL_REPLICATE] >>
  simp[EL_APPEND2, EL_DROP] >>
  simp[word_to_bytes_def, EL_word_to_bytes_aux]
QED

Theorem asm_sign_extend_get_byte[local]:
  k < 31 /\ j < 32 ==>
  get_byte (n2w j) (vfmExecution$sign_extend (n2w k:bytes32) x) T =
  if j < 31-k then
    (if get_byte (n2w (31-k)) x T >> 7 = 0w then 0w else 255w)
  else get_byte (n2w j) x T
Proof
  strip_tac >>
  `~NULL (DROP (31-k) (word_to_bytes (x:bytes32) T))`
    by (simp[NULL_EQ, LENGTH_NIL] >> decide_tac) >>
  `HD (DROP (31-k) (word_to_bytes x T)) = get_byte (n2w (31-k)) x T`
    by simp[HD_DROP, word_to_bytes_def, EL_word_to_bytes_aux] >>
  simp[vfmExecutionTheory.sign_extend_def, WORD_GREATER,
       word_lt_n2w, sign_extend_bytes_get_byte]
QED

Theorem venom_sign_extend_get_byte[local]:
  k < 31 /\ j < 32 ==>
  get_byte (n2w j) (venomExecSemantics$sign_extend (n2w k:bytes32) x) T =
  if j < 31-k then
    (if get_byte (n2w (31-k)) x T >> 7 = 0w then 0w else 255w)
  else get_byte (n2w j) x T
Proof
  strip_tac >>
  simp[venomExecSemanticsTheory.sign_extend_def, get_byte_def, byte_index_def] >>
  pure_rewrite_tac[GSYM word_sub_def] >>
  qmatch_goalsub_abbrev_tac `word_1comp mask` >>
  `!i. i < 256 ==> (mask ' i <=> i < 8*k+8)`
    by simp[Abbr `mask`, SHIFT_1_SUB_1] >>
  srw_tac [wordsLib.WORD_BIT_EQ_ss] []
QED

Theorem asm_sign_extend_eq_venom:
  !n x:bytes32. vfmExecution$sign_extend n x = venomExecSemantics$sign_extend n x
Proof
  rpt gen_tac >>
  Cases_on `31 < w2n n` >- metis_tac[asm_sign_extend_large] >>
  Cases_on `w2n n = 31` >- metis_tac[asm_sign_extend_full_width] >>
  `w2n n < 31` by decide_tac >>
  irule word_eq_of_get_byte >>
  simp[dividesTheory.compute_divides] >>
  qexists_tac `T` >> rpt strip_tac >>
  mp_tac (Q.INST [`k` |-> `w2n (n:bytes32)`] asm_sign_extend_get_byte) >>
  mp_tac (Q.INST [`k` |-> `w2n (n:bytes32)`] venom_sign_extend_get_byte) >>
  simp[]
QED
