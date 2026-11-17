(* Bitwise operations preserve the left-aligned fixed-byte word encoding. *)
Theory valueEncodingBitwise
Ancestors
  valueEncoding valueEncodingProofs vyperValue byte words list rich_list
Libs
  wordsLib

Theorem get_byte_bitwise:
  get_byte a (x && y : bytes32) T = get_byte a x T && get_byte a y T /\
  get_byte a (x || y : bytes32) T = get_byte a x T || get_byte a y T /\
  get_byte a (word_xor x y : bytes32) T = word_xor (get_byte a x T) (get_byte a y T)
Proof
  rw[get_byte_def] >> srw_tac[wordsLib.WORD_BIT_EQ_ss][]
QED

Theorem word_of_bytes_be_bitwise:
  LENGTH xs = LENGTH ys /\ LENGTH xs <= 32 ==>
  (word_of_bytes_be (MAP2 word_and xs ys) : bytes32) =
    word_of_bytes_be xs && word_of_bytes_be ys /\
  (word_of_bytes_be (MAP2 word_or xs ys) : bytes32) =
    word_of_bytes_be xs || word_of_bytes_be ys /\
  (word_of_bytes_be (MAP2 word_xor xs ys) : bytes32) =
    word_xor (word_of_bytes_be xs) (word_of_bytes_be ys)
Proof
  strip_tac >> rpt conj_tac >>
  irule (Q.INST [`be` |-> `T`]
    (INST_TYPE [alpha |-> ``:256``] word_eq_of_get_byte)) >>
  simp[dividesTheory.compute_divides] >> rpt strip_tac >>
  simp[get_byte_bitwise, word_of_bytes_be_def, get_byte_word_of_bytes_be,
       first_byte_at_0w, dimword_def] >>
  Cases_on `j < LENGTH ys` >> simp[EL_MAP2]
QED

Theorem typed_bytes_word:
  typed_val_to_w256 (BaseTV (BytesT (Fixed n))) (BytesV bs) =
    word_of_bytes_be bs
Proof
  simp[typed_val_to_w256_def, word_of_bytes_be_pad_right]
QED

