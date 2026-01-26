Theory vyperMisc
Ancestors
  byte pair int_bitwise rich_list
  cv_std vfmTypes
Libs
  cv_transLib blastLib

(* Miscellaneous definitions/theorems/translations that need to be organised
 * and upstreamed to HOL where appropriate *)

Definition CHR_o_w2n_def:
  CHR_o_w2n (b: byte) = CHR (w2n b)
End

val CHR_o_w2n_pre_def = cv_auto_trans_pre "CHR_o_w2n_pre" CHR_o_w2n_def;

Theorem CHR_o_w2n_pre[cv_pre]:
  CHR_o_w2n_pre x
Proof
  rw[CHR_o_w2n_pre_def]
  \\ qspec_then`x`mp_tac wordsTheory.w2n_lt
  \\ rw[]
QED

Theorem CHR_o_w2n_eq:
  CHR_o_w2n = CHR o w2n
Proof
  rw[FUN_EQ_THM, CHR_o_w2n_def]
QED

(* Inverse: convert char to word8 *)
Definition n2w_o_ORD_def:
  n2w_o_ORD (c: char) = (n2w (ORD c) : word8)
End

val () = cv_auto_trans n2w_o_ORD_def;

Theorem n2w_o_ORD_eq:
  n2w_o_ORD = n2w o ORD
Proof
  rw[FUN_EQ_THM, n2w_o_ORD_def]
QED

Definition MAP_HEX_def:
  MAP_HEX [] = [] ∧
  MAP_HEX (x::xs) = HEX x :: MAP_HEX xs
End

val MAP_HEX_pre_def = cv_auto_trans_pre "MAP_HEX_pre" MAP_HEX_def;

Theorem MAP_HEX_pre_EVERY:
  MAP_HEX_pre ls = EVERY (λx. x < 16) ls
Proof
  Induct_on`ls` \\ rw[Once MAP_HEX_pre_def]
QED

Theorem MAP_HEX_MAP:
  MAP_HEX = MAP HEX
Proof
  simp[FUN_EQ_THM]
  \\ Induct \\ rw[MAP_HEX_def]
QED

val num_to_dec_string_pre_def =
  ASCIInumbersTheory.num_to_dec_string_def
  |> SRULE [ASCIInumbersTheory.n2s_def, FUN_EQ_THM, GSYM MAP_HEX_MAP]
  |> cv_trans_pre "num_to_dec_string_pre";

Theorem num_to_dec_string_pre[cv_pre]:
  num_to_dec_string_pre x
Proof
  rw[num_to_dec_string_pre_def, MAP_HEX_pre_EVERY]
  \\ qspecl_then[`10`,`x`]mp_tac numposrepTheory.n2l_BOUND
  \\ rw[listTheory.EVERY_MEM]
  \\ first_x_assum drule \\ rw[]
QED

Theorem int_exp_num:
  (i:int) ** n =
  if 0 ≤ i then &(Num i ** n)
  else if EVEN n then &(Num (-i) ** n)
  else -&(Num (-i) ** n)
Proof
  Cases_on`i` \\ simp[integerTheory.INT_POW_NEG]
QED

val () = cv_trans int_exp_num;

Theorem Num_int_exp:
  0 ≤ i ⇒ Num (i ** n) = Num i ** n
Proof
  Cases_on`i` \\ rw[]
QED

(* TODO: I don't know if this is the best way to translate this... *)
val () = cv_auto_trans num_of_bits_def;
val () = cv_auto_trans int_of_bits_def;
val () = cv_auto_trans bits_of_int_def;

Definition bits_bitwise_and_def:
  bits_bitwise_and = bits_bitwise $/\
End

val bits_bitwise_and_pre_def = (bits_bitwise_def
 |> oneline
 |> Q.GEN`f`
 |> Q.ISPEC`$/\`
 |> SRULE [GSYM bits_bitwise_and_def]
 |> cv_trans_pre_rec "bits_bitwise_and_pre")
    (WF_REL_TAC `inv_image ($< LEX $<) (λ(x,y). (cv_size x, cv_size y))`
     \\ rw[]
     \\ Cases_on`cv_v` \\ gvs[]
     \\ Cases_on`cv_v0` \\ gvs[]
     \\ qmatch_assum_rename_tac`_ (cv_ispair p)`
     \\ Cases_on`p` \\ gvs[]
     \\ qmatch_assum_rename_tac`_ (cv_ispair p)`
     \\ Cases_on`p` \\ gvs[]);

Theorem bits_bitwise_and_pre[cv_pre]:
  ∀x y. bits_bitwise_and_pre x y
Proof
  simp[FORALL_PROD]
  \\ qid_spec_tac`f:bool -> bool -> bool`
  \\ ho_match_mp_tac bits_bitwise_ind
  \\ rw[]
  \\ rw[Once bits_bitwise_and_pre_def]
QED

val () = int_and_def
  |> SRULE [FUN_EQ_THM, int_bitwise_def, GSYM bits_bitwise_and_def]
  |> cv_trans;

Definition bits_bitwise_or_def:
  bits_bitwise_or = bits_bitwise $\/
End

val bits_bitwise_or_pre_def = (bits_bitwise_def
 |> oneline
 |> Q.GEN`f`
 |> Q.ISPEC`$\/`
 |> SRULE [GSYM bits_bitwise_or_def]
 |> cv_trans_pre_rec "bits_bitwise_or_pre")
    (WF_REL_TAC `inv_image ($< LEX $<) (λ(x,y). (cv_size x, cv_size y))`
     \\ rw[]
     \\ Cases_on`cv_v` \\ gvs[]
     \\ Cases_on`cv_v0` \\ gvs[]
     \\ qmatch_assum_rename_tac`_ (cv_ispair p)`
     \\ Cases_on`p` \\ gvs[]
     \\ qmatch_assum_rename_tac`_ (cv_ispair p)`
     \\ Cases_on`p` \\ gvs[]);

Theorem bits_bitwise_or_pre[cv_pre]:
  ∀x y. bits_bitwise_or_pre x y
Proof
  simp[FORALL_PROD]
  \\ qid_spec_tac`f:bool -> bool -> bool`
  \\ ho_match_mp_tac bits_bitwise_ind
  \\ rw[]
  \\ rw[Once bits_bitwise_or_pre_def]
QED

val () = int_or_def
  |> SRULE [FUN_EQ_THM, int_bitwise_def, GSYM bits_bitwise_or_def]
  |> cv_trans;

Definition bits_bitwise_xor_def:
  bits_bitwise_xor = bits_bitwise ((≠) : bool -> bool -> bool)
End

val bits_bitwise_xor_pre_def = (bits_bitwise_def
 |> oneline
 |> Q.GEN`f`
 |> Q.ISPEC`λx:bool y. x ≠ y`
 |> SRULE [GSYM bits_bitwise_xor_def]
 |> cv_trans_pre_rec "bits_bitwise_xor_pre")
    (WF_REL_TAC `inv_image ($< LEX $<) (λ(x,y). (cv_size x, cv_size y))`
     \\ rw[]
     \\ Cases_on`cv_v` \\ gvs[]
     \\ Cases_on`cv_v0` \\ gvs[]
     \\ qmatch_assum_rename_tac`_ (cv_ispair p)`
     \\ Cases_on`p` \\ gvs[]
     \\ qmatch_assum_rename_tac`_ (cv_ispair p)`
     \\ Cases_on`p` \\ gvs[]);

Theorem bits_bitwise_xor_pre[cv_pre]:
  ∀x y. bits_bitwise_xor_pre x y
Proof
  simp[FORALL_PROD]
  \\ qid_spec_tac`f:bool -> bool -> bool`
  \\ ho_match_mp_tac bits_bitwise_ind
  \\ rw[]
  \\ rw[Once bits_bitwise_xor_pre_def]
QED

val () = int_xor_def
  |> SRULE [FUN_EQ_THM, int_bitwise_def, GSYM bits_bitwise_xor_def]
  |> cv_trans;

val () = cv_auto_trans int_shift_left_def;
val () = cv_auto_trans int_shift_right_def;

Theorem set_byte_160:
  set_byte a b (w: 160 word) be =
  let i = byte_index a be in
       if i =   0 then w2w b        || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00w
  else if i =   8 then w2w b <<   8 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFw
  else if i =  16 then w2w b <<  16 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFw
  else if i =  24 then w2w b <<  24 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFw
  else if i =  32 then w2w b <<  32 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFw
  else if i =  40 then w2w b <<  40 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFw
  else if i =  48 then w2w b <<  48 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFw
  else if i =  56 then w2w b <<  56 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFw
  else if i =  64 then w2w b <<  64 || w && 0xFFFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFw
  else if i =  72 then w2w b <<  72 || w && 0xFFFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFw
  else if i =  80 then w2w b <<  80 || w && 0xFFFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFw
  else if i =  88 then w2w b <<  88 || w && 0xFFFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFw
  else if i =  96 then w2w b <<  96 || w && 0xFFFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 104 then w2w b << 104 || w && 0xFFFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 112 then w2w b << 112 || w && 0xFFFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 120 then w2w b << 120 || w && 0xFFFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 128 then w2w b << 128 || w && 0xFFFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 136 then w2w b << 136 || w && 0xFFFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 144 then w2w b << 144 || w && 0xFF00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else if i = 152 then w2w b << 152 || w && 0x00FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
  else                 w2w b << 160 || w && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFw
Proof
  rw_tac std_ss [set_byte_def, word_slice_alt_def]
  \\ reverse(rpt IF_CASES_TAC)
  >- (
    `i = 160`
    by (
      qunabbrev_tac`i`
      \\ full_simp_tac (std_ss ++ boolSimps.LET_ss ++ ARITH_ss) [
            byte_index_def, EVAL``dimindex(:160)``]
      \\ `w2n a MOD 20 < 20` by rw[]
      \\ pop_assum mp_tac
      \\ qmatch_goalsub_abbrev_tac`z < 20 ⇒ f`
      \\ simp_tac std_ss [wordsTheory.NUMERAL_LESS_THM]
      \\ strip_tac \\ gs[Abbr`f`]
      \\ rw[] \\ gs[] )
    \\ asm_simp_tac std_ss []
    \\ simp_tac (srw_ss()) []
    \\ BBLAST_TAC)
  \\ asm_simp_tac std_ss []
  \\ simp_tac (srw_ss()) []
  \\ BBLAST_TAC
QED

val () = cv_auto_trans set_byte_160;

val () = cv_auto_trans (INST_TYPE [alpha |-> “:160”] word_of_bytes_def);

Theorem SUM_MAP_FILTER_MEM_LE:
  MEM x ls /\ ~P x ==>
  SUM (MAP f (FILTER P ls)) + f x <= SUM (MAP f ls)
Proof
  qid_spec_tac`x`
  \\ Induct_on`ls`
  \\ rw[] \\ gs[]
  >- (
    irule SUM_SUBLIST \\ simp[]
    \\ irule MAP_SUBLIST \\ simp[]
    \\ irule FILTER_sublist )
  \\ first_x_assum drule \\ rw[]
QED

Theorem list_size_SUM_MAP:
  list_size f ls = LENGTH ls + SUM (MAP f ls)
Proof
  Induct_on `ls` \\ rw[listTheory.list_size_def]
QED

Theorem list_size_pair_size_map:
  list_size (pair_size f1 f2) ls =
  list_size f1 (MAP FST ls) +
  list_size f2 (MAP SND ls)
Proof
  Induct_on`ls` \\ rw[]
  \\ Cases_on`h` \\ gvs[]
QED

Definition member_def:
  member x [] = F ∧
  member x (y::ys) = ((x = y) ∨ member x ys)
End

val () = cv_trans member_def;

Theorem member_intro:
  ∀x ys. MEM x ys = member x ys
Proof
  Induct_on `ys` \\ rw[member_def]
QED

Theorem cv_size_cv_map_snd_le:
  ∀l. cv_size (cv_map_snd l) ≤ cv_size l
Proof
  ho_match_mp_tac cv_map_snd_ind
  \\ rw[]
  \\ rw[Once cv_map_snd_def] \\ gvs[]
  \\ Cases_on`l` \\ gvs[]
  \\ qmatch_goalsub_rename_tac`cv_snd p`
  \\ Cases_on`p` \\ gvs[]
QED

Definition string_to_num_def:
  string_to_num s = l2n 257 (MAP (SUC o ORD) s)
End

val () = cv_auto_trans string_to_num_def;

(* Integer square root using Newton's method iteration *)
Definition num_sqrt_aux_def:
  num_sqrt_aux n r =
    if r = 0 then 0
    else let r' = (r + n DIV r) DIV 2 in
      if r' < r then num_sqrt_aux n r'
      else r
Termination
  WF_REL_TAC `measure SND`
End

val () = cv_auto_trans num_sqrt_aux_def;

Definition num_sqrt_def:
  num_sqrt n = if n = 0 then 0 else num_sqrt_aux n n
End

val () = cv_auto_trans num_sqrt_def;
