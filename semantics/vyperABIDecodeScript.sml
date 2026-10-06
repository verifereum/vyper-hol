Theory vyperABIDecode
Ancestors
  contractABI
  arithmetic bit byte combin list rich_list pair numposrep
  integer words integer_word cv cv_std vfmTypes
Libs
  cv_transLib wordsLib

(* ===== Vyper-specific ABI decoding =====

   TOP-LEVEL (API):
     vyper_abi_dec          decode an abi_value at a buffer offset
     vyper_abi_valid_enc    acceptance gate for vyper_abi_dec (Vyper clamps)

   Helper (internal):
     vyper_abi_dec_array / vyper_abi_dec_tuple
     vyper_abi_valid_enc_array / vyper_abi_valid_enc_tuple
     vyper_abi_head_target

   This theory is heavily based on verifereum's contractABI `dec`/`valid_enc`,
   changing only the head-offset arithmetic.  Vyper computes ABI head targets
   with EVM pointer arithmetic `base + head` in 256-bit words, which wraps
   modulo 2**256: a head word close to 2**256 points back into data preceding
   the sub-buffer (Vyper's "lenient" offset arithmetic, preserved for
   calldata and CODE/constructor argument decoding; see the test_abi_arg_wrapped
   cases in Vyper's test_abi_decode.py).  The contractABI decoder instead
   treats heads as plain list offsets without wrap-around, reading empty data
   past the end.

   Representation: decoding threads the whole buffer `bs` together with the
   byte offset `off` at which the current value starts, so a wrapped head can
   land anywhere in `bs`, including before the current sub-buffer.  Reads at
   or past the end of `bs` yield zeros/empty, matching EVM calldata/code
   reads.  When no head wraps (base + head < 2**256), this coincides with
   contractABI's dec/valid_enc applied to the suffix of bs at off. *)

(* Helper: where a head word lands.  The only change vs. contractABI, which
   uses `DROP head bs` with unbounded offsets: the EVM wraps at 2**256. *)
Definition vyper_abi_head_target_def:
  vyper_abi_head_target (base:num) (head:num) = (base + head) MOD dimword(:256)
End

val () = cv_auto_trans vyper_abi_head_target_def;

(* TOP-LEVEL: Vyper's ABI decoding.  Mirrors contractABI's dec, threading the
   whole buffer and the offset of the current value instead of suffixes. *)
Definition vyper_abi_dec_def:
  vyper_abi_dec (Tuple ts) bs off = vyper_abi_dec_tuple ts bs off off [] ∧
  vyper_abi_dec (Array (SOME n) t) bs off = (
    let lt = if is_dynamic t then NONE else SOME $ static_length t in
    vyper_abi_dec_array n lt t bs off off [] ) ∧
  vyper_abi_dec (Array NONE t) bs off = (
    let lt = if is_dynamic t then NONE else SOME $ static_length t in
    let n = dest_NumV (dec_number (Uint 256) (TAKE 32 (DROP off bs))) in
    let h = off + 32 in
      vyper_abi_dec_array n lt t bs h h [] ) ∧
  vyper_abi_dec (Bytes NONE) bs off = (
    let k = dest_NumV (dec_number (Uint 256) (TAKE 32 (DROP off bs))) in
      BytesV (TAKE k (DROP (off + 32) bs)) ) ∧
  vyper_abi_dec String bs off = (
    let k = dest_NumV (dec_number (Uint 256) (TAKE 32 (DROP off bs))) in
      BytesV (TAKE k (DROP (off + 32) bs)) ) ∧
  vyper_abi_dec (Bytes (SOME m)) bs off = BytesV $ TAKE m (DROP off bs) ∧
  vyper_abi_dec t bs off = dec_number t (TAKE 32 (DROP off bs)) ∧
  vyper_abi_dec_array 0 _ _ _ _ _ acc = ListV (REVERSE acc) ∧
  vyper_abi_dec_array (SUC n) NONE t bs boff hoff acc = (
    let j = dest_NumV (dec_number (Uint 256) (TAKE 32 (DROP hoff bs))) in
    let v = vyper_abi_dec t bs (vyper_abi_head_target boff j) in
    vyper_abi_dec_array n NONE t bs boff (hoff + 32) (v::acc) ) ∧
  vyper_abi_dec_array (SUC n) (SOME l) t bs boff hoff acc = (
    let v = vyper_abi_dec t bs hoff in
    vyper_abi_dec_array n (SOME l) t bs boff (hoff + l) (v::acc) ) ∧
  vyper_abi_dec_tuple [] _ _ _ acc = ListV (REVERSE acc) ∧
  vyper_abi_dec_tuple (t::ts) bs boff hoff acc =
    if is_dynamic t then
      let j = dest_NumV (dec_number (Uint 256) (TAKE 32 (DROP hoff bs))) in
      let v = vyper_abi_dec t bs (vyper_abi_head_target boff j) in
      vyper_abi_dec_tuple ts bs boff (hoff + 32) (v::acc)
    else
      let n = static_length t in
      let v = vyper_abi_dec t bs hoff in
      vyper_abi_dec_tuple ts bs boff (hoff + n) (v::acc)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    (INR (INR (ts,_,_,_,_))) => (list_size abi_type_size ts, 0)
  | (INR (INL (n,_,t,_,_,_,_))) => (abi_type_size t, n)
  | (INL (t,_,_)) => (abi_type_size t, 0))’
End

val pre = cv_trans_pre_rec
  "vyper_abi_dec_pre vyper_abi_dec_array_pre vyper_abi_dec_tuple_pre"
  vyper_abi_dec_def (
  WF_REL_TAC ‘inv_image ($< LEX $<)
  (λx. case x of
    (INR (INR (ts,_,_,_,_))) => (cv_size ts, 0)
  | (INR (INL (n,_,t,_,_,_,_))) => (cv_size t, cv$c2n n)
  | (INL (t,_,_)) => (cv_size t, 0))’
  \\ rpt conj_tac
  \\ Cases_on`cv_v` \\ rw[] \\ gs[cv_lt_Num_0]
  \\ qmatch_goalsub_rename_tac`cv_snd p`
  \\ Cases_on`p` \\ gs[]
);

Theorem vyper_abi_dec_pre[cv_pre]:
  (∀v bs off. vyper_abi_dec_pre v bs off) ∧
  (∀v0 v v1 v2 v3 v4 acc. vyper_abi_dec_array_pre v0 v v1 v2 v3 v4 acc) ∧
  (∀v v4 v5 v6 acc. vyper_abi_dec_tuple_pre v v4 v5 v6 acc)
Proof
  ho_match_mp_tac vyper_abi_dec_ind
  \\ rw[]
  \\ rw[Once pre]
QED

(* TOP-LEVEL: the acceptance gate for vyper_abi_dec.  Mirrors contractABI's
   valid_enc with the same wrap-around head arithmetic as vyper_abi_dec. *)
Definition vyper_abi_valid_enc_def:
  vyper_abi_valid_enc (Tuple ts) bs off =
    (LENGTH ts < dimword (:256) ∧
     vyper_abi_valid_enc_tuple ts bs off off) ∧
  vyper_abi_valid_enc (Array (SOME n) t) bs off =
    (let lt = if is_dynamic t then NONE else SOME $ static_length t in
     n < dimword (:256) ∧
     vyper_abi_valid_enc_array n lt t bs off off) ∧
  vyper_abi_valid_enc (Array NONE t) bs off =
    (off + 32 ≤ LENGTH bs ∧
     let
       lt = if is_dynamic t then NONE else SOME $ static_length t;
       dn = dec_number (Uint 256) (TAKE 32 (DROP off bs))
     in is_num_value dn ∧ let
       n = dest_NumV dn;
       h = off + 32
     in n < dimword (:256) ∧
        vyper_abi_valid_enc_array n lt t bs h h) ∧
  vyper_abi_valid_enc (Bytes NONE) bs off =
    (off + 32 ≤ LENGTH bs ∧
     let
       ls = TAKE 32 (DROP off bs);
       rest = DROP (off + 32) bs;
       dn = dec_number (Uint 256) ls
     in is_num_value dn ∧ let
       n = dest_NumV dn;
       pn = ceil32 n
     in
       n ≤ LENGTH rest ∧
       EVERY ((=) 0w) (DROP n (TAKE pn rest))) ∧
  vyper_abi_valid_enc String bs off =
    (off + 32 ≤ LENGTH bs ∧
     let
       ls = TAKE 32 (DROP off bs);
       rest = DROP (off + 32) bs;
       dn = dec_number (Uint 256) ls
     in is_num_value dn ∧ let
       n = dest_NumV dn;
       pn = ceil32 n
     in
       n ≤ LENGTH rest ∧
       EVERY ((=) 0w) (DROP n (TAKE pn rest))) ∧
  vyper_abi_valid_enc (Bytes (SOME m)) bs off =
    (valid_bytes_bound (SOME m) ∧
     m ≤ LENGTH (DROP off bs) ∧
     EVERY ((=) 0w) (DROP m (TAKE 32 (DROP off bs)))) ∧
  vyper_abi_valid_enc t bs off =
    (off + 32 ≤ LENGTH bs ∧
     let v = dec_number t (TAKE 32 (DROP off bs)) in
     has_type t v) ∧
  vyper_abi_valid_enc_array 0 _ _ _ _ _ = T ∧
  vyper_abi_valid_enc_array (SUC n) NONE t bs boff hoff =
    (hoff + 32 ≤ LENGTH bs ∧
     let
       dn = dec_number (Uint 256) (TAKE 32 (DROP hoff bs))
     in is_num_value dn ∧ let
       j = dest_NumV dn
     in
       vyper_abi_valid_enc t bs (vyper_abi_head_target boff j) ∧
       vyper_abi_valid_enc_array n NONE t bs boff (hoff + 32)) ∧
  vyper_abi_valid_enc_array (SUC n) (SOME l) t bs boff hoff =
    (hoff + l ≤ LENGTH bs ∧
     vyper_abi_valid_enc t bs hoff ∧
     vyper_abi_valid_enc_array n (SOME l) t bs boff (hoff + l)) ∧
  vyper_abi_valid_enc_tuple [] _ _ _ = T ∧
  vyper_abi_valid_enc_tuple (t::ts) bs boff hoff =
    (if is_dynamic t then
       hoff + 32 ≤ LENGTH bs ∧
       let
         dn = dec_number (Uint 256) (TAKE 32 (DROP hoff bs))
       in is_num_value dn ∧ let
         j = dest_NumV dn
       in
         vyper_abi_valid_enc t bs (vyper_abi_head_target boff j) ∧
         vyper_abi_valid_enc_tuple ts bs boff (hoff + 32)
     else let
       n = static_length t
     in
       hoff + n ≤ LENGTH bs ∧
       vyper_abi_valid_enc t bs hoff ∧
       vyper_abi_valid_enc_tuple ts bs boff (hoff + n))
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    (INR (INR (ts,_,_,_))) => (list_size abi_type_size ts, 0)
  | (INR (INL (n,_,t,_,_,_))) => (abi_type_size t, n)
  | (INL (t,_,_)) => (abi_type_size t, 0))’
End

val pre = cv_trans_pre_rec
  "vyper_abi_valid_enc_pre vyper_abi_valid_enc_array_pre vyper_abi_valid_enc_tuple_pre"
  (PURE_REWRITE_RULE [every_zero_intro] vyper_abi_valid_enc_def) (
  WF_REL_TAC ‘inv_image ($< LEX $<)
  (λx. case x of
    (INR (INR (ts,_,_,_))) => (cv_size ts, 0)
  | (INR (INL (n,_,t,_,_,_))) => (cv_size t, cv$c2n n)
  | (INL (t,_,_)) => (cv_size t, 0))’
  \\ rpt conj_tac
  \\ Cases_on`cv_v` \\ rw[] \\ gs[cv_lt_Num_0]
  \\ qmatch_goalsub_rename_tac`cv_snd p`
  \\ Cases_on`p` \\ gs[]
);

Theorem vyper_abi_valid_enc_pre[cv_pre]:
  (∀v bs off. vyper_abi_valid_enc_pre v bs off) ∧
  (∀v0 v v1 v2 v3 v4. vyper_abi_valid_enc_array_pre v0 v v1 v2 v3 v4) ∧
  (∀v v4 v5 v6. vyper_abi_valid_enc_tuple_pre v v4 v5 v6)
Proof
  ho_match_mp_tac vyper_abi_valid_enc_ind
  \\ rpt strip_tac
  \\ once_rewrite_tac [pre]
  \\ simp []
QED

(* Helper: without 2**256 wrap-around, the head target is plain addition,
   i.e. the contractABI `DROP head bs0` offset. *)
Theorem vyper_abi_head_target_no_wrap:
  ∀base head. base + head < dimword(:256) ⇒
    vyper_abi_head_target base head = base + head
Proof
  rw[vyper_abi_head_target_def]
QED
