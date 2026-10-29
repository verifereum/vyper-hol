Theory vyperABI
Ancestors
  contractABI vyperAST vyperValue vyperMisc vyperNsidFmap
  arithmetic byte combin cv cv_std divides
  finite_map list option pair rich_list string words
Libs
  cv_transLib wordsLib dep_rewrite

(* Overloads to disambiguate ABI value constructors from Vyper value constructors *)
Overload abi_IntV[local] = ``IntV : int -> abi_value``
Overload abi_BytesV[local] = ``BytesV : word8 list -> abi_value``

Definition vyper_base_to_abi_type_def[simp]:
  vyper_base_to_abi_type (UintT n) = Uint n ∧
  vyper_base_to_abi_type (IntT n) = Int n ∧
  vyper_base_to_abi_type BoolT = Bool ∧
  vyper_base_to_abi_type DecimalT = Int 168 ∧
  vyper_base_to_abi_type (StringT _) = String ∧
  vyper_base_to_abi_type (BytesT (Dynamic _)) = Bytes NONE ∧
  vyper_base_to_abi_type (BytesT (Fixed n)) = Bytes (SOME n) ∧
  vyper_base_to_abi_type AddressT = Address
End
val () = cv_auto_trans vyper_base_to_abi_type_def;

Definition vyper_to_abi_type_def[simp]:
  vyper_to_abi_type env (BaseT bt) = vyper_base_to_abi_type bt ∧
  vyper_to_abi_type env (TupleT ts) = Tuple (vyper_to_abi_types env ts) ∧
  vyper_to_abi_type env (ArrayT t (Dynamic _)) = Array NONE (vyper_to_abi_type env t) ∧
  vyper_to_abi_type env (ArrayT t (Fixed n)) = Array (SOME n) (vyper_to_abi_type env t) ∧
  vyper_to_abi_type env (StructT nsid) =
    (case FLOOKUP env nsid of
     | SOME (StructArgs args) => Tuple (vyper_to_abi_types (env \\ nsid) (MAP SND args))
     | _ => Tuple []) ∧
  vyper_to_abi_type env (FlagT _) = Uint 256 ∧
  vyper_to_abi_type env NoneT = Tuple [] ∧
  vyper_to_abi_types env [] = [] ∧
  vyper_to_abi_types env (t::ts) = vyper_to_abi_type env t :: vyper_to_abi_types env ts
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
      INL (env, t) => (CARD (FDOM env), type_size t)
    | INR (env, ts) => (CARD (FDOM env), list_size type_size ts))’
  \\ rw[FLOOKUP_DEF] >> gvs[]
  \\ disj1_tac
  \\ CCONTR_TAC
  \\ fs[]
End

val () = cv_auto_trans_rec vyper_to_abi_type_def (
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
      INL (env, t) => (cv_nsid_count env, cv_size t)
    | INR (env, ts) => (cv_nsid_count env, cv_size ts))’
  \\ rw[]
  \\ TRY (Cases_on `cv_v` \\ gvs[cv_size_def] \\ NO_TAC)
  \\ TRY (Cases_on `cv_v` \\ gvs[cv_size_def]
          \\ qmatch_goalsub_rename_tac `cv_fst cv_v`
          \\ Cases_on `cv_v` \\ gvs[cv_size_def] \\ NO_TAC)
  \\ disj1_tac
  \\ irule cv_nsid_delete_count
  \\ gvs[cv_nsid_ispair_bool]
);

Definition check_IntV_def:
  check_IntV b i =
  if within_int_bound b i then SOME $ IntV i else NONE
End

Definition abi_to_vyper_def[simp]:
  abi_to_vyper env (BaseT $ UintT z) (NumV n) = check_IntV (Unsigned z) (&n) ∧
  abi_to_vyper env (BaseT $ IntT z) (IntV i) = check_IntV (Signed z) i ∧
  abi_to_vyper env (BaseT $ AddressT) (NumV n) =
    (if within_int_bound (Unsigned 160) (&n)
     then SOME $ AddressV (n2w n)
     else NONE) ∧
  abi_to_vyper env (BaseT $ BoolT) (NumV n) =
    (if n ≤ 1 then SOME $ BoolV (n = 1) else NONE) ∧
  abi_to_vyper env (BaseT $ BytesT b) (BytesV bs) =
    (if compatible_bound b (LENGTH bs) then SOME $ BytesV bs else NONE) ∧
  abi_to_vyper env (BaseT $ StringT z) (BytesV bs) =
    (if LENGTH bs ≤ z then SOME $ StringV (MAP (CHR o w2n) bs) else NONE) ∧
  abi_to_vyper env (BaseT $ DecimalT) (IntV i) =
    (if within_int_bound decimal_bound i then SOME $ DecimalV i else NONE) ∧
  abi_to_vyper env (TupleT ts) (ListV vs) =
    (case abi_to_vyper_list env ts vs of NONE => NONE
        | SOME vs => SOME $ ArrayV $ TupleV vs) ∧
  abi_to_vyper env (ArrayT t b) (ListV vs) = (
    let n = LENGTH vs in
      if compatible_bound b n then
        case abi_to_vyper_list env (REPLICATE n t) vs of NONE => NONE
           | SOME vs => case evaluate_type env t of NONE => NONE
	     | SOME tv => SOME $ ArrayV $ make_array_value tv b vs
      else NONE ) ∧
  abi_to_vyper env NoneT (ListV ls) = (if NULL ls then SOME NoneV else NONE) ∧
  abi_to_vyper env (StructT nsid) (ListV vs) =
    (case FLOOKUP env nsid of
       | SOME (StructArgs args) =>
         (case abi_to_vyper_list (env \\ nsid) (MAP SND args) vs of NONE => NONE
          | SOME vs => SOME $ StructV $ ZIP (MAP FST args, vs))
       | _ => NONE) ∧
  abi_to_vyper env (FlagT nsid) (NumV n) =
    (case FLOOKUP env nsid of
      | SOME (FlagArgs m) =>
        if m ≤ 256 ∧ n < 2 ** m then SOME $ FlagV (&n) else NONE
      | _ => NONE) ∧
  abi_to_vyper _ _ _ = NONE ∧
  abi_to_vyper_list env [] [] = SOME [] ∧
  abi_to_vyper_list env (t::ts) (v::vs) =
    (case abi_to_vyper env t v of NONE => NONE | SOME v =>
       case abi_to_vyper_list env ts vs of NONE => NONE | SOME vs =>
         SOME (v::vs)) ∧
  abi_to_vyper_list _ _ _ = NONE
Termination
  WF_REL_TAC ‘measure (λx. case x of INL (_, _, v) => abi_value_size v
                                   | INR (_, _, vs) => list_size abi_value_size vs)’
End

val abi_to_vyper_pre_def =
  abi_to_vyper_def
  |> REWRITE_RULE[GSYM CHR_o_w2n_eq]
  |> cv_auto_trans_pre "abi_to_vyper_pre abi_to_vyper_list_pre";

Theorem abi_to_vyper_pre[cv_pre]:
  (!v1 v0 v. abi_to_vyper_pre v1 v0 v) ∧
  (!v1 v0 v. abi_to_vyper_list_pre v1 v0 v)
Proof
  ho_match_mp_tac abi_to_vyper_ind
  \\ rw[]
  \\ rw[Once abi_to_vyper_pre_def]
QED

(* Whether a Vyper type has dynamic ABI encoding, defined directly on Vyper types.
   This mirrors is_dynamic on ABI types but avoids calling vyper_to_abi_type. *)
Definition vyper_is_dynamic_def:
  vyper_is_dynamic env (BaseT (StringT _)) = T ∧
  vyper_is_dynamic env (BaseT (BytesT (Dynamic _))) = T ∧
  vyper_is_dynamic env (BaseT _) = F ∧
  vyper_is_dynamic env (TupleT ts) = vyper_any_dynamic env ts ∧
  vyper_is_dynamic env (ArrayT t (Dynamic _)) = T ∧
  vyper_is_dynamic env (ArrayT t (Fixed _)) = vyper_is_dynamic env t ∧
  vyper_is_dynamic env (StructT nsid) =
    (case FLOOKUP env nsid of
     | SOME (StructArgs args) => vyper_any_dynamic (env \\ nsid) (MAP SND args)
     | _ => F) ∧
  vyper_is_dynamic env (FlagT _) = F ∧
  vyper_is_dynamic env NoneT = F ∧
  vyper_any_dynamic env [] = F ∧
  vyper_any_dynamic env (t::ts) =
    (vyper_is_dynamic env t ∨ vyper_any_dynamic env ts)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
      INL (env, t) => (CARD (FDOM env), type_size t)
    | INR (env, ts) => (CARD (FDOM env), list_size type_size ts))’
  \\ rw[FLOOKUP_DEF] >> gvs[]
  \\ disj1_tac
  \\ CCONTR_TAC
  \\ fs[]
End

val () = cv_auto_trans_rec vyper_is_dynamic_def (
  WF_REL_TAC `inv_image ($< LEX $<) (λx. case x of
      INL (env, t) => (cv_nsid_count env, cv_size t)
    | INR (env, ts) => (cv_nsid_count env, cv_size ts))`
  \\ reverse $ rw[]
  \\ TRY (Cases_on `cv_v` \\ gvs[cv_size_def] \\ NO_TAC)
  >- (
    qmatch_goalsub_rename_tac`cv_snd cv_v`
    \\ Cases_on`cv_v` \\ gvs[]
    \\ qmatch_goalsub_rename_tac`cv_fst cv_v`
    \\ Cases_on`cv_v` \\ gvs[] )
  \\ disj1_tac
  \\ irule cv_nsid_delete_count
  \\ gvs[cv_nsid_ispair_bool]
);

(* Maximum encoding size for a Vyper type, matching Vyper's abi_type.size_bound().
   This is used to zero-pad calldata to model EVM semantics where reads past the
   end of calldata return zero bytes. The bounds for dynamic arrays and strings
   come from the Vyper type (not available in the ABI type alone). *)
Definition vyper_abi_size_bound_def:
  vyper_abi_size_bound env (BaseT (StringT n)) = 32 + ceil32 n ∧
  vyper_abi_size_bound env (BaseT (BytesT (Dynamic n))) = 32 + ceil32 n ∧
  vyper_abi_size_bound env (BaseT _) = 32 ∧
  vyper_abi_size_bound env (TupleT ts) =
    vyper_abi_size_bound_list env ts ∧
  vyper_abi_size_bound env (ArrayT t (Dynamic n)) =
    32 + n * vyper_abi_embedded_size env t ∧
  vyper_abi_size_bound env (ArrayT t (Fixed n)) =
    n * vyper_abi_embedded_size env t ∧
  vyper_abi_size_bound env (StructT nsid) =
    (case FLOOKUP env nsid of
     | SOME (StructArgs args) =>
         vyper_abi_size_bound_list (env \\ nsid) (MAP SND args)
     | _ => 0) ∧
  vyper_abi_size_bound env (FlagT _) = 32 ∧
  vyper_abi_size_bound env NoneT = 0 ∧
  vyper_abi_embedded_size env t =
    (if vyper_is_dynamic env t
     then 32 + vyper_abi_size_bound env t
     else vyper_abi_size_bound env t) ∧
  vyper_abi_size_bound_list env [] = 0 ∧
  vyper_abi_size_bound_list env (t::ts) =
    vyper_abi_embedded_size env t + vyper_abi_size_bound_list env ts
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    (* vyper_abi_size_bound *)
      INL (env, t) => (CARD (FDOM env), 2 * type_size t)
    (* vyper_abi_embedded_size *)
    | INR (INL (env, t)) => (CARD (FDOM env), 2 * type_size t + 1)
    (* vyper_abi_size_bound_list *)
    | INR (INR (env, ts)) => (CARD (FDOM env), 2 * list_size type_size ts))’
  \\ rw[FLOOKUP_DEF] >> gvs[]
  \\ TRY (disj1_tac \\ CCONTR_TAC \\ fs[] \\ NO_TAC)
  \\ simp[type_size_def]
End

val () = cv_auto_trans_rec vyper_abi_size_bound_def (
  WF_REL_TAC `inv_image ($< LEX $<) (λx. case x of
      INL (env, t) => (cv_nsid_count env, 2 * cv_size t)
    | INR (INL (env, t)) => (cv_nsid_count env, 2 * cv_size t + 1)
    | INR (INR (env, ts)) => (cv_nsid_count env, 2 * cv_size ts))`
  \\ rw[]
  \\ TRY (Cases_on `cv_v` \\ gvs[cv_size_def] \\ NO_TAC)
  \\ TRY (Cases_on `cv_v` \\ gvs[cv_size_def]
          \\ qmatch_goalsub_rename_tac `cv_fst cv_v`
          \\ Cases_on `cv_v` \\ gvs[cv_size_def] \\ NO_TAC)
  \\ disj1_tac
  \\ irule cv_nsid_delete_count
  \\ gvs[cv_nsid_ispair_bool]
);

(* ===== Vyper's stricter ABI decode validation =====
   See vyperABIValidScript. *)

Definition abi_head_word_def:
  abi_head_word (bs:byte list) = dest_NumV (dec_number (Uint 256) (TAKE 32 bs))
End

val () = cv_auto_trans abi_head_word_def;

Definition vyper_strict_enc_def:
  vyper_strict_enc env t bs =
    (static_length (vyper_to_abi_type env t) ≤ LENGTH bs ∧
     LENGTH bs ≤ vyper_abi_size_bound env t)
End

val () = cv_auto_trans vyper_strict_enc_def;

(* Vyper ignores the unused bytes in the final word of dynamic Bytes/String
   values.  This otherwise mirrors contractABI$valid_enc, retaining all
   head, length, scalar, fixed-bytes, array, and tuple checks. *)
Definition vyper_decode_valid_enc_def:
  vyper_decode_valid_enc (Tuple ts) bs =
    (LENGTH ts < dimword (:256) ∧
     vyper_decode_valid_enc_tuple ts bs bs) ∧
  vyper_decode_valid_enc (Array (SOME n) t) bs =
    (let lt = if is_dynamic t then NONE else SOME $ static_length t in
     n < dimword (:256) ∧
     vyper_decode_valid_enc_array n lt t bs bs) ∧
  vyper_decode_valid_enc (Array NONE t) bs =
    (32 ≤ LENGTH bs ∧
     let
       lt = if is_dynamic t then NONE else SOME $ static_length t;
       dn = dec_number (Uint 256) (TAKE 32 bs)
     in is_num_value dn ∧ let
       n = dest_NumV dn;
       rest = DROP 32 bs
     in n < dimword (:256) ∧
        vyper_decode_valid_enc_array n lt t rest rest) ∧
  vyper_decode_valid_enc (Bytes NONE) bs =
    (32 ≤ LENGTH bs ∧
     let
       dn = dec_number (Uint 256) (TAKE 32 bs);
       rest = DROP 32 bs
     in is_num_value dn ∧ dest_NumV dn ≤ LENGTH rest) ∧
  vyper_decode_valid_enc String bs =
    (32 ≤ LENGTH bs ∧
     let
       dn = dec_number (Uint 256) (TAKE 32 bs);
       rest = DROP 32 bs
     in is_num_value dn ∧ dest_NumV dn ≤ LENGTH rest) ∧
  vyper_decode_valid_enc (Bytes (SOME m)) bs =
    (valid_bytes_bound (SOME m) ∧
     m ≤ LENGTH bs ∧
     EVERY ((=) 0w) (DROP m (TAKE 32 bs))) ∧
  vyper_decode_valid_enc t bs =
    (32 ≤ LENGTH bs ∧
     let v = dec_number t (TAKE 32 bs) in has_type t v) ∧
  vyper_decode_valid_enc_array 0 _ _ _ _ = T ∧
  vyper_decode_valid_enc_array (SUC n) NONE t bs hds =
    (32 ≤ LENGTH hds ∧
     let dn = dec_number (Uint 256) (TAKE 32 hds)
     in is_num_value dn ∧ let j = dest_NumV dn
     in vyper_decode_valid_enc t (DROP j bs) ∧
        vyper_decode_valid_enc_array n NONE t bs (DROP 32 hds)) ∧
  vyper_decode_valid_enc_array (SUC n) (SOME l) t bs hds =
    (l ≤ LENGTH hds ∧
     vyper_decode_valid_enc t (TAKE l hds) ∧
     vyper_decode_valid_enc_array n (SOME l) t bs (DROP l hds)) ∧
  vyper_decode_valid_enc_tuple [] _ _ = T ∧
  vyper_decode_valid_enc_tuple (t::ts) bs hds =
    (if is_dynamic t then
       32 ≤ LENGTH hds ∧
       let dn = dec_number (Uint 256) (TAKE 32 hds)
       in is_num_value dn ∧ let j = dest_NumV dn
       in vyper_decode_valid_enc t (DROP j bs) ∧
          vyper_decode_valid_enc_tuple ts bs (DROP 32 hds)
     else let n = static_length t
     in n ≤ LENGTH hds ∧
        vyper_decode_valid_enc t (TAKE n hds) ∧
        vyper_decode_valid_enc_tuple ts bs (DROP n hds))
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
    (INR (INR (ts,_,_))) => (list_size abi_type_size ts, 0)
  | (INR (INL (n,_,t,_,_))) => (abi_type_size t, n)
  | (INL (t,_)) => (abi_type_size t, 0))’
End

val vyper_decode_valid_enc_pre_def = cv_trans_pre_rec
  "vyper_decode_valid_enc_pre vyper_decode_valid_enc_array_pre vyper_decode_valid_enc_tuple_pre"
  (PURE_REWRITE_RULE [every_zero_intro] vyper_decode_valid_enc_def) (
  WF_REL_TAC ‘inv_image ($< LEX $<)
  (λx. case x of
         (INR (INR (ts,_,_))) => (cv_size ts, 0)
       | (INR (INL (n,_,t,_,_))) => (cv_size t, cv$c2n n)
       | (INL (t,_)) => (cv_size t, 0))’
  \\ rpt conj_tac
  \\ Cases_on `cv_v` \\ rw[] \\ gs[cv_lt_Num_0]
  \\ qmatch_goalsub_rename_tac `cv_snd p`
  \\ Cases_on `p` \\ gs[]
);

Theorem vyper_decode_valid_enc_pre[cv_pre]:
  (∀v bs. vyper_decode_valid_enc_pre v bs) ∧
  (∀n l t bs hds. vyper_decode_valid_enc_array_pre n l t bs hds) ∧
  (∀ts bs hds. vyper_decode_valid_enc_tuple_pre ts bs hds)
Proof
  ho_match_mp_tac vyper_decode_valid_enc_ind
  \\ rpt strip_tac
  \\ rw[Once vyper_decode_valid_enc_pre_def]
QED


(* Preserve Vyper's bounded decode window in addition to ABI shape checks. *)
Definition vyper_valid_enc_def:
  vyper_valid_enc env t bs ⇔
    (vyper_decode_valid_enc (vyper_to_abi_type env t) bs ∧
     vyper_strict_enc env t bs)
End

val () = cv_auto_trans vyper_valid_enc_def;

(* Shared decode step, after the buffer has been validated. *)
Definition decode_abi_value_def:
  decode_abi_value tenv typ bs =
    case abi_to_vyper tenv typ (dec (vyper_to_abi_type tenv typ) bs) of
      SOME v => INL v
    | NONE => INR "abi_decode conversion"
End

val () = cv_auto_trans decode_abi_value_def;

(* Decode a validated buffer (_abi_decode path). *)
Definition evaluate_abi_decode_def:
  evaluate_abi_decode tenv typ bs =
    if vyper_valid_enc tenv typ bs then
      decode_abi_value tenv typ bs
    else INR "abi_decode invalid"
End

val () = cv_auto_trans evaluate_abi_decode_def;

(* Returndata gate, without the upper bound the cap enforces. *)
Definition vyper_valid_enc_returndata_def:
  vyper_valid_enc_returndata env t bs ⇔
    (vyper_decode_valid_enc (vyper_to_abi_type env t) bs ∧
     static_length (vyper_to_abi_type env t) ≤ LENGTH bs)
End

val () = cv_auto_trans vyper_valid_enc_returndata_def;

(* Decode extcall returndata, over the size-capped buffer. *)
Definition evaluate_abi_decode_returndata_def:
  evaluate_abi_decode_returndata tenv typ bs =
    let bs = TAKE (vyper_abi_size_bound tenv typ) bs in
    if vyper_valid_enc_returndata tenv typ bs then
      decode_abi_value tenv typ bs
    else INR "abi_decode invalid"
End

val () = cv_auto_trans evaluate_abi_decode_returndata_def;

(* Per Vyper ABI spec: wrap return type in tuple unless it's already
   a multi-element tuple (length > 1). See vyper/codegen/core.py *)
Definition needs_external_call_wrap_def:
  needs_external_call_wrap (TupleT ts) = (LENGTH ts ≤ 1) ∧
  needs_external_call_wrap _ = T
End

val () = cv_auto_trans needs_external_call_wrap_def;

(* Decode ABI-encoded function return data.
   Function returns are always encoded as tuples per ABI spec. *)
Definition evaluate_abi_decode_return_def:
  evaluate_abi_decode_return tenv ret_type bs =
    if needs_external_call_wrap ret_type then
      case evaluate_abi_decode_returndata tenv (TupleT [ret_type]) bs of
      | INL (ArrayV (TupleV [v])) => INL v
      | INL _ => INR "decode return unwrap"
      | INR e => INR e
    else
      evaluate_abi_decode_returndata tenv ret_type bs
End

val () = cv_auto_trans evaluate_abi_decode_return_def;

(* Helper for termination: convert default value directly to ABI encoding.
   This exists only to simplify the termination argument for vyper_to_abi_sparse,
   which needs to fill in defaults for missing indices in sparse static arrays.
   Using default_value would create intermediate Vyper values that complicate
   the termination measure.

   The theorem vyper_to_abi_default_value (in vyperABIRoundtripTheory) proves
   this is equivalent to vyper_to_abi on default_value, so this is not a
   separate concept. *)
Definition default_to_abi_def:
  default_to_abi (BaseTV (UintT _)) = NumV 0 ∧
  default_to_abi (BaseTV (IntT _)) = contractABI$IntV 0 ∧
  default_to_abi (BaseTV BoolT) = NumV 0 ∧
  default_to_abi (BaseTV DecimalT) = contractABI$IntV 0 ∧
  default_to_abi (BaseTV AddressT) = NumV 0 ∧
  default_to_abi (BaseTV (StringT _)) = BytesV [] ∧
  default_to_abi (BaseTV (BytesT (Fixed n))) = BytesV (REPLICATE n 0w) ∧
  default_to_abi (BaseTV (BytesT (Dynamic _))) = BytesV [] ∧
  default_to_abi (TupleTV tvs) = ListV (default_to_abi_list tvs) ∧
  default_to_abi (ArrayTV tv (Fixed n)) = ListV (REPLICATE n (default_to_abi tv)) ∧
  default_to_abi (ArrayTV _ (Dynamic _)) = ListV [] ∧
  default_to_abi (StructTV fields) = ListV (default_to_abi_fields fields) ∧
  default_to_abi (FlagTV _) = NumV 0 ∧
  default_to_abi NoneTV = ListV [] ∧
  default_to_abi_list [] = [] ∧
  default_to_abi_list (tv::tvs) = default_to_abi tv :: default_to_abi_list tvs ∧
  default_to_abi_fields [] = [] ∧
  default_to_abi_fields ((id,tv)::rest) = default_to_abi tv :: default_to_abi_fields rest
Termination
  WF_REL_TAC `measure (λx. case x of
    | INL tv => type_value_size tv
    | INR (INL tvs) => list_size type_value_size tvs
    | INR (INR fields) => list_size (pair_size (λx. 0) type_value_size) fields)`
  \\ rw[]
  \\ Induct_on `fields` \\ rw[]
  \\ Cases_on `h` \\ rw[]
End

(* Helper theorems to connect explicit recursion with MAP *)
Theorem default_to_abi_list_MAP:
  ∀tvs. default_to_abi_list tvs = MAP default_to_abi tvs
Proof
  Induct \\ rw[default_to_abi_def]
QED

Theorem default_to_abi_fields_MAP:
  ∀fields. default_to_abi_fields fields = MAP (default_to_abi o SND) fields
Proof
  Induct \\ rw[default_to_abi_def]
  \\ PairCases_on `h` \\ rw[default_to_abi_def]
QED

val () = cv_auto_trans_rec default_to_abi_def (
  WF_REL_TAC `measure (λx. case x of
    | INL tv => cv_size tv
    | INR (INL tvs) => cv_size tvs
    | INR (INR fields) => cv_size fields)`
  \\ rw[]
  \\ Cases_on `cv_v` \\ gvs[]
  \\ rename [`cv_snd p`]
  \\ Cases_on `p` \\ gvs[]
  \\ rename [`cv_fst p`]
  \\ Cases_on `p` \\ gvs[]);

(* Helper: convert base type values to ABI values.
   Factored out to reduce pattern completion in the main mutual recursion,
   which allows cv_auto_trans to succeed. *)
Definition vyper_to_abi_base_def[simp]:
  vyper_to_abi_base (UintT _) (IntV i) = SOME (NumV (Num i)) ∧
  vyper_to_abi_base (IntT _) (IntV i) = SOME (contractABI$IntV i) ∧
  vyper_to_abi_base BoolT (BoolV b) = SOME (NumV (if b then 1 else 0)) ∧
  vyper_to_abi_base DecimalT (DecimalV i) = SOME (contractABI$IntV i) ∧
  vyper_to_abi_base (StringT _) (StringV s) = SOME (contractABI$BytesV (MAP n2w_o_ORD s)) ∧
  vyper_to_abi_base (BytesT _) (BytesV bs) = SOME (contractABI$BytesV bs) ∧
  (* AddressT uses BytesV but converts to NumV - must come after BytesT to avoid
     pattern overlap issues in cv_trans *)
  vyper_to_abi_base AddressT (BytesV bs) =
    SOME (NumV (w2n (word_of_bytes_be bs : address))) ∧
  vyper_to_abi_base _ _ = NONE
End

val () = cv_auto_trans vyper_to_abi_base_def;

(* Convert Vyper value to ABI value for encoding *)
Definition vyper_to_abi_def[simp]:
  vyper_to_abi env (BaseT bt) v = vyper_to_abi_base bt v ∧
  vyper_to_abi env (TupleT ts) (ArrayV (TupleV vs)) =
    (case vyper_to_abi_list env ts vs of
     | SOME avs => SOME (ListV avs)
     | NONE => NONE) ∧
  vyper_to_abi env (ArrayT t _) (ArrayV (DynArrayV vs)) =
    (case vyper_to_abi_same env t vs of
     | SOME avs => SOME (ListV avs)
     | NONE => NONE) ∧
  vyper_to_abi env (ArrayT t (Fixed n)) (ArrayV (SArrayV sparse)) =
    (case evaluate_type env t of
     | NONE => NONE
     | SOME tv =>
         case vyper_to_abi_sparse env t tv n sparse of
         | SOME avs => SOME (ListV avs)
         | NONE => NONE) ∧
  vyper_to_abi env (FlagT _) (FlagV n) = SOME (NumV n) ∧
  vyper_to_abi env NoneT NoneV = SOME (ListV []) ∧
  vyper_to_abi env (StructT nsid) (StructV fields) =
    (case FLOOKUP env nsid of
     | SOME (StructArgs args) =>
         (case vyper_to_abi_list (env \\ nsid) (MAP SND args) (MAP SND fields) of
          | SOME avs => SOME (ListV avs)
          | NONE => NONE)
     | _ => NONE) ∧
  vyper_to_abi _ _ _ = NONE ∧
  (* List: different type for each element *)
  vyper_to_abi_list env [] [] = SOME [] ∧
  vyper_to_abi_list env (t::ts) (v::vs) =
    (case vyper_to_abi env t v of
     | SOME av =>
         (case vyper_to_abi_list env ts vs of
          | SOME avs => SOME (av::avs)
          | NONE => NONE)
     | NONE => NONE) ∧
  vyper_to_abi_list _ _ _ = NONE ∧
  (* Same: same type for all elements *)
  vyper_to_abi_same env t [] = SOME [] ∧
  vyper_to_abi_same env t (v::vs) =
    (case vyper_to_abi env t v of
     | SOME av =>
         (case vyper_to_abi_same env t vs of
          | SOME avs => SOME (av::avs)
          | NONE => NONE)
     | NONE => NONE) ∧
  (* Sparse: encode static array, filling in defaults for missing indices *)
  vyper_to_abi_sparse env t tv 0 sparse = SOME [] ∧
  vyper_to_abi_sparse env t tv (SUC n) sparse =
    (case vyper_to_abi_sparse env t tv n sparse of
     | NONE => NONE
     | SOME avs =>
         case ALOOKUP sparse n of
         | SOME v =>
             (case vyper_to_abi env t v of
              | SOME av => SOME (avs ++ [av])
              | NONE => NONE)
         | NONE => SOME (avs ++ [default_to_abi tv]))
Termination
  WF_REL_TAC `inv_image ($< LEX $<) (λx. case x of
    | INL (_, _, v) => (value_size v, 0)
    | INR (INL (_, _, vs)) => (list_size value_size vs, 0)
    | INR (INR (INL (_, _, vs))) => (list_size value_size vs, 0)
    | INR (INR (INR (_, _, _, n, sparse))) =>
        (list_size (pair_size (λx. 0) value_size) sparse, n))`
  \\ simp[] \\ rpt conj_tac
  (* Goal 1: StructV *)
  >- (rw[] \\ Induct_on `fields` \\ simp[] \\ rw[] \\ Cases_on `h` \\ simp[])
  (* Goal 2 *)
  >- (
    rw[]
    \\ `list_size (pair_size (λx. 0) value_size) sparse ≤
         list_size (pair_size (λx. x) value_size) sparse`
         by (Induct_on `sparse` \\ simp[] \\ rw[] \\ PairCases_on `h` \\ simp[])
    \\ simp[])
  (* Goal 3 *)
  >- (rpt strip_tac \\ disj1_tac
      \\ pop_assum mp_tac
      \\ pop_assum kall_tac
      \\ Induct_on `sparse` \\ simp[] \\ rw[]
      \\ PairCases_on `h` \\ fs[]
      \\ Cases_on `h0 = n` \\ fs[])
End

(* Helper: cv_ALOOKUP result size is smaller than sparse list *)
Theorem cv_ALOOKUP_snd_size:
  !sparse k. cv$c2b (cv_ispair (cv_ALOOKUP sparse k)) ==>
    cv_size (cv_snd (cv_ALOOKUP sparse k)) < cv_size sparse
Proof
  Induct_on `sparse`
  >- rw[Once cv_ALOOKUP_def]
  >- (rw[Once cv_ALOOKUP_def]
      >- (simp[Once cv_ALOOKUP_def, cv_if_def0]
          \\ Cases_on `sparse`
          \\ gvs[cv_repTheory.cv_termination_simp, cv_ispair_def,
                 cv_snd_def, cv_size_def])
      >- (simp[Once cv_ALOOKUP_def, cv_if_def0]
          \\ qpat_x_assum `∀k. cv$c2b (cv_ispair (cv_ALOOKUP sparse' k)) ⇒ _`
               (qspec_then `k` mp_tac)
          \\ gvs[cv_nsid_ispair_bool]))
QED

Theorem cv_ALOOKUP_snd_size_pair:
  !sparse k. cv_ispair (cv_ALOOKUP sparse k) = cv$Num 1 ==>
    cv_size (cv_snd (cv_ALOOKUP sparse k)) < cv_size sparse
Proof
  rpt strip_tac \\ irule cv_ALOOKUP_snd_size \\ simp[cv_nsid_ispair_bool]
QED

(* Helper tactic: find cv_fst/cv_snd subterms in the goal and add bounds as assumptions.
   Also adds c2n bounds for terms like c2n (cv_fst x). Returns ALL_TAC if no terms found. *)
fun cv_bounds_tac (asl, concl) = let
  val cv_fst_tm = ``cv_fst``
  val cv_snd_tm = ``cv_snd``
  val c2n_tm = ``cv$c2n``
  fun is_cv_proj tm =
    is_comb tm andalso let val (f, _) = dest_comb tm in
      f ~~ cv_fst_tm orelse f ~~ cv_snd_tm
    end
  fun is_c2n tm =
    is_comb tm andalso (rator tm ~~ c2n_tm)
  (* Find all cv_fst/cv_snd projections *)
  fun find_cv_projs tm acc =
    if is_cv_proj tm then
      find_cv_projs (rand tm) (tm :: acc)
    else if is_comb tm then
      find_cv_projs (rator tm) (find_cv_projs (rand tm) acc)
    else acc
  (* Find all c2n applications (any argument, not just projections) *)
  fun find_c2n_projs tm acc =
    if is_c2n tm then (tm :: acc)
    else if is_comb tm then
      find_c2n_projs (rator tm) (find_c2n_projs (rand tm) acc)
    else acc
  val projs = find_cv_projs concl []
  val c2n_projs = find_c2n_projs concl []
  fun mk_proj_bound_tac proj = let
      val (f, a) = dest_comb proj
    in
      if f ~~ cv_fst_tm then
        ASSUME_TAC (SPEC a cv_size_cv_fst_le)
      else
        ASSUME_TAC (SPEC a cv_size_cv_snd_le)
    end
  fun mk_c2n_bound_tac c2n_app = let
      val inner = rand c2n_app
    in
      ASSUME_TAC (SPEC inner c2n_le_cv_size)
    end
  val proj_tacs = map mk_proj_bound_tac projs
  val c2n_tacs = map mk_c2n_bound_tac c2n_projs
  val all_tacs = proj_tacs @ c2n_tacs
in
  if null all_tacs then ALL_TAC (asl, concl)
  else EVERY all_tacs (asl, concl)
end;

val vyper_to_abi_pre_def = cv_auto_trans_pre_rec
  "vyper_to_abi_pre vyper_to_abi_list_pre vyper_to_abi_same_pre vyper_to_abi_sparse_pre"
  vyper_to_abi_def (
  WF_REL_TAC `inv_image ($< LEX $< LEX $<)
    (λx. case x of
      | INL (env, t, v) => (cv_nsid_count env, cv_size t + cv_size v, 0)
      | INR (INL (env, ts, vs)) => (cv_nsid_count env, cv_size ts + cv_size vs, 0)
      | INR (INR (INL (env, t, vs))) => (cv_nsid_count env, cv_size t + cv_size vs, 0)
      | INR (INR (INR (env, t, tv, n, sparse))) =>
          (cv_nsid_count env, cv_size t + cv_size sparse + cv$c2n n, cv$c2n n))`
  \\ rw[]
  (* Handle simple cv_snd cases *)
  \\ TRY (gvs[cv_repTheory.cv_termination_simp, cv_size_def, cv_snd_def]
          \\ rw[cv_snd_def, cv_size_def] \\ NO_TAC)
  (* Handle cv_sub for sparse n-1 *)
  \\ TRY (gvs[cv_repTheory.cv_termination_simp, cv_sub_def, c2n_def] \\ NO_TAC)
  (* Handle ALOOKUP result *)
  \\ TRY (drule cv_ALOOKUP_snd_size_pair
          \\ gvs[cv_repTheory.cv_termination_simp, c2n_def] \\ NO_TAC)
  (* Handle StructT list projection (second lex component) - these are direct inequalities
     (not disjunctions), so we can't use disj1_tac. Use cv_size bounds and arithmetic. *)
  \\ TRY (
      gvs[cv_repTheory.cv_termination_simp]
      \\ sg `!x. cv_size (cv_snd (cv_snd x)) <= cv_size x`
      >- (gen_tac >> irule LESS_EQ_TRANS >> qexists_tac `cv_size (cv_snd x)` >> rw[cv_size_cv_snd_le])
      \\ sg `!x. cv_size (cv_snd (cv_snd (cv_snd x))) <= cv_size x`
      >- (gen_tac >> irule LESS_EQ_TRANS >> qexists_tac `cv_size (cv_snd (cv_snd x))` >> gvs[])
      \\ sg `!x. cv$c2n (cv_fst (cv_snd x)) <= cv_size x`
      >- (gen_tac >> irule LESS_EQ_TRANS >> qexists_tac `cv_size (cv_fst (cv_snd x))` >> rw[c2n_le_cv_size]
          >> irule LESS_EQ_TRANS >> qexists_tac `cv_size (cv_snd x)` >> rw[cv_size_cv_fst_le, cv_size_cv_snd_le])
      \\ gvs[]
      \\ NO_TAC)
  (* A resolved struct field deletes its type definition before recursion. *)
  \\ TRY (disj1_tac
          \\ irule cv_nsid_delete_count
          \\ gvs[cv_nsid_ispair_bool]
          \\ NO_TAC)
  (* DynArrayV/SArrayV cases: expose Pair overhead via case splits. *)
  \\ rpt strip_tac
  \\ Cases_on `cv_v` >> fs[cv_ispair_def, c2b_def]
  \\ TRY (Cases_on `cv_v0` >> fs[cv_ispair_def, c2b_def])
  \\ simp[cv_size_def, cv_snd_def, cv_fst_def]
  \\ cv_bounds_tac
  \\ TRY decide_tac
  (* SArrayV case: for c2n (cv_fst (cv_snd v)), split v (its Num case
     contradicts cv_lt), then the inner pair, so decide_tac sees enough Pair
     overhead. *)
  \\ TRY (let
       val c2n_tm = ``cv$c2n``
       fun fc tm =
         if is_comb tm then let val (f,a) = dest_comb tm in
           if f ~~ c2n_tm then SOME a
           else case fc a of SOME x => SOME x | NONE => fc f end
         else NONE
       fun split_c2n_parent (asl, g) =
         (case fc g of
          | NONE => ALL_TAC (asl, g)
          | SOME ca => Cases_on [ANTIQUOTE (rand (rand ca))] (asl, g))
       fun split_c2n_arg (asl, g) =
         (case fc g of
          | NONE => ALL_TAC (asl, g)
          | SOME ca => Cases_on [ANTIQUOTE (rand ca)] (asl, g))
     in
       split_c2n_parent
       >> fs[cv_fst_def, cv_snd_def, cv_size_def, c2n_def, cv_lt_def]
       >> split_c2n_arg
       >> simp[cv_fst_def, cv_snd_def, cv_size_def, c2n_def]
       >> cv_bounds_tac
       >> fs[cv_fst_def, cv_snd_def, cv_size_def]
       >> decide_tac
     end)
);

Theorem vyper_to_abi_pre[cv_pre]:
  (∀env t v. vyper_to_abi_pre env t v) ∧
  (∀env ts vs. vyper_to_abi_list_pre env ts vs) ∧
  (∀env t vs. vyper_to_abi_same_pre env t vs) ∧
  (∀env t tv n sparse. vyper_to_abi_sparse_pre env t tv n sparse)
Proof
  ho_match_mp_tac vyper_to_abi_ind
  \\ rw[]
  \\ CONV_TAC (ONCE_REWRITE_CONV [vyper_to_abi_pre_def])
  \\ rw[] \\ gvs[]
QED

(* ===== ABI Encoding ===== *)

Definition evaluate_abi_encode_bytes_def:
  evaluate_abi_encode_bytes tenv typ v =
    let abiTy = vyper_to_abi_type tenv typ in
    case vyper_to_abi tenv typ v of
      SOME av => INL (enc abiTy av)
    | NONE => INR "abi_encode conversion"
End

val () = cv_auto_trans evaluate_abi_encode_bytes_def;

Definition evaluate_abi_encode_def:
  evaluate_abi_encode tenv typ v =
    case evaluate_abi_encode_bytes tenv typ v of
      INL bs => INL (BytesV bs)
    | INR err => INR err
End

val () = cv_auto_trans evaluate_abi_encode_def;

(* ===== External Call Calldata Building ===== *)

(* Build calldata for external call:
   4-byte function selector ++ ABI-encoded arguments

   func_name: function name (string)
   arg_types: list of Vyper types for the arguments
   arg_vals: list of Vyper values for the arguments

   Returns: byte list (selector ++ encoded args) or NONE on encoding failure *)
Definition build_ext_calldata_def:
  build_ext_calldata env func_name arg_types arg_vals =
    let actual_types = TAKE (LENGTH arg_vals) arg_types in
    let abi_types = vyper_to_abi_types env actual_types in
    let selector = function_selector func_name abi_types in
    case vyper_to_abi_list env actual_types arg_vals of
    | SOME abi_vals =>
        SOME (selector ++ enc (Tuple abi_types) (ListV abi_vals))
    | NONE => NONE
End

val () = cv_auto_trans build_ext_calldata_def;

(* Custom errors use the function-selector algorithm, but unlike function calls
   have no default arguments: every declared value must be present exactly once. *)
Definition build_custom_error_data_def:
  build_custom_error_data env error_name arg_types arg_vals =
    if LENGTH arg_types ≠ LENGTH arg_vals then NONE else
    let abi_types = vyper_to_abi_types env arg_types in
    let selector = function_selector error_name abi_types in
    case vyper_to_abi_list env arg_types arg_vals of
    | SOME abi_vals =>
        SOME (selector ++ enc (Tuple abi_types) (ListV abi_vals))
    | NONE => NONE
End

val () = cv_auto_trans build_custom_error_data_def;

(* ===== External Return Encoding (incl. @raw_return) ===== *)

(* Returndata of an external call that produced value v for declared type typ.
   An ordinary function returns the ABI encoding of v (evaluate_abi_encode_bytes,
   inverse of the evaluate_abi_decode_return the call sites apply to observed
   returndata).  A @raw_return function returns its bytestring value's content
   bytes verbatim: no length word, no padding, possibly empty.  The error branch
   is unreachable for a well-typed return value: call_external_function reports
   only safe_casted values, and safe_cast_bytestring_raw_return_bytes gives such
   a value raw bytes whenever typ is a Bytes/String type. *)
Definition external_returndata_def:
  external_returndata raw_return tenv typ v =
    if raw_return then
      case raw_return_bytes v of
        SOME bs => INL bs
      | NONE => INR "external_returndata: @raw_return needs a bytestring value"
    else evaluate_abi_encode_bytes tenv typ v
End

val () = cv_auto_trans external_returndata_def;

(* The @raw_return branch returns exactly the value's own bytes. *)
Theorem external_returndata_raw_SOME_iff:
  ∀tenv typ v bs.
    external_returndata T tenv typ v = INL bs ⇔ raw_return_bytes v = SOME bs
Proof
  simp[external_returndata_def]
  >> Cases_on `raw_return_bytes v` >> simp[]
QED

(* An ordinary external call returns the ABI encoding. *)
Theorem external_returndata_plain:
  ∀tenv typ v.
    external_returndata F tenv typ v = evaluate_abi_encode_bytes tenv typ v
Proof
  simp[external_returndata_def] >> metis_tac[]
QED

(* Whether observed returndata agrees with the value the semantics computed.
   An ordinary function ABI-encodes, so returndata must decode back to v; a
   @raw_return function returns raw content bytes, so returndata must be exactly
   those, as external_returndata produces. *)
Definition external_returndata_agrees_def:
  external_returndata_agrees is_raw tenv ret v out =
    if is_raw then
      (case external_returndata T tenv ret v of
         INR e => F
       | INL expected => (out = expected))
    else
      (case evaluate_abi_decode_return tenv ret out of
         INR e => F
       | INL decoded => (decoded = v))
End

val () = cv_auto_trans external_returndata_agrees_def;

(* The @raw_return agreement is exactly byte equality against the
   raw encoding; the ordinary agreement is exactly successful decoding. *)
Theorem external_returndata_agrees_T:
  ∀tenv ret v out.
    external_returndata_agrees T tenv ret v out ⇔
    ∃bs. external_returndata T tenv ret v = INL bs ∧ out = bs
Proof
  simp[external_returndata_agrees_def] >> Cases_on `external_returndata T tenv ret v`
  >> simp[EQ_SYM_EQ]
QED

Theorem external_returndata_agrees_F:
  ∀tenv ret v out.
    external_returndata_agrees F tenv ret v out ⇔
    evaluate_abi_decode_return tenv ret out = INL v
Proof
  simp[external_returndata_agrees_def] >> Cases_on `evaluate_abi_decode_return tenv ret out`
  >> simp[]
QED

(* A @raw_return value with no bytestring representation is
   rejected rather than silently encoded. *)
Theorem external_returndata_raw_NONE:
  ∀tenv typ v.
    raw_return_bytes v = NONE ⇒
      external_returndata T tenv typ v =
        INR "external_returndata: @raw_return needs a bytestring value"
Proof
  rw[external_returndata_def, option_CASE_rator] >> metis_tac[]
QED
