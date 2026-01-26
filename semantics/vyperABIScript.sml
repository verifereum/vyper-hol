Theory vyperABI
Ancestors
  contractABI vyperAST vyperTypeValue
  vyperMisc byte string words list rich_list
  divides alist combin pair arithmetic option
Libs
  cv_transLib
  wordsLib
  dep_rewrite

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

Definition vyper_to_abi_type_def[simp]:
  vyper_to_abi_type (BaseT bt) = vyper_base_to_abi_type bt ∧
  vyper_to_abi_type (TupleT ts) = Tuple (vyper_to_abi_types ts) ∧
  vyper_to_abi_type (ArrayT t (Dynamic _)) = Array NONE (vyper_to_abi_type t) ∧
  vyper_to_abi_type (ArrayT t (Fixed n)) = Array (SOME n) (vyper_to_abi_type t) ∧
  vyper_to_abi_type (StructT id) = Tuple [] (* TODO *) ∧
  vyper_to_abi_type (FlagT _) = Uint 256 ∧
  vyper_to_abi_type NoneT = Tuple [] ∧
  vyper_to_abi_types [] = [] ∧
  vyper_to_abi_types (t::ts) = vyper_to_abi_type t :: vyper_to_abi_types ts
Termination
  WF_REL_TAC ‘measure (λx. case x of INL t => type_size t
                                   | INR ts => list_size type_size ts)’
End

val () = cv_auto_trans vyper_base_to_abi_type_def;
val () = cv_auto_trans_rec vyper_to_abi_type_def (
  WF_REL_TAC `measure (λx. case x of INL t => cv_size t
                                   | INR ts => cv_size ts)`
  \\ rw[]
  \\ TRY (Cases_on `cv_v` \\ gvs[cvTheory.cv_size_def] \\ NO_TAC)
  \\ Cases_on `cv_v` \\ gvs[cvTheory.cv_size_def]
  \\ qmatch_goalsub_rename_tac `cv_fst p`
  \\ Cases_on `p` \\ gvs[cvTheory.cv_size_def]
);

Definition check_IntV_def:
  check_IntV b i =
  if within_int_bound b i then SOME $ IntV b i else NONE
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
    (if compatible_bound b (LENGTH bs) then SOME $ BytesV b bs else NONE) ∧
  abi_to_vyper env (BaseT $ StringT z) (BytesV bs) =
    (if LENGTH bs ≤ z then SOME $ StringV z (MAP (CHR o w2n) bs) else NONE) ∧
  abi_to_vyper env (BaseT $ DecimalT) (IntV i) =
    (if within_int_bound (Signed 168) i then SOME $ DecimalV i else NONE) ∧
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
  abi_to_vyper env (StructT id) (ListV vs) =
    (let nid = string_to_num id in
      case FLOOKUP env nid of
       | SOME (StructArgs args) =>
         (case abi_to_vyper_list (env \\ nid) (MAP SND args) vs of NONE => NONE
          | SOME vs => SOME $ StructV $ ZIP (MAP FST args, vs))
       | _ => NONE) ∧
  abi_to_vyper env (FlagT id) (NumV n) =
    (case FLOOKUP env (string_to_num id) of
      | SOME (FlagArgs m) =>
        if m ≤ 256 ∧ n < 2 ** m then SOME $ FlagV m (&n) else NONE
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

Definition evaluate_abi_decode_def:
  evaluate_abi_decode tenv typ bs =
    let abiTy = vyper_to_abi_type typ in
    if valid_enc abiTy bs then
      case abi_to_vyper tenv typ (dec abiTy bs) of
        SOME v => INL v
      | NONE => INR "abi_decode conversion"
    else INR "abi_decode invalid"
End

val () = cv_auto_trans evaluate_abi_decode_def;

(* Helper for termination: convert default value directly to ABI encoding.
   This exists only to simplify the termination argument for vyper_to_abi_sparse,
   which needs to fill in defaults for missing indices in sparse static arrays.
   Using default_value would create intermediate Vyper values that complicate
   the termination measure.

   The theorem vyper_to_abi_default_value proves this is equivalent to
   vyper_to_abi on default_value, so this is not a separate concept. *)
Definition default_to_abi_def:
  default_to_abi (BaseTV (UintT _)) = NumV 0 ∧
  default_to_abi (BaseTV (IntT _)) = contractABI$IntV 0 ∧
  default_to_abi (BaseTV BoolT) = NumV 0 ∧
  default_to_abi (BaseTV DecimalT) = contractABI$IntV 0 ∧
  default_to_abi (BaseTV AddressT) = NumV 0 ∧
  default_to_abi (BaseTV (StringT _)) = BytesV [] ∧
  default_to_abi (BaseTV (BytesT (Fixed n))) = BytesV (REPLICATE n 0w) ∧
  default_to_abi (BaseTV (BytesT (Dynamic _))) = BytesV [] ∧
  default_to_abi (TupleTV tvs) = ListV (MAP default_to_abi tvs) ∧
  default_to_abi (ArrayTV tv (Fixed n)) = ListV (REPLICATE n (default_to_abi tv)) ∧
  default_to_abi (ArrayTV _ (Dynamic _)) = ListV [] ∧
  default_to_abi (StructTV fields) = ListV (MAP (default_to_abi o SND) fields) ∧
  default_to_abi (FlagTV _) = NumV 0 ∧
  default_to_abi NoneTV = ListV []
Termination
  WF_REL_TAC `measure type_value_size`
End

(* Convert Vyper value to ABI value for encoding *)
Definition vyper_to_abi_def[simp]:
  vyper_to_abi env (BaseT (UintT _)) (IntV (Unsigned _) i) = SOME (NumV (Num i)) ∧
  vyper_to_abi env (BaseT (IntT _)) (IntV (Signed _) i) = SOME (contractABI$IntV i) ∧
  vyper_to_abi env (BaseT BoolT) (BoolV b) = SOME (NumV (if b then 1 else 0)) ∧
  vyper_to_abi env (BaseT AddressT) (BytesV (Fixed 20) bs) =
    SOME (NumV (w2n (word_of_bytes T (0w:address) bs))) ∧
  vyper_to_abi env (BaseT (BytesT _)) (BytesV _ bs) = SOME (BytesV bs) ∧
  vyper_to_abi env (BaseT (StringT _)) (StringV _ s) = SOME (BytesV (MAP (n2w o ORD) s)) ∧
  vyper_to_abi env (BaseT DecimalT) (DecimalV i) = SOME (contractABI$IntV i) ∧
  vyper_to_abi env (TupleT ts) (ArrayV (TupleV vs)) =
    (case vyper_to_abi_list env ts vs of
     | SOME avs => SOME (ListV avs)
     | NONE => NONE) ∧
  vyper_to_abi env (ArrayT t _) (ArrayV (DynArrayV _ _ vs)) =
    (case vyper_to_abi_same env t vs of
     | SOME avs => SOME (ListV avs)
     | NONE => NONE) ∧
  vyper_to_abi env (ArrayT t (Fixed _)) (ArrayV (SArrayV tv n sparse)) =
    (case vyper_to_abi_sparse env t tv n sparse of
     | SOME avs => SOME (ListV avs)
     | NONE => NONE) ∧
  vyper_to_abi env (FlagT _) (FlagV _ n) = SOME (NumV n) ∧
  vyper_to_abi env NoneT NoneV = SOME (ListV []) ∧
  vyper_to_abi env (StructT id) (StructV fields) =
    (let nid = string_to_num id in
     case FLOOKUP env nid of
     | SOME (StructArgs args) =>
         (case vyper_to_abi_list (env \\ nid) (MAP SND args) (MAP SND fields) of
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
  WF_REL_TAC `measure (λx. case x of
    | INL (_, _, v) => value_size v
    | INR (INL (_, _, vs)) => list_size value_size vs
    | INR (INR (INL (_, _, vs))) => list_size value_size vs
    | INR (INR (INR (_, _, _, n, sparse))) =>
        list_size (pair_size (λx. 0) value_size) sparse + n)`
  \\ simp[] \\ rpt conj_tac
  (* Goal 1: StructV *)
  >- (rw[] \\ Induct_on `fields` \\ simp[] \\ rw[] \\ Cases_on `h` \\ simp[])
  (* Goal 2: Sparse ALOOKUP case *)
  >- (rpt strip_tac
      \\ sg `∀sp n' v'. ALOOKUP sp n' = SOME v' ⇒
             value_size v' < SUC n' + list_size (pair_size (λx. 0) value_size) sp`
      >- (Induct \\ simp[] \\ rw[]
          \\ PairCases_on `h` \\ fs[]
          \\ Cases_on `h0 = n'` \\ fs[]
          \\ first_x_assum drule \\ simp[])
      \\ first_x_assum drule \\ simp[])
  (* Goal 3: Main -> sparse *)
  \\ rw[]
  \\ `list_size (pair_size (λx. 0) value_size) sparse ≤
      list_size (pair_size (λx. x) value_size) sparse`
       by (Induct_on `sparse` \\ simp[] \\ rw[] \\ PairCases_on `h` \\ simp[])
  \\ simp[]
End

(* ===== Roundtrip Theorems ===== *)

(* TODO: move *)
Theorem OPT_MMAP_SOME_IFF:
  ∀f ls vs.
    OPT_MMAP f ls = SOME vs ⇔
    EVERY IS_SOME (MAP f ls) ∧
    vs = MAP (THE o f) ls
Proof
  Induct_on `ls` \\ rw[]
  \\ Cases_on `f h` \\ rw[EQ_IMP_THM]
QED

Theorem ZIP_REPLICATE:
  ZIP (REPLICATE n x, REPLICATE n y) =
  REPLICATE n (x,y)
Proof
  Induct_on `n` \\ rw[]
QED

(* Helper: default_value_tuple computes MAP default_value *)
Theorem default_value_tuple_MAP:
  ∀ts acc. default_value_tuple acc ts = ArrayV (TupleV (REVERSE acc ++ MAP default_value ts))
Proof
  Induct \\ rw[default_value_def] \\ gvs[]
QED

(* Helper: default_value_struct computes MAP with default_value on SND *)
Theorem default_value_struct_MAP:
  ∀ps acc. default_value_struct acc ps =
           StructV (REVERSE acc ++ MAP (λ(id,t). (id, default_value t)) ps)
Proof
  Induct \\ rw[default_value_def]
  \\ PairCases_on `h` \\ rw[default_value_def]
QED

(* Helper: abi_to_vyper_list in terms of OPT_MMAP *)
Theorem abi_to_vyper_list_OPT_MMAP:
  ∀ts vs. abi_to_vyper_list env ts vs =
    if LENGTH ts = LENGTH vs then
      OPT_MMAP (UNCURRY (abi_to_vyper env)) (ZIP (ts, vs))
    else NONE
Proof
  Induct \\ rw[abi_to_vyper_def]
  \\ Cases_on `vs` \\ gvs[abi_to_vyper_def]
  \\ CASE_TAC \\ gvs[]
  \\ CASE_TAC \\ gvs[]
QED

(* Bytes encoding roundtrip: n2w o ORD o CHR o w2n = id for word8 *)
Theorem bytes_encode_decode_roundtrip:
  ∀bs:word8 list. MAP ((n2w:num->word8) o ORD o CHR o w2n) bs = bs
Proof
  Induct \\ simp[]
  \\ rw[]
  \\ ASSUME_TAC (Q.SPEC `h` (INST_TYPE [``:α`` |-> ``:8``] w2n_lt))
  \\ gvs[dimword_8, ORD_CHR]
QED

Theorem bytes_encode_decode_roundtrip':
  ∀bs:word8 list. MAP (n2w o ORD) (MAP (CHR o w2n) bs) = bs
Proof
  rw[MAP_MAP_o, o_DEF]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ rw[GSYM o_DEF, bytes_encode_decode_roundtrip]
QED

(* Helper: evaluate_types in terms of OPT_MMAP *)
Theorem evaluate_types_OPT_MMAP:
  ∀ts acc. evaluate_types env ts acc =
    OPTION_MAP ((++) (REVERSE acc)) (OPT_MMAP (evaluate_type env) ts)
Proof
  Induct \\ rw[evaluate_type_def]
  \\ CASE_TAC \\ gvs[]
  \\ Cases_on `OPT_MMAP (evaluate_type env) ts` \\ gvs[]
QED

(* ===== Helper Lemmas for Roundtrip Theorems ===== *)

(* Helper 1: Address word roundtrip *)
Theorem address_word_roundtrip:
  ∀n. n < dimword (:160) ⇒
      w2n (word_of_bytes T (0w:address) (word_to_bytes (n2w n : address) T)) = n
Proof
  rpt strip_tac \\
  DEP_REWRITE_TAC[word_of_bytes_word_to_bytes] \\
  gvs[divides_def]
QED

Theorem within_int_bound_Unsigned_dimword:
  within_int_bound (Unsigned n) (&m) ⇒ m < 2 ** n
Proof
  rw[within_int_bound_def]
QED

Theorem vyper_to_abi_list_OPT_MMAP:
  !ts vs. vyper_to_abi_list env ts vs =
  if LENGTH ts = LENGTH vs then
    OPT_MMAP (UNCURRY (vyper_to_abi env)) (ZIP (ts,vs))
  else NONE
Proof
  Induct \\ rw[vyper_to_abi_def]
  \\ Cases_on `vs` \\ gvs[vyper_to_abi_def]
  \\ CASE_TAC \\ gvs[]
  \\ CASE_TAC \\ gvs[]
QED

Theorem vyper_to_abi_same_OPT_MMAP:
  !vs. vyper_to_abi_same env t vs =
    OPT_MMAP (vyper_to_abi env t) vs
Proof
  Induct \\ rw[vyper_to_abi_def]
  \\ Cases_on `vs` \\ gvs[vyper_to_abi_def]
  \\ CASE_TAC \\ gvs[]
  \\ CASE_TAC \\ gvs[]
QED

(* Helper 2: vyper_to_abi_same equals vyper_to_abi_list with REPLICATE *)
Theorem vyper_to_abi_same_REPLICATE:
  ∀env t vs avs.
    vyper_to_abi_list env (REPLICATE (LENGTH vs) t) vs = SOME avs ⇒
    vyper_to_abi_same env t vs = SOME avs
Proof
  rw[vyper_to_abi_list_OPT_MMAP, vyper_to_abi_same_OPT_MMAP]
  \\ pop_assum $ SUBST1_TAC o SYM
  \\ Induct_on `vs` \\ rw[]
QED

Theorem MEM_enumerate_static_array_iff:
  ∀vs n.
  MEM (i,v) (enumerate_static_array d n vs) ⇔
  n ≤ i ∧ i-n < LENGTH vs ∧ EL (i-n) vs = v ∧ v ≠ d
Proof
  Induct
  \\ simp[enumerate_static_array_def]
  \\ rpt gen_tac
  \\ IF_CASES_TAC \\ gvs[]
  \\ Cases_on `i < n` \\ gvs[]
  \\ Cases_on `i = n` \\ gvs[]
  \\ TRY(rw[EQ_IMP_THM] \\ NO_TAC)
  \\ simp[EL_CONS, PRE_SUB1, ADD1]
  \\ Cases_on `0 < LENGTH vs` \\ gvs[]
QED

Theorem ALL_DISTINCT_MAP_FST_enumerate_static_array[simp]:
  ∀vs n. ALL_DISTINCT (MAP FST (enumerate_static_array d n vs))
Proof
  Induct \\ rw[enumerate_static_array_def, MEM_MAP, EXISTS_PROD]
  \\ rw[MEM_enumerate_static_array_iff]
QED

(* Helper 3: enumerate_static_array lookup *)
Theorem enumerate_static_array_ALOOKUP:
  ∀d k vs i. i < LENGTH vs ⇒
    ALOOKUP (enumerate_static_array d k vs) (k + i) =
      if EL i vs = d then NONE else SOME (EL i vs)
Proof
  rw[]
  >- rw[ALOOKUP_FAILS, MEM_enumerate_static_array_iff]
  \\ irule ALOOKUP_ALL_DISTINCT_MEM
  \\ rw[MEM_enumerate_static_array_iff]
QED

(* Helper 4: Default value inverse - if decoding gives default, input was default encoding *)
Theorem abi_to_vyper_default_value_inv_mutual:
  (∀env t av v. abi_to_vyper env t av = SOME v ⇒
                ∀tv. evaluate_type env t = SOME tv ⇒
                     v = default_value tv ⇒ av = default_to_abi tv) ∧
  (∀env ts avs vs. abi_to_vyper_list env ts avs = SOME vs ⇒
                   ∀tvs. OPT_MMAP (evaluate_type env) ts = SOME tvs ⇒
                         vs = MAP default_value tvs ⇒ avs = MAP default_to_abi tvs)
Proof
  ho_match_mp_tac abi_to_vyper_ind
  \\ rw[]
  \\ gvs[evaluate_type_def, abi_to_vyper_def, default_value_def, default_to_abi_def,
         check_IntV_def, AllCaseEqs(), within_int_bound_def, compatible_bound_def,
         make_array_value_def, default_value_tuple_MAP, ETA_AX, NULL_EQ,
         default_value_struct_MAP, evaluate_types_OPT_MMAP]
  >- (
    first_x_assum(mp_tac o Q.AP_TERM`word_of_bytes T (0w:address)`)
    \\ DEP_REWRITE_TAC[word_of_bytes_word_to_bytes]
    \\ rw[divides_def] )
  \\ TRY (
    rename1`BytesT bd`
    \\ Cases_on `bd` \\ gvs[default_value_def, default_to_abi_def] )
  \\ TRY (
    Cases_on `b`
    \\ gvs[evaluate_type_def, abi_to_vyper_def, default_value_def,
           default_to_abi_def, check_IntV_def, AllCaseEqs(),
           within_int_bound_def, compatible_bound_def,
           make_array_value_def, default_value_tuple_MAP, ETA_AX, NULL_EQ,
           default_value_struct_MAP, evaluate_types_OPT_MMAP,
           OPT_MMAP_SOME_IFF, abi_to_vyper_list_OPT_MMAP, ZIP_EQ_NIL]
    \\ first_x_assum irule
    \\ rw[LIST_EQ_REWRITE, EL_MAP, EL_REPLICATE, EL_ZIP]
    \\ gvs[NIL_NO_MEM, FORALL_PROD, MEM_enumerate_static_array_iff]
    \\ first_x_assum(qspec_then`x`mp_tac) \\ rw[EL_MAP, EL_ZIP, EL_REPLICATE])
 \\ gvs[OPT_MMAP_SOME_IFF, ZIP_MAP, abi_to_vyper_list_OPT_MMAP]
 \\ gvs[MAP_MAP_o, o_DEF]
 \\ gvs[LIST_EQ_REWRITE, EL_MAP, EL_ZIP]
QED

(* Original single-type version with partial proof *)
Theorem abi_to_vyper_default_value_inv:
  ∀env t tv av.
    evaluate_type env t = SOME tv ∧
    abi_to_vyper env t av = SOME (default_value tv) ⇒
    av = default_to_abi tv
Proof
  metis_tac[abi_to_vyper_default_value_inv_mutual]
QED

(* Helper: ALOOKUP enumerate_static_array agrees on indices < n for full list vs TAKE *)
Theorem enumerate_ALOOKUP_TAKE:
  ∀d n i vs'. i < n ∧ n ≤ LENGTH vs' ⇒
    ALOOKUP (enumerate_static_array d 0 vs') i =
    ALOOKUP (enumerate_static_array d 0 (TAKE n vs')) i
Proof
  rw[]
  \\ `i < LENGTH vs'` by gvs[]
  \\ `i < LENGTH (TAKE n vs')` by gvs[LENGTH_TAKE]
  \\ `ALOOKUP (enumerate_static_array d 0 vs') (0 + i) =
      if EL i vs' = d then NONE else SOME (EL i vs')`
      by (irule enumerate_static_array_ALOOKUP \\ gvs[])
  \\ `ALOOKUP (enumerate_static_array d 0 (TAKE n vs')) (0 + i) =
      if EL i (TAKE n vs') = d then NONE else SOME (EL i (TAKE n vs'))`
      by (irule enumerate_static_array_ALOOKUP \\ gvs[])
  \\ gvs[EL_TAKE]
QED

(* Helper: vyper_to_abi_sparse only depends on ALOOKUP for indices < n *)
Theorem vyper_to_abi_sparse_ALOOKUP_cong:
  ∀n env t tv sparse1 sparse2.
    (∀i. i < n ⇒ ALOOKUP sparse1 i = ALOOKUP sparse2 i) ⇒
    vyper_to_abi_sparse env t tv n sparse1 = vyper_to_abi_sparse env t tv n sparse2
Proof
  Induct_on `n` \\ rw[vyper_to_abi_def]
  \\ simp[Once vyper_to_abi_def]
  \\ `vyper_to_abi_sparse env t tv n sparse1 = vyper_to_abi_sparse env t tv n sparse2`
      by (first_x_assum irule \\ rw[])
  \\ `ALOOKUP sparse1 n = ALOOKUP sparse2 n` by gvs[]
  \\ pop_assum SUBST_ALL_TAC
  \\ pop_assum SUBST_ALL_TAC
  \\ rw[]
QED

(* Corollary: vyper_to_abi_sparse for full vs' = for TAKE n vs' *)
Theorem vyper_to_abi_sparse_TAKE:
  ∀n env t tv d vs'. n ≤ LENGTH vs' ⇒
    vyper_to_abi_sparse env t tv n (enumerate_static_array d 0 vs') =
    vyper_to_abi_sparse env t tv n (enumerate_static_array d 0 (TAKE n vs'))
Proof
  rw[]
  \\ irule vyper_to_abi_sparse_ALOOKUP_cong
  \\ rw[]
  \\ irule enumerate_ALOOKUP_TAKE
  \\ gvs[]
QED

(* Helper: TAKE n vs ++ [EL n vs] = vs when LENGTH vs = SUC n *)
Theorem TAKE_SNOC_EL:
  LENGTH vs = SUC n ⇒ TAKE n vs ++ [EL n vs] = vs
Proof
  rw[LIST_EQ_REWRITE, EL_APPEND_EQN, EL_TAKE, LENGTH_TAKE]
  \\ Cases_on `x < n` \\ gvs[EL_TAKE]
  \\ `x = n` by gvs[] \\ gvs[]
QED

(* Helper 5: vyper_to_abi_sparse reconstruction *)
Theorem vyper_to_abi_sparse_correct:
  ∀env t tv n vs' vs.
    LENGTH vs' = n ∧
    LENGTH vs = n ∧
    evaluate_type env t = SOME tv ∧
    (∀i. i < n ⇒ abi_to_vyper env t (EL i vs) = SOME (EL i vs')) ∧
    (∀i. i < n ⇒ vyper_to_abi env t (EL i vs') = SOME (EL i vs)) ⇒
    vyper_to_abi_sparse env t tv n (enumerate_static_array (default_value tv) 0 vs') = SOME vs
Proof
  Induct_on `n`
  (* Base case *)
  >- (rw[vyper_to_abi_def] \\ gvs[LENGTH_EQ_NUM_compute])
  (* Inductive case *)
  \\ rw[]
  \\ simp[Once vyper_to_abi_def, CaseEq"option"]
  (* Rewrite recursive call using TAKE lemma *)
  \\ `vyper_to_abi_sparse env t tv n (enumerate_static_array (default_value tv) 0 vs') =
      vyper_to_abi_sparse env t tv n (enumerate_static_array (default_value tv) 0 (TAKE n vs'))`
      by (irule vyper_to_abi_sparse_TAKE \\ gvs[])
  \\ pop_assum SUBST_ALL_TAC
  (* Apply IH *)
  \\ `vyper_to_abi_sparse env t tv n (enumerate_static_array (default_value tv) 0 (TAKE n vs')) =
      SOME (TAKE n vs)` by (first_x_assum irule \\ rw[LENGTH_TAKE, EL_TAKE])
  (* Witness: TAKE n vs *)
  \\ qexists_tac `TAKE n vs` \\ gvs[]
  (* ALOOKUP at index n *)
  \\ `ALOOKUP (enumerate_static_array (default_value tv) 0 vs') n =
      if EL n vs' = default_value tv then NONE else SOME (EL n vs')` by (
       `ALOOKUP (enumerate_static_array (default_value tv) 0 vs') (0 + n) =
        if EL n vs' = default_value tv then NONE else SOME (EL n vs')` suffices_by gvs[]
       \\ irule enumerate_static_array_ALOOKUP \\ gvs[])
  (* Case split *)
  \\ Cases_on `EL n vs' = default_value tv`
  (* Case 1: EL n vs' = default_value tv - need abi_to_vyper_default_value_inv *)
  >- (disj1_tac \\ gvs[]
      \\ `abi_to_vyper env t (EL n vs) = SOME (default_value tv)` by gvs[]
      \\ `EL n vs = default_to_abi tv` by (
          irule abi_to_vyper_default_value_inv \\ qexists_tac `env` \\ qexists_tac `t` \\ gvs[])
      \\ `TAKE n vs ++ [EL n vs] = vs` suffices_by gvs[]
      \\ irule TAKE_SNOC_EL \\ gvs[])
  (* Case 2: EL n vs' ≠ default_value tv - use vyper_to_abi directly *)
  \\ disj2_tac
  \\ qexists_tac `EL n vs'`
  \\ conj_tac >- gvs[]
  \\ qexists_tac `EL n vs`
  \\ conj_tac >- gvs[]
  \\ irule TAKE_SNOC_EL \\ gvs[]
QED

(* Helper 6: Element-wise correspondence from list operations *)
Theorem abi_to_vyper_list_EL:
  ∀env ts avs vs.
    abi_to_vyper_list env ts avs = SOME vs ⇒
    LENGTH ts = LENGTH avs ∧
    LENGTH vs = LENGTH avs ∧
    (∀i. i < LENGTH avs ⇒ abi_to_vyper env (EL i ts) (EL i avs) = SOME (EL i vs))
Proof
  rw[abi_to_vyper_list_OPT_MMAP]
  \\ gvs[OPT_MMAP_SOME_IFF]
  \\ rw[EL_MAP, EL_ZIP]
  \\ gvs[EVERY_MEM, MEM_ZIP, MEM_MAP, PULL_EXISTS, IS_SOME_EXISTS]
  \\ res_tac \\ gvs[]
QED

Theorem vyper_to_abi_list_EL:
  ∀env ts vs avs.
    vyper_to_abi_list env ts vs = SOME avs ⇒
    LENGTH ts = LENGTH vs ∧
    LENGTH avs = LENGTH vs ∧
    (∀i. i < LENGTH vs ⇒ vyper_to_abi env (EL i ts) (EL i vs) = SOME (EL i avs))
Proof
  rw[vyper_to_abi_list_OPT_MMAP]
  \\ gvs[OPT_MMAP_SOME_IFF]
  \\ rw[EL_MAP, EL_ZIP]
  \\ gvs[EVERY_MEM, MEM_ZIP, MEM_MAP, PULL_EXISTS, IS_SOME_EXISTS]
  \\ res_tac \\ gvs[]
QED

(* ===== Encoding default values ===== *)

(* Helper: sparse encoding with empty sparse list fills all slots with defaults.
   Simple induction on n. *)
Theorem vyper_to_abi_sparse_empty:
  ∀n env t tv. vyper_to_abi_sparse env t tv n [] = SOME (REPLICATE n (default_to_abi tv))
Proof
  Induct \\ rw[vyper_to_abi_def]
  \\ rw[LIST_EQ_REWRITE, EL_APPEND_EQN]
  \\ rw[EL_REPLICATE]
  \\ Cases_on `x` \\ gvs[EL_REPLICATE]
  \\ rw[iffRL SUB_EQ_0]
QED

(* Main theorem: encoding default_value gives the same result as default_to_abi.
   This justifies that default_to_abi is not a separate concept - it's just
   a shortcut that avoids creating intermediate Vyper values. *)
Theorem vyper_to_abi_default_value:
  (∀env t tv. evaluate_type env t = SOME tv ⇒
              vyper_to_abi env t (default_value tv) = SOME (default_to_abi tv)) ∧
  (∀env ts acc tvs. evaluate_types env ts acc = SOME tvs ⇒
    vyper_to_abi_list env ts (MAP default_value (DROP (LENGTH acc) tvs)) =
      SOME (MAP default_to_abi (DROP (LENGTH acc) tvs)))
Proof
  ho_match_mp_tac evaluate_type_ind
  (* BaseT bt: direct computation, AddressT needs word_of_bytes_word_to_bytes *)
  \\ conj_tac >- (
    Cases_on `bt` \\
    rw[evaluate_type_def, vyper_to_abi_def,
       default_value_def, default_to_abi_def] \\
    TRY (rename1`BytesT bd` \\ Cases_on `bd`) \\
    rw[evaluate_type_def, vyper_to_abi_def,
       default_value_def, default_to_abi_def] \\
    DEP_REWRITE_TAC[word_of_bytes_word_to_bytes] \\
    rw[divides_def] )
  (* TupleT ts: use IH on list, default_value_tuple_MAP *)
  \\ conj_tac >- (
    rw[evaluate_type_def, vyper_to_abi_def, CaseEq"option"] \\ gvs[]
    \\ gvs[vyper_to_abi_def, default_value_def, default_to_abi_def]
    \\ rw[default_value_tuple_MAP, vyper_to_abi_def, ETA_AX] )
  (* ArrayT t bd: Dynamic is trivial, Fixed uses vyper_to_abi_sparse_empty *)
  \\ conj_tac >- (
    Cases_on `bd` \\ rw[evaluate_type_def, CaseEq"option"]
    \\ gvs[default_to_abi_def, default_value_def]
    \\ rw[vyper_to_abi_sparse_empty] )
  (* StructT id: use IH on field types, default_value_struct_MAP *)
  \\ conj_tac >- (
    rw[evaluate_type_def, CaseEq"type_args", CaseEq"option"]
    \\ gvs[default_value_def, default_to_abi_def, default_value_struct_MAP]
    \\ gvs[evaluate_types_OPT_MMAP, OPT_MMAP_SOME_IFF]
    \\ gvs[MAP_ZIP, ZIP_MAP, MAP_MAP_o, o_DEF] )
  (* FlagT id: direct computation *)
  \\ conj_tac >- (
    rw[evaluate_type_def, CaseEq"option", CaseEq"type_args"]
    \\ gvs[default_value_def, default_to_abi_def] )
  (* NoneT: direct computation *)
  (* evaluate_types [] acc: trivial *)
  (* evaluate_types (t::ts) acc: list induction using single-type IH *)
  \\ rw[evaluate_type_def, CaseEq"option"]
  \\ gvs[default_value_def, default_to_abi_def, DROP_LENGTH_TOO_LONG]
  \\ gvs[evaluate_types_OPT_MMAP, OPT_MMAP_SOME_IFF, DROP_APPEND, iffRL SUB_EQ_0]
  \\ gvs[DROP_LENGTH_TOO_LONG]
QED

(* ===== Main Roundtrip Theorem: abi_to_vyper then vyper_to_abi ===== *)

Theorem abi_to_vyper_vyper_to_abi:
  (∀env ty av v. abi_to_vyper env ty av = SOME v ⇒ vyper_to_abi env ty v = SOME av) ∧
  (∀env tys avs vs. abi_to_vyper_list env tys avs = SOME vs ⇒ vyper_to_abi_list env tys vs = SOME avs)
Proof
  ho_match_mp_tac abi_to_vyper_ind \\ rw[]
  \\ gvs[abi_to_vyper_def, vyper_to_abi_def, check_IntV_def, AllCaseEqs(),
         integerTheory.NUM_OF_INT, bytes_encode_decode_roundtrip', NULL_EQ]
  (* AddressT: need word roundtrip *)
  >- (drule within_int_bound_Unsigned_dimword
      \\ gvs[address_word_roundtrip, dimword_def])
  (* ArrayT: Fixed and Dynamic cases *)
  >- (gvs[vyper_to_abi_def]
      \\ Cases_on `b`
      \\ gvs[make_array_value_def]
      (* Fixed case: need vyper_to_abi_sparse reconstruction *)
      >- (drule abi_to_vyper_list_EL \\ rw[]
          \\ `vyper_to_abi_sparse env t tv n
                (enumerate_static_array (default_value tv) 0 vs') = SOME avs`
             suffices_by rw[]
          \\ irule vyper_to_abi_sparse_correct
          \\ gvs[compatible_bound_def]
          \\ drule vyper_to_abi_list_EL \\ rw[]
          \\ gvs[EL_REPLICATE])
      (* Dynamic case: need vyper_to_abi_same from vyper_to_abi_list *)
      >- (drule abi_to_vyper_list_EL \\ rw[]
          \\ `vyper_to_abi_same env t vs' = SOME avs` suffices_by rw[]
          \\ irule vyper_to_abi_same_REPLICATE
          \\ gvs[]))
  (* StructT: need MAP SND (ZIP ...) = vs' *)
  >- (drule abi_to_vyper_list_EL \\ rw[]
      \\ gvs[MAP_ZIP])
QED

(* ===== ABI Encoding ===== *)

Definition evaluate_abi_encode_def:
  evaluate_abi_encode tenv typ v =
    let abiTy = vyper_to_abi_type typ in
    case vyper_to_abi tenv typ v of
      SOME av => INL $ BytesV (Dynamic (LENGTH (enc abiTy av))) (enc abiTy av)
    | NONE => INR "abi_encode conversion"
End

(* Note: cv_auto_trans skipped for evaluate_abi_encode because it uses
   vyper_to_abi which is not cv-translated. *)
