Theory vyperABI
Ancestors
  contractABI vyperAST vyperInterpreter
  vyperMisc string words list rich_list combin pair arithmetic
Libs
  cv_transLib
  wordsLib

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
  vyper_to_abi_type (TupleT ts) = Tuple (MAP vyper_to_abi_type ts) ∧
  vyper_to_abi_type (ArrayT t (Dynamic _)) = Array NONE (vyper_to_abi_type t) ∧
  vyper_to_abi_type (ArrayT t (Fixed n)) = Array (SOME n) (vyper_to_abi_type t) ∧
  vyper_to_abi_type (StructT id) = Tuple [] (* TODO *) ∧
  vyper_to_abi_type (FlagT _) = Uint 256 ∧
  vyper_to_abi_type NoneT = Tuple []
Termination
  WF_REL_TAC ‘measure type_size’
End

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

(* Convert default value for a type directly to ABI encoding.
   This avoids creating an intermediate Vyper value. *)
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

(* String encoding roundtrip: CHR o w2n o n2w o ORD = id *)
Theorem string_encode_decode_roundtrip:
  ∀s. MAP (CHR o w2n) (MAP ((n2w:num->word8) o ORD) s) = s
Proof
  Induct \\ simp[]
  \\ rw[] \\ `ORD h < 256` by simp[ORD_BOUND]
  \\ simp[CHR_ORD]
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

(* Helper: evaluate_types in terms of OPT_MMAP *)
Theorem evaluate_types_OPT_MMAP:
  ∀ts acc. evaluate_types env ts acc =
    OPTION_MAP ((++) (REVERSE acc)) (OPT_MMAP (evaluate_type env) ts)
Proof
  Induct \\ rw[evaluate_type_def]
  \\ CASE_TAC \\ gvs[]
  \\ Cases_on `OPT_MMAP (evaluate_type env) ts` \\ gvs[]
QED

(* Decoding default_to_abi always succeeds and gives default_value. *)
Theorem abi_to_vyper_default_to_abi:
  (∀env t tv. evaluate_type env t = SOME tv ⇒
              abi_to_vyper env t (default_to_abi tv) = SOME (default_value tv)) ∧
  (∀env ts acc tvs. evaluate_types env ts acc = SOME tvs ⇒
    LENGTH tvs = LENGTH ts + LENGTH acc ∧
    abi_to_vyper_list env ts (MAP default_to_abi (DROP (LENGTH acc) tvs)) = 
      SOME (MAP default_value (DROP (LENGTH acc) tvs)))
Proof
  ho_match_mp_tac evaluate_type_ind
  (* Case 1: BaseT bt *)
  \\ conj_tac >- (
    Cases_on `bt` \\
    rw[evaluate_type_def, abi_to_vyper_def, default_value_def] \\
    gvs[default_to_abi_def, default_value_def, check_IntV_def] \\
    TRY(Cases_on `b`) \\ gvs[default_to_abi_def, default_value_def] \\
    EVAL_TAC \\ rw[] )
  (* Case 2: TupleT ts *)
  \\ conj_tac >- (
    rw[evaluate_type_def, CaseEq"option"]
    \\ first_x_assum drule
    \\ gvs[abi_to_vyper_def, default_to_abi_def, CaseEq"option", ETA_AX]
    \\ rw[default_value_def, default_value_tuple_MAP] )
 (* Case 3: ArrayT t bd *)
  \\ conj_tac >- (
    Cases_on `bd` \\ rw[evaluate_type_def, CaseEq"option"]
    \\ first_x_assum drule
    \\ gvs[abi_to_vyper_def, default_to_abi_def, CaseEq"option",
           default_value_def, make_array_value_def]
    \\ rw[]
    \\ TRY(rename1`compatible_bound` \\ EVAL_TAC)
    \\ gvs[abi_to_vyper_list_OPT_MMAP]
    \\ simp[OPT_MMAP_SOME_IFF]
    \\ simp[EVERY_MAP, ZIP_REPLICATE]
    \\ qspec_tac(`0`,`m`)
    \\ Induct_on `n` \\ rw[enumerate_static_array_def]
    \\ gvs[CaseEq"option"]
    \\ rw[enumerate_static_array_def] )
  (* Case 4: StructT id *)
  \\ conj_tac >- (
    rw[evaluate_type_def, CaseEq"option", CaseEq"type_args"]
    \\ first_x_assum drule
    \\ gvs[abi_to_vyper_def, default_to_abi_def, CaseEq"option", ETA_AX]
    \\ rw[default_value_def, default_value_struct_MAP]
    \\ rw[MAP_ZIP]
    \\ gvs[ZIP_MAP]
    \\ gvs[MAP_MAP_o,o_DEF] )
  (* Case 5: FlagT id *)
  \\ conj_tac >- (
    rw[evaluate_type_def, CaseEq"option", CaseEq"type_args"]
    \\ gvs[default_to_abi_def, default_value_def] )
  (* Case 6: NoneT *)
  \\ conj_tac >- (
    rw[evaluate_type_def, default_value_def]
    \\ gvs[default_to_abi_def] )
  (* Case 7: evaluate_types [] acc *)
  \\ conj_tac >- (
    rw[evaluate_type_def]
    \\ gvs[DROP_LENGTH_TOO_LONG] )
  (* Case 8: evaluate_types (t::ts) acc *)
  \\ rw[evaluate_type_def, CaseEq"option"]
  \\ gvs[evaluate_types_OPT_MMAP]
  \\ gvs[DROP_APPEND, DROP_LENGTH_TOO_LONG, iffRL SUB_EQ_0]
QED
