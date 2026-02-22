Theory vyperValue
Ancestors
  alist arithmetic finite_map list pair rich_list
  cv cv_std vfmState vyperAST vyperMisc
Libs
  cv_transLib wordsLib

(* `evaluate_type` is used to convert a Vyper `type` to a `type_value` with
* structure and flag declaration information inlined *)

Datatype:
  type_value
  = BaseTV base_type
  | TupleTV (type_value list)
  | ArrayTV type_value bound
  | StructTV ((identifier # type_value) list)
  | FlagTV num
  | NoneTV
End

Datatype:
  type_args
  = StructArgs (argument list)
  | FlagArgs num
  | InterfaceArgs (interface_func list)
End

Definition evaluate_type_def:
  evaluate_type tenv (BaseT bt) =
    (if bt = IntT 0 then NONE
     else SOME $ BaseTV bt) ∧
  evaluate_type tenv (TupleT ts) =
    (case evaluate_types tenv ts [] of
     | NONE => NONE
     | SOME tvs => SOME $ TupleTV tvs) ∧
  evaluate_type tenv (ArrayT t bd) =
    (case evaluate_type tenv t of
     | SOME tv => SOME $ ArrayTV tv bd
     | _ => NONE) ∧
  evaluate_type tenv (StructT id) =
  (let nid = string_to_num id in
   case FLOOKUP tenv nid of
   | SOME $ StructArgs args =>
     (let names = MAP FST args in
      case evaluate_types (tenv \\ nid) (MAP SND args) []
      of SOME tvs => SOME $ StructTV (ZIP (names, tvs))
       | _ => NONE)
   | _ => NONE) ∧
  evaluate_type tenv (FlagT id) =
  (let nid = string_to_num id in
   case FLOOKUP tenv nid of
   | SOME $ FlagArgs m =>
       (if m ≤ 256 then SOME $ FlagTV m
        else NONE)
   | _ => NONE) ∧
  evaluate_type tenv (NoneT) = SOME NoneTV ∧
  evaluate_types tenv [] acc = SOME $ REVERSE acc ∧
  evaluate_types tenv (t::ts) acc =
  (case evaluate_type tenv t of
   | SOME tv => evaluate_types tenv ts (tv::acc)
   | _ => NONE)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx.
    case x
      of INL (env, t) => (CARD (FDOM env), type_size t)
       | INR (env, ts, _) => (CARD (FDOM env), list_size type_size ts))’
  \\ rw[FLOOKUP_DEF]
  \\ disj1_tac
  \\ CCONTR_TAC
  \\ fs[]
End

(* the long termination argument below can be ignored: it is an artefact of the
* cv_compute machinery's need for a termination proof over _all_ cv values, and
* the fact that evaluate_type's termination argument is a little complex
* (uses the fact that we disallow cycles of struct dependency) *)

val () = cv_auto_trans_rec evaluate_type_def (
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx.
    case x
      of INL (env, t) => (cv$c2n $ cv_size' env, cv_size t)
       | INR (env, ts, _) => (cv$c2n (cv_size' env), cv_size ts))’
  \\ rw[]
  \\ TRY(Cases_on`cv_v` \\ gs[] \\ NO_TAC)
  \\ TRY(Cases_on`cv_v` \\ gs[]
         \\ qmatch_asmsub_rename_tac`cv_ispair cv_v`
         \\ Cases_on`cv_v` \\ gs[] \\ NO_TAC)
  \\ TRY(Cases_on`cv_v` \\ gs[]
         \\ qmatch_goalsub_rename_tac`cv_fst cv_v`
         \\ Cases_on`cv_v` \\ gs[] \\ NO_TAC)
  \\ disj1_tac
  \\ pop_assum mp_tac
  \\ qmatch_goalsub_abbrev_tac`cv_lookup ck`
  \\ `cv_ispair ck = cv$Num 0`
  by (
    rw[Abbr`ck`, cv_string_to_num_def]
    \\ rw[Once keccakTheory.cv_l2n_def]
    \\ rw[cv_ispair_cv_add] )
  \\ pop_assum mp_tac
  \\ qid_spec_tac`cv_tenv`
  \\ qid_spec_tac`ck`
  \\ rpt (pop_assum kall_tac)
  \\ ho_match_mp_tac cv_stdTheory.cv_delete_ind
  \\ rpt gen_tac \\ strip_tac
  \\ simp[Once cv_lookup_def]
  \\ IF_CASES_TAC \\ gs[]
  \\ strip_tac \\ gs[]
  \\ reverse(IF_CASES_TAC \\ gs[])
  >- (
    Cases_on`ck` \\ gs[]
    \\ IF_CASES_TAC \\ gs[]
    \\ Cases_on`cv_tenv` \\ gs[]
    \\ Cases_on`0 < m` \\ gs[]
    \\ simp[Once cv_delete_def]
    \\ rw[Once cv_stdTheory.cv_size'_def]
    \\ rw[Once cv_stdTheory.cv_size'_def] )
  \\ Cases_on`cv_tenv` \\ gs[]
  \\ Cases_on`ck` \\ gs[]
  \\ strip_tac
  \\ simp[Once cv_delete_def]
  \\ Cases_on`g` \\ gs[]
  \\ Cases_on`m=0` \\ gs[]
  >- (
    rw[] \\ gs[]
    \\ rw[Once cv_stdTheory.cv_size'_def]
    \\ rw[Once cv_stdTheory.cv_size'_def, SimpR``prim_rec$<``]
    \\ rw[] )
  \\ simp[Once cv_stdTheory.cv_size'_def, SimpR``prim_rec$<``]
  \\ qmatch_goalsub_rename_tac`2 < p`
  \\ Cases_on`p=0` \\ gs[]
  \\ Cases_on`p=1` \\ gs[]
  \\ Cases_on`p=2` \\ gvs[]
  >- (IF_CASES_TAC \\ gs[cv_size'_cv_mk_BN])
  \\ IF_CASES_TAC \\ gs[]
);

(* Helper: evaluate_types in terms of OPT_MMAP *)
Theorem evaluate_types_OPT_MMAP:
  ∀ts acc. evaluate_types env ts acc =
    OPTION_MAP ((++) (REVERSE acc)) (OPT_MMAP (evaluate_type env) ts)
Proof
  Induct \\ rw[evaluate_type_def]
  \\ CASE_TAC \\ gvs[]
  \\ Cases_on `OPT_MMAP (evaluate_type env) ts` \\ gvs[]
QED

(* Vyper (runtime) values *)

Datatype:
  value
  = NoneV
  | BoolV bool
  | ArrayV array_value
  | IntV int_bound int
  | FlagV num num
  | DecimalV int
  | StringV num string
  | BytesV bound (word8 list)
  | StructV ((identifier, value) alist) ;
  array_value
  = DynArrayV type_value num (value list)
  | SArrayV type_value num ((num, value) alist)
  | TupleV (value list)
End

val from_to_value_thm = cv_typeLib.from_to_thm_for “:value”;
val from_value = from_to_value_thm |> concl |> rator |> rand
val to_value = from_to_value_thm |> concl |> rand

Overload AddressV = “λw: address. BytesV (Fixed 20) (word_to_bytes w T)”

(* default value at each type *)

Definition default_value_def:
  default_value (BaseTV (UintT n)) = IntV (Unsigned n) 0 ∧
  default_value (BaseTV (IntT n)) = IntV (Signed n) 0 ∧
  default_value (BaseTV DecimalT) = DecimalV 0 ∧
  default_value (TupleTV ts) = default_value_tuple [] ts ∧
  default_value (ArrayTV t (Dynamic n)) = ArrayV (DynArrayV t n []) ∧
  default_value (ArrayTV t (Fixed n)) = ArrayV (SArrayV t n []) ∧
  default_value (StructTV args) = default_value_struct [] args ∧
  default_value (FlagTV m) = FlagV m 0 ∧
  default_value NoneTV = NoneV ∧
  default_value (BaseTV BoolT) = BoolV F ∧
  default_value (BaseTV AddressT) = AddressV 0w ∧
  default_value (BaseTV (StringT n)) = StringV n "" ∧
  default_value (BaseTV (BytesT (Fixed n))) = BytesV (Fixed n) (REPLICATE n 0w) ∧
  default_value (BaseTV (BytesT (Dynamic n))) = BytesV (Dynamic n) [] ∧
  default_value_tuple acc [] = ArrayV $ TupleV $ REVERSE acc ∧
  default_value_tuple acc (t::ts) =
    default_value_tuple (default_value t :: acc) ts ∧
  default_value_struct acc [] = StructV (REVERSE acc) ∧
  default_value_struct acc ((id,t)::ps) =
    default_value_struct ((id,default_value t)::acc) ps
Termination
  WF_REL_TAC `measure (λx.
    case x
      of INL t => (type_value_size t)
       | INR (INL (_, ts)) => (list_size type_value_size ts)
       | INR (INR (_, ps)) => (list_size type_value_size (MAP SND ps)))`
  \\ rw[list_size_pair_size_map]
End

val () = cv_auto_trans default_value_def;

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

(* creating arrays *)

Definition enumerate_static_array_def:
  enumerate_static_array _ _ [] = [] ∧
  enumerate_static_array d n (v::vs) =
    let r = enumerate_static_array d (SUC n) vs in
    if v = d then r else (n,v)::r
End

val () = cv_trans enumerate_static_array_def;

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

Definition make_array_value_def:
  make_array_value tv (Fixed n) vs =
    SArrayV tv n (enumerate_static_array (default_value tv) 0 vs) ∧
  make_array_value tv (Dynamic n) vs =
    DynArrayV tv n vs
End

val () = cv_trans make_array_value_def;

(* bounds checking *)

Definition compatible_bound_def:
  compatible_bound (Fixed n) m = (n = m) ∧
  compatible_bound (Dynamic n) m = (m ≤ n)
End

val () = cv_auto_trans compatible_bound_def;

Definition within_int_bound_def:
  within_int_bound (Unsigned b) i = (
    0i ≤ i ∧ Num i < 2 ** b) ∧
  within_int_bound (Signed b) i = (
    0 < b ∧
    let b = b - 1 in
    let m = 2 ** b in
    if i < 0 then Num (-i) ≤ m
    else Num i < m
  )
End

(* value destructors *)

Definition dest_NumV_def:
  dest_NumV (IntV _ i) =
    (if i < 0 then NONE else SOME (Num i)) ∧
  dest_NumV _ = NONE
End

val () = cv_auto_trans dest_NumV_def;

Definition dest_AddressV_def:
  dest_AddressV (BytesV (Fixed b) bs) =
    (if b = 20 ∧ LENGTH bs = 20 then
      SOME (word_of_bytes T (0w:address) bs)
     else NONE) ∧
  dest_AddressV _ = NONE
End

val () = cv_auto_trans dest_AddressV_def;

Definition dest_StringV_def:
  dest_StringV (StringV _ s) = SOME s ∧
  dest_StringV _ = NONE
End

val () = cv_auto_trans dest_StringV_def;
