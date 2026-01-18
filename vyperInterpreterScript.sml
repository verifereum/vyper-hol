Theory vyperInterpreter
Ancestors
  arithmetic alist combin list finite_map pair rich_list
  cv cv_std vfmState vfmExecution[ignore_grammar] vyperAST
  vyperMisc
Libs
  cv_transLib wordsLib monadsyntax
  integerTheory[qualified] intSimps[qualified]

(* cv_rep theorem for FUNION on num-keyed fmaps *)
Theorem cv_rep_FUNION[cv_rep]:
  from_fmap f (FUNION m1 m2) = cv_union (from_fmap f m1) (from_fmap f m2)
Proof
  rw[cv_stdTheory.from_fmap_def, GSYM cv_stdTheory.cv_union_thm]
  \\ AP_TERM_TAC
  \\ dep_rewrite.DEP_REWRITE_TAC[sptreeTheory.spt_eq_thm]
  \\ simp[sptreeTheory.wf_union, sptreeTheory.wf_fromAList]
  \\ simp[sptreeTheory.lookup_union, sptreeTheory.lookup_fromAList]
  \\ simp[FLOOKUP_FUNION]
QED

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
  type_args = StructArgs (argument list) | FlagArgs num
End

Definition evaluate_type_def:
  evaluate_type tenv (BaseT bt) = SOME $ BaseTV bt ∧
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
   | SOME $ FlagArgs m => SOME $ FlagTV m
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

(* `subscript`s are the possible kinds of keys into HashMaps *)

Datatype:
  subscript
  = IntSubscript int
  | StrSubscript string
  | BytesSubscript (word8 list)
  | AttrSubscript identifier
End

(* since HashMaps can only appear at the top level, they are not mutually
* recursive with other `value`s, and we have `toplevel_value` as follows: *)

Datatype:
  toplevel_value = Value value | HashMap value_type ((subscript, toplevel_value) alist)
End

Definition is_Value_def[simp]:
  (is_Value (Value _) ⇔ T) ∧
  (is_Value _ ⇔ F)
End

val () = cv_auto_trans is_Value_def;

Type hmap = “:(subscript, toplevel_value) alist”

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
  WF_REL_TAC ‘measure (λx.
    case x
      of INL t => (type_value_size t)
       | INR (INL (_, ts)) => (list_size type_value_size ts)
       | INR (INR (_, ps)) => (list_size type_value_size (MAP SND ps)))’
  \\ rw[list_size_pair_size_map]
End

val () = cv_auto_trans default_value_def;

(* Evaluation of some of the simpler language constructs *)

Definition evaluate_literal_def:
  evaluate_literal (BoolL b) = BoolV b ∧
  evaluate_literal (StringL n s) = StringV n s ∧
  evaluate_literal (BytesL b bs) = BytesV b bs ∧
  evaluate_literal (IntL ib i) = IntV ib i ∧
  evaluate_literal (DecimalL i) = DecimalV i
End

val () = cv_auto_trans evaluate_literal_def;

(* reading arrays *)

Definition array_length_def:
  array_length av =
  case av of
  | DynArrayV _ _ ls => LENGTH ls
  | SArrayV _ n _ => n
  | TupleV ls => LENGTH ls
End

val () = cv_trans array_length_def;

Definition evaluate_in_array_def:
  evaluate_in_array v av =
  case av of
  | DynArrayV _ _ ls => MEM v ls
  | SArrayV t n al => (MEM v (MAP SND al) ∨
                       (LENGTH al < n ∧ v = default_value t))
  | TupleV ls => MEM v ls
End

val () = cv_auto_trans $
  REWRITE_RULE[member_intro]evaluate_in_array_def;

Definition array_index_def:
  array_index av i =
  if 0 ≤ i then let j = Num i in
  case av
    of DynArrayV _ _ ls => oEL j ls
     | SArrayV t n al =>
         if j < n then case ALOOKUP al j
         of SOME v => SOME v
          | NONE => SOME $ default_value t
         else NONE
     | TupleV ls => oEL j ls
  else NONE
End

val () = cv_trans array_index_def;

Definition extract_elements_def:
  extract_elements (ArrayV av) =
  (SOME $ case av
     of TupleV vs => vs
      | DynArrayV _ _ vs => vs
      | SArrayV t n al =>
          let d = default_value t in
          GENLIST (λi. case ALOOKUP al i of SOME v => v | NONE => d) n) ∧
  extract_elements _ = NONE
End

val () = cv_auto_trans extract_elements_def;

(* creating arrays *)

Definition enumerate_static_array_def:
  enumerate_static_array _ _ [] = [] ∧
  enumerate_static_array d n (v::vs) =
    let r = enumerate_static_array d (SUC n) vs in
    if v = d then r else (n,v)::r
End

val () = cv_trans enumerate_static_array_def;

Definition make_array_value_def:
  make_array_value tv (Fixed n) vs =
    SArrayV tv n (enumerate_static_array (default_value tv) 0 vs) ∧
  make_array_value tv (Dynamic n) vs =
    DynArrayV tv n vs
End

val () = cv_trans make_array_value_def;

(* binary operators and bounds checking *)

Definition binop_negate_def:
  binop_negate (INL (BoolV b)) = INL (BoolV (¬b)) ∧
  binop_negate x = x
End

val () = cv_auto_trans binop_negate_def;

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

Definition bounded_int_op_def:
  bounded_int_op u1 u2 r =
  if u1 = u2 then
    if within_int_bound u1 r
    then INL (IntV u1 r)
    else INR "bounded_int_op bound"
  else INR "bounded_int_op type"
End

(* optimisation on exponentiation: overflow immediately if power is too big *)
Theorem bounded_exp:
  bounded_int_op u1 u2 (i1 ** n2) =
  if u1 = u2 then
    if 2 ≤ ABS i1 ∧ int_bound_bits u1 < n2
    then INR "bounded_int_op bound"
    else let r = i1 ** n2 in
      if within_int_bound u1 r then INL (IntV u1 r)
    else INR "bounded_int_op bound"
  else INR "bounded_int_op type"
Proof
  rw[bounded_int_op_def]
  \\ gvs[int_exp_num]
  \\ `Num (ABS i1 ** n2) < 2 ** int_bound_bits u1`
  by (
    reverse $ Cases_on`u1`
    >- (
      gvs[within_int_bound_def]
      \\ gvs[integerTheory.INT_ABS]
      \\ IF_CASES_TAC
      \\ fsrw_tac[intSimps.INT_ARITH_ss][Num_int_exp]
      \\ Cases_on`EVEN n2`
      \\ fsrw_tac[intSimps.INT_ARITH_ss][] )
    \\ gvs[within_int_bound_def]
    \\ gvs[integerTheory.INT_ABS]
    \\ IF_CASES_TAC
    \\ fsrw_tac[intSimps.INT_ARITH_ss][Num_int_exp]
    >- (
      Cases_on`EVEN n2`
      \\ fsrw_tac[intSimps.INT_ARITH_ss][]
      >- (
        irule LESS_LESS_EQ_TRANS
        \\ goal_assum drule \\ simp[] )
      \\ irule LESS_EQ_LESS_TRANS
      \\ goal_assum $ drule_at Any \\ simp[] )
    \\ irule LESS_LESS_EQ_TRANS
    \\ goal_assum drule \\ simp[] )
  \\ gvs[Num_int_exp]
  \\ qmatch_asmsub_abbrev_tac`b < n2`
  \\ `2 ** b < 2 ** n2` by simp[]
  \\ qmatch_asmsub_abbrev_tac`n1 ** n2 < _`
  \\ `2 ≤ n1` by (
    simp[Abbr`n1`]
    \\ irule integerTheory.LE_NUM_OF_INT
    \\ simp[] )
  \\ `2 ** n2 ≤ n1 ** n2` by simp[]
  \\ `2n ** n2 < 2 ** b` by (
    irule LESS_EQ_LESS_TRANS
    \\ goal_assum drule \\ simp[] )
  \\ fs[]
QED

Definition bounded_decimal_op_def:
  bounded_decimal_op i =
  if within_int_bound (Signed 168) i
  then INL $ DecimalV i
  else INR "bounded_decimal_op"
End

Definition wrapped_int_op_def:
  wrapped_int_op u1 u2 i =
  if u1 = u2 then
    let b = int_bound_bits u1 in
      INL $ IntV u1 (int_mod i &(2 ** b))
  else INR "wrapped_int_op"
End

val wrapped_int_op_pre_def = cv_trans_pre "wrapped_int_op_pre" wrapped_int_op_def;

Theorem wrapped_int_op_pre[cv_pre]:
  wrapped_int_op_pre x y z
Proof
  rw[wrapped_int_op_pre_def]
QED

Definition evaluate_binop_def:
  evaluate_binop bop v1 v2 =
  case bop
    of Add => (case v1 of
         IntV u1 i1 => (case v2 of IntV u2 i2 =>
           bounded_int_op u1 u2 (i1 + i2) | _ => INR "binop")
       | DecimalV i1 => (case v2 of DecimalV i2 =>
           bounded_decimal_op (i1 + i2) | _ => INR "binop")
       | _ => INR "binop")
     | Sub => (case v1 of
         IntV u1 i1 => (case v2 of IntV u2 i2 =>
           bounded_int_op u1 u2 (i1 - i2) | _ => INR "binop")
       | DecimalV i1 => (case v2 of DecimalV i2 =>
           bounded_decimal_op (i1 - i2) | _ => INR "binop")
       | _ => INR "binop")
     | Mul => (case v1 of
         IntV u1 i1 => (case v2 of IntV u2 i2 =>
           bounded_int_op u1 u2 (i1 * i2) | _ => INR "binop")
       | DecimalV i1 => (case v2 of DecimalV i2 =>
           (let p = i1 * i2 in
            if within_int_bound (Signed 168) ((ABS p) / 10000000000)
            then INL $ DecimalV $ w2i $ word_quot (i2w p) (10000000000w: bytes32)
            else INR "Decimal Mul bound") | _ => INR "binop")
       | _ => INR "binop")
     | Div => (case v1 of
         IntV u1 i1 => (case v2 of IntV u2 i2 =>
           (if i2 = 0 then INR "Div0" else
            bounded_int_op u1 u2 $
              w2i $ (if is_Unsigned u1 then word_div else word_quot)
                      ((i2w i1):bytes32) (i2w i2)) | _ => INR "binop")
       | DecimalV i1 => (case v2 of DecimalV i2 =>
           (if i2 = 0 then INR "Div0" else
            bounded_decimal_op $
              w2i $ word_quot ((i2w (i1 * 10000000000)):bytes32) (i2w i2))
                         | _ => INR "binop")
       | _ => INR "binop")
     | UAdd => (case v1 of
         IntV u1 i1 => (case v2 of IntV u2 i2 =>
           wrapped_int_op u1 u2 (i1 + i2) | _ => INR "binop")
       | _ => INR "binop")
     | USub => (case v1 of
         IntV u1 i1 => (case v2 of IntV u2 i2 =>
           wrapped_int_op u1 u2 (i1 - i2) | _ => INR "binop")
       | _ => INR "binop")
     | UMul => (case v1 of
         IntV u1 i1 => (case v2 of IntV u2 i2 =>
           wrapped_int_op u1 u2 (i1 * i2) | _ => INR "binop")
       | _ => INR "binop")
     | UDiv => (case v1 of
         IntV u1 i1 => (case v2 of IntV u2 i2 =>
           if i2 = 0 then INR "UDiv0" else
           wrapped_int_op u1 u2 (i1 / i2) | _ => INR "binop")
       | _ => INR "binop")
     | Mod => (case v1 of
         IntV u1 i1 => (case v2 of IntV u2 i2 =>
           (if i2 = 0 then INR "Mod0" else
            bounded_int_op u1 u2 $
              w2i $ (if is_Unsigned u1 then word_mod else word_rem)
                      ((i2w i1):bytes32) (i2w i2)) | _ => INR "binop")
       | DecimalV i1 => (case v2 of DecimalV i2 =>
           (if i2 = 0 then INR "Mod0" else
            bounded_decimal_op $
              (w2i $ word_rem ((i2w i1):bytes32) (i2w i2)))
                         | _ => INR "binop")
       | _ => INR "binop")
     | Exp => (case v1 of
         IntV u1 i1 => (case v2 of IntV u2 i2 =>
           (if i2 < 0 then INR "Exp~" else
            bounded_int_op u1 u2 $ (i1 ** (Num i2))) | _ => INR "binop")
       | _ => INR "binop")
     | ExpMod => (case v1 of
         IntV u1 i1 => (case v2 of IntV u2 i2 =>
           (if u1 = Unsigned 256 ∧ u2 = u1
            then INL $ IntV u1 (w2i (word_exp (i2w i1 : bytes32) (i2w i2)))
            else INR "ExpMod") | _ => INR "binop")
       | _ => INR "binop")
     | ShL => (case v1 of
         IntV u1 i1 => (case v2 of IntV u2 i2 =>
           (* TODO: check type constraints on shifts *)
           (if i2 < 0 then INR "ShL0"
            else INL $ IntV u1 $ int_shift_left (Num i2) i1) | _ => INR "binop")
       | _ => INR "binop")
     | ShR => (case v1 of
         IntV u1 i1 => (case v2 of IntV u2 i2 =>
           (* TODO: check type constraints on shifts *)
           (if i2 < 0 then INR "ShR0"
            else INL $ IntV u1 $ int_shift_right (Num i2) i1) | _ => INR "binop")
       | _ => INR "binop")
     | And => (case v1 of
         IntV u1 i1 => (case v2 of IntV u2 i2 =>
           bounded_int_op u1 u2 (int_and i1 i2) | _ => INR "binop")
       | BoolV b1 => (case v2 of BoolV b2 =>
           INL $ BoolV (b1 ∧ b2) | _ => INR "binop")
       | FlagV m1 n1 => (case v2 of FlagV m2 n2 =>
           (if m1 = m2
            then INL $ FlagV m1 (Num(int_and (&n1) (&n2))) (* TODO: bitwise nums *)
            else INR "binop flag type") | _ => INR "binop")
       | _ => INR "binop")
     | Or => (case v1 of
         IntV u1 i1 => (case v2 of IntV u2 i2 =>
           bounded_int_op u1 u2 (int_or i1 i2) | _ => INR "binop")
       | BoolV b1 => (case v2 of BoolV b2 =>
           INL $ BoolV (b1 ∨ b2) | _ => INR "binop")
       | FlagV m1 n1 => (case v2 of FlagV m2 n2 =>
           (if m1 = m2
            then INL $ FlagV m1 (Num(int_or (&n1) (&n2))) (* TODO: bitwise nums *)
            else INR "binop flag type") | _ => INR "binop")
       | _ => INR "binop")
     | XOr => (case v1 of
         IntV u1 i1 => (case v2 of IntV u2 i2 =>
           bounded_int_op u1 u2 (int_xor i1 i2) | _ => INR "binop")
       | BoolV b1 => (case v2 of BoolV b2 =>
           INL $ BoolV (b1 ≠ b2) | _ => INR "binop")
       | FlagV m1 n1 => (case v2 of FlagV m2 n2 =>
           (if m1 = m2
            then INL $ FlagV m1 (Num(int_xor (&n1) (&n2))) (* TODO: bitwise nums *)
            else INR "binop flag type") | _ => INR "binop")
       | _ => INR "binop")
     | In => (case v2 of
         FlagV m2 n2 => (case v1 of FlagV m1 n1 =>
           (if m1 = m2
            then INL $ BoolV (int_and (&n1) (&n2) ≠ 0) (* TODO: use bitwise ∧ on nums *)
            else INR "In type") | _ => INR "binop")
       | ArrayV av => INL $ BoolV $ evaluate_in_array v1 av
       | _ => INR "binop")
     | Eq => (case v1 of
         IntV u1 i1 => (case v2 of IntV u2 i2 =>
           (if u1 = u2 then INL (BoolV (i1 = i2)) else INR "Eq type")
                                 | _ => INR "binop")
       | FlagV m1 n1 => (case v2 of FlagV m2 n2 =>
           (if m1 = m2 then INL (BoolV (n1 = n2)) else INR "Eq type")
                                 | _ => INR "binop")
       | StringV _ s1 => (case v2 of StringV _ s2 =>
           INL (BoolV (s1 = s2)) | _ => INR "binop")
       | BytesV _ s1 => (case v2 of BytesV _ s2 =>
           INL (BoolV (s1 = s2)) | _ => INR "binop")
       | BoolV s1 => (case v2 of BoolV s2 =>
           INL (BoolV (s1 = s2)) | _ => INR "binop")
       | DecimalV s1 => (case v2 of DecimalV s2 =>
           INL (BoolV (s1 = s2)) | _ => INR "binop")
       | _ => INR "binop")
     | Lt => (case v1 of
         IntV u1 i1 => (case v2 of IntV u2 i2 =>
           (if u1 = u2 then INL (BoolV (i1 < i2)) else INR "Lt type") | _ => INR "binop")
       | DecimalV i1 => (case v2 of DecimalV i2 =>
           INL (BoolV (i1 < i2)) | _ => INR "binop")
       | _ => INR "binop")
     | Gt => (case v1 of
         IntV u1 i1 => (case v2 of IntV u2 i2 =>
           (if u1 = u2 then INL (BoolV (i1 > i2)) else INR "Gt type") | _ => INR "binop")
       | DecimalV i1 => (case v2 of DecimalV i2 =>
           INL (BoolV (i1 > i2)) | _ => INR "binop")
       | _ => INR "binop")
     | LtE => (case v1 of
         IntV u1 i1 => (case v2 of IntV u2 i2 =>
           (if u1 = u2 then INL (BoolV (i1 ≤ i2)) else INR "LtE type") | _ => INR "binop")
       | DecimalV i1 => (case v2 of DecimalV i2 =>
           INL (BoolV (i1 ≤ i2)) | _ => INR "binop")
       | _ => INR "binop")
     | GtE => (case v1 of
         IntV u1 i1 => (case v2 of IntV u2 i2 =>
           (if u1 = u2 then INL (BoolV (i1 ≥ i2)) else INR "GtE type") | _ => INR "binop")
       | DecimalV i1 => (case v2 of DecimalV i2 =>
           INL (BoolV (i1 ≥ i2)) | _ => INR "binop")
       | _ => INR "binop")
     | Min => (case v1 of
         IntV u1 i1 => (case v2 of IntV u2 i2 =>
           (if u1 = u2 then INL (IntV u1 (if i1 < i2 then i1 else i2))
            else INR "Min type") | _ => INR "binop")
       | DecimalV i1 => (case v2 of DecimalV i2 =>
           INL (DecimalV (if i1 < i2 then i1 else i2)) | _ => INR "binop")
       | _ => INR "binop")
     | Max => (case v1 of
         IntV u1 i1 => (case v2 of IntV u2 i2 =>
           (if u1 = u2 then INL (IntV u1 (if i1 < i2 then i2 else i1))
            else INR "Min type") | _ => INR "binop")
       | DecimalV i1 => (case v2 of DecimalV i2 =>
           INL (DecimalV (if i1 < i2 then i2 else i1)) | _ => INR "binop")
       | _ => INR "binop")
     | NotIn => binop_negate $ evaluate_binop In v1 v2
     | NotEq => binop_negate $ evaluate_binop Eq v1 v2
     | _ => INR "binop"
Termination
  WF_REL_TAC ‘inv_image $< (λ(b,x,y). if b = NotIn ∨ b = NotEq then 2n else 0n)’
  \\ rw[]
End

val cv_NotIn_tm = rand $ rhs $ concl $ cv_eval_raw “NotIn”;
val cv_NotEq_tm = rand $ rhs $ concl $ cv_eval_raw “NotEq”;

val () = cv_auto_trans_rec
  (REWRITE_RULE [bounded_exp, COND_RATOR] evaluate_binop_def)
  (WF_REL_TAC
    ‘inv_image $< (λ(b,x,y).
       if b = ^cv_NotIn_tm ∨ b = ^cv_NotEq_tm
       then 2n else 0n)’
   \\ rw[] \\ rw[] \\ gvs[]
   \\ Cases_on`cv_bop` \\ gvs[]
   \\ rw[]);

Definition compatible_bound_def:
  compatible_bound (Fixed n) m = (n = m) ∧
  compatible_bound (Dynamic n) m = (m ≤ n)
End

val () = cv_auto_trans compatible_bound_def;

(* concat *)

Definition init_concat_output_def:
  init_concat_output n (BytesV _ bs) = SOME $ BytesV (Dynamic n) bs ∧
  init_concat_output n (StringV _ s) = SOME $ StringV n s ∧
  init_concat_output _ _ = NONE
End

val () = cv_auto_trans init_concat_output_def;

Definition evaluate_concat_loop_def:
  evaluate_concat_loop (StringV n s1) sa ba [] =
  (let s = FLAT $ s1::REVERSE sa in
   (if compatible_bound (Dynamic n) (LENGTH s)
    then INL (StringV n s)
    else INR "concat bound")) ∧
  evaluate_concat_loop (BytesV b b1) sa ba [] =
  (let bs = FLAT $ b1::REVERSE ba in
   (if compatible_bound b (LENGTH bs)
    then INL (BytesV b bs)
    else INR "concat bound")) ∧
  evaluate_concat_loop (StringV n s1) sa ba ((StringV _ s2)::vs) =
  evaluate_concat_loop (StringV n s1) (s2::sa) ba vs ∧
  evaluate_concat_loop (BytesV b b1) sa ba ((BytesV _ b2)::vs) =
  evaluate_concat_loop (BytesV b b1) sa (b2::ba) vs ∧
  evaluate_concat_loop _ _ _ _ = INR "concat types"
End

val () = cv_auto_trans evaluate_concat_loop_def;

Definition evaluate_concat_def:
  evaluate_concat n vs =
  if NULL vs ∨ NULL (TL vs) then INR "concat <2"
  else
    case init_concat_output n (HD vs)
      of SOME v => evaluate_concat_loop v [] [] (TL vs)
       | NONE => INR "concat type or bound"
End

val evaluate_concat_pre_def = cv_auto_trans_pre "evaluate_concat_pre" evaluate_concat_def;

Theorem evaluate_concat_pre[cv_pre]:
  evaluate_concat_pre b vs
Proof
  rw[evaluate_concat_pre_def]
  \\ strip_tac \\ gvs[]
QED

(* slice *)

Definition evaluate_slice_def:
  evaluate_slice v sv lv n =
  let b = Dynamic n in
  case dest_NumV sv of NONE => INR "evaluate_slice start" | SOME start =>
  case dest_NumV lv of NONE => INR "evaluate_slice length" | SOME length =>
  case v
  of BytesV bb bs => (
       if (case bb of Fixed m => m = 32 | _ => T) then
       if start + length ≤ LENGTH bs then
       if compatible_bound b length then
         INL $ BytesV b (TAKE length (DROP start bs))
       else INR "evaluate_slice bound"
       else INR "evaluate_slice range"
       else INR "evaluate_slice BytesV bound")
   | StringV _ s => (
       if start + length ≤ LENGTH s then
       if compatible_bound b length then
         INL $ StringV n (TAKE length (DROP start s))
       else INR "evaluate_slice bound"
       else INR "evaluate_slice range")
  | _ => INR "evaluate_slice v"
End

val () = cv_auto_trans evaluate_slice_def;

(* some more builtins *)

Definition evaluate_as_wei_value_def:
  evaluate_as_wei_value dn v =
  let m = case dn of
          | Wei => 1
          | Kwei => 1000
          | Mwei => 1000000
          | Gwei => 1000000000
          | Szabo => 1000000000000
          | Finney => 1000000000000000
          | Ether => 1000000000000000000
          | KEther => 1000000000000000000000
          | MEther => 1000000000000000000000000
          | GEther => 1000000000000000000000000000
          | TEther => 1000000000000000000000000000000 in
  let r = case v of IntV u i => i * m
                  | DecimalV i => (i * m) / 1000000000
                  | _ => -1 in
  if 0 ≤ r then
    let u = Unsigned 256 in
    if within_int_bound u r then
      INL $ IntV u r
    else INR "ewv bound"
  else INR "ewv neg"
End

val evaluate_as_wei_value_pre_def =
  cv_auto_trans_pre "evaluate_as_wei_value_pre" evaluate_as_wei_value_def;

Theorem evaluate_as_wei_value_pre[cv_pre]:
  evaluate_as_wei_value_pre x y
Proof
  rw[evaluate_as_wei_value_pre_def]
QED

Definition evaluate_max_value_def:
  evaluate_max_value (BaseT (UintT n)) = INL $ IntV (Unsigned n) (&(2 ** n) - 1) ∧
  evaluate_max_value (BaseT (IntT n)) = (if n = 0
                                         then INR "max_value IntT"
                                         else INL $ IntV (Signed n) (&(2 ** (n-1)) - 1)) ∧
  evaluate_max_value (BaseT DecimalT) = INL $ DecimalV (&(2 ** 167) - 1) ∧
  evaluate_max_value _ = INR "evaluate_max_value"
End

val () = cv_auto_trans evaluate_max_value_def;

Definition evaluate_min_value_def:
  evaluate_min_value (BaseT (UintT n)) = INL $ IntV (Unsigned n) 0 ∧
  evaluate_min_value (BaseT (IntT n)) = (if n = 0
                                         then INR "min_value IntT"
                                         else INL $ IntV (Signed n) (-&(2 ** (n-1)))) ∧
  evaluate_min_value (BaseT DecimalT) = INL $ DecimalV (-&(2 ** 167)) ∧
  evaluate_min_value _ = INR "evaluate_min_value"
End

val () = cv_auto_trans evaluate_min_value_def;

(* subscripting into arrays, structs, hashmaps *)

Definition evaluate_attribute_def:
  evaluate_attribute (StructV kvs) id =
  (case ALOOKUP kvs id of SOME v => INL v
   | _ => INR "attribute") ∧
  evaluate_attribute _ _ = INR "evaluate_attribute"
End

val () = cv_auto_trans evaluate_attribute_def;

Definition value_to_key_def:
  value_to_key (IntV _ i) = SOME $ IntSubscript i ∧
  value_to_key (StringV _ s) = SOME $ StrSubscript s ∧
  value_to_key (BytesV _ bs) = SOME $ BytesSubscript bs ∧
  value_to_key (FlagV _ n) = SOME $ IntSubscript $ &n ∧
  value_to_key _ = NONE
End

val () = cv_auto_trans value_to_key_def;

Definition evaluate_subscript_def:
  evaluate_subscript tenv (Value (ArrayV av)) (IntV _ i) =
  (case array_index av i
   of SOME v => INL $ Value v
   | _ => INR "subscript array_index") ∧
  evaluate_subscript tenv (HashMap vt hm) kv =
  (case value_to_key kv of SOME k =>
    (case ALOOKUP hm k of SOME tv => INL tv
        | _ => (case vt of Type typ =>
                  (case evaluate_type tenv typ of
                   | SOME tv => INL $ Value $ default_value tv
                   | NONE => INR "HashMap evaluate type")
                | _ => INR "HashMap final value type" ))
   | _ => INR "evaluate_subscript value_to_key") ∧
  evaluate_subscript _ _ _ = INR "evaluate_subscript"
End

val () = cv_auto_trans evaluate_subscript_def;

Definition evaluate_subscripts_def:
  evaluate_subscripts a [] = INL a ∧
  evaluate_subscripts a ((IntSubscript i)::is) =
  (case a of ArrayV av =>
   (case array_index av i of SOME v =>
    (case evaluate_subscripts v is of INL vj => INL vj
     | INR err => INR err)
    | _ => INR "evaluate_subscripts array_index")
   | _ => INR "evaluate_subscripts type") ∧
  evaluate_subscripts (StructV al) ((AttrSubscript id)::is) =
  (case ALOOKUP al id of SOME v =>
    (case evaluate_subscripts v is of INL v' => INL v'
     | INR err => INR err)
   | _ => INR "evaluate_subscripts AttrSubscript") ∧
  evaluate_subscripts _ _ = INR "evaluate_subscripts"
End

val evaluate_subscripts_pre_def =
  cv_auto_trans_pre "evaluate_subscripts_pre" evaluate_subscripts_def;

Theorem evaluate_subscripts_pre[cv_pre]:
  !a b. evaluate_subscripts_pre a b
Proof
  ho_match_mp_tac evaluate_subscripts_ind
  \\ rw[Once evaluate_subscripts_pre_def]
  \\ rw[Once evaluate_subscripts_pre_def]
  \\ gvs[] \\ rw[]
  \\ qmatch_asmsub_rename_tac`0i ≤ w`
  \\ Cases_on`w` \\ gs[]
QED

(* convert *)

Definition evaluate_convert_def:
  evaluate_convert (IntV _ i) (BaseT BoolT) = INL $ BoolV (i ≠ 0) ∧
  evaluate_convert (BoolV b) (BaseT (IntT n)) =
    INL $ IntV (Signed n) (if b then 1 else 0) ∧
  evaluate_convert (BoolV b) (BaseT (UintT n)) =
    INL $ IntV (Unsigned n) (if b then 1 else 0) ∧
  evaluate_convert (BytesV _ bs) (BaseT (BytesT bd)) =
    (if compatible_bound bd (LENGTH bs)
     then INL $ BytesV bd bs
     else INR "convert BytesV bound") ∧
  evaluate_convert (BytesV _ bs) (BaseT (UintT n)) =
    (let i = w2i $ word_of_bytes T (0w:bytes32) bs in
     if within_int_bound (Unsigned n) i
     then INL $ IntV (Unsigned n) i
     else INR "convert BytesV uint bound") ∧
  evaluate_convert (BytesV _ bs) (BaseT (IntT n)) =
    (let i = w2i $ word_of_bytes T (0w:bytes32) bs in
     if within_int_bound (Signed n) i
     then INL $ IntV (Signed n) i
     else INR "convert BytesV int bound") ∧
  evaluate_convert (IntV u i) (BaseT (IntT n)) =
    (if within_int_bound (Signed n) i
     then INL $ IntV (Signed n) i
     else INR "convert int bound") ∧
  evaluate_convert (IntV u i) (BaseT (UintT n)) =
    (if within_int_bound (Unsigned n) i
     then INL $ IntV (Unsigned n) i
     else INR "convert uint bound") ∧
  evaluate_convert (IntV u i) (BaseT AddressT) =
    (if within_int_bound (Unsigned 160) i
     then INL $ AddressV (i2w i)
     else INR $ "convert int address") ∧
  evaluate_convert (FlagV _ m) (BaseT (IntT n)) =
    (let i = &m in
     if within_int_bound (Signed n) i
     then INL $ IntV (Signed n) i
     else INR "convert flag int bound") ∧
  evaluate_convert (FlagV _ m) (BaseT (UintT n)) =
    (let i = &m in
     if within_int_bound (Unsigned n) i
     then INL $ IntV (Unsigned n) i
     else INR "convert flag uint bound") ∧
  evaluate_convert (IntV u i) (BaseT (BytesT bd)) =
  (* TODO: check and use type for width etc. *)
    (if compatible_bound bd 32
     then INL $ BytesV bd (word_to_bytes ((i2w i):bytes32) T)
     else INR "convert int to bytes") ∧
  evaluate_convert (BytesV _ bs) (BaseT (StringT n)) =
    (if LENGTH bs ≤ n
     then INL $ StringV n (MAP (CHR o w2n) bs)
     else INR "convert bytes string") ∧
  evaluate_convert (StringV _ s) (BaseT (BytesT bd)) =
    (if compatible_bound bd (LENGTH s)
     then INL $ BytesV bd (MAP (n2w o ORD) s)
     else INR "convert string bytes") ∧
  evaluate_convert (IntV _ i) (BaseT DecimalT) =
    bounded_decimal_op (i * 10000000000) ∧
  evaluate_convert (DecimalV i) (BaseT (IntT n)) =
    (if within_int_bound (Signed 168) ((ABS i) / 10000000000)
     then INL $ IntV (Signed n) (i / 10000000000)
     else INR "convert decimal int") ∧
  evaluate_convert (DecimalV i) (BaseT (UintT n)) =
    (let r = i / 10000000000 in
     if 0 ≤ i ∧ within_int_bound (Signed 168) r
     then INL $ IntV (Unsigned n) r
     else INR "convert decimal uint") ∧
  evaluate_convert _ _ = INR "convert"
End

val evaluate_convert_pre_def =
  cv_auto_trans_pre "evaluate_convert_pre" $
  REWRITE_RULE [GSYM CHR_o_w2n_eq]
  evaluate_convert_def;

Theorem evaluate_convert_pre[cv_pre]:
  evaluate_convert_pre x y
Proof
  rw[evaluate_convert_pre_def]
QED

(* implicit conversion from one type to another, used e.g. for function
* calls/returns. only "safe" conversions are allowed, e.g., extending the
* maximum length of a dynamic array*)

Definition safe_cast_def:
  safe_cast t v = (
  case t of
  | BaseTV (UintT n) =>
    (case v of
     | IntV (Unsigned m) _
       => if n = m then SOME v else NONE
     | _ => NONE)
  | BaseTV (IntT n) =>
    (case v of
     | IntV (Signed m) _
       => if n = m then SOME v else NONE
     | _ => NONE)
  | BaseTV BoolT =>
    (case v of
     | BoolV _ => SOME v
     | _ => NONE)
  | BaseTV DecimalT =>
    (case v of
     | DecimalV _ => SOME v
     | _ => NONE)
  | BaseTV (StringT n) =>
    (case v of
     | StringV m str
       => if m ≤ n then SOME $ StringV n str else NONE
     | _ => NONE)
  | BaseTV (BytesT (Fixed n)) =>
    (case v of
     | BytesV (Fixed m) _ => if n = m then SOME v else NONE
     | _ => NONE)
  | BaseTV (BytesT (Dynamic n)) =>
    (case v of
     | BytesV (Dynamic m) bs =>
       if m ≤ n then SOME $ BytesV (Dynamic n) bs else NONE
     | _ => NONE)
  | BaseTV AddressT =>
    (case v of
     | BytesV (Fixed m) _ => if 20 = m then SOME v else NONE
     | _ => NONE)
  | FlagTV n =>
    (case v of
     | FlagV m _ => if n = m then SOME v else NONE
     | _ => NONE)
  | TupleTV ts =>
    (case v of
     | ArrayV (TupleV vs) =>
       (case safe_cast_list ts vs []
        of SOME vs => SOME $ ArrayV (TupleV vs)
        | _ => NONE)
     | _ => NONE)
  | ArrayTV t bd =>
    (case (bd, v) of
     | (Dynamic n, ArrayV (DynArrayV _ _ vs)) =>
       (let lvs = LENGTH vs in
        if n < lvs then NONE else
        case safe_cast_list (REPLICATE lvs t) vs []
        of SOME vs => SOME $ ArrayV (DynArrayV t n vs)
         | _ => NONE)
     | (Fixed n, ArrayV (SArrayV _ m al)) =>
       (if n ≠ m then NONE else
        case safe_cast_list (REPLICATE (LENGTH al) t) (MAP SND al) []
        of SOME vs => SOME $ ArrayV (SArrayV t n (ZIP (MAP FST al, vs)))
         | _ => NONE)
     | _ => NONE)
  | StructTV args =>
    (case v of StructV al =>
      (let names = MAP FST al in
       if names = MAP FST args then
       (case safe_cast_list (MAP SND args) (MAP SND al) []
        of SOME vs => SOME $ StructV (ZIP (names, vs))
        | _ => NONE)
       else NONE)
     | _ => NONE)
  | NoneTV =>
    (case v of NoneV => SOME v
     | _ => NONE)) ∧
  safe_cast_list [] [] acc = SOME $ REVERSE acc ∧
  safe_cast_list (t::ts) (v::vs) acc = (
    case safe_cast t v of
    | SOME v => safe_cast_list ts vs (v::acc)
    | _ => NONE) ∧
  safe_cast_list _ _ _ = NONE
Termination
  WF_REL_TAC `measure (λx. case x of
    INR (_,vs,_) => list_size value_size vs
  | INL (_,v) => value_size v)`
  \\ rw[list_size_SUM_MAP, list_size_pair_size_map]
End

val safe_cast_pre_def = cv_auto_trans_pre_rec
  "safe_cast_pre safe_cast_list_pre" safe_cast_def (
  WF_REL_TAC `measure (λx. case x of
    INR (_,vs,_) => cv_size vs
  | INL (_,v) => cv_size v)`
  \\ rw[]
  \\ Cases_on`cv_v` \\ gvs[]
  >- (
    qmatch_goalsub_rename_tac`cv_snd (cv_snd (cv_snd p))`
    \\ Cases_on`p` \\ gvs[]
    \\ qmatch_goalsub_rename_tac`cv_snd (cv_snd p)`
    \\ Cases_on`p` \\ gvs[]
    \\ qmatch_goalsub_rename_tac`cv_snd p`
    \\ Cases_on`p` \\ gvs[] )
  >- (
    qmatch_goalsub_rename_tac`cv_map_snd p`
    \\ Cases_on`g` \\ gvs[]
    \\ qid_spec_tac`m`
    \\ qid_spec_tac`p`
    \\ rpt (pop_assum kall_tac)
    \\ ho_match_mp_tac cv_map_snd_ind
    \\ rw[]
    \\ rw[Once cv_map_snd_def]
    \\ gvs[]
    \\ Cases_on`p` \\ gvs[]
    \\ qmatch_goalsub_rename_tac`cv_snd p`
    \\ Cases_on`p` \\ gvs[]
    >- (
      first_x_assum(qspec_then`m + m'`mp_tac)
      \\ rw[] )
    \\ first_x_assum(qspec_then`m + cv_size g`mp_tac)
    \\ rw[] )
  >- (
    qmatch_goalsub_rename_tac`cv_snd (cv_snd (cv_snd p))`
    \\ Cases_on`p` \\ gvs[]
    \\ qmatch_goalsub_rename_tac`cv_snd (cv_snd p)`
    \\ Cases_on`p` \\ gvs[]
    >- rw[Once cv_map_snd_def]
    \\ qmatch_goalsub_rename_tac`cv_snd p`
    \\ Cases_on`p` \\ gvs[]
    >- rw[Once cv_map_snd_def]
    \\ qmatch_goalsub_rename_tac`cv_map_snd l`
    \\ qspec_then`l`mp_tac cv_size_cv_map_snd_le
    \\ simp[])
  >- (
    qmatch_goalsub_rename_tac`cv_snd p`
    \\ Cases_on`p` \\ gvs[] )
);

Theorem safe_cast_pre[cv_pre]:
  (∀t v. safe_cast_pre t v) ∧
  (∀x y z. safe_cast_list_pre x y z)
Proof
  ho_match_mp_tac safe_cast_ind \\ rw[]
  \\ rw[Once safe_cast_pre_def]
QED

(* mutating arrays *)

Definition append_element_def:
  append_element (ArrayV (DynArrayV tv n vs)) v =
    (if compatible_bound (Dynamic n) (SUC (LENGTH vs))
     then case safe_cast tv v of NONE => INR "append cast"
          | SOME v => INL $ ArrayV $ DynArrayV tv n (SNOC v vs)
     else INR "append overflow") ∧
  append_element _ _ = INR "append_element"
End

val () = cv_auto_trans append_element_def;

Definition pop_element_def:
  pop_element (ArrayV (DynArrayV tv n vs)) =
    (if vs = [] then INR "pop empty"
     else INL $ ArrayV $ DynArrayV tv n (FRONT vs)) ∧
  pop_element _ = INR "pop_element"
End

val () = cv_auto_trans pop_element_def;

Definition insert_sarray_def:
  insert_sarray k v [] = [(k:num,v:value)] ∧
  insert_sarray k v ((k1,v1)::al) =
  if k = k1 then ((k,v)::al)
  else if k < k1 then (k,v)::(k1,v1)::al
  else (k1,v1)::(insert_sarray k v al)
End

val () = cv_trans insert_sarray_def;

Definition array_set_index_def:
  array_set_index av i v =
  if 0 ≤ i then let j = Num i in
    case av of DynArrayV tv n vs =>
      if j < LENGTH vs then
        INL $ ArrayV $ DynArrayV tv n (TAKE j vs ++ [v] ++ DROP (SUC j) vs)
      else INR "array_set_index index"
    | SArrayV tv n al =>
      if j < n then
        INL $ ArrayV $ SArrayV tv n $
        if v = default_value tv then
          ADELKEY j al
        else
          insert_sarray j v al
      else INR "array_set_index size"
    | TupleV vs => INR "array_set_index tuple"
  else INR "array_set_index negative"
End

val () = cv_auto_trans array_set_index_def;

(* mutating inside arrays, structs, hashmaps *)

Datatype:
  assign_operation
  = Replace value
  | Update binop value
  | AppendOp value
  | PopOp
End

Definition assign_subscripts_def:
  assign_subscripts a [] (Replace v) = INL v (* TODO: cast to type of a *) ∧
  assign_subscripts a [] (Update bop v) = evaluate_binop bop a v ∧
  assign_subscripts a [] (AppendOp v) = append_element a v ∧
  assign_subscripts a [] PopOp = pop_element a ∧
  assign_subscripts a ((IntSubscript i)::is) ao =
  (case a of ArrayV av =>
   (case array_index av i of SOME v =>
    (case assign_subscripts v is ao of INL vj =>
       array_set_index av i vj
     | INR err => INR err)
    | _ => INR "assign_subscripts array_index")
   | _ => INR "assign_subscripts type") ∧
  assign_subscripts (StructV al) ((AttrSubscript id)::is) ao =
  (case ALOOKUP al id of SOME v =>
    (case assign_subscripts v is ao of INL v' =>
      INL $ StructV $ AFUPDKEY id (K v') al
     | INR err => INR err)
   | _ => INR "assign_subscripts AttrSubscript") ∧
  assign_subscripts _ _ _ = INR "assign_subscripts"
End

val assign_subscripts_pre_def =
  cv_auto_trans_pre "assign_subscripts_pre" assign_subscripts_def;

Theorem assign_subscripts_pre[cv_pre]:
  !a b c. assign_subscripts_pre a b c
Proof
  ho_match_mp_tac assign_subscripts_ind
  \\ rw[Once assign_subscripts_pre_def]
  \\ rw[Once assign_subscripts_pre_def]
  \\ gvs[] \\ rw[]
  \\ qmatch_asmsub_rename_tac`0i ≤ w`
  \\ Cases_on`w` \\ gs[]
QED

Definition assign_hashmap_def:
  assign_hashmap _ _ hm [] _ = INR "assign_hashmap null" ∧
  assign_hashmap tenv vt hm (k::ks) ao =
  (case ALOOKUP hm k
   of SOME (HashMap vt hm') =>
    (case assign_hashmap tenv vt hm' ks ao of
     | INL hm' => INL $ (k, HashMap vt hm') :: (ADELKEY k hm)
     | INR err => INR err)
   | SOME (Value v) =>
    (case assign_subscripts v ks ao of
     | INL v' => INL $ (k, Value v') :: (ADELKEY k hm)
     | INR err => INR err)
   | NONE =>
     (case vt of HashMapT kt vt' =>
        (case assign_hashmap tenv vt' [] ks ao of
         | INL hm' => INL $ (k, HashMap vt' hm') :: hm
         | INR err => INR err)
      | Type t =>
        (case evaluate_type tenv t
           of NONE => INR "assign_hashmap evaluate_type"
            | SOME tv =>
         (case assign_subscripts (default_value tv) ks ao of
          | INL v => INL $ (k, Value v) :: hm
          | INR err => INR err))))
End

val assign_hashmap_pre_def = cv_auto_trans_pre "assign_hashmap_pre" assign_hashmap_def;

Theorem assign_hashmap_pre[cv_pre]:
  ∀v w x y z. assign_hashmap_pre v w x y z
Proof
  Induct_on `y` \\ rw[Once assign_hashmap_pre_def]
QED

Definition sum_map_left_def:
  sum_map_left f (INL x) = INL (f x) ∧
  sum_map_left _ (INR y) = INR y
End

Definition assign_toplevel_def:
  assign_toplevel tenv (Value a) is ao =
    sum_map_left Value $ assign_subscripts a is ao ∧
  assign_toplevel tenv (HashMap vt hm) is ao =
    sum_map_left (HashMap vt) $ assign_hashmap tenv vt hm is ao
End

val () = assign_toplevel_def
  |> SRULE [oneline sum_map_left_def]
  |> cv_auto_trans;

(* Environment and context for a contract call *)

(* external environment (tx, msg, block) *)
Datatype:
  call_txn = <|
    sender: address
  ; target: address
  ; function_name: identifier
  ; args: value list
  ; value: num
  ; time_stamp: num
  ; block_number: num
  ; block_hashes: bytes32 list
  ; blob_hashes: bytes32 list
  ; blob_base_fee: num
  ; gas_price: num
  ; is_creation: bool
  |>
End

Definition empty_call_txn_def:
  empty_call_txn = <|
    sender := 0w;
    target := 0w;
    function_name := "";
    args := [];
    value := 0;
    time_stamp := 0;
    block_number := 0;
    block_hashes := [];
    blob_hashes := [];
    blob_base_fee := 0;
    gas_price := 0;
    is_creation := F
  |>
End

(* Vyper-internal environment *)
(* sources maps address to module map, where NONE is the main contract and SOME n is module with source_id=n *)
Datatype:
  evaluation_context = <|
    stk: (num option # identifier) list
  ; txn: call_txn
  ; sources: (address, (num option, toplevel list) alist) alist
  |>
End

Theorem with_stk_updated_by_id[simp]:
  (cx with stk updated_by (λx. x)) = cx
Proof
  rw[theorem"evaluation_context_component_equality"]
QED

Definition empty_evaluation_context_def:
  empty_evaluation_context = <|
    stk := []
  ; txn := empty_call_txn
  ; sources := []
  |>
End

val () = cv_auto_trans empty_evaluation_context_def;

(* Now we can define semantics for builtins that depend on the environment *)

Definition evaluate_account_op_def:
  evaluate_account_op Address bs _ = BytesV (Fixed 20) bs ∧
  evaluate_account_op Balance _ a = IntV (Unsigned 256) &a.balance ∧
  evaluate_account_op Codehash _ a = BytesV (Fixed 32) (Keccak_256_w64 a.code) ∧
  evaluate_account_op Codesize _ a = IntV (Unsigned 256) $ &LENGTH a.code ∧
  evaluate_account_op IsContract _ a = BoolV (a.code ≠ []) ∧
  evaluate_account_op Code _ a = BytesV (Dynamic (LENGTH a.code)) a.code
End

val () = cv_auto_trans evaluate_account_op_def;

Definition evaluate_block_hash_def:
  evaluate_block_hash t n =
  let pbn = t.block_number - 1 in
  if t.block_number ≤ n ∨
     LENGTH t.block_hashes ≤ pbn - n
  then INR "evaluate_block_hash"
  else INL $ BytesV (Fixed 32)
    (word_to_bytes (EL (pbn - n) t.block_hashes) T)
End

val evaluate_block_hash_pre_def = cv_auto_trans_pre "evaluate_block_hash_pre" evaluate_block_hash_def;

Theorem evaluate_block_hash_pre[cv_pre]:
  evaluate_block_hash_pre t n
Proof
  rw[evaluate_block_hash_pre_def]
QED

Definition evaluate_blob_hash_def:
  evaluate_blob_hash t n =
    BytesV (Fixed 32) $
      word_to_bytes (if n < LENGTH t.blob_hashes
                     then EL n t.blob_hashes
                     else 0w) T
End

val () = cv_auto_trans evaluate_blob_hash_def;

(* Get code for a specific module by source_id (NONE = main contract) *)
Definition get_module_code_def:
  get_module_code cx src_id_opt =
    case ALOOKUP cx.sources cx.txn.target of
      NONE => NONE
    | SOME mods => ALOOKUP mods src_id_opt
End

val () = cv_auto_trans get_module_code_def;

(* Get main contract code (source_id = NONE) *)
Definition get_self_code_def:
  get_self_code cx = get_module_code cx NONE
End

val () = cv_auto_trans get_self_code_def;

Definition type_env_def:
  type_env [] = FEMPTY ∧
  type_env (StructDecl id args :: ts) =
    type_env ts |+ (string_to_num id, StructArgs args) ∧
  type_env (FlagDecl id ls :: ts) =
    type_env ts |+ (string_to_num id, FlagArgs (LENGTH ls)) ∧
  type_env (_ :: ts) = type_env ts
End

val () = cv_auto_trans type_env_def;

Definition evaluate_extract32_def:
  evaluate_extract32 bs n bt =
  if n < LENGTH bs then let
    bs = DROP n bs
  in case bt
     of BytesT (Fixed m) =>
          if m ≤ LENGTH bs then
            INL $ BytesV (Fixed m) (TAKE m bs)
          else INR "evaluate_extract32 bytesM"
      | UintT m =>
          evaluate_convert (BytesV (Dynamic 32) (TAKE 32 bs)) (BaseT (UintT m))
      | IntT m =>
          evaluate_convert (BytesV (Dynamic 32) (TAKE 32 bs)) (BaseT (IntT m))
      | AddressT =>
          if 20 ≤ LENGTH bs then
            INL $ BytesV (Fixed 20) (TAKE 20 bs)
          else INR "evaluate_extract32 address"
      | _ => INR "evaluate_extract32 type"
  else INR "evaluate_extract32 start"
End

val () = cv_trans evaluate_extract32_def;

Definition evaluate_type_builtin_def:
  evaluate_type_builtin cx Empty typ vs =
  (case get_self_code cx
     of SOME ts =>
        (case evaluate_type (type_env ts) typ
         of SOME tv => INL $ default_value tv
          | NONE => INR "Empty evaluate_type")
      | _ => INR "Empty get_self_code") ∧
  evaluate_type_builtin cx MaxValue typ vs =
    evaluate_max_value typ ∧
  evaluate_type_builtin cx MinValue typ vs =
    evaluate_min_value typ ∧
  evaluate_type_builtin cx Convert typ [v] =
    evaluate_convert v typ ∧
  evaluate_type_builtin cx Epsilon typ [] =
    (if typ = BaseT DecimalT then INL $ DecimalV 1
     else INR "Epsilon: not decimal") ∧
  evaluate_type_builtin cx Extract32 (BaseT bt) [BytesV _ bs; IntV u i] =
    (if u = Unsigned 256 then evaluate_extract32 bs (Num i) bt
     else INR "Extract32 type") ∧
  evaluate_type_builtin _ _ _ _ =
    INR "evaluate_type_builtin"
End

val () = cv_auto_trans evaluate_type_builtin_def;

Definition evaluate_ecrecover_def:
  evaluate_ecrecover [BytesV _ hash_bytes; IntV u1 v_int; IntV u2 r_int; IntV u3 s_int] =
    (if u1 = Unsigned 256 ∧ u2 = Unsigned 256 ∧ u3 = Unsigned 256 ∧
        LENGTH hash_bytes = 32
     then let
       hash = word_of_bytes T (0w:bytes32) hash_bytes;
       v = Num v_int;
       r = Num r_int;
       s = Num s_int
     in case vfmExecution$ecrecover hash v r s of
          NONE => INL $ AddressV 0w
        | SOME addr => INL $ AddressV addr
     else INR "ECRecover type") ∧
  evaluate_ecrecover _ = INR "ECRecover args"
End

val () = cv_auto_trans evaluate_ecrecover_def;

Definition evaluate_ecadd_def:
  evaluate_ecadd [ArrayV (TupleV [IntV u1 x1; IntV u2 y1]);
                  ArrayV (TupleV [IntV u3 x2; IntV u4 y2])] =
    (if u1 = Unsigned 256 ∧ u2 = Unsigned 256 ∧
        u3 = Unsigned 256 ∧ u4 = Unsigned 256
     then let
       p1 = (Num x1, Num y1);
       p2 = (Num x2, Num y2)
     in case vfmExecution$ecadd p1 p2 of
          NONE => INL $ ArrayV $ TupleV
            [IntV (Unsigned 256) 0; IntV (Unsigned 256) 0]
        | SOME (rx, ry) => INL $ ArrayV $ TupleV
            [IntV (Unsigned 256) (&rx); IntV (Unsigned 256) (&ry)]
     else INR "ECAdd type") ∧
  evaluate_ecadd _ = INR "ECAdd args"
End

val () = cv_auto_trans evaluate_ecadd_def;

Definition evaluate_ecmul_def:
  evaluate_ecmul [ArrayV (TupleV [IntV u1 x; IntV u2 y]); IntV u3 scalar] =
    (if u1 = Unsigned 256 ∧ u2 = Unsigned 256 ∧ u3 = Unsigned 256
     then let
       p = (Num x, Num y);
       n = Num scalar
     in case vfmExecution$ecmul p n of
          NONE => INL $ ArrayV $ TupleV
            [IntV (Unsigned 256) 0; IntV (Unsigned 256) 0]
        | SOME (rx, ry) => INL $ ArrayV $ TupleV
            [IntV (Unsigned 256) (&rx); IntV (Unsigned 256) (&ry)]
     else INR "ECMul type") ∧
  evaluate_ecmul _ = INR "ECMul args"
End

val () = cv_auto_trans evaluate_ecmul_def;

Definition evaluate_builtin_def:
  evaluate_builtin cx _ Len [BytesV _ ls] = INL (IntV (Unsigned 256) &(LENGTH ls)) ∧
  evaluate_builtin cx _ Len [StringV _ ls] = INL (IntV (Unsigned 256) &(LENGTH ls)) ∧
  evaluate_builtin cx _ Len [ArrayV av] = INL (IntV (Unsigned 256) &(array_length av)) ∧
  evaluate_builtin cx _ Not [BoolV b] = INL (BoolV (¬b)) ∧
  evaluate_builtin cx _ Not [IntV u i] =
    (if is_Unsigned u ∧ 0 ≤ i then INL (IntV u (int_not i)) else INR "signed Not") ∧
  evaluate_builtin cx _ Not [FlagV m n] = INL $ FlagV m $
    w2n $ (~((n2w n):bytes32)) && ~(~(0w:bytes32) << m) ∧
  evaluate_builtin cx _ Neg [IntV u i] = bounded_int_op u u (-i) ∧
  evaluate_builtin cx _ Neg [DecimalV i] = bounded_decimal_op (-i) ∧
  evaluate_builtin cx _ Keccak256 [BytesV _ ls] = INL $ BytesV (Fixed 32) $
    Keccak_256_w64 ls ∧
  (* TODO: reject BytesV with invalid bounds for Keccak256 *)
  (* TODO: support Keccak256 on strings *)
  evaluate_builtin cx _ (Uint2Str n) [IntV u i] =
    (if is_Unsigned u then INL $ StringV n (num_to_dec_string (Num i))
     else INR "Uint2Str") ∧
  evaluate_builtin cx _ (AsWeiValue dn) [v] = evaluate_as_wei_value dn v ∧
  evaluate_builtin cx _ AddMod [IntV u1 i1; IntV u2 i2; IntV u3 i3] =
    (if u1 = Unsigned 256 ∧ u2 = u1 ∧ u3 = u1
     then INL $ IntV u1 $ &((Num i1 + Num i2) MOD Num i3)
     else INR "AddMod type") ∧
  evaluate_builtin cx _ MulMod [IntV u1 i1; IntV u2 i2; IntV u3 i3] =
    (if u1 = Unsigned 256 ∧ u2 = u1 ∧ u3 = u1
     then INL $ IntV u1 $ &((Num i1 * Num i2) MOD Num i3)
     else INR "MulMod type") ∧
  evaluate_builtin cx _ Floor [DecimalV i] =
    INL $ IntV (Signed 256) (i / 10000000000) ∧
  evaluate_builtin cx _ Ceil [DecimalV i] =
    INL $ IntV (Signed 256) ((i + 9999999999) / 10000000000) ∧
  evaluate_builtin cx _ (Bop bop) [v1; v2] = evaluate_binop bop v1 v2 ∧
  evaluate_builtin cx _ (Env Sender) [] = INL $ AddressV cx.txn.sender ∧
  evaluate_builtin cx _ (Env SelfAddr) [] = INL $ AddressV cx.txn.target ∧
  evaluate_builtin cx _ (Env ValueSent) [] = INL $ IntV (Unsigned 256) &cx.txn.value ∧
  evaluate_builtin cx _ (Env TimeStamp) [] = INL $ IntV (Unsigned 256) &cx.txn.time_stamp ∧
  evaluate_builtin cx _ (Env BlockNumber) [] = INL $ IntV (Unsigned 256) &cx.txn.block_number ∧
  evaluate_builtin cx _ (Env BlobBaseFee) [] = INL $ IntV (Unsigned 256) &cx.txn.blob_base_fee ∧
  evaluate_builtin cx _ (Env GasPrice) [] = INL $ IntV (Unsigned 256) &cx.txn.gas_price ∧
  evaluate_builtin cx _ (Env PrevHash) [] = evaluate_block_hash cx.txn (cx.txn.block_number - 1) ∧
  evaluate_builtin cx _ BlockHash [IntV u i] =
    (if u = Unsigned 256 then evaluate_block_hash cx.txn (Num i)
     else INR "BlockHash type") ∧
  evaluate_builtin cx _ BlobHash [IntV u i] =
    (if u = Unsigned 256 then INL $ evaluate_blob_hash cx.txn (Num i)
     else INR "BlobHash type") ∧
  evaluate_builtin cx _ (Concat n) vs = evaluate_concat n vs ∧
  evaluate_builtin cx _ (Slice n) [v1; v2; v3] = evaluate_slice v1 v2 v3 n ∧
  evaluate_builtin cx _ (MakeArray to bd) vs =
    (case get_self_code cx of SOME ts =>
     (case to
      of NONE => INL $ ArrayV $ TupleV vs
       | SOME t =>
         (case evaluate_type (type_env ts) t
          of NONE => INR "MakeArray type"
           | SOME tv => INL $ ArrayV $ make_array_value tv bd vs))
     | _ => INR "MakeArray code") ∧
  evaluate_builtin cx acc (Acc aop) [BytesV _ bs] =
    (let a = lookup_account (word_of_bytes T (0w:address) bs) acc in
      INL $ evaluate_account_op aop bs a) ∧
  evaluate_builtin cx _ Isqrt [IntV u i] =
    (if is_Unsigned u ∧ 0 ≤ i then INL $ IntV u &(num_sqrt (Num i))
     else INR "Isqrt type") ∧
  evaluate_builtin cx _ ECRecover vs = evaluate_ecrecover vs ∧
  evaluate_builtin cx _ ECAdd vs = evaluate_ecadd vs ∧
  evaluate_builtin cx _ ECMul vs = evaluate_ecmul vs ∧
  evaluate_builtin _ _ _ _ = INR "builtin"
End

val evaluate_builtin_pre_def = cv_auto_trans_pre "evaluate_builtin_pre" evaluate_builtin_def;

Theorem evaluate_builtin_pre[cv_pre]:
  evaluate_builtin_pre a b c d
Proof
  rw[evaluate_builtin_pre_def]
QED

Definition type_builtin_args_length_ok_def:
  type_builtin_args_length_ok Empty n = (n = 0n) ∧
  type_builtin_args_length_ok MaxValue n = (n = 0) ∧
  type_builtin_args_length_ok MinValue n = (n = 0) ∧
  type_builtin_args_length_ok Epsilon n = (n = 0) ∧
  type_builtin_args_length_ok Extract32 n = (n = 2) ∧
  type_builtin_args_length_ok Convert n = (n = 1)
End

val () = cv_auto_trans type_builtin_args_length_ok_def;

Definition builtin_args_length_ok_def:
  builtin_args_length_ok Len n = (n = 1n) ∧
  builtin_args_length_ok Not n = (n = 1) ∧
  builtin_args_length_ok Neg n = (n = 1) ∧
  builtin_args_length_ok Keccak256 n = (n = 1) ∧
  builtin_args_length_ok (Uint2Str _) n = (n = 1) ∧
  builtin_args_length_ok (AsWeiValue _) n = (n = 1) ∧
  builtin_args_length_ok (Concat _) n = (2 ≤ n) ∧
  builtin_args_length_ok (Slice _) n = (n = 3) ∧
  builtin_args_length_ok (MakeArray _ b) n = compatible_bound b n ∧
  builtin_args_length_ok Floor n = (n = 1) ∧
  builtin_args_length_ok Ceil n = (n = 1) ∧
  builtin_args_length_ok AddMod n = (n = 3) ∧
  builtin_args_length_ok MulMod n = (n = 3) ∧
  builtin_args_length_ok (Bop _) n = (n = 2) ∧
  builtin_args_length_ok (Env _) n = (n = 0) ∧
  builtin_args_length_ok BlockHash n = (n = 1) ∧
  builtin_args_length_ok BlobHash n = (n = 1) ∧
  builtin_args_length_ok (Acc _) n = (n = 1) ∧
  builtin_args_length_ok Isqrt n = (n = 1) ∧
  builtin_args_length_ok ECRecover n = (n = 4) ∧
  builtin_args_length_ok ECAdd n = (n = 2) ∧
  builtin_args_length_ok ECMul n = (n = 2)
End

val () = cv_auto_trans builtin_args_length_ok_def;

(* Machinery for managing variables (local, top-level, mutable, immutable), and
* other stateful data during execution (e.g., EVM account states, logs)*)

(*
We don't use identifiers directly because cv compute prefers num keys
Type scope = “:identifier |-> value”;
*)
Type scope = “:num |-> value”;

(* find a variable in a list of nested scopes *)
Definition lookup_scopes_def:
  lookup_scopes id [] = NONE ∧
  lookup_scopes id ((env: scope)::rest) =
  case FLOOKUP env id of NONE =>
    lookup_scopes id rest
  | SOME v => SOME v
End

(* find the location of a variable in a list of nested scopes (as well as its
* value): this is used when assigning to that variable *)
Definition find_containing_scope_def:
  find_containing_scope id ([]:scope list) = NONE ∧
  find_containing_scope id (env::rest) =
  case FLOOKUP env id of NONE =>
    OPTION_MAP (λ(p,q). (env::p, q)) (find_containing_scope id rest)
  | SOME v => SOME ([], env, v, rest)
End

val () = cv_auto_trans find_containing_scope_def;

Type log = “:nsid # (value list)”;

(* Module-aware globals: keyed by source_id *)
(* NONE = main contract, SOME n = module with source_id n *)
Datatype:
  module_globals = <|
    mutables: num |-> toplevel_value
  ; transients: num |-> toplevel_value
  ; immutables: num |-> value
  |>
End

Definition empty_module_globals_def:
  empty_module_globals : module_globals = <|
    mutables := FEMPTY
  ; transients := FEMPTY
  ; immutables := FEMPTY
  |>
End

val () = cv_auto_trans empty_module_globals_def;

Type globals_state = “:(num option, module_globals) alist”

Definition empty_globals_def:
  empty_globals : globals_state = []
End

val () = cv_auto_trans empty_globals_def;

Datatype:
  evaluation_state = <|
    globals: (address, globals_state) alist
  ; logs: log list
  ; scopes: scope list
  ; accounts: evm_accounts
  |>
End

Definition empty_state_def:
  empty_state : evaluation_state = <|
    accounts := empty_accounts;
    globals := [];
    logs := [];
    scopes := []
  |>
End

val () = cv_trans empty_state_def;

(* state-exception monad used for the main interpreter *)

Datatype:
  exception
  = AssertException string
  | Error string
  | BreakException
  | ContinueException
  | ReturnException value
End

Type evaluation_result = “:(α + exception) # evaluation_state”

Definition return_def:
  return x s = (INL x, s) : α evaluation_result
End

val () = cv_auto_trans return_def;

Definition raise_def:
  raise e s = (INR e, s) : α evaluation_result
End

val () = cv_auto_trans raise_def;

Definition bind_def:
  bind f g (s: evaluation_state) : α evaluation_result =
  case f s of (INL x, s) => g x s | (INR e, s) => (INR e, s)
End

Definition ignore_bind_def:
  ignore_bind f g = bind f (λx. g)
End

Definition assert_def:
  assert b e s = ((if b then INL () else INR e), s) : unit evaluation_result
End

val () = cv_auto_trans assert_def;

Definition check_def:
  check b str = assert b (Error str)
End

val () = cv_auto_trans check_def;

val () = declare_monad ("vyper_evaluation",
  { bind = “bind”, unit = “return”,
    ignorebind = SOME “ignore_bind”, choice = NONE,
    fail = SOME “raise”, guard = SOME “assert”
  });
val () = enable_monad "vyper_evaluation";
val () = enable_monadsyntax();

Definition try_def:
  try f h s : α evaluation_result =
  case f s of (INR e, s) => h e s | x => x
End

Definition finally_def:
  finally f g s : α evaluation_result =
  case f s of (INL x, s) => ignore_bind g (return x) s
     | (INR e, s) => ignore_bind g (raise e) s
End

val option_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="option",Tyop="option"}));

val sum_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="sum",Tyop="sum"}));

val list_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="list",Tyop="list"}));

val prod_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="pair",Tyop="prod"}));

Definition lift_option_def:
  lift_option x str =
    case x of SOME v => return v | NONE => raise $ Error str
End

val () = lift_option_def
  |> SRULE [FUN_EQ_THM, option_CASE_rator]
  |> cv_auto_trans;

Definition lift_sum_def:
  lift_sum x =
    case x of INL v => return v | INR str => raise $ Error str
End

val () = lift_sum_def
  |> SRULE [FUN_EQ_THM, sum_CASE_rator]
  |> cv_auto_trans;

(* reading from the state *)

Definition get_current_globals_def:
  get_current_globals cx st =
    lift_option (ALOOKUP st.globals cx.txn.target) "get_current_globals" st
End

val () = get_current_globals_def
  |> SRULE [lift_option_def, option_CASE_rator]
  |> cv_auto_trans;

(* Helper: get module_globals for a source_id, or empty if not present *)
Definition get_module_globals_def:
  get_module_globals src_id_opt (gbs: globals_state) =
    case ALOOKUP gbs src_id_opt of
      NONE => empty_module_globals
    | SOME mg => mg
End

val () = cv_auto_trans get_module_globals_def;

(* Helper: update module_globals for a source_id in globals_state *)
Definition set_module_globals_def:
  set_module_globals src_id_opt (mg: module_globals) (gbs: globals_state) =
    (src_id_opt, mg) :: ADELKEY src_id_opt gbs
End

val () = cv_auto_trans set_module_globals_def;

(* Module-aware global lookup: look up variable n in module src_id_opt *)
Definition lookup_global_def:
  lookup_global cx src_id_opt n = do
    gbs <- get_current_globals cx;
    let mg = get_module_globals src_id_opt gbs in
    case FLOOKUP mg.mutables n of
      NONE => raise $ Error "lookup_global: no var"
    | SOME v => return v
  od
End

val () = lookup_global_def
  |> SRULE [bind_def, FUN_EQ_THM, option_CASE_rator, UNCURRY, LET_THM]
  |> cv_auto_trans;

(* Module-aware immutables lookup *)
Definition get_immutables_module_def:
  get_immutables_module cx src_id_opt = do
    gbs <- get_current_globals cx;
    let mg = get_module_globals src_id_opt gbs in
    return mg.immutables
  od
End

val () = get_immutables_module_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM]
  |> cv_auto_trans;

Definition get_immutables_def:
  get_immutables cx = get_immutables_module cx NONE
End

val () = cv_auto_trans get_immutables_def;

(* Pure helpers for updating module globals in a globals_state *)
Definition update_module_mutable_def:
  update_module_mutable src_id key v (gbs: globals_state) =
    let mg = get_module_globals src_id gbs in
    let mg' = mg with mutables updated_by (λm. m |+ (key, v)) in
    set_module_globals src_id mg' gbs
End

val () = cv_auto_trans update_module_mutable_def;

Definition update_module_transient_def:
  update_module_transient src_id key v (gbs: globals_state) =
    let mg = get_module_globals src_id gbs in
    let mg' = mg with <|
      mutables updated_by (λm. m |+ (key, v))
    ; transients updated_by (λt. t |+ (key, v))
    |> in
    set_module_globals src_id mg' gbs
End

val () = cv_auto_trans update_module_transient_def;

Definition update_module_immutable_def:
  update_module_immutable src_id key v (gbs: globals_state) =
    let mg = get_module_globals src_id gbs in
    let mg' = mg with immutables updated_by (λm. m |+ (key, v)) in
    set_module_globals src_id mg' gbs
End

val () = cv_auto_trans update_module_immutable_def;

Definition get_accounts_def:
  get_accounts st = return st.accounts st
End

val () = cv_auto_trans get_accounts_def;

Definition get_scopes_def:
  get_scopes st = return st.scopes st
End

val () = cv_auto_trans get_scopes_def;

Definition lookup_flag_def:
  lookup_flag fid [] = NONE ∧
  lookup_flag fid (FlagDecl id ls :: ts) =
    (if fid = id then SOME ls else lookup_flag fid ts) ∧
  lookup_flag fid (t :: ts) = lookup_flag fid ts
End

val () = cv_auto_trans lookup_flag_def;

Definition lookup_flag_mem_def:
  lookup_flag_mem cx (src_id_opt, fid) mid =
  case get_module_code cx src_id_opt
    of NONE => raise $ Error "lookup_flag_mem code"
     | SOME ts =>
  case lookup_flag fid ts
    of NONE => raise $ Error "lookup_flag"
     | SOME ls =>
  case INDEX_OF mid ls
    of NONE => raise $ Error "lookup_flag_mem index"
     | SOME i => return $ Value $ FlagV (LENGTH ls) (2 ** i)
End

val () = lookup_flag_mem_def
  |> SRULE [FUN_EQ_THM, option_CASE_rator]
  |> cv_auto_trans;

(* writing to the state *)

Definition set_current_globals_def:
  set_current_globals cx gbs st =
  let addr = cx.txn.target in
    return () $ st with globals updated_by
      (λal. (addr, gbs) :: (ADELKEY addr al))
End

val () = cv_auto_trans set_current_globals_def;

(* Module-aware global set *)
Definition set_global_def:
  set_global cx src_id_opt n v = do
    gbs <- get_current_globals cx;
    let mg = get_module_globals src_id_opt gbs in
    let mg' = mg with mutables updated_by (λm. m |+ (n, v)) in
    set_current_globals cx $ set_module_globals src_id_opt mg' gbs
  od
End

val () = set_global_def
  |> SRULE [bind_def, FUN_EQ_THM, UNCURRY, LET_THM]
  |> cv_auto_trans;

Definition set_immutable_def:
  set_immutable cx src_id_opt n v = do
    gbs <- get_current_globals cx;
    let mg = get_module_globals src_id_opt gbs in
    let mg' = mg with immutables updated_by (λm. m |+ (n, v)) in
    set_current_globals cx $ set_module_globals src_id_opt mg' gbs
  od
End

val () = set_immutable_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM]
  |> cv_auto_trans;

Definition update_accounts_def:
  update_accounts f st = return () (st with accounts updated_by f)
End

Definition set_scopes_def:
  set_scopes env st = return () $ st with scopes := env
End

val () = cv_auto_trans set_scopes_def;

Definition push_scope_def:
  push_scope st = return () $ st with scopes updated_by CONS FEMPTY
End

val () = cv_auto_trans push_scope_def;

Definition push_scope_with_var_def:
  push_scope_with_var nm v st =
    return () $  st with scopes updated_by CONS (FEMPTY |+ (nm, v))
End

val () = cv_auto_trans push_scope_with_var_def;

Definition pop_scope_def:
  pop_scope st =
    case st.scopes
    of [] => raise (Error "pop_scope") st
       | _::tl => return () (st with scopes := tl)
End

val () = cv_auto_trans pop_scope_def;

(* writing variables *)

Definition new_variable_def:
  new_variable id v = do
    n <<- string_to_num id;
    env <- get_scopes;
    check (IS_NONE (lookup_scopes n env)) "new_variable bound";
    case env of [] => raise $ Error "new_variable null"
    | e::es => set_scopes ((e |+ (n, v))::es)
  od
End

val () = new_variable_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def,
            LET_RATOR, list_CASE_rator]
  |> cv_auto_trans;

Definition set_variable_def:
  set_variable id v = do
    n <<- string_to_num id;
    sc <- get_scopes;
    (pre, env, _, rest) <-
      lift_option (find_containing_scope n sc) "set_variable not found";
    set_scopes (pre ++ (env |+ (n, v))::rest)
  od
End

val () = set_variable_def
  |> SRULE [FUN_EQ_THM, bind_def, lift_option_def,
            LET_RATOR, UNCURRY, option_CASE_rator]
  |> cv_auto_trans;

(* assignment to existing locations *)

Definition get_Value_def[simp]:
  get_Value (Value v) = return v ∧
  get_Value _ = raise $ Error "not Value"
End

val () = get_Value_def
  |> SIMP_RULE std_ss [FUN_EQ_THM]
  |> cv_auto_trans;

Datatype:
  location
  = ScopedVar identifier
  | ImmutableVar identifier
  | TopLevelVar (num option) identifier  (* source_id (NONE=self), var_name *)
End

Datatype:
  assignment_value
  = BaseTargetV location (subscript list)
  | TupleTargetV (assignment_value list)
End

Type base_target_value = “:location # subscript list”;

Definition assign_target_def:
  assign_target cx (BaseTargetV (ScopedVar id) is) ao = do
    ni <<- string_to_num id;
    sc <- get_scopes;
    (pre, env, a, rest) <- lift_option (find_containing_scope ni sc) "assign_target lookup";
    a' <- lift_sum $ assign_subscripts a (REVERSE is) ao;
    set_scopes $ pre ++ env |+ (ni, a') :: rest;
    return $ Value a
  od ∧
  assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) is) ao = do
    ni <<- string_to_num id;
    tv <- lookup_global cx src_id_opt ni;
    ts <- lift_option (get_module_code cx src_id_opt) "assign_target get_module_code";
    tv' <- lift_sum $ assign_toplevel (type_env ts) tv (REVERSE is) ao;
    set_global cx src_id_opt ni tv';
    return tv
  od ∧
  assign_target cx (BaseTargetV (ImmutableVar id) is) ao = do
    ni <<- string_to_num id;
    imms <- get_immutables cx;
    a <- lift_option (FLOOKUP imms ni) "assign_target ImmutableVar";
    a' <- lift_sum $ assign_subscripts a (REVERSE is) ao;
    set_immutable cx NONE ni a';
    return $ Value a
  od ∧
  assign_target cx (TupleTargetV gvs) (Replace (ArrayV (TupleV vs))) = do
    check (LENGTH gvs = LENGTH vs) "TupleTargetV length";
    ws <- assign_targets cx gvs vs;
    return $ Value $ ArrayV (TupleV ws)
  od ∧
  assign_target _ _ _ = raise (Error "assign_target") ∧
  assign_targets cx [] [] = return [] ∧
  assign_targets cx (gv::gvs) (v::vs) = do
    tw <- assign_target cx gv (Replace v);
    w <- get_Value tw;
    ws <- assign_targets cx gvs vs;
    return $ w::ws
  od ∧
  assign_targets _ _ _ = raise (Error "assign_targets")
End

val assign_target_pre_def = assign_target_def
  |> SRULE [FUN_EQ_THM, bind_def, LET_RATOR, ignore_bind_def,
            UNCURRY, option_CASE_rator, lift_option_def]
  |> cv_auto_trans_pre "assign_target_pre assign_targets_pre";

Theorem assign_target_pre[cv_pre]:
  (∀w x y z. assign_target_pre w x y z) ∧
  (∀w x y z. assign_targets_pre w x y z)
Proof
  ho_match_mp_tac assign_target_ind \\ rw[]
  \\ rw[Once assign_target_pre_def]
QED

(* writing logs *)

Definition push_log_def:
  push_log log st = return () $ st with logs updated_by CONS log
End

val () = cv_auto_trans push_log_def;

(* manipulating (internal call) function stack *)

Definition push_function_def:
  push_function src_fn sc cx st =
  return (cx with stk updated_by CONS src_fn)
    $ st with scopes := [sc]
End

val () = cv_auto_trans push_function_def;

Definition pop_function_def:
  pop_function prev = set_scopes prev
End

val () = cv_auto_trans pop_function_def;

(* helper for sending ether between accounts *)

Definition transfer_value_def:
  transfer_value fromAddr toAddr amount = do
    acc <- get_accounts;
    sender <<- lookup_account fromAddr acc;
    check (amount <= sender.balance) "transfer_value amount";
    recipient <<- lookup_account toAddr acc;
    update_accounts (
      update_account fromAddr (sender with balance updated_by (flip $- amount)) o
      update_account toAddr (recipient with balance updated_by ($+ amount)));
  od
End

val () = transfer_value_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def,
            LET_RATOR, update_accounts_def, o_DEF, C_DEF]
  |> cv_auto_trans;

(* machinery for calls to functions in a Vyper contract, and for internal calls
* within a contract, including implicit functions associated with public
* variables *)

Definition build_getter_def:
  build_getter e kt (Type vt) n =
    (let vn = num_to_dec_string n in
      if is_ArrayT vt then
        (let (args, ret, exp) =
           build_getter (Subscript e (Name vn))
             (BaseT (UintT 256)) (Type (ArrayT_type vt)) (SUC n) in
           ((vn, kt)::args, ret, exp))
      else ([(vn, kt)], vt, Subscript e (Name vn))) ∧
  build_getter e kt (HashMapT typ vtyp) n =
    (let vn = num_to_dec_string n in
     let (args, ret, exp) =
       build_getter (Subscript e (Name vn)) typ vtyp (SUC n) in
     ((vn, kt)::args, ret, exp))
Termination
  WF_REL_TAC ‘measure (value_type_size o FST o SND o SND)’
  \\ Cases \\ rw[type_size_def]
End

val () = cv_auto_trans_rec build_getter_def (
  WF_REL_TAC ‘measure (cv_size o FST o SND o SND)’
  \\ conj_tac \\ Cases \\ rw[]
  >- (
    qmatch_goalsub_rename_tac`cv_snd p`
    \\ Cases_on`p` \\ rw[] )
  \\ qmatch_asmsub_rename_tac`cv_is_ArrayT a`
  \\ Cases_on `a` \\ gvs[cv_is_ArrayT_def, cv_ArrayT_type_def]
  \\ rw[] \\ gvs[]
  \\ qmatch_goalsub_rename_tac`cv_fst p`
  \\ Cases_on `p` \\ gvs[]
);

Definition getter_def:
  getter ne kt vt =
  let (args, ret, exp) =
    build_getter ne kt vt 0
  in
    (View, args, ret, [Return $ SOME exp])
End

val () = cv_auto_trans getter_def;

Definition name_expression_def:
  name_expression mut id =
  if mut = Immutable ∨ is_Constant mut
  then Name id
  else TopLevelName (NONE, id)
End

val () = cv_auto_trans name_expression_def;

Definition lookup_function_def:
  lookup_function name Deploy [] = SOME (Payable, [], NoneT, [Pass]) ∧
  lookup_function name vis [] = NONE ∧
  lookup_function name vis (FunctionDecl fv fm id args ret body :: ts) =
  (if id = name ∧ vis = fv then SOME (fm, args, ret, body)
   else lookup_function name vis ts) ∧
  lookup_function name External (VariableDecl Public mut id typ :: ts) =
  (if id = name then
    if ¬is_ArrayT typ
    then SOME (View, [], typ, [Return (SOME (name_expression mut id))])
    else SOME $ getter (name_expression mut id) (BaseT (UintT 256)) (Type (ArrayT_type typ))
   else lookup_function name External ts) ∧
  lookup_function name External (HashMapDecl Public _ id kt vt :: ts) =
  (if id = name then SOME $ getter (TopLevelName (NONE, id)) kt vt
   else lookup_function name External ts) ∧
  lookup_function name vis (_ :: ts) =
    lookup_function name vis ts
End

val () = cv_auto_trans lookup_function_def;

Definition bind_arguments_def:
  bind_arguments tenv ([]: argument list) [] = SOME (FEMPTY: scope) ∧
  bind_arguments tenv ((id, typ)::params) (v::vs) =
    (case evaluate_type tenv typ of NONE => NONE | SOME tv =>
     case safe_cast tv v of NONE => NONE | SOME v =>
      OPTION_MAP (λm. m |+ (string_to_num id, v))
        (bind_arguments tenv params vs)) ∧
  bind_arguments _ _ _ = NONE
End

val bind_arguments_pre_def = cv_auto_trans_pre "bind_arguments_pre" bind_arguments_def;

Theorem bind_arguments_pre[cv_pre]:
  ∀x y z. bind_arguments_pre x y z
Proof
  ho_match_mp_tac bind_arguments_ind \\ rw[]
  \\ rw[Once bind_arguments_pre_def]
QED

Definition handle_function_def:
  handle_function (ReturnException v) = return v ∧
  handle_function (Error str) = raise $ Error str ∧
  handle_function (AssertException str) = raise $ AssertException str ∧
  handle_function _ = raise $ Error "handle_function"
End

val () = handle_function_def
  |> SRULE [FUN_EQ_THM]
  |> cv_auto_trans;

(* helpers for the termination argument for the main interpreter definition
* (evaulate_def below) *)

Theorem expr1_size_map:
  expr1_size ls = LENGTH ls + SUM (MAP expr2_size ls)
Proof
  Induct_on`ls` \\ rw[expr_size_def]
QED

Theorem expr2_size_map:
  expr2_size x = 1 + list_size char_size (FST x) + expr_size (SND x)
Proof
  Cases_on`x` \\ rw[expr_size_def]
QED

Theorem SUM_MAP_expr2_size:
  SUM (MAP expr2_size ls) =
  LENGTH ls +
  SUM (MAP (list_size char_size o FST) ls) +
  SUM (MAP (expr_size o SND) ls)
Proof
  Induct_on`ls` \\ rw[expr2_size_map]
QED

(* recursion bound for the termination measure *)
Definition bound_def:
  stmt_bound ts Pass = 0n ∧
  stmt_bound ts Continue = 0 ∧
  stmt_bound ts Break = 0 ∧
  stmt_bound ts (Return NONE) = 0 ∧
  stmt_bound ts (Return (SOME e)) =
    1 + expr_bound ts e ∧
  stmt_bound ts (Raise e) =
    1 + expr_bound ts e ∧
  stmt_bound ts (Assert e1 e2) =
    1 + expr_bound ts e1
      + expr_bound ts e2 ∧
  stmt_bound ts (Log _ es) =
    1 + exprs_bound ts es ∧
  stmt_bound ts (AnnAssign _ _ e) =
    1 + expr_bound ts e ∧
  stmt_bound ts (Append bt e) =
    1 + base_target_bound ts bt
      + expr_bound ts e ∧
  stmt_bound ts (Assign g e) =
    1 + target_bound ts g
      + expr_bound ts e ∧
  stmt_bound ts (AugAssign bt _ e) =
    1 + base_target_bound ts bt
      + expr_bound ts e ∧
  stmt_bound ts (If e ss1 ss2) =
    1 + expr_bound ts e +
     MAX (stmts_bound ts ss1)
         (stmts_bound ts ss2) ∧
  stmt_bound ts (For _ _ it n ss) =
    1 + iterator_bound ts it +
    1 + n + n * (stmts_bound ts ss) ∧
  stmt_bound ts (Expr e) =
    1 + expr_bound ts e ∧
  stmts_bound ts [] = 0 ∧
  stmts_bound ts (s::ss) =
    1 + stmt_bound ts s
      + stmts_bound ts ss ∧
  iterator_bound ts (Array e) =
    1 + expr_bound ts e ∧
  iterator_bound ts (Range e1 e2) =
    1 + expr_bound ts e1
      + expr_bound ts e2 ∧
  target_bound ts (BaseTarget bt) =
    1 + base_target_bound ts bt ∧
  target_bound ts (TupleTarget gs) =
    1 + targets_bound ts gs ∧
  targets_bound ts [] = 0 ∧
  targets_bound ts (g::gs) =
    1 + target_bound ts g
      + targets_bound ts gs ∧
  base_target_bound ts (NameTarget _) = 0 ∧
  base_target_bound ts (TopLevelNameTarget _) = 0 ∧
  base_target_bound ts (AttributeTarget bt _) =
    1 + base_target_bound ts bt ∧
  base_target_bound ts (SubscriptTarget bt e) =
    1 + base_target_bound ts bt
      + expr_bound ts e ∧
  expr_bound ts (Name _) = 0 ∧
  expr_bound ts (TopLevelName _) = 0 ∧
  expr_bound ts (FlagMember _ _) = 0 ∧
  expr_bound ts (IfExp e1 e2 e3) =
    1 + expr_bound ts e1
      + MAX (expr_bound ts e2)
            (expr_bound ts e3) ∧
  expr_bound ts (Subscript e1 e2) =
    1 + expr_bound ts e1
      + expr_bound ts e2 ∧
  expr_bound ts (Attribute e _) =
    1 + expr_bound ts e ∧
  expr_bound ts (Literal _) = 0 ∧
  expr_bound ts (StructLit _ kes) =
    1 + exprs_bound ts (MAP SND kes) ∧
  expr_bound ts (Builtin _ es) =
    1 + exprs_bound ts es ∧
  expr_bound ts (Pop bt) =
    1 + base_target_bound ts bt ∧
  expr_bound ts (TypeBuiltin _ _ es) =
    1 + exprs_bound ts es ∧
  expr_bound ts (Call (IntCall src_id_opt fn) es) =
    1 + exprs_bound ts es
      + (case ALOOKUP ts (src_id_opt, fn) of NONE => 0 |
         SOME ss => stmts_bound (ADELKEY (src_id_opt, fn) ts) ss) ∧
  expr_bound ts (Call t es) =
    1 + exprs_bound ts es ∧
  exprs_bound ts [] = 0 ∧
  exprs_bound ts (e::es) =
    1 + expr_bound ts e
      + exprs_bound ts es
Termination
  WF_REL_TAC ‘measure (λx. case x of
  | INR (INR (INR (INR (INR (INR (INR (ts, es))))))) =>
      SUM (MAP (list_size stmt_size o SND) ts) +
      list_size expr_size es
  | INR (INR (INR (INR (INR (INR (INL (ts, e))))))) =>
      SUM (MAP (list_size stmt_size o SND) ts) +
      expr_size e
  | INR (INR (INR (INR (INR (INL (ts, bt)))))) =>
      SUM (MAP (list_size stmt_size o SND) ts) +
      base_assignment_target_size bt
  | INR (INR (INR (INR (INL (ts, gs))))) =>
      SUM (MAP (list_size stmt_size o SND) ts) +
      list_size assignment_target_size gs
  | INR (INR (INR (INL (ts, g)))) =>
      SUM (MAP (list_size stmt_size o SND) ts) +
      assignment_target_size g
  | INR (INR (INL (ts, it))) =>
      SUM (MAP (list_size stmt_size o SND) ts) +
      iterator_size it
  | INR (INL (ts, ss)) =>
      SUM (MAP (list_size stmt_size o SND) ts) +
      list_size stmt_size ss
  | INL (ts, s) =>
      SUM (MAP (list_size stmt_size o SND) ts) +
      stmt_size s)’
  \\ rw[expr1_size_map, expr2_size_map, SUM_MAP_expr2_size,
        MAP_MAP_o, list_size_pair_size_map]
  \\ drule ALOOKUP_MEM
  \\ rw[ADELKEY_def]
  \\ qmatch_goalsub_abbrev_tac`MAP f (FILTER P ts)`
  \\ drule_then(qspecl_then[`f`,`P`]mp_tac) SUM_MAP_FILTER_MEM_LE
  \\ simp[Abbr`P`, Abbr`f`]
End

Definition dest_Internal_FunctionDef_def:
  dest_Internal_FunctionDef (FunctionDecl Internal _ fn _ _ ss) = [(fn, ss)] ∧
  dest_Internal_FunctionDef _ = []
End

(* For a single module, get its internal function definitions tagged with source_id *)
Definition module_fns_def:
  module_fns src_id ts =
    MAP (λ(fn, ss). ((src_id, fn), ss)) (FLAT (MAP dest_Internal_FunctionDef ts))
End

(* Get all function definitions from all modules, keyed by (source_id, function_name) *)
Definition remcode_def:
  remcode cx =
  case ALOOKUP cx.sources cx.txn.target of
    NONE => []
  | SOME mods =>
      FILTER (λ((src_id, fn), ss). ¬MEM (src_id, fn) cx.stk)
        (FLAT (MAP (λ(src_id, ts). module_fns src_id ts) mods))
End

(* these helpers are also for termination, to enable HOL4's definition machinery
* to "see through" the state-exception monad when constructing the termination
* conditions *)

Theorem bind_cong_implicit[defncong]:
  (f = f') ∧
  (∀s x t. f' s = (INL x, t) ==> g x t = g' x t)
  ⇒
  bind f g = bind f' g'
Proof
  rw[bind_def, FUN_EQ_THM] \\ CASE_TAC \\ CASE_TAC \\ gs[]
  \\ first_x_assum irule \\ goal_assum drule
QED

Theorem ignore_bind_cong_implicit[defncong]:
  (f = f') ∧
  (∀s x t. f' s = (INL x, t) ⇒ g t = g' t)
  ⇒
  ignore_bind f g = ignore_bind f' g'
Proof
  rw[ignore_bind_def]
  \\ irule bind_cong_implicit
  \\ rw[]
  \\ first_x_assum irule
  \\ goal_assum drule
QED

Theorem try_cong[defncong]:
  (f s = f' s') ∧
  (∀e t. f' s = (INR e, t) ⇒ h e t = h' e t) ∧
  (s = s')
  ⇒
  try f h s = try f' h' s'
Proof
  rw[try_def] \\ CASE_TAC \\ CASE_TAC \\ gs[]
QED

Theorem try_cong_implicit[defncong]:
  (f = f') ∧
  (∀s e t. f' s = (INR e, t) ⇒ h e t = h' e t)
  ⇒
  try f h = try f' h'
Proof
  rw[FUN_EQ_THM]
  \\ irule try_cong \\ rw[]
  \\ first_x_assum irule
  \\ metis_tac[]
QED

Theorem bind_cong[defncong]:
  (f s = f' s') ∧
  (∀x t. f' s = (INL x, t) ==> g x t = g' x t) ∧
  (s = s')
  ⇒
  bind f g s = bind f' g' s'
Proof
  rw[bind_def] \\ CASE_TAC \\ CASE_TAC \\ gs[]
QED

Theorem ignore_bind_cong[defncong]:
  (f s = f' s') ∧
  (∀x t. f' s = (INL x, t) ⇒ g t = g' t) ∧
  (s = s')
  ⇒
  ignore_bind f g s = ignore_bind f' g' s'
Proof
  rw[ignore_bind_def]
  \\ irule bind_cong
  \\ rw[]
QED

Theorem finally_cong[defncong]:
  (f s = f' s') ∧
  (∀x t. f' s = (x, t) ⇒ g t = g' t) ∧
  (s = s')
  ⇒
  finally f g s = finally f' g' s'
Proof
  rw[finally_def]
  \\ CASE_TAC \\ CASE_TAC
  \\ irule ignore_bind_cong \\ gs[]
QED

Theorem lookup_function_Internal_imp_ALOOKUP_FLAT:
  ∀fn vis ts v x y z. vis = Internal ∧
  lookup_function fn vis ts = SOME (v,x,y,z) ⇒
  ALOOKUP (FLAT (MAP dest_Internal_FunctionDef ts)) fn = SOME z
Proof
  ho_match_mp_tac lookup_function_ind
  \\ rw[lookup_function_def, dest_Internal_FunctionDef_def]
  \\ Cases_on`fv` \\ gvs[dest_Internal_FunctionDef_def]
QED

(* New lemma for module support: connect lookup_function to module_fns *)
Theorem lookup_function_Internal_imp_ALOOKUP_module_fns:
  ∀fn vis ts (src_id : num option) v x y z. vis = Internal ∧
  lookup_function fn vis ts = SOME (v,x,y,z) ⇒
  ALOOKUP (module_fns src_id ts) (src_id, fn) = SOME z
Proof
  ho_match_mp_tac lookup_function_ind
  \\ rw[lookup_function_def, dest_Internal_FunctionDef_def, module_fns_def]
  \\ Cases_on`fv` \\ gvs[dest_Internal_FunctionDef_def, module_fns_def]
QED

(* Helper: ALOOKUP in module_fns is NONE when src_id doesn't match *)
Theorem ALOOKUP_module_fns_diff_src:
  ∀ts sid1 sid2 fn.
    sid1 ≠ sid2 ⇒ ALOOKUP (module_fns sid1 ts) (sid2, fn) = NONE
Proof
  rw[module_fns_def, ALOOKUP_FAILS, MEM_MAP, PULL_EXISTS, FORALL_PROD]
QED

(* Helper for ALOOKUP in FLAT of MAPs *)
Theorem ALOOKUP_FLAT_MAP_module_fns:
  ∀mods src_id ts fn body.
    ALOOKUP mods src_id = SOME ts ∧
    ALOOKUP (module_fns src_id ts) (src_id, fn) = SOME body ⇒
    ALOOKUP (FLAT (MAP (λ(sid, tl). module_fns sid tl) mods)) (src_id, fn) = SOME body
Proof
  Induct \\ rw[]
  \\ simp[ALOOKUP_APPEND]
  \\ PairCases_on`h`
  \\ gvs[ALOOKUP_module_fns_diff_src, AllCaseEqs()]
QED

(* a few more helper functions used in the main interpreter *)

Definition handle_loop_exception_def:
  handle_loop_exception e =
  if e = ContinueException then return F
  else if e = BreakException then return T
  else raise e
End

val () = handle_loop_exception_def
  |> SRULE [FUN_EQ_THM, COND_RATOR]
  |> cv_auto_trans;

Definition switch_BoolV_def:
  switch_BoolV v f g =
  if v = Value $ BoolV T then f
  else if v = Value $ BoolV F then g
  else raise $ Error (if is_Value v then "not BoolV" else "not Value")
End

Definition exactly_one_option_def:
  exactly_one_option NONE NONE = INR "no option" ∧
  exactly_one_option (SOME _) (SOME _) = INR "two options" ∧
  exactly_one_option (SOME x) _ = INL x ∧
  exactly_one_option _ (SOME y) = INL y
End

val () = cv_auto_trans exactly_one_option_def;

Definition immutable_target_def:
  immutable_target (imms: num |-> value) id n =
  case FLOOKUP imms n of SOME _ => SOME $ ImmutableVar id
     | _ => NONE
End

val () = cv_auto_trans immutable_target_def;

Definition get_range_limits_def:
  get_range_limits (IntV u1 n1) (IntV u2 n2) =
  (if u1 = u2 then
     if n1 ≤ n2
     then INL (u1, n1, Num (n2 - n1))
     else INR "no range"
   else INR "range type") ∧
  get_range_limits _ _ = INR "range not IntV"
End

val () = cv_auto_trans get_range_limits_def;

(* top-level definition of the Vyper interpreter *)

Definition evaluate_def:
  eval_stmt cx Pass = return () ∧
  eval_stmt cx Continue = raise ContinueException ∧
  eval_stmt cx Break = raise BreakException ∧
  eval_stmt cx (Return NONE) = raise $ ReturnException NoneV ∧
  eval_stmt cx (Return (SOME e)) = do
    tv <- eval_expr cx e;
    v <- get_Value tv;
    raise $ ReturnException v
  od ∧
  eval_stmt cx (Raise e) = do
    tv <- eval_expr cx e;
    v <- get_Value tv;
    s <- lift_option (dest_StringV v) "not StringV";
    raise $ AssertException s
  od ∧
  eval_stmt cx (Assert e se) = do
    tv <- eval_expr cx e;
    switch_BoolV tv
      (return ())
      (do
         stv <- eval_expr cx se;
         sv <- get_Value stv;
         s <- lift_option (dest_StringV sv) "not StringV";
         raise $ AssertException s
       od)
  od ∧
  eval_stmt cx (Log id es) = do
    (* TODO: check arguments length and types *)
    vs <- eval_exprs cx es;
    push_log (id, vs)
  od ∧
  eval_stmt cx (AnnAssign id typ e) = do
    tv <- eval_expr cx e;
    v <- get_Value tv;
    (* TODO: check type *)
    new_variable id v
  od ∧
  eval_stmt cx (Append t e) = do
    (loc, sbs) <- eval_base_target cx t;
    tv <- eval_expr cx e;
    v <- get_Value tv;
    assign_target cx (BaseTargetV loc sbs) (AppendOp v);
    return ()
  od ∧
  eval_stmt cx (Assign g e) = do
    gv <- eval_target cx g;
    tv <- eval_expr cx e;
    v <- get_Value tv;
    assign_target cx gv (Replace v);
    return ()
  od ∧
  eval_stmt cx (AugAssign t bop e) = do
    (loc, sbs) <- eval_base_target cx t;
    tv <- eval_expr cx e;
    v <- get_Value tv;
    assign_target cx (BaseTargetV loc sbs) (Update bop v);
    return ()
  od ∧
  eval_stmt cx (If e ss1 ss2) = do
    tv <- eval_expr cx e;
    push_scope;
    finally (
      switch_BoolV tv
        (eval_stmts cx ss1)
        (eval_stmts cx ss2)
    ) pop_scope
  od ∧
  eval_stmt cx (For id typ it n body) = do
    (* TODO: check and cast to the type *)
    vs <- eval_iterator cx it;
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long";
    (* TODO: check id is not in scope already? *)
    eval_for cx (string_to_num id) body vs
  od ∧
  eval_stmt cx (Expr e) = do
    tv <- eval_expr cx e;
    get_Value tv;
    return ()
  od ∧
  eval_stmts cx [] = return () ∧
  eval_stmts cx (s::ss) = do
    eval_stmt cx s; eval_stmts cx ss
  od ∧
  eval_iterator cx (Array e) = do
    tv <- eval_expr cx e;
    v <- get_Value tv;
    vs <- lift_option (extract_elements v) "For not ArrayV";
    return vs
  od ∧
  eval_iterator cx (Range e1 e2) = do
    tv1 <- eval_expr cx e1;
    v1 <- get_Value tv1;
    tv2 <- eval_expr cx e2;
    v2 <- get_Value tv2;
    rl <- lift_sum $ get_range_limits v1 v2;
    u <<- FST rl; ns <<- SND rl; n1 <<- FST ns; n2 <<- SND ns;
    return $ GENLIST (λn. IntV u (n1 + &n)) n2
  od ∧
  eval_target cx (BaseTarget t) = do
    (loc, sbs) <- eval_base_target cx t;
    return $ BaseTargetV loc sbs
  od ∧
  eval_target cx (TupleTarget gs) = do
    gvs <- eval_targets cx gs;
    return $ TupleTargetV gvs
  od ∧
  eval_targets cx [] = return [] ∧
  eval_targets cx (g::gs) = do
    gv <- eval_target cx g;
    gvs <- eval_targets cx gs;
    return $ gv::gvs
  od ∧
  eval_base_target cx (NameTarget id) = do
    sc <- get_scopes;
    n <<- string_to_num id;
    svo <<- if IS_SOME (lookup_scopes n sc)
            then SOME $ ScopedVar id
	    else NONE;
    ivo <- if cx.txn.is_creation
           then do imms <- get_immutables cx;
                   return $ immutable_target imms id n
                od
           else return NONE;
    v <- lift_sum $ exactly_one_option svo ivo;
    return $ (v, [])
  od ∧
  eval_base_target cx (TopLevelNameTarget (src_id_opt, id)) =
    return $ (TopLevelVar src_id_opt id, []) ∧
  eval_base_target cx (AttributeTarget t id) = do
    (loc, sbs) <- eval_base_target cx t;
    return $ (loc, AttrSubscript id :: sbs)
  od ∧
  eval_base_target cx (SubscriptTarget t e) = do
    (loc, sbs) <- eval_base_target cx t;
    tv <- eval_expr cx e;
    v <- get_Value tv;
    k <- lift_option (value_to_key v) "SubscriptTarget value_to_key";
    return $ (loc, k :: sbs)
  od ∧
  eval_for cx nm body [] = return () ∧
  eval_for cx nm body (v::vs) = do
    push_scope_with_var nm v;
    broke <- finally
      (try (do eval_stmts cx body; return F od) handle_loop_exception)
      pop_scope ;
    if broke then return () else eval_for cx nm body vs
  od ∧
  eval_expr cx (Name id) = do
    env <- get_scopes;
    imms <- get_immutables cx;
    n <<- string_to_num id;
    v <- lift_sum $ exactly_one_option
           (lookup_scopes n env) (FLOOKUP imms n);
    return $ Value v
  od ∧
  eval_expr cx (TopLevelName (src_id_opt, id)) =
    lookup_global cx src_id_opt (string_to_num id) ∧
  eval_expr cx (FlagMember nsid mid) = lookup_flag_mem cx nsid mid ∧
  eval_expr cx (IfExp e1 e2 e3) = do
    tv <- eval_expr cx e1;
    switch_BoolV tv
      (eval_expr cx e2)
      (eval_expr cx e3)
  od ∧
  eval_expr cx (Literal l) = return $ Value $ evaluate_literal l ∧
  eval_expr cx (StructLit (src_id_opt, id) kes) = do
    (* TODO: type checking - validate fields against struct definition from src_id_opt *)
    ks <<- MAP FST kes;
    vs <- eval_exprs cx (MAP SND kes);
    return $ Value $ StructV $ ZIP (ks, vs)
  od ∧
  eval_expr cx (Subscript e1 e2) = do
    tv1 <- eval_expr cx e1;
    tv2 <- eval_expr cx e2;
    v2 <- get_Value tv2;
    ts <- lift_option (get_self_code cx) "Subscript get_self_code";
    tv <- lift_sum $ evaluate_subscript (type_env ts) tv1 v2;
    return tv
  od ∧
  eval_expr cx (Attribute e id) = do
    tv <- eval_expr cx e;
    sv <- get_Value tv;
    v <- lift_sum $ evaluate_attribute sv id;
    return $ Value $ v
  od ∧
  eval_expr cx (Builtin bt es) = do
    check (builtin_args_length_ok bt (LENGTH es)) "Builtin args";
    vs <- eval_exprs cx es;
    acc <- get_accounts;
    v <- lift_sum $ evaluate_builtin cx acc bt vs;
    return $ Value v
  od ∧
  eval_expr cx (Pop bt) = do
    (loc, sbs) <- eval_base_target cx bt;
    tv <- assign_target cx (BaseTargetV loc sbs) PopOp;
    v <- get_Value tv;
    av <- lift_sum $ evaluate_subscripts v (REVERSE sbs);
    vs <- lift_option (extract_elements av) "pop not ArrayV";
    return $ Value $ LAST vs
  od ∧
  eval_expr cx (TypeBuiltin tb typ es) = do
    check (type_builtin_args_length_ok tb (LENGTH es)) "TypeBuiltin args";
    vs <- eval_exprs cx es;
    v <- lift_sum $ evaluate_type_builtin cx tb typ vs;
    return $ Value v
  od ∧
  eval_expr cx (Call Send es) = do
    check (LENGTH es = 2) "Send args";
    vs <- eval_exprs cx es;
    toAddr <- lift_option (dest_AddressV $ EL 0 vs) "Send not AddressV";
    amount <- lift_option (dest_NumV $ EL 1 vs) "Send not NumV";
    transfer_value cx.txn.target toAddr amount;
    return $ Value $ NoneV
  od ∧
  eval_expr cx (Call (ExtCall _) _) = raise $ Error "TODO: ExtCall" ∧
  eval_expr cx (Call (IntCall src_id_opt fn) es) = do
    check (¬MEM (src_id_opt, fn) cx.stk) "recursion";
    (* src_id_opt is NONE for self calls, SOME src_id for module calls *)
    ts <- lift_option (get_module_code cx src_id_opt) "IntCall get_module_code";
    tup <- lift_option (lookup_function fn Internal ts) "IntCall lookup_function";
    stup <<- SND tup; args <<- FST stup; sstup <<- SND stup;
    ret <<- FST $ sstup; body <<- SND $ sstup;
    check (LENGTH args = LENGTH es) "IntCall args length"; (* TODO: needed? *)
    vs <- eval_exprs cx es;
    tenv <<- type_env ts;
    env <- lift_option (bind_arguments tenv args vs) "IntCall bind_arguments";
    prev <- get_scopes;
    rtv <- lift_option (evaluate_type tenv ret) "IntCall eval ret";
    cxf <- push_function (src_id_opt, fn) env cx;
    rv <- finally
      (try (do eval_stmts cxf body; return NoneV od) handle_function)
      (pop_function prev);
    crv <- lift_option (safe_cast rtv rv) "IntCall cast ret";
    return $ Value crv
  od ∧
  eval_exprs cx [] = return [] ∧
  eval_exprs cx (e::es) = do
    tv <- eval_expr cx e;
    v <- get_Value tv;
    vs <- eval_exprs cx es;
    return $ v::vs
  od
Termination
  WF_REL_TAC ‘measure (λx. case x of
  | INR (INR (INR (INR (INR (INR (INR (INR (cx, es))))))))
    => exprs_bound (remcode cx) es
  | INR (INR (INR (INR (INR (INR (INR (INL (cx, e))))))))
    => expr_bound (remcode cx) e
  | INR (INR (INR (INR (INR (INR (INL (cx, nm, body, vs)))))))
    => 1 + LENGTH vs + (LENGTH vs) * (stmts_bound (remcode cx) body)
  | INR (INR (INR (INR (INR (INL (cx, t))))))
    => base_target_bound (remcode cx) t
  | INR (INR (INR (INR (INL (cx, gs)))))
    => targets_bound (remcode cx) gs
  | INR (INR (INR (INL (cx, g))))
    => target_bound (remcode cx) g
  | INR (INR (INL (cx, it)))
    => iterator_bound (remcode cx) it
  | INR (INL (cx, ss)) => stmts_bound (remcode cx) ss
  | INL (cx, s) => stmt_bound (remcode cx) s)’
  \\ reverse(rw[bound_def, MAX_DEF, MULT])
  >- (
    gvs[compatible_bound_def, check_def, assert_def]
    \\ qmatch_goalsub_abbrev_tac`(LENGTH vs) * x`
    \\ irule LESS_EQ_LESS_TRANS
    \\ qexists_tac`LENGTH vs + n * x + 1` \\ simp[]
    \\ PROVE_TAC[MULT_COMM, LESS_MONO_MULT])
  \\ gvs[check_def, assert_def]
  \\ gvs[push_function_def, return_def]
  \\ gvs[lift_option_def, CaseEq"option", CaseEq"prod", option_CASE_rator,
         raise_def, return_def]
  \\ gvs[remcode_def, get_module_code_def, ADELKEY_def]
  \\ qpat_x_assum`OUTR _ _ = _`kall_tac
  \\ gvs[CaseEq"option"]
  \\ qmatch_goalsub_abbrev_tac`ALOOKUP (FILTER P1 _)`
  \\ sg `P1 = λ(k,v). (λx. ¬MEM x cx.stk) k`
  >- rw[Abbr`P1`, FUN_EQ_THM, FORALL_PROD]
  \\ gvs[ALOOKUP_FILTER, Abbr`P1`]
  \\ first_x_assum (mp_then Any mp_tac
       lookup_function_Internal_imp_ALOOKUP_module_fns)
  \\ rw[]
  \\ drule ALOOKUP_FLAT_MAP_module_fns
  \\ first_x_assum(qspec_then`src_id_opt`strip_assume_tac)
  \\ disch_then drule \\ rw[]
  \\ rw[FILTER_FILTER]
  \\ rpt(pop_assum kall_tac)
  \\ simp[LAMBDA_PROD]
End

Theorem eval_exprs_length:
  ∀es cx st vs rt.
  eval_exprs cx es st = (INL vs, rt)
  ⇒ LENGTH vs = LENGTH es
Proof
  Induct \\ rw[evaluate_def, return_def, bind_def]
  \\ gvs[CaseEq"prod", CaseEq"sum"]
  \\ first_x_assum irule
  \\ goal_assum drule
QED

(* Semantics of initial state of a contract after deployment *)

Definition flag_value_def:
  flag_value m n acc [] = StructV $ REVERSE acc ∧
  flag_value m n acc (id::ids) =
  flag_value m (2n*n) ((id,FlagV m n)::acc) ids
End

val () = cv_auto_trans flag_value_def;

(* TODO: propagate errors? *)
Definition force_default_value_def:
  force_default_value env typ =
  case evaluate_type env typ of SOME tv => default_value tv
     | NONE => NoneV
End

(* TODO: assumes unique identifiers, but should check? *)
(* All initial_globals are for main contract (NONE source_id) *)
Definition initial_globals_def:
  initial_globals env [] = empty_globals ∧
  initial_globals env (VariableDecl _ Storage id typ :: ts) =
  (let gbs = initial_globals env ts in
   let key = string_to_num id in
   let iv = Value $ force_default_value env typ in
     update_module_mutable NONE key iv gbs) ∧
  initial_globals env (VariableDecl _ Transient id typ :: ts) =
  (let gbs = initial_globals env ts in
   let key = string_to_num id in
   let iv = Value $ force_default_value env typ in
     update_module_transient NONE key iv gbs) ∧
  initial_globals env (VariableDecl _ Immutable id typ :: ts) =
  (let gbs = initial_globals env ts in
   let key = string_to_num id in
   let iv = force_default_value env typ in
     update_module_immutable NONE key iv gbs) ∧
  (* TODO: prevent flag value being updated even in constructor *)
  initial_globals env (FlagDecl id ls :: ts) =
  (let gbs = initial_globals env ts in
   let key = string_to_num id in
   let iv = flag_value (LENGTH ls) 1 [] ls in
     update_module_immutable NONE key iv gbs) ∧
  (* TODO: handle Constants? or ignore since assuming folded into AST *)
  initial_globals env (HashMapDecl _ is_transient id kt vt :: ts) =
  (let gbs = initial_globals env ts in
   let key = string_to_num id in
   let iv = HashMap vt [] in
     if is_transient
     then update_module_transient NONE key iv gbs
     else update_module_mutable NONE key iv gbs) ∧
  initial_globals env (t :: ts) = initial_globals env ts
End

val () = cv_auto_trans initial_globals_def;

Definition initial_evaluation_context_def:
  initial_evaluation_context srcs tx =
  <| sources := srcs
   ; txn := tx
   ; stk := [(NONE, tx.function_name)]
   |>
End

val () = cv_auto_trans initial_evaluation_context_def;

Datatype:
  abstract_machine = <|
    sources: (address, (num option, toplevel list) alist) alist
  ; globals: (address, globals_state) alist
  ; accounts: evm_accounts
  |>
End

Definition initial_machine_state_def:
  initial_machine_state : abstract_machine = <|
    sources := []
  ; globals := []
  ; accounts := empty_accounts
  |>
End

Definition initial_state_def:
  initial_state (am: abstract_machine) scs : evaluation_state =
  <| accounts := am.accounts
   ; globals := am.globals
   ; logs := []
   ; scopes := scs
   |>
End

val () = cv_auto_trans initial_state_def;

Definition abstract_machine_from_state_def:
  abstract_machine_from_state srcs (st: evaluation_state) =
  <| sources := srcs
   ; globals := st.globals
   ; accounts := st.accounts
   |> : abstract_machine
End

val () = cv_auto_trans abstract_machine_from_state_def;

(* Reset transients in a single module_globals: merge transients back into mutables *)
Definition reset_module_transients_def:
  reset_module_transients (mg: module_globals) =
  mg with mutables := FUNION mg.transients mg.mutables
End

val () = cv_auto_trans reset_module_transients_def;

(* Reset transients for all modules in a globals_state *)
Definition reset_transient_globals_def:
  reset_transient_globals ([] : globals_state) = [] ∧
  reset_transient_globals ((k, mg) :: rest) =
    (k, reset_module_transients mg) :: reset_transient_globals rest
End

val () = cv_auto_trans reset_transient_globals_def;

(* Reset transients for all addresses in the global state *)
Definition reset_all_transient_globals_def:
  reset_all_transient_globals [] = [] ∧
  reset_all_transient_globals ((addr, gbs) :: rest) =
    (addr, reset_transient_globals gbs) :: reset_all_transient_globals rest
End

val () = cv_auto_trans reset_all_transient_globals_def;

(* Top-level entry-points into the semantics: loading (deploying) a contract,
* and calling its external functions *)

Definition constants_env_def:
  constants_env _ _ [] acc = SOME acc ∧
  constants_env cx am ((VariableDecl vis (Constant e) id typ)::ts) acc =
    (case FST $ eval_expr cx e (initial_state am [acc]) of
     | INL (Value v) => constants_env cx am ts $
                        acc |+ (string_to_num id, v)
     | _ => NONE) ∧
  constants_env cx am (t::ts) acc = constants_env cx am ts acc
End

Definition send_call_value_def:
  send_call_value mut cx =
  let n = cx.txn.value in
  if n = 0 then return () else do
    check (mut = Payable) "not Payable";
    transfer_value cx.txn.sender cx.txn.target n
  od
End

val () = send_call_value_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def,
            LET_RATOR, COND_RATOR]
  |> cv_auto_trans;

Definition call_external_function_def:
  call_external_function am cx mut ts args vals body ret =
  let tenv = type_env ts in
  case bind_arguments tenv args vals
  of NONE => (INR $ Error "call bind_arguments", am)
   | SOME env =>
  (case constants_env cx am ts FEMPTY
   of NONE => (INR $ Error "call constants_env", am)
    | SOME cenv => (* TODO: how do we stop constants being assigned to? *)
   let st = initial_state am [env; cenv] in
   let srcs = am.sources in
   let (res, st) =
     (case do send_call_value mut cx; eval_stmts cx body od st
      of
       | (INL (), st) => (INL NoneV, abstract_machine_from_state srcs st)
       | (INR (ReturnException v), st) =>
           (let am = abstract_machine_from_state srcs st in
            case evaluate_type tenv ret
            of NONE => (INR (Error "eval ret"), am)
             | SOME tv =>
            case safe_cast tv v
            of NONE => (INR (Error "ext cast ret"), am)
             | SOME v => (INL v, am))
       | (INR e, st) => (INR e, abstract_machine_from_state srcs st)) in
    (res, st (* with globals updated_by reset_all_transient_globals -- done separately *)))
End

Definition call_external_def:
  call_external am tx =
  let cx = initial_evaluation_context am.sources tx in
  case get_self_code cx
  of NONE => (INR $ Error "call get_self_code", am)
   | SOME ts =>
  case lookup_function tx.function_name External ts
  of NONE => (INR $ Error "call lookup_function", am)
   | SOME (mut, args, ret, body) =>
       call_external_function am cx mut ts args tx.args body ret
End

Definition load_contract_def:
  load_contract am tx ts =
  let addr = tx.target in
  let tenv = type_env ts in
  let gbs = initial_globals tenv ts in
  let am = am with globals updated_by CONS (addr, gbs) in
  (* Wrap toplevels in module map: NONE is the main contract *)
  let mods = [(NONE, ts)] in
  case lookup_function tx.function_name Deploy ts of
     | NONE => INR $ Error "no constructor"
     | SOME (mut, args, ret, body) =>
       let cx = initial_evaluation_context ((addr,mods)::am.sources) tx in
       case call_external_function am cx mut ts args tx.args body ret
         of (INR e, _) => INR e
       (* TODO: update balances on return *)
          | (_, am) => INL (am with sources updated_by CONS (addr, mods))
End
