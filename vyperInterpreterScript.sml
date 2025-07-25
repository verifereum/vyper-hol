open HolKernel boolLib bossLib Parse wordsLib blastLib dep_rewrite monadsyntax
     alistTheory rich_listTheory byteTheory finite_mapTheory keccakTheory
     int_bitwiseTheory arithmeticTheory combinTheory pairTheory whileTheory
     cv_typeTheory cv_stdTheory cv_transLib
open vfmTypesTheory vfmStateTheory vyperAstTheory

val () = new_theory "vyperInterpreter";

(* TODO: delete once merged upstream *)

Theorem cv_ispair_cv_add[simp]:
  cv_ispair (cv_add x y) = Num 0
Proof
  Cases_on`x` \\ Cases_on`y` \\ rw[]
QED

val FUPDATE_LIST_pre_def = FUPDATE_LIST_THM
 |> SRULE [FORALL_PROD]
 |> INST_TYPE [alpha |-> “:num”]
 |> cv_auto_trans_pre;

Theorem FUPDATE_LIST_pre[cv_pre]:
  ∀f ls. FUPDATE_LIST_pre f ls
Proof
  Induct_on`ls`
  \\ rw[Once FUPDATE_LIST_pre_def]
QED

Theorem cv_rep_DOMSUB[cv_rep]:
  from_fmap f (m \\ k) = cv_delete (Num k) (from_fmap f m)
Proof
  rw[from_fmap_def, GSYM cv_delete_thm]
  \\ AP_TERM_TAC
  \\ DEP_REWRITE_TAC[sptreeTheory.spt_eq_thm]
  \\ rw[sptreeTheory.wf_fromAList, sptreeTheory.wf_delete]
  \\ rw[sptreeTheory.lookup_delete, sptreeTheory.lookup_fromAList]
  \\ rw[DOMSUB_FLOOKUP_THM]
QED

Theorem cv_size'_Num[simp]:
  cv_size' (Num m) = Num 0
Proof
  rw[Once cv_size'_def]
QED

Theorem cv_size'_cv_mk_BN[simp]:
  cv_size' (cv_mk_BN x y) =
  cv_add (cv_size' x) (cv_size' y)
Proof
  rw[cv_mk_BN_def]
  \\ TRY (
    rw[Once cv_size'_def]
    \\ rw[Once cv_size'_def]
    \\ Cases_on`x` \\ gs[]
    \\ rw[Once cv_size'_def, SimpRHS]
    \\ NO_TAC)
  \\ rw[Once cv_size'_def]
  \\ rw[Once cv_size'_def]
  \\ Cases_on`y` \\ gs[]
  \\ rw[Once cv_size'_def]
  \\ rw[Once cv_size'_def]
  \\ rw[Once cv_size'_def]
QED

Theorem cv_size'_cv_mk_BS[simp]:
  cv_size' (cv_mk_BS x y z) =
  cv_add (cv_add (cv_size' x) (cv_size' z)) (Num 1)
Proof
  rw[cv_mk_BS_def]
  \\ rw[Q.SPEC`Pair x y`cv_size'_def]
  \\ Cases_on`x` \\ Cases_on`z` \\ gvs[]
  \\ gvs[Q.SPEC`Pair x y`cv_size'_def]
QED

(* TODO: move *)

Definition MAP_HEX_def:
  MAP_HEX [] = [] ∧
  MAP_HEX (x::xs) = HEX x :: MAP_HEX xs
End

val MAP_HEX_pre_def = cv_auto_trans_pre MAP_HEX_def;

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
  |> cv_trans_pre;

Theorem num_to_dec_string_pre[cv_pre]:
  num_to_dec_string_pre x
Proof
  rw[num_to_dec_string_pre_def, MAP_HEX_pre_EVERY]
  \\ qspecl_then[`10`,`x`]mp_tac numposrepTheory.n2l_BOUND
  \\ rw[listTheory.EVERY_MEM]
  \\ first_x_assum drule \\ rw[]
QED

val int_exp_pre_def = cv_auto_trans_pre integerTheory.int_exp;

Theorem int_exp_pre[cv_pre]:
  int_exp_pre p v
Proof
  qid_spec_tac`p`
  \\ Induct_on `v`
  \\ rw[Once int_exp_pre_def]
QED

(* TODO: I don't know if this is the best way to translate this... *)
val () = cv_auto_trans num_of_bits_def;
val () = cv_auto_trans int_of_bits_def;
val () = cv_auto_trans bits_of_int_def;

Definition bits_bitwise_and_def:
  bits_bitwise_and = bits_bitwise $/\
End

val bits_bitwise_and_pre_def = bits_bitwise_def
 |> oneline
 |> Q.GEN`f`
 |> Q.ISPEC`$/\`
 |> SRULE [GSYM bits_bitwise_and_def]
 |> (curry $ flip $ uncurry cv_trans_pre_rec)
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

val bits_bitwise_or_pre_def = bits_bitwise_def
 |> oneline
 |> Q.GEN`f`
 |> Q.ISPEC`$\/`
 |> SRULE [GSYM bits_bitwise_or_def]
 |> (curry $ flip $ uncurry cv_trans_pre_rec)
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

val bits_bitwise_xor_pre_def = bits_bitwise_def
 |> oneline
 |> Q.GEN`f`
 |> Q.ISPEC`λx:bool y. x ≠ y`
 |> SRULE [GSYM bits_bitwise_xor_def]
 |> (curry $ flip $ uncurry cv_trans_pre_rec)
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

(* -- *)

Definition string_to_num_def:
  string_to_num s = l2n 257 (MAP (SUC o ORD) s)
End

val () = cv_auto_trans string_to_num_def;

Datatype:
  value
  = NoneV
  | BoolV bool
  | ArrayV bound (value list)
  | IntV int_bound int
  | StringV num string
  | BytesV bound (word8 list)
  | StructV ((identifier, value) alist)
End

Overload AddressV = “λw: address. BytesV (Fixed 20) (word_to_bytes w T)”

val from_to_value_thm = cv_typeLib.from_to_thm_for “:value”;
val from_value = from_to_value_thm |> concl |> rator |> rand
val to_value = from_to_value_thm |> concl |> rand

Datatype:
  subscript
  = IntSubscript int
  | StrSubscript string
  | BytesSubscript (word8 list)
  | AttrSubscript identifier
End

Datatype:
  toplevel_value = Value value | HashMap value_type ((subscript, toplevel_value) alist)
End

Type hmap = “:(subscript, toplevel_value) alist”

Datatype:
  type_args = StructArgs (argument list) | FlagArgs num
End

Definition default_value_def:
  default_value env (BaseT (UintT n)) = IntV (Unsigned n) 0 ∧
  default_value env (BaseT (IntT n)) = IntV (Signed n) 0 ∧
  default_value env (BaseT DecimalT) = IntV (Signed 168) 0 ∧
  default_value env (TupleT ts) = default_value_tuple env [] ts ∧
  default_value env (ArrayT _ (Dynamic n)) = ArrayV (Dynamic n) [] ∧
  default_value env (ArrayT t (Fixed n)) =
    ArrayV (Fixed n) (REPLICATE n (default_value env t)) ∧
  default_value env (StructT id) =
    (let nid = string_to_num id in
     case FLOOKUP env nid
       of SOME (StructArgs args) => default_value_struct (env \\ nid) [] args
        | _ => StructV []) ∧
  default_value env (FlagT id) = IntV (Unsigned 256) 0 ∧
  default_value env NoneT = NoneV ∧
  default_value env (BaseT BoolT) = BoolV F ∧
  default_value env (BaseT AddressT) = AddressV 0w ∧
  default_value env (BaseT (StringT n)) = StringV n "" ∧
  default_value env (BaseT (BytesT (Fixed n))) = BytesV (Fixed n) (REPLICATE n 0w) ∧
  default_value env (BaseT (BytesT (Dynamic n))) = BytesV (Dynamic n) [] ∧
  default_value_tuple env acc [] = ArrayV (Fixed (LENGTH acc)) (REVERSE acc) ∧
  default_value_tuple env acc (t::ts) =
    default_value_tuple env (default_value env t :: acc) ts ∧
  default_value_struct env acc [] = StructV (REVERSE acc) ∧
  default_value_struct env acc ((id,t)::ps) =
    default_value_struct env ((id,default_value env t)::acc) ps
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx.
    case x
      of INL (env, t) => (CARD (FDOM env), type_size t)
       | INR (INL (env, _, ts)) => (CARD (FDOM env), list_size type_size ts)
       | INR (INR (env, _, ps)) => (CARD (FDOM env), list_size type_size (MAP SND ps)))’
  \\ rw[type_size_def, FLOOKUP_DEF]
  \\ disj1_tac
  \\ CCONTR_TAC
  \\ fs[]
End

val () = cv_auto_trans_rec default_value_def (
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx.
    case x
      of INL (env, t) => (cv$c2n $ cv_size' env, cv_size t)
       | INR (INL (env, _, ts)) => (cv$c2n (cv_size' env), cv_size ts)
       | INR (INR (env, _, ps)) => (cv$c2n (cv_size' env), cv_size ps))’
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
  \\ `cv_ispair ck = Num 0`
  by (
    rw[Abbr`ck`, definition"cv_string_to_num_def"]
    \\ rw[Once keccakTheory.cv_l2n_def]
    \\ rw[cv_ispair_cv_add] )
  \\ pop_assum mp_tac
  \\ qid_spec_tac`cv_env`
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
    \\ Cases_on`cv_env` \\ gs[]
    \\ Cases_on`0 < m` \\ gs[]
    \\ simp[Once cv_delete_def]
    \\ rw[Once cv_stdTheory.cv_size'_def]
    \\ rw[Once cv_stdTheory.cv_size'_def] )
  \\ Cases_on`cv_env` \\ gs[]
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

(*
We don't use this directly to support cv which prefers num keys
Type scope = “:identifier |-> value”;
*)
Type scope = “:num |-> value”;

Definition lookup_scopes_def:
  lookup_scopes id [] = NONE ∧
  lookup_scopes id ((env: scope)::rest) =
  case FLOOKUP env id of NONE =>
    lookup_scopes id rest
  | SOME v => SOME v
End

Type containing_scope = “:scope list # scope # scope list”;

Definition find_containing_scope_def:
  find_containing_scope id [] = NONE : containing_scope option ∧
  find_containing_scope id (env::rest) =
  if id ∈ FDOM env then SOME ([], env, rest)
  else OPTION_MAP (λ(p,q). (env::p, q)) (find_containing_scope id rest)
End

val () = cv_auto_trans (REWRITE_RULE[TO_FLOOKUP]find_containing_scope_def);

Datatype:
  location
  = ScopedVar containing_scope identifier
  | ImmutableVar identifier
  | TopLevelVar identifier
End

Datatype:
  assignment_value
  = BaseTargetV location (subscript list)
  | TupleTargetV (assignment_value list)
End

Type base_target_value = “:location # subscript list”;

Datatype:
  assign_operation
  = Replace value
  | Update binop value
  | AppendOp value
  | PopOp
End

Definition evaluate_literal_def:
  evaluate_literal (BoolL b) = BoolV b ∧
  evaluate_literal (StringL n s) = StringV n s ∧
  evaluate_literal (BytesL b bs) = BytesV b bs ∧
  evaluate_literal (IntL ib i) = IntV ib i
End

val () = cv_auto_trans evaluate_literal_def;

Definition evaluate_in_array_def:
  evaluate_in_array v ls =
  INL $ BoolV $ MEM v ls
End

val () = cv_auto_trans evaluate_in_array_def;

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

(* TODO: add unsafe ops and make these ones safe *)
Definition evaluate_binop_def:
  evaluate_binop (Add:binop) (IntV u1 i1) (IntV u2 i2) =
    bounded_int_op u1 u2 (i1 + i2) ∧
  evaluate_binop Sub (IntV u1 i1) (IntV u2 i2) =
    bounded_int_op u1 u2 (i1 - i2) ∧
  evaluate_binop Mul (IntV u1 i1) (IntV u2 i2) =
    bounded_int_op u1 u2 (i1 * i2) ∧
  evaluate_binop Div (IntV u1 i1) (IntV u2 i2) =
    (if i2 = 0 then INR "Div0" else
     bounded_int_op u1 u2 (i1 / i2)) ∧
  evaluate_binop Mod (IntV u1 i1) (IntV u2 i2) =
    (if i2 = 0 then INR "Mod0" else
     bounded_int_op u1 u2 (i1 % i2)) ∧
  evaluate_binop Exp (IntV u1 i1) (IntV u2 i2) =
    (if i2 < 0 then INR "Exp~"
     else bounded_int_op u1 u2 (i1 ** (Num i2))) ∧
  evaluate_binop And (IntV u1 i1) (IntV u2 i2) =
    bounded_int_op u1 u2 (int_and i1 i2) ∧
  evaluate_binop  Or (IntV u1 i1) (IntV u2 i2) =
    bounded_int_op u1 u2 (int_or i1 i2) ∧
  evaluate_binop XOr (IntV u1 i1) (IntV u2 i2) =
    bounded_int_op u1 u2 (int_xor i1 i2) ∧
  evaluate_binop And (BoolV b1) (BoolV b2) = INL (BoolV (b1 ∧ b2)) ∧
  evaluate_binop  Or (BoolV b1) (BoolV b2) = INL (BoolV (b1 ∨ b2)) ∧
  evaluate_binop XOr (BoolV b1) (BoolV b2) = INL (BoolV (b1 ≠ b2)) ∧
  evaluate_binop ShL (IntV u1 i1) (IntV u2 i2) =
    (* TODO: check type constraints on shifts *)
    (if i2 < 0 then INR "ShL0"
     else INL $ IntV u1 $ int_shift_left (Num i2) i1) ∧
  evaluate_binop ShR (IntV u1 i1) (IntV u2 i2) =
    (if i2 < 0 then INR "ShR0"
     else INL $ IntV u1 $ int_shift_right (Num i2) i1) ∧
  evaluate_binop In (IntV u1 i1) (IntV u2 i2) =
    (if u1 = u2 ∧ u2 = Unsigned 256
     then if i1 < 0 ∨ i2 < 0 then INR "In~"
          else INL $ BoolV (int_and i1 i2 ≠ 0)
     else INR "In type") ∧
  evaluate_binop In v (ArrayV _ ls) = evaluate_in_array v ls ∧
  evaluate_binop NotIn v1 v2 = binop_negate $ evaluate_binop In v1 v2 ∧
  evaluate_binop Eq (StringV _ s1) (StringV _ s2) = INL (BoolV (s1 = s2)) ∧
  evaluate_binop Eq (BytesV _ s1) (BytesV _ s2) = INL (BoolV (s1 = s2)) ∧
  evaluate_binop Eq (BoolV b1) (BoolV b2) = INL (BoolV (b1 = b2)) ∧
  evaluate_binop Eq (IntV u1 i1) (IntV u2 i2) =
    (if u1 = u2 then INL (BoolV (i1 = i2)) else INR "Eq type") ∧
  evaluate_binop NotEq v1 v2 = binop_negate $ evaluate_binop Eq v1 v2 ∧
  evaluate_binop Lt (IntV u1 i1) (IntV u2 i2) =
    (if u1 = u2 then INL (BoolV (i1 < i2)) else INR "Lt type") ∧
  evaluate_binop Gt (IntV u1 i1) (IntV u2 i2) =
    (if u1 = u2 then INL (BoolV (i1 > i2)) else INR "Gt type") ∧
  evaluate_binop _ _ _ = INR "binop"
Termination
  WF_REL_TAC ‘inv_image $< (λ(b,x,y). if b = NotIn ∨ b = NotEq then 2n else 0n)’
  \\ rw[]
End

val () = cv_auto_trans evaluate_binop_def;

Datatype:
  call_txn = <|
    sender: address
  ; target: address
  ; function_name: identifier
  ; args: value list
  ; value: num
  ; is_creation: bool
  |>
End

Datatype:
  evaluation_context = <|
    stk: identifier list
  ; txn: call_txn
  ; sources: (address, toplevel list) alist
  |>
End

Theorem with_stk_updated_by_id[simp]:
  (cx with stk updated_by (λx. x)) = cx
Proof
  rw[theorem"evaluation_context_component_equality"]
QED

Definition empty_call_txn_def:
  empty_call_txn = <|
    sender := 0w;
    target := 0w;
    function_name := "";
    args := [];
    value := 0;
    is_creation := F
  |>
End

Definition empty_evaluation_context_def:
  empty_evaluation_context = <|
    stk := []
  ; txn := empty_call_txn
  ; sources := []
  |>
End

val () = cv_auto_trans empty_evaluation_context_def;

Definition evaluate_account_op_def:
  evaluate_account_op Balance a = IntV (Unsigned 256) &a.balance ∧
  evaluate_account_op Codehash a = BytesV (Fixed 32) (Keccak_256_w64 a.code) ∧
  evaluate_account_op Codesize a = IntV (Unsigned 256) $ &LENGTH a.code ∧
  evaluate_account_op IsContract a = BoolV (a.code ≠ []) ∧
  evaluate_account_op Code a = BytesV (Dynamic (LENGTH a.code)) a.code
End

val () = cv_auto_trans evaluate_account_op_def;

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

Definition compatible_bound_def:
  compatible_bound (Fixed n) m = (n = m) ∧
  compatible_bound (Dynamic n) m = (m ≤ n)
End

val () = cv_auto_trans compatible_bound_def;

Definition init_concat_output_def:
  init_concat_output n (BytesV _ bs) = SOME $ BytesV (Dynamic n) bs ∧
  init_concat_output n (StringV _ s) = SOME $ StringV n s ∧
  init_concat_output _ _ = NONE
End

val () = cv_auto_trans init_concat_output_def;

Definition evaluate_concat_loop_def:
  evaluate_concat_loop (StringV n s1) sa ba [] =
  (let s = FLAT $ REV sa [s1] in
   (if compatible_bound (Dynamic n) (LENGTH s)
    then INL (StringV n s)
    else INR "concat bound")) ∧
  evaluate_concat_loop (BytesV b b1) sa ba [] =
  (let bs = FLAT $ REV ba [b1] in
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

val evaluate_concat_pre_def = cv_auto_trans_pre evaluate_concat_def;

Theorem evaluate_concat_pre[cv_pre]:
  evaluate_concat_pre b vs
Proof
  rw[evaluate_concat_pre_def]
  \\ strip_tac \\ gvs[]
QED

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
   | StringV n s => (
       if start + length < LENGTH s then
       if compatible_bound b length then
         INL $ StringV n (TAKE length (DROP start s))
       else INR "evaluate_slice bound"
       else INR "evaluate_slice range")
  | _ => INR "evaluate_slice v"
End

val () = cv_auto_trans evaluate_slice_def;

Definition is_Unsigned_def[simp]:
  (is_Unsigned (Unsigned _ ) = T) ∧
  (is_Unsigned _ = F)
End

Definition evaluate_builtin_def:
  evaluate_builtin cx _ Len [BytesV _ ls] = INL (IntV (Unsigned 256) &(LENGTH ls)) ∧
  evaluate_builtin cx _ Len [StringV _ ls] = INL (IntV (Unsigned 256) &(LENGTH ls)) ∧
  evaluate_builtin cx _ Len [ArrayV _ ls] = INL (IntV (Unsigned 256) &(LENGTH ls)) ∧
  evaluate_builtin cx _ Not [BoolV b] = INL (BoolV (¬b)) ∧
  evaluate_builtin cx _ Not [IntV u i] =
    (if is_Unsigned u ∧ 0 ≤ i then INL (IntV u (int_not i)) else INR "signed Not") ∧
  evaluate_builtin cx _ Neg [IntV u i] = INL (IntV u (-i)) ∧
  evaluate_builtin cx _ Keccak256 [BytesV _ ls] = INL $ BytesV (Fixed 32) $
    Keccak_256_w64 ls ∧
  (* TODO: reject BytesV with invalid bounds for Keccak256 *)
  (* TODO: support Keccak256 on strings *)
  evaluate_builtin cx _ (Bop bop) [v1; v2] = evaluate_binop bop v1 v2 ∧
  evaluate_builtin cx _ (Msg Sender) [] = INL $ AddressV cx.txn.sender ∧
  evaluate_builtin cx _ (Msg SelfAddr) [] = INL $ AddressV cx.txn.target ∧
  evaluate_builtin cx _ (Msg ValueSent) [] = INL $ IntV (Unsigned 256) &cx.txn.value ∧
  evaluate_builtin cx _ (Concat n) vs = evaluate_concat n vs ∧
  evaluate_builtin cx _ (Slice n) [v1; v2; v3] = evaluate_slice v1 v2 v3 n ∧
  evaluate_builtin cx _ (MakeArray bd) vs = INL $ ArrayV bd vs ∧
  evaluate_builtin cx acc (Acc aop) [BytesV _ bs] =
    (let a = lookup_account (word_of_bytes T (0w:address) bs) acc in
      INL $ evaluate_account_op aop a) ∧
  evaluate_builtin _ _ _ _ = INR "builtin"
End

val () = cv_auto_trans evaluate_builtin_def;

Definition type_builtin_args_length_ok_def:
  type_builtin_args_length_ok Empty n = (n = 0n) ∧
  type_builtin_args_length_ok MaxValue n = (n = 0) ∧
  type_builtin_args_length_ok MinValue n = (n = 0) ∧
  type_builtin_args_length_ok Epsilon n = (n = 0) ∧
  type_builtin_args_length_ok Convert n = (n = 1)
End

val () = cv_auto_trans type_builtin_args_length_ok_def;

Definition evaluate_max_value_def:
  evaluate_max_value (BaseT (UintT n)) = INL $ IntV (Unsigned n) (&(2 ** n) - 1) ∧
  evaluate_max_value (BaseT (IntT n)) = (if n = 0
                                         then INR "max_value IntT"
                                         else INL $ IntV (Signed n) (&(2 ** (n-1)) - 1)) ∧
  evaluate_max_value _ = INR "evaluate_max_value"
End

val () = cv_auto_trans evaluate_max_value_def;

Definition extract_elements_def:
  extract_elements (ArrayV _ vs) = SOME vs ∧
  extract_elements _ = NONE
End

val () = cv_auto_trans extract_elements_def;

Definition replace_elements_def:
  replace_elements (ArrayV b _) vs = INL (ArrayV b vs) ∧
  replace_elements _ _ = INR "replace_elements"
End

val () = cv_auto_trans replace_elements_def;

Definition integer_index_def:
  integer_index vs i =
   if Num i < LENGTH vs then
     SOME $ if 0 ≤ i then Num i else LENGTH vs - Num i
   else NONE
End

val () = cv_auto_trans integer_index_def;

Definition value_to_key_def:
  value_to_key (IntV _ i) = SOME $ IntSubscript i ∧
  value_to_key (StringV _ s) = SOME $ StrSubscript s ∧
  value_to_key (BytesV _ bs) = SOME $ BytesSubscript bs ∧
  value_to_key _ = NONE
End

val () = cv_auto_trans value_to_key_def;

Definition type_env_def:
  type_env [] = FEMPTY ∧
  type_env (StructDecl id args :: ts) =
    type_env ts |+ (string_to_num id, StructArgs args) ∧
  type_env (FlagDecl id ls :: ts) =
    type_env ts |+ (string_to_num id, FlagArgs (LENGTH ls)) ∧
  type_env (_ :: ts) = type_env ts
End

val () = cv_auto_trans type_env_def;

Definition evaluate_subscript_def:
  evaluate_subscript ts (Value av) (IntV _ i) =
  (case extract_elements av of SOME vs =>
    (case integer_index vs i of SOME j => INL $ Value (EL j vs)
     | _ => INR "integer_index")
   | _ => INR "extract_elements") ∧
  evaluate_subscript ts (HashMap vt hm) kv =
  (case value_to_key kv of SOME k =>
    (case ALOOKUP hm k of SOME tv => INL tv
        | _ => (case vt of Type typ =>
                  INL $ Value $ default_value (type_env ts) typ
                | _ => INR "HashMap final value type" ))
   | _ => INR "evaluate_subscript value_to_key") ∧
  evaluate_subscript _ _ _ = INR "evaluate_subscript"
End

val evaluate_subscript_pre_def = cv_auto_trans_pre evaluate_subscript_def;

Theorem evaluate_subscript_pre[cv_pre]:
  evaluate_subscript_pre ts av v
Proof
  rw[evaluate_subscript_pre_def, integer_index_def]
  \\ rw[]
  \\ qmatch_asmsub_rename_tac`0i ≤ w`
  \\ Cases_on`w` \\ gs[]
QED

Definition evaluate_attribute_def:
  evaluate_attribute (StructV kvs) id =
  (case ALOOKUP kvs id of SOME v => INL v
   | _ => INR "attribute") ∧
  evaluate_attribute _ _ = INR "evaluate_attribute"
End

val () = cv_auto_trans evaluate_attribute_def;

Definition builtin_args_length_ok_def:
  builtin_args_length_ok Len n = (n = 1n) ∧
  builtin_args_length_ok Not n = (n = 1) ∧
  builtin_args_length_ok Neg n = (n = 1) ∧
  builtin_args_length_ok Keccak256 n = (n = 1) ∧
  builtin_args_length_ok (Concat _) n = (2 ≤ n) ∧
  builtin_args_length_ok (Slice _) n = (n = 3) ∧
  builtin_args_length_ok (MakeArray b) n = compatible_bound b n ∧
  builtin_args_length_ok (Bop _) n = (n = 2) ∧
  builtin_args_length_ok (Msg _) n = (n = 0) ∧
  builtin_args_length_ok (Acc _) n = (n = 1)
End

val () = cv_auto_trans builtin_args_length_ok_def;

Type log = “:identifier # (value list)”;

Datatype:
  globals_state = <|
    mutables: num |-> toplevel_value
  ; transients: (num # toplevel_value) list
  ; immutables: num |-> value
  |>
End

Datatype:
  evaluation_state = <|
    globals: (address, globals_state) alist
  ; logs: log list
  ; scopes: scope list
  ; accounts: evm_accounts
  |>
End

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

Definition get_current_globals_def:
  get_current_globals cx st =
    lift_option (ALOOKUP st.globals cx.txn.target) "get_current_globals" st
End

val () = get_current_globals_def
  |> SRULE [lift_option_def, option_CASE_rator]
  |> cv_auto_trans;

Definition set_current_globals_def:
  set_current_globals cx gbs st =
  let addr = cx.txn.target in
    return () $ st with globals updated_by
      (λal. (addr, gbs) :: (ADELKEY addr al))
End

val () = cv_auto_trans set_current_globals_def;

Definition lookup_global_def:
  lookup_global cx n = do
    gbs <- get_current_globals cx;
    case FLOOKUP gbs.mutables n
      of NONE => raise $ Error "lookup_global"
       | SOME v => return v
  od
End

val () = lookup_global_def
  |> SRULE [bind_def, FUN_EQ_THM, option_CASE_rator, UNCURRY]
  |> cv_auto_trans;

Definition set_global_def:
  set_global cx n v = do
    gbs <- get_current_globals cx;
    set_current_globals cx $
      gbs with mutables updated_by (λm. m |+ (n,v))
  od
End

val () = set_global_def
  |> SRULE [bind_def, FUN_EQ_THM, UNCURRY]
  |> cv_auto_trans;

Definition get_immutables_def:
  get_immutables cx = do
    gbs <- get_current_globals cx;
    return gbs.immutables
  od
End

val () = get_immutables_def
  |> SRULE [bind_def]
  |> cv_auto_trans;

Definition set_immutable_def:
  set_immutable cx n v = do
    gbs <- get_current_globals cx;
    set_current_globals cx $
      gbs with immutables updated_by (λim. im |+ (n, v))
  od
End

val () = set_immutable_def
  |> SRULE [bind_def]
  |> cv_auto_trans;

Definition get_accounts_def:
  get_accounts st = return st.accounts st
End

val () = cv_auto_trans get_accounts_def;

Definition update_accounts_def:
  update_accounts f st = return () (st with accounts updated_by f)
End

Definition get_Value_def[simp]:
  get_Value (Value v) = return v ∧
  get_Value _ = raise $ Error "not Value"
End

val () = get_Value_def
  |> SIMP_RULE std_ss [FUN_EQ_THM]
  |> cv_auto_trans;

Definition check_def:
  check b str = assert b (Error str)
End

val () = cv_auto_trans check_def;

Definition is_Value_def[simp]:
  (is_Value (Value _) ⇔ T) ∧
  (is_Value _ ⇔ F)
End

Definition switch_BoolV_def:
  switch_BoolV v f g =
  if v = Value $ BoolV T then f
  else if v = Value $ BoolV F then g
  else raise $ Error (if is_Value v then "not BoolV" else "not Value")
End

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

Definition handle_loop_exception_def:
  handle_loop_exception e =
  if e = ContinueException then return F
  else if e = BreakException then return T
  else raise e
End

val () = handle_loop_exception_def
  |> SRULE [FUN_EQ_THM, COND_RATOR]
  |> cv_auto_trans;

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

Definition get_self_code_def:
  get_self_code cx = ALOOKUP cx.sources cx.txn.target
End

val () = cv_auto_trans get_self_code_def;

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
  evaluate_convert (IntV u i) (BaseT (IntT n)) =
    (if within_int_bound (Signed n) i
     then INL $ IntV (Signed n) i
     else INR "convert int bound") ∧
  evaluate_convert (IntV u i) (BaseT (UintT n)) =
    (if within_int_bound (Unsigned n) i
     then INL $ IntV (Unsigned n) i
     else INR "convert uint bound") ∧
  evaluate_convert (IntV u i) (BaseT (BytesT bd)) =
  (* TODO: check and use type for width etc. *)
    (if compatible_bound bd 32
     then INL $ BytesV bd (word_to_bytes ((i2w i):bytes32) T)
     else INR "convert int to bytes") ∧
  (* TODO: more conversions *)
  evaluate_convert _ _ = INR "convert"
End

val () = cv_auto_trans evaluate_convert_def;

Definition evaluate_type_builtin_def:
  evaluate_type_builtin cx Empty typ vs =
  (case get_self_code cx
     of SOME ts =>
        INL $ default_value (type_env ts) typ
      | _ => INR "Empty get_self_code") ∧
  evaluate_type_builtin cx MaxValue typ vs =
    evaluate_max_value typ ∧
  evaluate_type_builtin cx Convert typ [v] =
    evaluate_convert v typ ∧
  evaluate_type_builtin _ _ _ _ =
    INR "TODO: TypeBuiltin"
End

val () = cv_auto_trans evaluate_type_builtin_def;

Definition lookup_flag_def:
  lookup_flag fid [] = NONE ∧
  lookup_flag fid (FlagDecl id ls :: ts) =
    (if fid = id then SOME ls else lookup_flag fid ts) ∧
  lookup_flag fid (t :: ts) = lookup_flag fid ts
End

val () = cv_auto_trans lookup_flag_def;

Definition lookup_flag_mem_def:
  lookup_flag_mem cx fid mid =
  case get_self_code cx
    of NONE => raise $ Error "lookup_flag_mem code"
     | SOME ts =>
  case lookup_flag fid ts
    of NONE => raise $ Error "lookup_flag"
     | SOME ls =>
  case INDEX_OF mid ls
    of NONE => raise $ Error "lookup_flag_mem index"
     | SOME i => return $ Value $ IntV (Unsigned 256) $ &(2 ** i)
End

val () = lookup_flag_mem_def
  |> SRULE [FUN_EQ_THM, option_CASE_rator]
  |> cv_auto_trans;

Definition is_ArrayT_def[simp]:
  is_ArrayT (ArrayT _ _) = T ∧
  is_ArrayT _ = F
End

val () = cv_auto_trans is_ArrayT_def;

Definition ArrayT_type_def[simp]:
  ArrayT_type (ArrayT t _) = t ∧
  ArrayT_type _ = NoneT
End

val () = cv_auto_trans ArrayT_type_def;

Definition build_getter_def:
  build_getter e kt (Type vt) n =
    (let vn = num_to_dec_string n in
      if is_ArrayT vt then
        (let (args, ret, exp) =
           build_getter (Subscript e (Name vn))
             uint256 (Type (ArrayT_type vt)) (SUC n) in
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
  \\ Cases_on `a` \\ gvs[definition"cv_is_ArrayT_def",
                         definition"cv_ArrayT_type_def"]
  \\ rw[] \\ gvs[]
  \\ qmatch_goalsub_rename_tac`cv_fst p`
  \\ Cases_on `p` \\ gvs[]
);

Definition getter_def:
  getter id kt vt =
  let (args, ret, exp) =
    build_getter (TopLevelName id) kt vt 0
  in
    (View, args, ret, [Return $ SOME exp])
End

val () = cv_auto_trans getter_def;

Definition lookup_function_def:
  lookup_function name Deploy [] = SOME (Nonpayable, [], NoneT, [Pass]) ∧
  lookup_function name vis [] = NONE ∧
  lookup_function name vis (FunctionDecl fv fm id args ret body :: ts) =
  (if id = name ∧ vis = fv then SOME (fm, args, ret, body)
   else lookup_function name vis ts) ∧
  lookup_function name External (VariableDecl Public mut id typ :: ts) =
  (if id = name then
    if ¬is_ArrayT typ
    then SOME (View, [], typ, [
                 Return (SOME (if mut = Immutable then Name id
                               else TopLevelName id))
               ])
    else SOME $ getter id uint256 (Type (ArrayT_type typ))
   else lookup_function name External ts) ∧
  lookup_function name External (HashMapDecl Public _ id kt vt :: ts) =
  (if id = name then SOME $ getter id kt vt
   else lookup_function name External ts) ∧
  lookup_function name vis (_ :: ts) =
    lookup_function name vis ts
End

val () = cv_auto_trans lookup_function_def;

(* TODO: check types? *)
Definition bind_arguments_def:
  bind_arguments ([]: argument list) [] = SOME (FEMPTY: scope) ∧
  bind_arguments ((id, typ)::params) (v::vs) =
    OPTION_MAP (λm. m |+ (string_to_num id, v)) (bind_arguments params vs) ∧
  bind_arguments _ _ = NONE
End

val () = cv_auto_trans bind_arguments_def;

Definition get_scopes_def:
  get_scopes st = return st.scopes st
End

val () = cv_auto_trans get_scopes_def;

Definition set_scopes_def:
  set_scopes env st = return () $ st with scopes := env
End

val () = cv_auto_trans set_scopes_def;

Definition push_log_def:
  push_log log st = return () $ st with logs updated_by CONS log
End

val () = cv_auto_trans push_log_def;

Definition push_function_def:
  push_function fn sc cx st =
  return (cx with stk updated_by CONS fn)
    $ st with scopes := [sc]
End

val () = cv_auto_trans push_function_def;

Definition pop_function_def:
  pop_function prev = set_scopes prev
End

val () = cv_auto_trans pop_function_def;

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
    (pre, env, rest) <-
      lift_option (find_containing_scope n sc) "set_variable not found";
    set_scopes (pre ++ (env |+ (n, v))::rest)
  od
End

val () = set_variable_def
  |> SRULE [FUN_EQ_THM, bind_def, lift_option_def,
            LET_RATOR, UNCURRY, option_CASE_rator]
  |> cv_auto_trans;

Definition handle_function_def:
  handle_function (ReturnException v) = return v ∧
  handle_function (Error str) = raise $ Error str ∧
  handle_function (AssertException str) = raise $ AssertException str ∧
  handle_function _ = raise $ Error "handle_function"
End

val () = handle_function_def
  |> SRULE [FUN_EQ_THM]
  |> cv_auto_trans;

Definition append_element_def:
  append_element (ArrayV bd vs) v =
    (if compatible_bound bd (SUC (LENGTH vs))
     then INL $ ArrayV bd (SNOC v vs)
     else INR "Append Overflow") ∧
  append_element _ _ = INR "append_element"
End

val () = cv_auto_trans append_element_def;

Definition pop_element_def:
  pop_element (ArrayV (Dynamic n) vs) =
    (if vs = [] then INR "Pop empty"
     else INL $ ArrayV (Dynamic n) (FRONT vs)) ∧
  pop_element _ = INR "pop_element"
End

val () = cv_auto_trans pop_element_def;

Definition assign_subscripts_def:
  assign_subscripts a [] (Replace v) = INL v ∧
  assign_subscripts a [] (Update bop v) = evaluate_binop bop a v ∧
  assign_subscripts a [] (AppendOp v) = append_element a v ∧
  assign_subscripts a [] PopOp = pop_element a ∧
  assign_subscripts a ((IntSubscript i)::is) ao =
  (case extract_elements a of SOME vs =>
   (case integer_index vs i of SOME j =>
    (case assign_subscripts (EL j vs) is ao of INL vj =>
       replace_elements a (TAKE j vs ++ [vj] ++ DROP (SUC j) vs)
     | INR err => INR err)
    | _ => INR "assign_subscripts integer_index")
   | _ => INR "assign_subscripts extract_elements") ∧
  assign_subscripts (StructV al) ((AttrSubscript id)::is) ao =
  (case ALOOKUP al id of SOME v =>
    (case assign_subscripts v is ao of INL v' =>
      INL $ StructV $ AFUPDKEY id (K v') al
     | INR err => INR err)
   | _ => INR "assign_subscripts AttrSubscript") ∧
  assign_subscripts _ _ _ = INR "assign_subscripts"
End

val assign_subscripts_pre_def = cv_auto_trans_pre assign_subscripts_def;

Theorem assign_subscripts_pre[cv_pre]:
  !a b c. assign_subscripts_pre a b c
Proof
  ho_match_mp_tac assign_subscripts_ind
  \\ rw[Once assign_subscripts_pre_def]
  \\ rw[Once assign_subscripts_pre_def]
  \\ gvs[integer_index_def] \\ rw[]
  \\ qmatch_asmsub_rename_tac`0i ≤ w`
  \\ Cases_on`w` \\ gs[]
QED

Definition evaluate_subscripts_def:
  evaluate_subscripts a [] = INL a ∧
  evaluate_subscripts a ((IntSubscript i)::is) =
  (case extract_elements a of SOME vs =>
   (case integer_index vs i of SOME j =>
    (case evaluate_subscripts (EL j vs) is of INL vj => INL vj
     | INR err => INR err)
    | _ => INR "evaluate_subscripts integer_index")
   | _ => INR "evaluate_subscripts extract_elements") ∧
  evaluate_subscripts (StructV al) ((AttrSubscript id)::is) =
  (case ALOOKUP al id of SOME v =>
    (case evaluate_subscripts v is of INL v' => INL v'
     | INR err => INR err)
   | _ => INR "evaluate_subscripts AttrSubscript") ∧
  evaluate_subscripts _ _ = INR "evaluate_subscripts"
End

val evaluate_subscripts_pre_def = cv_auto_trans_pre evaluate_subscripts_def;

Theorem evaluate_subscripts_pre[cv_pre]:
  !a b. evaluate_subscripts_pre a b
Proof
  ho_match_mp_tac evaluate_subscripts_ind
  \\ rw[Once evaluate_subscripts_pre_def]
  \\ rw[Once evaluate_subscripts_pre_def]
  \\ gvs[integer_index_def] \\ rw[]
  \\ qmatch_asmsub_rename_tac`0i ≤ w`
  \\ Cases_on`w` \\ gs[]
QED

Definition assign_hashmap_def:
  assign_hashmap _ _ hm [] _ = INR "assign_hashmap null" ∧
  assign_hashmap ts vt hm (k::ks) ao =
  (case ALOOKUP hm k
   of SOME (HashMap vt hm') =>
    (case assign_hashmap ts vt hm' ks ao of
     | INL hm' => INL $ (k, HashMap vt hm') :: (ADELKEY k hm)
     | INR err => INR err)
   | SOME (Value v) =>
    (case assign_subscripts v ks ao of
     | INL v' => INL $ (k, Value v') :: (ADELKEY k hm)
     | INR err => INR err)
   | NONE =>
     (case vt of HashMapT kt vt' =>
        (case assign_hashmap ts vt' [] ks ao of
         | INL hm' => INL $ (k, HashMap vt' hm') :: hm
         | INR err => INR err)
      | Type t =>
        (case assign_subscripts (default_value (type_env ts) t) ks ao of
         | INL v => INL $ (k, Value v) :: hm
         | INR err => INR err)))
End

val assign_hashmap_pre_def = cv_auto_trans_pre assign_hashmap_def;

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
  assign_toplevel ts (Value a) is ao =
    sum_map_left Value $ assign_subscripts a is ao ∧
  assign_toplevel ts (HashMap vt hm) is ao =
    sum_map_left (HashMap vt) $ assign_hashmap ts vt hm is ao
End

val () = assign_toplevel_def
  |> SRULE [oneline sum_map_left_def]
  |> cv_auto_trans;

Definition assign_target_def:
  assign_target cx (BaseTargetV (ScopedVar (pre,env,rest) id) is) ao = do
    ni <<- string_to_num id;
    a <- lift_option (FLOOKUP env ni) "assign_target lookup";
    a' <- lift_sum $ assign_subscripts a (REVERSE is) ao;
    set_scopes $ pre ++ env |+ (ni, a') :: rest;
    return $ Value a
  od ∧
  assign_target cx (BaseTargetV (TopLevelVar id) is) ao = do
    ni <<- string_to_num id;
    tv <- lookup_global cx ni;
    ts <- lift_option (get_self_code cx) "assign_target get_self_code";
    tv' <- lift_sum $ assign_toplevel ts tv (REVERSE is) ao;
    set_global cx ni tv';
    return tv
  od ∧
  assign_target cx (BaseTargetV (ImmutableVar id) is) ao = do
    ni <<- string_to_num id;
    imms <- get_immutables cx;
    a <- lift_option (FLOOKUP imms ni) "assign_target ImmutableVar";
    a' <- lift_sum $ assign_subscripts a (REVERSE is) ao;
    set_immutable cx ni a';
    return $ Value a
  od ∧
  assign_target _ _ _ = raise (Error "TODO: TupleTargetV")
End

val () = assign_target_def
  |> SRULE [FUN_EQ_THM, bind_def, LET_RATOR, ignore_bind_def,
            option_CASE_rator, lift_option_def]
  |> cv_auto_trans;

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
  expr_bound ts (Call (IntCall fn) es) =
    1 + exprs_bound ts es
      + (case ALOOKUP ts fn of NONE => 0 |
         SOME ss => stmts_bound (ADELKEY fn ts) ss) ∧
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

Definition remcode_def:
  remcode cx =
  case get_self_code cx of NONE => []
     | SOME ts => FILTER (λ(fn,ss). ¬MEM fn cx.stk)
          (FLAT (MAP dest_Internal_FunctionDef ts))
End

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

Definition scoped_var_target_def:
  scoped_var_target sc id n =
  case find_containing_scope n sc of NONE => NONE |
    SOME cs => SOME $ ScopedVar cs id
End

val () = cv_auto_trans scoped_var_target_def;

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
    vs <- eval_iterator cx it;
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long";
    (* TODO: check the type? *)
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
    n1 <- lift_option (dest_NumV v1) "start not NumV";
    tv2 <- eval_expr cx e2;
    v2 <- get_Value tv2;
    n2 <- lift_option (dest_NumV v2) "end not NumV";
    (* TODO: check e1 and e2 are same type? *)
    check (n1 < n2) "no range";
    return $ GENLIST (λn. IntV (Unsigned 256) &(n1 + n)) (n2 - n1)
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
    svo <<- scoped_var_target sc id n;
    ivo <- if cx.txn.is_creation
           then do imms <- get_immutables cx;
                   return $ immutable_target imms id n
                od
           else return NONE;
    v <- lift_sum $ exactly_one_option svo ivo;
    return $ (v, [])
  od ∧
  eval_base_target cx (TopLevelNameTarget id) =
    return $ (TopLevelVar id, []) ∧
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
  eval_expr cx (TopLevelName id) = lookup_global cx (string_to_num id) ∧
  eval_expr cx (FlagMember fid mid) = lookup_flag_mem cx fid mid ∧
  eval_expr cx (IfExp e1 e2 e3) = do
    tv <- eval_expr cx e1;
    switch_BoolV tv
      (eval_expr cx e2)
      (eval_expr cx e3)
  od ∧
  eval_expr cx (Literal l) = return $ Value $ evaluate_literal l ∧
  eval_expr cx (StructLit id kes) = do
    (* TODO: check argument lengths and types *)
    ks <<- MAP FST kes;
    vs <- eval_exprs cx (MAP SND kes);
    return $ Value $ StructV $ ZIP (ks, vs)
  od ∧
  eval_expr cx (Subscript e1 e2) = do
    tv1 <- eval_expr cx e1;
    tv2 <- eval_expr cx e2;
    v2 <- get_Value tv2;
    ts <- lift_option (get_self_code cx) "Subscript get_self_code";
    tv <- lift_sum $ evaluate_subscript ts tv1 v2;
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
    transfer_value cx.txn.sender toAddr amount;
    return $ Value $ NoneV
  od ∧
  eval_expr cx (Call (ExtCall _) _) = raise $ Error "TODO: ExtCall" ∧
  eval_expr cx (Call (IntCall fn) es) = do
    check (¬MEM fn cx.stk) "recursion";
    ts <- lift_option (get_self_code cx) "IntCall get_self_code";
    tup <- lift_option (lookup_function fn Internal ts) "IntCall lookup_function";
    args <<- FST $ SND tup; body <<- SND $ SND $ SND tup;
    check (LENGTH args = LENGTH es) "IntCall args length"; (* TODO: needed? *)
    vs <- eval_exprs cx es;
    env <- lift_option (bind_arguments args vs) "IntCall bind_arguments";
    prev <- get_scopes;
    cxf <- push_function fn env cx;
    rv <- finally
      (try (do eval_stmts cxf body; return NoneV od) handle_function)
      (pop_function prev);
    (* TODO: check return type? *)
    return $ Value rv
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
  \\ gvs[remcode_def, get_self_code_def, ADELKEY_def]
  \\ qpat_x_assum`OUTR _ _ = _`kall_tac
  \\ gvs[ALOOKUP_FILTER]
  \\ drule (SRULE [] lookup_function_Internal_imp_ALOOKUP_FLAT)
  \\ rw[FILTER_FILTER, LAMBDA_PROD]
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

Definition empty_globals_def:
  empty_globals = <|
    mutables := FEMPTY
  ; transients := []
  ; immutables := FEMPTY
  |>
End

Definition flag_value_def:
  flag_value n acc [] = StructV $ REVERSE acc ∧
  flag_value n acc (id::ids) =
  flag_value (2n*n) ((id,IntV (Unsigned 256) &n)::acc) ids
End

val () = cv_auto_trans flag_value_def;

(* TODO: assumes unique identifiers, but should check? *)
Definition initial_globals_def:
  initial_globals env [] = empty_globals ∧
  initial_globals env (VariableDecl _ Storage id typ :: ts) =
  (let gbs = initial_globals env ts in
   let key = string_to_num id in
     gbs with mutables updated_by
       (λm. m |+ (key, Value $ default_value env typ))) ∧
  initial_globals env (VariableDecl _ Transient id typ :: ts) =
  (let gbs = initial_globals env ts in
   let key = string_to_num id in
   let iv = Value $ default_value env typ in
     gbs with <|
       mutables updated_by (λm. m |+ (key, iv))
     ; transients updated_by (λtrs. (key,iv)::trs)
     |>) ∧
  initial_globals env (VariableDecl _ Immutable id typ :: ts) =
  (let gbs = initial_globals env ts in
   let key = string_to_num id in
     gbs with immutables updated_by
       (λim. im |+ (key, default_value env typ))) ∧
  (* TODO: prevent flag value being updated even in constructor *)
  initial_globals env (FlagDecl id ls :: ts) =
  (let gbs = initial_globals env ts in
   let key = string_to_num id in
     gbs with immutables updated_by
       (λim. im |+ (key, flag_value 1 [] ls))) ∧
  (* TODO: handle Constants? or ignore since assuming folded into AST *)
  initial_globals env (HashMapDecl _ is_transient id kt vt :: ts) =
  (let gbs = initial_globals env ts in
   let key = string_to_num id in
   let iv = HashMap vt [] in
   let gbs = gbs with mutables updated_by (λm. m |+ (key, iv)) in
     if is_transient
     then gbs with transients updated_by (λtrs. (key,iv)::trs)
     else gbs) ∧
  initial_globals env (t :: ts) = initial_globals env ts
End

val () = cv_auto_trans initial_globals_def;

Definition initial_evaluation_context_def:
  initial_evaluation_context srcs tx =
  <| sources := srcs
   ; txn := tx
   ; stk := [tx.function_name]
   |>
End

val () = cv_auto_trans initial_evaluation_context_def;

Datatype:
  abstract_machine = <|
    sources: (address, toplevel list) alist
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

Definition reset_transient_globals_def:
  reset_transient_globals gbs =
  gbs with mutables updated_by (λm. m |++ gbs.transients)
End

val () = cv_auto_trans reset_transient_globals_def;

Definition reset_all_transient_globals_def:
  reset_all_transient_globals [] = [] ∧
  reset_all_transient_globals ((k,v)::ls) =
    (k, reset_transient_globals v) ::
    reset_all_transient_globals ls
End

val () = cv_auto_trans reset_all_transient_globals_def;

Definition empty_state_def:
  empty_state : evaluation_state = <|
    accounts := empty_accounts;
    globals := [];
    logs := [];
    scopes := []
  |>
End

val () = cv_trans empty_state_def;

(* TODO: state should have other constants in scope? *)
Definition constants_env_def:
  constants_env [] = SOME FEMPTY ∧
  constants_env ((VariableDecl vis (Constant e) id typ)::ts) =
    (case FST $ eval_expr empty_evaluation_context e empty_state of
     | INL (Value v) => OPTION_MAP (λm. m |+ (string_to_num id, v)) (constants_env ts)
     | _ => NONE) ∧
  constants_env (t::ts) = constants_env ts
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
  call_external_function am cx mut ts args vals body =
  case bind_arguments args vals
  of NONE => (INR $ Error "call bind_arguments", am)
   | SOME env =>
  (case constants_env ts
   of NONE => (INR $ Error "call constants_env", am)
    | SOME cenv => (* TODO: how do we stop constants being assigned to? *)
   let st = initial_state am [env; cenv] in
   let srcs = am.sources in
   let (res, st) =
     (case do send_call_value mut cx; eval_stmts cx body od st
      of
       | (INL (), st) => (INL NoneV, abstract_machine_from_state srcs st)
       | (INR (ReturnException v), st) => (INL v, abstract_machine_from_state srcs st)
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
       call_external_function am cx mut ts args tx.args body
End

Definition load_contract_def:
  load_contract am tx ts =
  let addr = tx.target in
  let tenv = type_env ts in
  let gbs = initial_globals tenv ts in
  let am = am with globals updated_by CONS (addr, gbs) in
  case lookup_function tx.function_name Deploy ts of
     | NONE => INR $ Error "no constructor"
     | SOME (mut, args, ret, body) =>
       let cx = initial_evaluation_context ((addr,ts)::am.sources) tx in
       case call_external_function am cx mut ts args tx.args body
         of (INR e, _) => INR e
       (* TODO: update balances on return *)
          | (_, am) => INL (am with sources updated_by CONS (addr, ts))
End

val () = export_theory();
