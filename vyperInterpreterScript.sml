open HolKernel boolLib bossLib Parse wordsLib blastLib dep_rewrite monadsyntax
     alistTheory rich_listTheory byteTheory finite_mapTheory
     int_bitwiseTheory arithmeticTheory combinTheory pairTheory whileTheory
     cv_typeTheory cv_stdTheory cv_transLib
open vfmTypesTheory vfmStateTheory vyperAstTheory

val () = new_theory "vyperInterpreter";

(* TODO: move *)

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

Theorem INDEX_OF_pre[cv_pre]:
  INDEX_OF_pre x y
Proof
  qid_spec_tac`x`
  \\ Induct_on`y`
  \\ rw[Once INDEX_OF_pre_cases]
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

Theorem cv_ispair_cv_add[simp]:
  cv_ispair (cv_add x y) = Num 0
Proof
  Cases_on`x` \\ Cases_on`y` \\ rw[]
QED

Theorem c2n_cv_add[simp]:
  cv$c2n (cv_add v1 v2) = cv$c2n v1 + cv$c2n v2
Proof
  Cases_on`v1` \\ Cases_on`v2` \\ rw[]
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
  \\ rw[Once cv_size'_def, SimpRHS]
  \\ rw[Once cv_size'_def, SimpRHS]
  \\ rw[Once cv_size'_def]
QED

Theorem cv_size'_Num[simp]:
  cv_size' (Num m) = Num 0
Proof
  rw[Once cv_size'_def]
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
  | IntV int
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
  toplevel_value = Value value | HashMap ((subscript, toplevel_value) alist)
End

Type hmap = “:(subscript, toplevel_value) alist”

Definition default_value_def:
  default_value env (BaseT (UintT _)) = IntV 0 ∧
  default_value env (BaseT (IntT _)) = IntV 0 ∧
  default_value env (BaseT DecimalT) = IntV 0 ∧
  default_value env (TupleT ts) = default_value_tuple env [] ts ∧
  default_value env (ArrayT _ (Dynamic n)) = ArrayV (Dynamic n) [] ∧
  default_value env (ArrayT t (Fixed n)) =
    ArrayV (Fixed n) (REPLICATE n (default_value env t)) ∧
  default_value env (StructT id) =
    (let nid = string_to_num id in
     case FLOOKUP env nid
       of NONE => StructV []
        | SOME args => default_value_struct (env \\ nid) [] args) ∧
  default_value env (FlagT id) = IntV 0 ∧
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
       | INR (INL (env, _, ts)) => (CARD (FDOM env), type1_size ts)
       | INR (INR (env, _, ps)) => (CARD (FDOM env), type1_size (MAP SND ps)))’
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
  | TopLevelVar identifier
End

Datatype:
  assignment_value
  = BaseTargetV location (subscript list)
  | TupleTargetV (assignment_value list)
End

Type base_target_value = “:location # subscript list”;

Datatype:
  assign_operation = Replace value | Update binop value
End

Definition evaluate_literal_def:
  evaluate_literal (BoolL b)   = BoolV b ∧
  evaluate_literal (StringL n s) = StringV n s ∧
  evaluate_literal (BytesL b bs) = BytesV b bs ∧
  evaluate_literal (IntL i)    = IntV i
End

val () = cv_auto_trans evaluate_literal_def;

(* TODO: IntV should carry bounds info for overflow checking *)
(* TODO: add unsafe ops and make these ones safe *)

Definition evaluate_binop_def:
  evaluate_binop (Add:binop) (IntV i1) (IntV i2) = INL (IntV (i1 + i2)) ∧
  evaluate_binop Sub (IntV i1) (IntV i2) = INL (IntV (i1 - i2)) ∧
  evaluate_binop Mul (IntV i1) (IntV i2) = INL (IntV (i1 * i2)) ∧
  evaluate_binop Div (IntV i1) (IntV i2) = (if i2 = 0 then INR "Div0" else INL (IntV (i1 / i2))) ∧
  evaluate_binop Mod (IntV i1) (IntV i2) = (if i2 = 0 then INR "Mod0" else INL (IntV (i1 % i2))) ∧
  evaluate_binop Exp (IntV i1) (IntV i2) = (if i2 < 0 then INR "Exp~"
                                            else INL (IntV (i1 ** (Num i2)))) ∧
  evaluate_binop And (IntV i1) (IntV i2) = INL (IntV (int_and i1 i2)) ∧
  evaluate_binop  Or (IntV i1) (IntV i2) = INL (IntV (int_or i1 i2)) ∧
  evaluate_binop XOr (IntV i1) (IntV i2) = INL (IntV (int_xor i1 i2)) ∧
  evaluate_binop And (BoolV b1) (BoolV b2) = INL (BoolV (b1 ∧ b2)) ∧
  evaluate_binop  Or (BoolV b1) (BoolV b2) = INL (BoolV (b1 ∨ b2)) ∧
  evaluate_binop XOr (BoolV b1) (BoolV b2) = INL (BoolV (b1 ≠ b2)) ∧
  evaluate_binop ShL (IntV i1) (IntV i2) = (if i2 < 0 then INR "ShL0"
                                            else INL $ IntV $
                                                 int_shift_left (Num i2) i1) ∧
  evaluate_binop ShR (IntV i1) (IntV i2) = (if i2 < 0 then INR "ShR0"
                                            else INL $ IntV $
                                                 int_shift_right (Num i2) i1) ∧
  (* TODO: in *)
  evaluate_binop _ _ _ = INR "binop"
End

val () = cv_auto_trans evaluate_binop_def;

Datatype:
  call_txn = <|
    sender: address
  ; target: address
  ; function_name: identifier
  ; args: value list
  ; value: num
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

Definition evaluate_builtin_def:
  evaluate_builtin cx _ Len [BytesV _ ls] = INL (IntV &(LENGTH ls)) ∧
  evaluate_builtin cx _ Len [StringV _ ls] = INL (IntV &(LENGTH ls)) ∧
  evaluate_builtin cx _ Len [ArrayV _ ls] = INL (IntV &(LENGTH ls)) ∧
  evaluate_builtin cx _ Eq [StringV _ s1; StringV _ s2] = INL (BoolV (s1 = s2)) ∧
  evaluate_builtin cx _ Eq [BytesV _ s1; BytesV _ s2] = INL (BoolV (s1 = s2)) ∧
  evaluate_builtin cx _ Eq [BoolV b1; BoolV b2] = INL (BoolV (b1 = b2)) ∧
  evaluate_builtin cx _ Eq  [IntV i1; IntV i2] = INL (BoolV (i1 = i2)) ∧
  evaluate_builtin cx _ Lt  [IntV i1; IntV i2] = INL (BoolV (i1 < i2)) ∧
  evaluate_builtin cx _ Not [BoolV b] = INL (BoolV (¬b)) ∧
  evaluate_builtin cx _ Not [IntV i] =
    (if 0 ≤ i then INL (IntV (int_not i)) else INR "signed Not") ∧
  evaluate_builtin cx _ (Bop bop) [v1; v2] = evaluate_binop bop v1 v2 ∧
  evaluate_builtin cx _ (Msg Sender) [] = INL $ AddressV cx.txn.sender ∧
  evaluate_builtin cx _ (Msg SelfAddr) [] = INL $ AddressV cx.txn.target ∧
  evaluate_builtin cx _ (Msg ValueSent) [] = INL $ IntV &cx.txn.value ∧
  evaluate_builtin cx acc (Acc Balance) [BytesV _ bs] =
    (let a = lookup_account (word_of_bytes T (0w:address) bs) acc in
          INL (IntV &a.balance)) ∧
  evaluate_builtin _ _ _ _ = INR "builtin"
End

val () = cv_auto_trans evaluate_builtin_def;

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
  value_to_key (IntV i) = SOME $ IntSubscript i ∧
  value_to_key (StringV _ s) = SOME $ StrSubscript s ∧
  value_to_key (BytesV _ bs) = SOME $ BytesSubscript bs ∧
  value_to_key _ = NONE
End

val () = cv_auto_trans value_to_key_def;

Definition evaluate_subscript_def:
  evaluate_subscript (Value av) (IntV i) =
  (case extract_elements av of SOME vs =>
    (case integer_index vs i of SOME j => INL $ Value (EL j vs)
     | _ => INR "integer_index")
   | _ => INR "extract_elements") ∧
  evaluate_subscript (HashMap hm) kv =
  (case value_to_key kv of SOME k =>
    (case ALOOKUP hm k of SOME tv => INL tv
        | _ => INR "ALOOKUP HashMap")
   | _ => INR "evaluate_subscript value_to_key") ∧
  evaluate_subscript _ _ = INR "evaluate_subscript"
End

val evaluate_subscript_pre_def = cv_auto_trans_pre evaluate_subscript_def;

Theorem evaluate_subscript_pre[cv_pre]:
  evaluate_subscript_pre av v
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

Definition compatible_bound_def:
  compatible_bound (Fixed n) m = (n = m) ∧
  compatible_bound (Dynamic n) m = (m ≤ n)
End

val () = cv_auto_trans compatible_bound_def;

Definition builtin_args_length_ok_def:
  builtin_args_length_ok Len n = (n = 1n) ∧
  builtin_args_length_ok Not n = (n = 1) ∧
  builtin_args_length_ok Eq n = (n = 2) ∧
  builtin_args_length_ok Lt n = (n = 2) ∧
  builtin_args_length_ok (Bop _) n = (n = 2) ∧
  builtin_args_length_ok (Msg _) n = (n = 0) ∧
  builtin_args_length_ok (Acc _) n = (n = 1)
End

val () = cv_auto_trans builtin_args_length_ok_def;

Type log = “:identifier # (value list)”;

Datatype:
  evaluation_state = <|
    globals: (address, num |-> toplevel_value) alist
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
    case FLOOKUP gbs n
      of NONE => raise $ Error "lookup_global"
       | SOME v => return v
  od
End

val () = lookup_global_def
  |> SRULE [bind_def, FUN_EQ_THM, option_CASE_rator]
  |> cv_auto_trans;

Definition set_global_def:
  set_global cx n v = do
    gbs <- get_current_globals cx;
    set_current_globals cx $ gbs |+ (n,v)
  od
End

val () = set_global_def
  |> SRULE [bind_def, FUN_EQ_THM]
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

Definition dest_NumV_def:
  dest_NumV (IntV i) =
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
     | SOME i => return $ Value $ IntV $ &(2 ** i)
End

val () = lookup_flag_mem_def
  |> SRULE [FUN_EQ_THM, option_CASE_rator]
  |> cv_auto_trans;

Definition is_ArrayT_def[simp]:
  is_ArrayT (ArrayT _ _) = T ∧
  is_ArrayT _ = F
End

val () = cv_auto_trans is_ArrayT_def;

Definition lookup_function_def:
  lookup_function name Deploy [] = SOME ([], NoneT, [Pass]) ∧
  lookup_function name vis [] = NONE ∧
  lookup_function name vis (FunctionDecl fv fm id args ret body :: ts) =
  (if id = name ∧ vis = fv then SOME (args, ret, body)
   else lookup_function name vis ts) ∧
  lookup_function name External (VariableDecl Public _ id typ :: ts) =
  (if id = name ∧ ¬is_ArrayT typ then SOME ([], typ, [Return (SOME (TopLevelName id))])
   else lookup_function name External ts) ∧
 (* TODO: handle arrays, array of array, hashmap of array, etc. *)
 (* TODO
  lookup_function name External (HashMapDecl Public id kt vt :: ts) =
  (if id = name then SOME ([("], typ, [Return (SOME (TopLevelName "id"))])
   else lookup_function name External ts) ∧
 *)
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

Definition assign_subscripts_def:
  assign_subscripts a [] (Replace v) = INL v ∧
  assign_subscripts a [] (Update bop v) = evaluate_binop bop a v ∧
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
      INL $ StructV ((id,v')::(ADELKEY id al))
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

Definition assign_hashmap_def:
  assign_hashmap hm [] _ = INR "assign_hashmap null" ∧
  assign_hashmap hm [k] (Replace v) =
    INL $ (k,Value v)::(ADELKEY k hm) ∧
  assign_hashmap hm [k] (Update bop v2) =
  (case ALOOKUP hm k of SOME (Value v1) =>
     (case evaluate_binop bop v1 v2 of INL w =>
        INL $ (k,Value w)::(ADELKEY k hm) | INR err => INR err)
   | _ => INR "assign_hashmap Update not found") ∧
  assign_hashmap hm (k::ks) ao =
  (case ALOOKUP hm k of SOME (HashMap hm') =>
    (case assign_hashmap hm' ks ao of
     | INL hm' => INL $ (k, HashMap hm') :: (ADELKEY k hm)
     | INR err => INR err)
    | _ => INR "assign_hashmap HashMap not found")
End

val () = cv_auto_trans assign_hashmap_def;

Definition sum_map_left_def:
  sum_map_left f (INL x) = INL (f x) ∧
  sum_map_left _ (INR y) = INR y
End

Definition assign_toplevel_def:
  assign_toplevel (Value a) is ao =
    sum_map_left Value $ assign_subscripts a is ao ∧
  assign_toplevel (HashMap hm) is ao =
    sum_map_left HashMap $ assign_hashmap hm is ao
End

val () = assign_toplevel_def
  |> SRULE [oneline sum_map_left_def]
  |> cv_auto_trans;

Definition assign_target_def:
  assign_target cx (BaseTargetV (ScopedVar (pre,env,rest) id) is) ao = do
    ni <<- string_to_num id;
    a <- lift_option (FLOOKUP env ni) "assign_target lookup";
    a' <- lift_sum $ assign_subscripts a is ao;
    set_scopes $ pre ++ env |+ (ni, a') :: rest
  od ∧
  assign_target cx (BaseTargetV (TopLevelVar id) is) ao = do
    ni <<- string_to_num id;
    tv <- lookup_global cx ni;
    tv' <- lift_sum $ assign_toplevel tv is ao;
    set_global cx ni tv'
  od ∧
  assign_target _ _ _ = raise (Error "TODO: TupleTargetV")
End

val () = assign_target_def
  |> SRULE [FUN_EQ_THM, bind_def, LET_RATOR,
            option_CASE_rator, lift_option_def]
  |> cv_auto_trans;

Definition type_env_def:
  type_env [] = FEMPTY ∧
  type_env (StructDecl id args :: ts) =
    type_env ts |+ (string_to_num id, args) ∧
  type_env (_ :: ts) = type_env ts
End

val () = cv_auto_trans type_env_def;

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

Definition bound_def:
  stmt_bound ts Pass = 0n ∧
  stmt_bound ts Continue = 0 ∧
  stmt_bound ts Break = 0 ∧
  stmt_bound ts (Return NONE) = 0 ∧
  stmt_bound ts (Return (SOME e)) =
    1 + expr_bound ts e ∧
  stmt_bound ts (Raise _) = 0 ∧
  stmt_bound ts (Assert e _) =
    1 + expr_bound ts e ∧
  stmt_bound ts (Log _ es) =
    1 + exprs_bound ts es ∧
  stmt_bound ts (AnnAssign _ _ e) =
    1 + expr_bound ts e ∧
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
  expr_bound ts (ArrayLit _ es) =
    1 + exprs_bound ts es ∧
  expr_bound ts (StructLit _ kes) =
    1 + exprs_bound ts (MAP SND kes) ∧
  expr_bound ts (Builtin _ es) =
    1 + exprs_bound ts es ∧
  expr_bound ts (Empty _) = 0 ∧
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
  \\ rw[expr1_size_map, expr2_size_map, list_size_SUM_MAP, SUM_MAP_expr2_size,
        MAP_MAP_o]
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
  ∀fn vis ts x y z. vis = Internal ∧
  lookup_function fn vis ts = SOME (x,y,z) ⇒
  ALOOKUP (FLAT (MAP dest_Internal_FunctionDef ts)) fn = SOME z
Proof
  ho_match_mp_tac lookup_function_ind
  \\ rw[lookup_function_def, dest_Internal_FunctionDef_def]
  \\ Cases_on`fv` \\ gvs[dest_Internal_FunctionDef_def]
QED

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
  eval_stmt cx (Raise str) = raise $ AssertException str ∧
  eval_stmt cx (Assert e str) = do
    tv <- eval_expr cx e;
    switch_BoolV tv
      (return ())
      (raise $ AssertException str)
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
  eval_stmt cx (Assign g e) = do
    gv <- eval_target cx g;
    tv <- eval_expr cx e;
    v <- get_Value tv;
    assign_target cx gv (Replace v)
  od ∧
  eval_stmt cx (AugAssign t bop e) = do
    (loc, sbs) <- eval_base_target cx t;
    tv <- eval_expr cx e;
    v <- get_Value tv;
    assign_target cx (BaseTargetV loc sbs) (Update bop v)
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
    return $ GENLIST (λn. IntV &(n1 + n)) (n2 - n1)
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
    cs <- lift_option (find_containing_scope n sc) "NameTarget lookup";
    return $ (ScopedVar cs id, [])
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
    v <- lift_option (lookup_scopes (string_to_num id) env) "lookup Name";
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
  eval_expr cx (ArrayLit b es) = do
    check (compatible_bound b (LENGTH es)) "ArrayLit bound";
    vs <- eval_exprs cx es;
    return $ Value $ ArrayV b vs
  od ∧
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
    tv <- lift_sum $ evaluate_subscript tv1 v2;
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
  eval_expr cx (Empty typ) = do
    ts <- lift_option (get_self_code cx) "Empty get_self_code";
    return $ Value $ default_value (type_env ts) typ
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
    args <<- FST tup; body <<- SND $ SND tup;
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

(* TODO: assumes unique identifiers, but should check? *)
Definition initial_globals_def:
  initial_globals env [] = FEMPTY ∧
  initial_globals env (VariableDecl _ Storage id typ :: ts) =
  initial_globals env ts |+ (string_to_num id, Value $ default_value env typ) ∧
  initial_globals env (VariableDecl _ Transient id typ :: ts) =
  initial_globals env ts |+ (string_to_num id, Value $ default_value env typ) ∧
  (* TODO: handle Constants and  Immutables *)
  initial_globals env (HashMapDecl _ id kt vt :: ts) =
  initial_globals env ts |+ (string_to_num id, HashMap []) ∧
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
  ; globals: (address, num |-> toplevel_value) alist
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
  initial_state (am: abstract_machine) env : evaluation_state =
  <| accounts := am.accounts
   ; globals := am.globals
   ; logs := []
   ; scopes := [env]
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

Definition call_external_function_def:
  call_external_function am cx args vals body =
  case bind_arguments args vals
  of NONE => (INR $ Error "call bind_arguments", am)
   | SOME env =>
  (let st = initial_state am env in
   let srcs = am.sources in
   (case eval_stmts cx body st
    of
     | (INL (), st) => (INL NoneV, abstract_machine_from_state srcs st)
     | (INR (ReturnException v), st) => (INL v, abstract_machine_from_state srcs st)
     | (INR e, st) => (INR e, abstract_machine_from_state srcs st)))
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

Definition call_external_def:
  call_external am tx =
  let cx = initial_evaluation_context am.sources tx in
  case get_self_code cx
  of NONE => (INR $ Error "call get_self_code", am)
   | SOME ts =>
  case lookup_function tx.function_name External ts
  of NONE => (INR $ Error "call lookup_function", am)
   | SOME (args, ret, body) =>
       call_external_function am cx args tx.args body
End

Definition load_contract_def:
  load_contract am tx ts =
  let addr = tx.target in
  let tenv = type_env ts in
  let gbs = initial_globals tenv ts in
  let am = am with globals updated_by CONS (addr, gbs) in
  case lookup_function tx.function_name Deploy ts of
     | NONE => INR $ Error "no constructor"
     | SOME (args, ret, body) =>
       (* TODO: update balances on return *)
       let cx = initial_evaluation_context am.sources tx in
       case call_external_function am cx args tx.args body
         of (INR e, _) => INR e
          | (_, am) => INL (am with sources updated_by CONS (addr, ts))
End

val () = export_theory();
