open HolKernel boolLib bossLib Parse wordsLib blastLib dep_rewrite monadsyntax
     alistTheory rich_listTheory byteTheory finite_mapTheory
     arithmeticTheory combinTheory pairTheory whileTheory
     cv_typeTheory cv_stdTheory cv_transLib
open vfmTypesTheory vfmStateTheory vyperAstTheory

val () = new_theory "vyperInterpreter";

(* TODO: move *)

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
  default_value env (TupleT ts) = default_value_tuple env [] ts ∧
  default_value env (ArrayT _ (Dynamic n)) = ArrayV (Dynamic n) [] ∧
  default_value env (ArrayT t (Fixed n)) =
    ArrayV (Fixed n) (REPLICATE n (default_value env t)) ∧
  default_value env (StructT id) =
    (let nid = string_to_num id in
     case FLOOKUP env nid
       of NONE => StructV []
        | SOME args => default_value_struct (env \\ nid) [] args) ∧
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

Definition evaluate_binop_def:
  evaluate_binop (Add:binop) (IntV i1) (IntV i2) = INL (IntV (i1 + i2)) ∧
  evaluate_binop Sub (IntV i1) (IntV i2) = INL (IntV (i1 - i2)) ∧
  evaluate_binop Mul (IntV i1) (IntV i2) = INL (IntV (i1 * i2)) ∧
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

Datatype:
  evaluation_state = <|
    globals: (address, num |-> toplevel_value) alist
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

val toplevel_value_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="vyperInterpreter",Tyop="toplevel_value"}));

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

Definition is_ArrayT_def[simp]:
  is_ArrayT (ArrayT _ _) = T ∧
  is_ArrayT _ = F
End

val () = cv_auto_trans is_ArrayT_def;

Definition lookup_function_def:
  lookup_function name Deploy [] = SOME ([], NoneT, [Pass]) ∧
  lookup_function name vis [] = NONE ∧
  lookup_function name vis (FunctionDef fv fm id args ret body :: ts) =
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
  stmt_bound ts (For _ _ e n ss) =
    1 + expr_bound ts e +
    1 + n + n * (stmts_bound ts ss) ∧
  stmt_bound ts (Expr e) =
    1 + expr_bound ts e ∧
  stmts_bound ts [] = 0 ∧
  stmts_bound ts (s::ss) =
    1 + stmt_bound ts s
      + stmts_bound ts ss ∧
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
  expr_bound ts (IfExp e1 e2 e3) =
    1 + expr_bound ts e1
      + MAX (expr_bound ts e2)
            (expr_bound ts e3) ∧
  expr_bound ts (Subscript e1 e2) =
    1 + expr_bound ts e1
      + expr_bound ts e2 ∧
  expr_bound ts (Literal _) = 0 ∧
  expr_bound ts (ArrayLit _ es) =
    1 + exprs_bound ts es ∧
  expr_bound ts (Builtin _ es) =
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
  | INR (INR (INR (INR (INR (INR (ts, es)))))) =>
      SUM (MAP (list_size stmt_size o SND) ts) +
      list_size expr_size es
  | INR (INR (INR (INR (INR (INL (ts, e)))))) =>
      SUM (MAP (list_size stmt_size o SND) ts) +
      expr_size e
  | INR (INR (INR (INR (INL (ts, bt))))) =>
      SUM (MAP (list_size stmt_size o SND) ts) +
      base_assignment_target_size bt
  | INR (INR (INR (INL (ts, gs)))) =>
      SUM (MAP (list_size stmt_size o SND) ts) +
      list_size assignment_target_size gs
  | INR (INR (INL (ts, g))) =>
      SUM (MAP (list_size stmt_size o SND) ts) +
      assignment_target_size g
  | INR (INL (ts, ss)) =>
      SUM (MAP (list_size stmt_size o SND) ts) +
      list_size stmt_size ss
  | INL (ts, s) =>
      SUM (MAP (list_size stmt_size o SND) ts) +
      stmt_size s)’
  \\ rw[]
  \\ drule ALOOKUP_MEM
  \\ rw[ADELKEY_def]
  \\ qmatch_goalsub_abbrev_tac`MAP f (FILTER P ts)`
  \\ drule_then(qspecl_then[`f`,`P`]mp_tac) SUM_MAP_FILTER_MEM_LE
  \\ simp[Abbr`P`, Abbr`f`]
End

Definition dest_Internal_FunctionDef_def:
  dest_Internal_FunctionDef (FunctionDef Internal _ fn _ _ ss) = [(fn, ss)] ∧
  dest_Internal_FunctionDef _ = []
End

Definition remcode_def:
  remcode cx =
  case get_self_code cx of NONE => []
     | SOME ts => FILTER (λ(fn,ss). ¬MEM fn cx.stk)
          (FLAT (MAP dest_Internal_FunctionDef ts))
End

Theorem bind_cong[defncong]:
  (f s = f' s') ∧
  (∀x t. f s = (INL x, t) ==> g x t = g' x t) ∧
  (s = s')
  ⇒
  bind f g s = bind f' g' s'
Proof
  rw[bind_def] \\ CASE_TAC \\ CASE_TAC \\ gs[]
QED

Theorem bind_cong_implicit[defncong]:
  (f = f') ∧
  (∀s x t. f s = (INL x, t) ==> g x t = g' x t)
  ⇒
  bind f g = bind f' g'
Proof
  rw[bind_def, FUN_EQ_THM] \\ CASE_TAC \\ CASE_TAC \\ gs[]
  \\ first_x_assum irule \\ goal_assum drule
QED

(*
Theorem bind_cong_implicit_hyp[defncong]:
  (f = f') ∧
  (∀s x t. f s = (INL x, t) ==> g x = g' x)
  ⇒
  bind f g = bind f' g'
Proof
  rw[bind_def, FUN_EQ_THM] \\ CASE_TAC \\ CASE_TAC \\ gs[]
  \\ first_x_assum irule \\ goal_assum drule
QED
*)

Theorem ignore_bind_cong[defncong]:
  (f s = f' s') ∧
  (∀x t. f s = (INL x, t) ⇒ g t = g' t) ∧
  (s = s')
  ⇒
  ignore_bind f g s = ignore_bind f' g' s'
Proof
  rw[ignore_bind_def]
  \\ irule bind_cong
  \\ rw[]
QED

Theorem ignore_bind_cong_implicit[defncong]:
  (f = f') ∧
  (∀s x t. f s = (INL x, t) ⇒ g t = g' t)
  ⇒
  ignore_bind f g = ignore_bind f' g'
Proof
  rw[ignore_bind_def]
  \\ irule bind_cong_implicit
  \\ rw[]
  \\ first_x_assum irule
  \\ goal_assum drule
QED

(*
Theorem ignore_bind_cong_implicit_hyp[defncong]:
  (f = f') ∧
  (∀s x t. f s = (INL x, t) ⇒ g = g')
  ⇒
  ignore_bind f g = ignore_bind f' g'
Proof
  rw[ignore_bind_def]
  \\ irule bind_cong_implicit
  \\ rw[] \\ AP_THM_TAC
  \\ first_x_assum irule
  \\ goal_assum drule
QED
*)

Theorem try_cong[defncong]:
  (f s = f' s') ∧
  (∀e t. f s = (INR e, t) ⇒ h e t = h' e t) ∧
  (s = s')
  ⇒
  try f h s = try f' h' s'
Proof
  rw[try_def] \\ CASE_TAC \\ CASE_TAC \\ gs[]
QED

Theorem try_cong_implicit[defncong]:
  (f = f') ∧
  (∀s e t. f s = (INR e, t) ⇒ h e t = h' e t)
  ⇒
  try f h = try f' h'
Proof
  rw[FUN_EQ_THM]
  \\ irule try_cong \\ rw[]
  \\ first_x_assum irule
  \\ metis_tac[]
QED

(*
Theorem try_cong_implicit_hyp[defncong]:
  (f = f') ∧
  (∀s e t. f s = (INR e, t) ⇒ h e = h' e)
  ⇒
  try f h = try f' h'
Proof
  rw[FUN_EQ_THM]
  \\ irule try_cong \\ rw[]
  \\ first_x_assum irule
  \\ metis_tac[]
QED
*)

Theorem finally_cong[defncong]:
  (f s = f' s') ∧
  (∀x t. f s = (x, t) ⇒ g t = g' t) ∧
  (s = s')
  ⇒
  finally f g s = finally f' g' s'
Proof
  rw[finally_def]
  \\ CASE_TAC \\ CASE_TAC
  \\ irule ignore_bind_cong \\ gs[]
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
  eval_stmt cx (For id typ e n body) = do
    tv <- eval_expr cx e;
    v <- get_Value tv;
    vs <- lift_option (extract_elements v) "For not ArrayV";
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
  | INR (INR (INR (INR (INR (INR (INR (cx, es)))))))
    => exprs_bound (remcode cx) es
  | INR (INR (INR (INR (INR (INR (INL (cx, e)))))))
    => expr_bound (remcode cx) e
  | INR (INR (INR (INR (INR (INL (cx, nm, body, vs))))))
    => 1 + LENGTH vs + (LENGTH vs) * (stmts_bound (remcode cx) body)
  | INR (INR (INR (INR (INL (cx, t)))))
    => base_target_bound (remcode cx) t
  | INR (INR (INR (INL (cx, gs))))
    => targets_bound (remcode cx) gs
  | INR (INR (INL (cx, g)))
    => target_bound (remcode cx) g
  | INR (INL (cx, ss)) => stmts_bound (remcode cx) ss
  | INL (cx, s) => stmt_bound (remcode cx) s)’
  \\ rw[bound_def, MAX_DEF, MULT]
  >- (
    gvs[compatible_bound_def, check_def, assert_def]
    \\ qmatch_goalsub_abbrev_tac`(LENGTH vs) * x`
    \\ irule LESS_EQ_LESS_TRANS
    \\ qexists_tac`LENGTH vs + n * x + 1` \\ simp[]
    \\ metis_tac[MULT_COMM, LESS_MONO_MULT])
  \\ gvs[check_def, assert_def]
  \\ cheat (* congruence rules in function case ? *)
End

(*
  overall plan:
  - define the same functions as in evaluate_def, but with an additional
    continuation argument. make the state argument explicit.
  - whenever there's a recursive call, make it a tail call and store anything
    required for the remainder on top of the given continuation
  - whenever there's a return (or raise), call an "apply" function (these are
    additional compared to evaluate_def) that applies the continuation to the
    result (there will be a kind of apply function for each kind of result)
  - applying a continuation to a result that it doesn't expect is an error: find
    the results it could expect by looking at where it was created
*)

Datatype:
  eval_continuation
  = ReturnK eval_continuation
  | AssertK string eval_continuation
  | AnnAssignK identifier eval_continuation
  | AssignK expr eval_continuation
  | AssignK1 assignment_value eval_continuation
  | AugAssignK binop expr eval_continuation
  | AugAssignK1 base_target_value binop eval_continuation
  | IfK (stmt list) (stmt list) eval_continuation
  | IfK1 toplevel_value (stmt list) (stmt list) eval_continuation
  | IfK2 eval_continuation
  | ForK identifier num (stmt list) eval_continuation
  | ForK1 num (stmt list) (value list) eval_continuation
  | ExprK eval_continuation
  | StmtsK (stmt list) eval_continuation
  | BaseTargetK eval_continuation
  | TupleTargetK eval_continuation
  | TargetsK (assignment_target list) eval_continuation
  | TargetsK1 assignment_value eval_continuation
  | AttributeTargetK identifier eval_continuation
  | SubscriptTargetK expr eval_continuation
  | SubscriptTargetK1 base_target_value eval_continuation
  | IfExpK expr expr eval_continuation
  | ArrayLitK bound eval_continuation
  | SubscriptK expr eval_continuation
  | SubscriptK1 toplevel_value eval_continuation
  | AttributeK identifier eval_continuation
  | BuiltinK builtin eval_continuation
  | CallSendK eval_continuation
  | IntCallK identifier ((identifier # type) list) (stmt list) eval_continuation
  | IntCallK1 (scope list) eval_continuation
  | ExprsK (expr list) eval_continuation
  | ExprsK1 value eval_continuation
  | DoneK
End

Datatype:
  apply_base_continuation
  = Apply
  | ApplyExc exception
  | ApplyTarget assignment_value
  | ApplyTargets (assignment_value list)
  | ApplyBaseTarget base_target_value
  | ApplyTv toplevel_value
  | ApplyVal value
  | ApplyVals (value list)
End

Datatype:
  apply_continuation
  = AK evaluation_context apply_base_continuation
       evaluation_state eval_continuation
End

Definition liftk_def:
  liftk cx a (INL x, st) = AK cx (a x) (st:evaluation_state) ∧
  liftk cx a (INR (ex:exception), st) = AK cx (ApplyExc ex) st
End

val liftk1 = oneline liftk_def;

Definition no_recursion_def:
  no_recursion (fn:identifier) stk ⇔ ¬MEM fn stk
End

val () = cv_auto_trans no_recursion_def;

Definition eval_expr_cps_def:
  eval_expr_cps cx1 (Name id) st k =
    liftk cx1 ApplyTv
      (do env <- get_scopes;
          v <- lift_option (lookup_scopes (string_to_num id) env) "lookup Name";
          return $ Value v od st) k ∧
  eval_expr_cps cx2 (TopLevelName id) st k =
    liftk cx2 ApplyTv (lookup_global cx2 (string_to_num id) st) k ∧
  eval_expr_cps cx3 (IfExp e1 e2 e3) st k =
    eval_expr_cps cx3 e1 st (IfExpK e2 e3 k) ∧
  eval_expr_cps cx4 (Literal l) st k =
    AK cx4 (ApplyTv (Value $ evaluate_literal l)) st k ∧
  eval_expr_cps cx5 (ArrayLit b es) st k =
    (case check (compatible_bound b (LENGTH es)) "ArrayLit bound" st of
       (INR ex, st) => AK cx5 (ApplyExc ex) st k
     | (INL (), st) => eval_exprs_cps cx5 es st (ArrayLitK b k)) ∧
  eval_expr_cps cx6 (Subscript e1 e2) st k =
    eval_expr_cps cx6 e1 st (SubscriptK e2 k) ∧
  eval_expr_cps cx7 (Attribute e id) st k =
    eval_expr_cps cx7 e st (AttributeK id k) ∧
  eval_expr_cps cx8 (Builtin bt es) st k =
    (case check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" st of
       (INR ex, st) => AK cx8 (ApplyExc ex) st k
     | (INL (), st) => eval_exprs_cps cx8 es st (BuiltinK bt k)) ∧
  eval_expr_cps cx9 (Call Send es) st k =
    (case check (LENGTH es = 2) "Send args" st of
       (INR ex, st) => AK cx9 (ApplyExc ex) st k
     | (INL (), st) => eval_exprs_cps cx9 es st (CallSendK k)) ∧
  eval_expr_cps cx10 (Call (ExtCall _) _) st k =
    AK cx10 (ApplyExc (Error "TODO: ExtCall")) st k ∧
  eval_expr_cps cx10 (Call (IntCall fn) es) st k =
    (case do
      check (no_recursion fn cx10.stk) "recursion";
      ts <- lift_option (get_self_code cx10) "IntCall get_self_code";
      tup <- lift_option (lookup_function fn Internal ts) "IntCall lookup_function";
      args <<- FST tup; body <<- SND $ SND tup;
      check (LENGTH args = LENGTH es) "IntCall args length";
      return (args, body) od st
     of (INR ex, st) => AK cx10 (ApplyExc ex) st k
      | (INL (args, body), st) =>
          eval_exprs_cps cx10 es st (IntCallK fn args body k)) ∧
  eval_exprs_cps cx11 [] st k = AK cx11 (ApplyVals []) st k ∧
  eval_exprs_cps cx12 (e::es) st k =
    eval_expr_cps cx12 e st (ExprsK es k)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    | INL (cx,e,st,k) => expr_size e
    | INR (cx,es,st,k) => list_size expr_size es)’
End

val eval_expr_cps_pre_def = eval_expr_cps_def
   |> SRULE
        [liftk1, bind_def, ignore_bind_def,
         LET_RATOR, option_CASE_rator,
         sum_CASE_rator, prod_CASE_rator, lift_option_def]
   |> cv_auto_trans_pre;

Theorem eval_expr_cps_pre[cv_pre]:
  (∀a b c d. eval_expr_cps_pre a b c d) ∧
  (∀x y z w. eval_exprs_cps_pre x y z w)
Proof
  ho_match_mp_tac eval_expr_cps_ind \\ rw[]
  \\ rw[Once eval_expr_cps_pre_def]
  \\ gvs[CaseEq"prod", CaseEq"sum", CaseEq"option", raise_def, check_def]
  \\ first_x_assum irule
  \\ gvs[bind_def, ignore_bind_def, lift_option_def]
QED

Definition eval_base_target_cps_def:
  eval_base_target_cps cx (NameTarget id) st k =
    (let r = do
        sc <- get_scopes;
        n <<- string_to_num id;
        cs <- lift_option (find_containing_scope n sc) "NameTarget lookup";
        return $ (ScopedVar cs id, []) od st in
     liftk cx ApplyBaseTarget r k) ∧
  eval_base_target_cps cx (TopLevelNameTarget id) st k =
    AK cx (ApplyBaseTarget (TopLevelVar id, [])) st k ∧
  eval_base_target_cps cx (AttributeTarget t id) st k =
    eval_base_target_cps cx t st (AttributeTargetK id k) ∧
  eval_base_target_cps cx (SubscriptTarget t e) st k =
    eval_base_target_cps cx t st (SubscriptTargetK e k)
End

val () = eval_base_target_cps_def
  |> SRULE [bind_def, ignore_bind_def,
            LET_RATOR, lift_option_def,
            prod_CASE_rator, sum_CASE_rator,
            option_CASE_rator, liftk1]
  |> cv_auto_trans;

Definition eval_target_cps_def:
  eval_target_cps cx (BaseTarget t) st k =
    eval_base_target_cps cx t st (BaseTargetK k) ∧
  eval_target_cps cx (TupleTarget gs) st k =
    eval_targets_cps cx gs st (TupleTargetK k) ∧
  eval_targets_cps cx [] st k = AK cx (ApplyTargets []) st k ∧
  eval_targets_cps cx (g::gs) st k =
    eval_target_cps cx g st (TargetsK gs k)
End

val () = eval_target_cps_def |> cv_auto_trans;

Definition eval_stmt_cps_def:
  eval_stmt_cps cx Pass st k = AK cx Apply st k ∧
  eval_stmt_cps cx Continue st k = AK cx (ApplyExc ContinueException) st k ∧
  eval_stmt_cps cx Break st k = AK cx (ApplyExc BreakException) st k ∧
  eval_stmt_cps cx (Return NONE) st k = AK cx (ApplyExc (ReturnException NoneV)) st k ∧
  eval_stmt_cps cx (Return (SOME e)) st k = eval_expr_cps cx e st (ReturnK k) ∧
  eval_stmt_cps cx (Raise str) st k = AK cx (ApplyExc (AssertException str)) st k ∧
  eval_stmt_cps cx (Assert e str) st k = eval_expr_cps cx e st (AssertK str k) ∧
  eval_stmt_cps cx (AnnAssign id typ e) st k =
    eval_expr_cps cx e st (AnnAssignK id k) ∧
  eval_stmt_cps cx (Assign g e) st k =
    eval_target_cps cx g st (AssignK e k) ∧
  eval_stmt_cps cx (AugAssign t bop e) st k =
    eval_base_target_cps cx t st (AugAssignK bop e k) ∧
  eval_stmt_cps cx (If e ss1 ss2) st k =
    eval_expr_cps cx e st (IfK ss1 ss2 k) ∧
  eval_stmt_cps cx (For id typ e n body) st k =
    eval_expr_cps cx e st (ForK id n body k) ∧
  eval_stmt_cps cx (Expr e) st k =
    eval_expr_cps cx e st (ExprK k)
End

val () = cv_auto_trans eval_stmt_cps_def;

Definition eval_stmts_cps_def:
  eval_stmts_cps cx [] st k = AK cx Apply st k ∧
  eval_stmts_cps cx (s::ss) st k =
    eval_stmt_cps cx s st (StmtsK ss k)
End

val () = cv_auto_trans eval_stmts_cps_def;

Definition eval_for_cps_def:
  eval_for_cps cx nm body [] st k = AK cx Apply st k ∧
  eval_for_cps cx nm body (v::vs) st k =
  (case push_scope_with_var nm v st of
        (INR ex, st) => AK cx (ApplyExc ex) st k
      | (INL (), st) => eval_stmts_cps cx body st (ForK1 nm body vs k))
End

val () = cv_auto_trans eval_for_cps_def;

Definition apply_def:
  apply cx st (StmtsK ss k) =
    eval_stmts_cps cx ss st k ∧
  apply cx st (ForK1 nm body vs k) =
    (case pop_scope st
     of (INR ex, st) => AK cx (ApplyExc ex) st k
      | (INL (), st) => eval_for_cps cx nm body vs st k) ∧
  apply cx st (IfK2 k) =
    (case pop_scope st
     of (INR ex, st) => AK cx (ApplyExc ex) st k
      | (INL (), st) => AK cx Apply st k) ∧
  apply cx st (IfK1 (Value (BoolV b)) ss1 ss2 k) =
    eval_stmts_cps cx (if b then ss1 else ss2) st (IfK2 k) ∧
  apply cx st (IfK1 (Value _) ss1 ss2 k) =
    AK cx (ApplyExc $ Error "not BoolV") st (IfK2 k) ∧
  apply cx st (IfK1 _ ss1 ss2 k) =
    AK cx (ApplyExc $ Error "not Value") st (IfK2 k) ∧
  apply cx st (IntCallK1 prev k) =
    liftk (cx with stk updated_by TL) (ApplyTv o Value)
      (do pop_function prev; return NoneV od st) k ∧
  apply cx st DoneK = AK cx Apply st DoneK ∧
  apply cx st _ = AK cx (ApplyExc $ Error "apply k") st DoneK
End

val () = apply_def
  |> SRULE [liftk1, ignore_bind_def, bind_def, prod_CASE_rator, sum_CASE_rator]
  |> cv_auto_trans;

Definition apply_exc_def:
  apply_exc cx ex st (ReturnK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AssertK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AnnAssignK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AssignK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AssignK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AugAssignK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AugAssignK1 _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IfK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IfK1 _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IfK2 k) =
    (case pop_scope st
     of (INR ex, st) => AK cx (ApplyExc ex) st k
      | (INL (), st) => AK cx (ApplyExc ex) st k) ∧
  apply_exc cx ex st (ForK _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (ForK1 nm body vs k) =
    (case finally (handle_loop_exception ex) pop_scope st
     of (INR ex, st) => AK cx (ApplyExc ex) st k
      | (INL broke, st) =>
          if broke then AK cx Apply st k
          else eval_for_cps cx nm body vs st k) ∧
  apply_exc cx ex st (ExprK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (StmtsK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (BaseTargetK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (TupleTargetK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (TargetsK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (TargetsK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AttributeTargetK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (SubscriptTargetK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (SubscriptTargetK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IfExpK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (ArrayLitK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (SubscriptK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (SubscriptK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AttributeK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (BuiltinK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (CallSendK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IntCallK _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IntCallK1 prev k) =
    liftk (cx with stk updated_by TL) (ApplyTv o Value)
      (finally (handle_function ex) (pop_function prev) st)
      k ∧
  apply_exc cx ex st (ExprsK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (ExprsK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st DoneK = AK cx (ApplyExc ex) st DoneK
End

val () = apply_exc_def
  |> SRULE [finally_def, bind_def, ignore_bind_def,
            liftk1, prod_CASE_rator, sum_CASE_rator]
  |> cv_auto_trans;

Definition apply_targets_def:
  apply_targets cx gvs st (TargetsK1 gv k) =
    AK cx (ApplyTargets (gv::gvs)) st k ∧
  apply_targets cx gvs st (TupleTargetK k) =
      AK cx (ApplyTarget (TupleTargetV gvs)) st k ∧
  apply_targets cx _ st _ =
    AK cx (ApplyExc $ Error "apply_targets k") st DoneK
End

val () = cv_auto_trans apply_targets_def;

Definition apply_base_target_def:
  apply_base_target cx btv st (BaseTargetK k) =
    AK cx (ApplyTarget (BaseTargetV (FST btv) (SND btv))) st k ∧
  apply_base_target cx btv st (AttributeTargetK id k) =
    AK cx (ApplyBaseTarget (FST btv, AttrSubscript id :: SND btv)) st k ∧
  apply_base_target cx btv st (SubscriptTargetK e k) =
    eval_expr_cps cx e st (SubscriptTargetK1 btv k) ∧
  apply_base_target cx btv st (AugAssignK bop e k) =
    eval_expr_cps cx e st (AugAssignK1 btv bop k) ∧
  apply_base_target cx btv st DoneK = AK cx (ApplyBaseTarget btv) st DoneK ∧
  apply_base_target cx _ st _ =
    AK cx (ApplyExc $ Error "apply_base_target k") st DoneK
End

val () = cv_auto_trans apply_base_target_def;

Definition apply_target_def:
  apply_target cx gv st (AssignK e k) =
    eval_expr_cps cx e st (AssignK1 gv k) ∧
  apply_target cx gv st (TargetsK gs k) =
    eval_targets_cps cx gs st (TargetsK1 gv k) ∧
  apply_target cx gv st _ =
    AK cx (ApplyExc $ Error "apply_target k") st DoneK
End

val () = cv_auto_trans apply_target_def;

Definition apply_tv_def:
  apply_tv cx tv st (SubscriptK e k) =
    eval_expr_cps cx e st (SubscriptK1 tv k) ∧
  apply_tv cx tv st (IfK ss1 ss2 k) =
    liftk cx (K Apply) (push_scope st) (IfK1 tv ss1 ss2 k) ∧
  apply_tv cx tv st DoneK = AK cx (ApplyTv tv) st DoneK ∧
  apply_tv cx tv st k =
    liftk cx ApplyVal (get_Value tv st) k
End

val () = apply_tv_def
  |> SRULE [liftk1, prod_CASE_rator, sum_CASE_rator]
  |> cv_auto_trans;

Definition apply_val_def:
  apply_val cx v st (ReturnK k) = apply_exc cx (ReturnException v) st k ∧
  apply_val cx (BoolV T) st (AssertK str k) = apply cx st k ∧
  apply_val cx (BoolV F) st (AssertK str k) =
    apply_exc cx (AssertException str) st k ∧
  apply_val cx v st (AssertK _ k) = apply_exc cx (Error "not BoolV") st k ∧
  apply_val cx v st (AnnAssignK id k) =
    liftk cx (K Apply) (new_variable id v st) k ∧
  apply_val cx v st (AssignK1 gv k) =
    liftk cx (K Apply) (assign_target cx gv (Replace v) st) k ∧
  apply_val cx v st (AugAssignK1 (loc, sbs) bop k) =
    liftk cx (K Apply) (assign_target cx (BaseTargetV loc sbs) (Update bop v) st) k ∧
  apply_val cx v st (ForK id n body k) =
    (case do vs <- lift_option (extract_elements v) "For not ArrayV";
             check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long";
             return vs od st
     of (INR ex, st) => apply_exc cx ex st k
      | (INL vs, st) => eval_for_cps cx (string_to_num id) body vs st k) ∧
  apply_val cx v st (ExprK k) = apply cx st k ∧
  apply_val cx v st (SubscriptTargetK1 (loc, sbs) k) =
    (case lift_option (value_to_key v) "SubscriptTarget value_to_key" st
       of (INR ex, st) => apply_exc cx ex st k
        | (INL sk, st) => apply_base_target cx (loc, sk :: sbs) st k) ∧
  apply_val cx (BoolV T) st (IfExpK e2 e3 k) =
    eval_expr_cps cx e2 st k ∧
  apply_val cx (BoolV F) st (IfExpK e2 e3 k) =
    eval_expr_cps cx e3 st k ∧
  apply_val cx v st (IfExpK _ _ k) =
    apply_exc cx (Error "not BoolV") st k ∧
  apply_val cx v2 st (SubscriptK1 tv1 k) =
    liftk cx ApplyTv (lift_sum (evaluate_subscript tv1 v2) st) k ∧
  apply_val cx v st (AttributeK id k) =
    liftk cx (ApplyTv o Value) (lift_sum (evaluate_attribute v id) st) k ∧
  apply_val cx v st (ExprsK es k) =
    eval_exprs_cps cx es st (ExprsK1 v k) ∧
  apply_val cx v st DoneK = AK cx (ApplyVal v) st DoneK ∧
  apply_val cx v st _ =
    AK cx (ApplyExc $ Error "apply_val k") st DoneK
End

val () = apply_val_def
  |> SRULE [liftk1, prod_CASE_rator, sum_CASE_rator,
            option_CASE_rator, lift_option_def, lift_sum_def,
            bind_def, ignore_bind_def]
  |> cv_auto_trans;

Definition apply_vals_def:
  apply_vals cx vs st (ExprsK1 v k) =
    apply_vals cx (v::vs) st k ∧
  apply_vals cx vs st (ArrayLitK b k) =
    apply_tv cx (Value $ ArrayV b vs) st k ∧
  apply_vals cx vs st (BuiltinK bt k) =
    liftk cx ApplyTv (do
      acc <- get_accounts;
      v <- lift_sum $ evaluate_builtin cx acc bt vs;
      return $ Value v
    od st) k ∧
  apply_vals cx vs st (CallSendK k) =
    liftk cx ApplyTv (do
      check (LENGTH vs = 2) "CallSendK nargs";
      toAddr <- lift_option (dest_AddressV $ EL 0 vs) "Send not AddressV";
      amount <- lift_option (dest_NumV $ EL 1 vs) "Send not NumV";
      transfer_value cx.txn.sender toAddr amount;
      return $ Value NoneV
    od st) k ∧
  apply_vals cx vs st (IntCallK fn args body k) =
    (case do
      env <- lift_option (bind_arguments args vs) "IntCall bind_arguments";
      prev <- get_scopes;
      cxf <- push_function fn env cx;
      return (prev, cxf, body) od st
     of (INR ex, st) => apply_exc cx ex st k
      | (INL (prev, cxf, body), st) =>
          eval_stmts_cps cxf body st (IntCallK1 prev k)) ∧
  apply_vals cx vs st DoneK = AK cx (ApplyVals vs) st DoneK ∧
  apply_vals cx vs st _ =
    AK cx (ApplyExc $ Error "apply_vals k") st DoneK
End

val apply_vals_pre_def = apply_vals_def
  |> SRULE [liftk1, bind_def, ignore_bind_def, lift_option_def,
            lift_sum_def, prod_CASE_rator,
            sum_CASE_rator, option_CASE_rator]
  |> cv_auto_trans_pre;

Theorem apply_vals_pre[cv_pre]:
  ∀a b c d. apply_vals_pre a b c d
Proof
  ho_match_mp_tac apply_vals_ind \\ rw[]
  \\ rw[Once apply_vals_pre_def]
  \\ gvs[check_def, assert_def]
  \\ strip_tac \\ gvs[]
QED

Definition nextk_def[simp]:
  nextk (AK _ _ _ k) = k
End

val () = cv_auto_trans nextk_def;

Definition stepk_def:
  stepk (AK cx ak st k) =
  case ak of
     | Apply => apply cx st k
     | ApplyExc ex => apply_exc cx ex st k
     | ApplyTarget gv => apply_target cx gv st k
     | ApplyTargets gvs => apply_targets cx gvs st k
     | ApplyBaseTarget bv => apply_base_target cx bv st k
     | ApplyTv tv => apply_tv cx tv st k
     | ApplyVal v => apply_val cx v st k
     | ApplyVals vs => apply_vals cx vs st k
End

val () = cv_auto_trans stepk_def;

Definition cont_def:
  cont ak = OWHILE (λak. nextk ak ≠ DoneK) stepk ak
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

Theorem with_stk_updated_by_id[simp]:
  (cx with stk updated_by (λx. x)) = cx
Proof
  rw[theorem"evaluation_context_component_equality"]
QED

Theorem eval_cps_eq:
  (∀cx s st k.
     cont (eval_stmt_cps cx s st k) =
     cont ((
       case eval_stmt cx s st
         of (INL (), st1) => (AK cx Apply st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k)) ∧
  (∀cx ss st k.
     cont (eval_stmts_cps cx ss st k) =
     cont ((
       case eval_stmts cx ss st
         of (INL (), st1) => (AK cx Apply st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k)) ∧
  (∀cx g st k.
     cont (eval_target_cps cx g st k) =
     cont ((
       case eval_target cx g st
         of (INL gv, st1) => (AK cx (ApplyTarget gv) st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k)) ∧
  (∀cx gs st k.
     cont (eval_targets_cps cx gs st k) =
     cont ((
       case eval_targets cx gs st
         of (INL gvs, st1) => (AK cx (ApplyTargets gvs) st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k)) ∧
  (∀cx bt st k.
     cont (eval_base_target_cps cx bt st k) =
     cont ((
       case eval_base_target cx bt st
         of (INL bv, st1) => (AK cx (ApplyBaseTarget bv) st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k)) ∧
  (∀cx nm body vs st k.
     cont (eval_for_cps cx nm body vs st k) =
     cont ((
       case eval_for cx nm body vs st
         of (INL (), st1) => (AK cx Apply st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k)) ∧
  (∀cx e st k.
     cont (eval_expr_cps cx e st k) =
     cont ((
       case eval_expr cx e st
         of (INL tv, st1) => (AK cx (ApplyTv tv) st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k)) ∧
  (∀cx es st k.
     cont (eval_exprs_cps cx es st k) =
     cont ((
       case eval_exprs cx es st
         of (INL vs, st1) => (AK cx (ApplyVals vs) st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k))
Proof
  ho_match_mp_tac evaluate_ind
  \\ conj_tac >- rw[eval_stmt_cps_def, evaluate_def, return_def]
  \\ conj_tac >- rw[eval_stmt_cps_def, evaluate_def, raise_def]
  \\ conj_tac >- rw[eval_stmt_cps_def, evaluate_def, raise_def]
  \\ conj_tac >- rw[eval_stmt_cps_def, evaluate_def, raise_def]
  \\ conj_tac >- (
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- (
      rw[cont_def]
      \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def] )
    \\ rw[cont_def]
    \\ rw[Once OWHILE_THM, stepk_def]
    \\ rw[apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[raise_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def]
    \\ rw[Once OWHILE_THM, stepk_def, SimpRHS] \\ gvs[]
    \\ rw[apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def] )
  \\ conj_tac >- rw[eval_stmt_cps_def, evaluate_def, raise_def]
  \\ conj_tac >- (
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ reverse (Cases_on `x`) \\ simp[switch_BoolV_def, raise_def]
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ simp[return_def, Once OWHILE_THM, stepk_def]
    \\ rw[apply_val_def, return_def, raise_def]
    >- (
      rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
      \\ rw[apply_def]
      \\ rw[Once OWHILE_THM] )
    >- (
      rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
      \\ rw[apply_exc_def, Once OWHILE_THM] )
    >- (
      rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
      \\ Cases_on`v` \\ rw[apply_val_def, apply_exc_def]
      \\ rw[Once OWHILE_THM] ))
  \\ conj_tac >- (
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ reverse CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, liftk1, apply_val_def] )
  \\ conj_tac >- (
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_target_def]
    \\ gvs[cont_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_val_def, liftk1] )
  \\ conj_tac >- (
    rw[eval_stmt_cps_def, evaluate_def, bind_def, UNCURRY]
    \\ CASE_TAC \\ gs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_base_target_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ gvs[oneline get_Value_def, toplevel_value_CASE_rator,
           CaseEq"toplevel_value", CaseEq"prod", raise_def, return_def]
    \\ qmatch_goalsub_rename_tac`AugAssignK1 p` \\ Cases_on`p`
    >> rw[Once OWHILE_THM, stepk_def, apply_val_def, liftk1] )
  \\ conj_tac >- (
    rw[eval_stmt_cps_def, evaluate_def, bind_def, ignore_bind_def, UNCURRY]
    \\ CASE_TAC \\ gs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_def]
    \\ gvs[switch_BoolV_def]
    \\ IF_CASES_TAC \\ gvs[]
    >- (
      rw[apply_def, finally_def, bind_def, ignore_bind_def]
      \\ gvs[push_scope_def, return_def]
      \\ CASE_TAC \\ reverse CASE_TAC
      >- (
        rw[Once OWHILE_THM, stepk_def, apply_exc_def]
        \\ CASE_TAC \\ CASE_TAC \\ rw[raise_def] )
      \\ rw[Once OWHILE_THM, stepk_def, apply_def]
      \\ CASE_TAC \\ CASE_TAC )
    \\ IF_CASES_TAC \\ gvs[]
    >- (
      rw[apply_def, finally_def, bind_def, ignore_bind_def]
      \\ gvs[push_scope_def, return_def]
      \\ CASE_TAC \\ reverse CASE_TAC
      >- (
        rw[Once OWHILE_THM, stepk_def, apply_exc_def]
        \\ CASE_TAC \\ CASE_TAC \\ rw[raise_def] )
      \\ rw[Once OWHILE_THM, stepk_def, apply_def]
      \\ CASE_TAC \\ CASE_TAC )
    \\ qmatch_goalsub_abbrev_tac`Error str`
    \\ gvs[push_scope_def, return_def]
    \\ reverse $ Cases_on`x`
    \\ rw[apply_def, finally_def, raise_def, ignore_bind_def, bind_def]
    \\ gvs[]
    >- (
      rw[pop_scope_def, return_def]
      \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def]
      \\ rw[pop_scope_def, return_def] )
    \\ Cases_on `v` \\ rw[apply_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[pop_scope_def, return_def] )
  \\ conj_tac >- (
    rw[eval_stmt_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_val_def, bind_def, ignore_bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- (
      gvs[lift_option_def, option_CASE_rator, CaseEq"option",
          return_def, raise_def]
      \\ rw[Once OWHILE_THM, SimpRHS, stepk_def, apply_exc_def]
      \\ gvs[]
      \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def] )
    \\ CASE_TAC \\ reverse CASE_TAC
    >- (
      gvs[check_def, assert_def, raise_def]
      \\ rw[Once OWHILE_THM, SimpRHS, stepk_def, apply_exc_def]
      \\ gvs[]
      \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def] )
    \\ rw[return_def]
    \\ gvs[check_def, assert_def, raise_def] )
  \\ conj_tac >- (
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ rw[ignore_bind_def, bind_def, return_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def]
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def, apply_val_def]
    \\ gvs[] \\ rw[apply_def]
    \\ rw[Once OWHILE_THM, stepk_def] )
  \\ conj_tac >- rw[eval_stmts_cps_def, evaluate_def, return_def]
  \\ conj_tac >- (
    rw[eval_stmts_cps_def, evaluate_def, return_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_def]
    \\ cheat (* RESTRICTed defn appears in induction theorem... *)
    )
  \\ conj_tac >- (
    rw[eval_target_cps_def, evaluate_def, bind_def, return_def, UNCURRY]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_base_target_def] )
  \\ conj_tac >- (
    rw[eval_target_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_targets_def, return_def] )
  \\ conj_tac >- rw[eval_target_cps_def, evaluate_def, bind_def, return_def]
  \\ conj_tac >- (
    rw[eval_target_cps_def, evaluate_def, bind_def, return_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_target_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_targets_def] )
  \\ conj_tac >- rw[eval_base_target_cps_def, evaluate_def, liftk1]
  \\ conj_tac >- rw[eval_base_target_cps_def, evaluate_def, return_def]
  \\ conj_tac >- (
    rw[eval_base_target_cps_def, evaluate_def, bind_def, UNCURRY, return_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_base_target_def] )
  \\ conj_tac >- (
    rw[eval_base_target_cps_def, evaluate_def, bind_def, UNCURRY]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_base_target_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ qmatch_asmsub_rename_tac`get_Value tv`
    \\ Cases_on`tv` \\ gvs[get_Value_def, raise_def, return_def]
    \\ qmatch_goalsub_rename_tac`SubscriptTargetK1 p`
    \\ Cases_on`p`
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- (
      gvs[lift_option_def, option_CASE_rator, CaseEq"option",
          raise_def, return_def]
      \\ rw[Once OWHILE_THM, SimpRHS, stepk_def, apply_exc_def]
      \\ gvs[]
      \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def] )
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def, apply_exc_def]
    \\ gvs[]
    \\ rw[Once OWHILE_THM, stepk_def, apply_base_target_def] )
  \\ conj_tac >- rw[eval_for_cps_def, evaluate_def, return_def]
  \\ conj_tac >- (
    rw[eval_for_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC \\ gvs[]
    \\ first_assum drule \\ simp_tac std_ss [] \\ disch_then kall_tac
    \\ rw[finally_def, try_def, bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- (
      rw[Once OWHILE_THM, stepk_def, apply_exc_def, finally_def]
      \\ CASE_TAC \\ CASE_TAC
      \\ rw[ignore_bind_def, bind_def, return_def, raise_def]
      \\ CASE_TAC \\ CASE_TAC
      \\ rw[return_def]
      \\ last_x_assum drule \\ rw[] )
    \\ rw[return_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    \\ rw[return_def]
    \\ last_x_assum drule \\ rw[] )
  \\ conj_tac >- rw[eval_expr_cps_def, evaluate_def, liftk1]
  \\ conj_tac >- rw[eval_expr_cps_def, evaluate_def, liftk1]
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ simp[switch_BoolV_def]
    >> simp[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ IF_CASES_TAC \\ gvs[return_def]
    >- rw[Once OWHILE_THM, stepk_def, apply_val_def]
    \\ IF_CASES_TAC \\ gvs[return_def]
    >- rw[Once OWHILE_THM, stepk_def, apply_val_def]
    \\ simp[raise_def]
    \\ Cases_on`x` \\ gvs[return_def]
    >- (
      Cases_on`v`
      \\ rw[Once OWHILE_THM, stepk_def, apply_val_def, apply_exc_def]
      \\ rw[Once OWHILE_THM, SimpRHS, stepk_def, apply_exc_def]
      \\ gvs[]
      \\ rw[Once OWHILE_THM, stepk_def, apply_val_def, apply_exc_def] )
    \\ gvs[raise_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def, apply_exc_def] )
  \\ conj_tac >- rw[eval_expr_cps_def, evaluate_def, return_def]
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    \\ gvs[]
    \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[return_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_vals_def]
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def]
    \\ gvs[]
    \\ simp[apply_tv_def]
    \\ rw[Once OWHILE_THM, stepk_def] )
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_val_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    \\ rw[return_def] )
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_val_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    \\ rw[return_def] )
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    \\ gvs[] \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_vals_def, bind_def, liftk1] )
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    \\ gvs[] \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_vals_def,
          bind_def, ignore_bind_def, liftk1]
    \\ qmatch_goalsub_abbrev_tac`check b c d`
    \\ `check b c d = (INL (), d)`
    by (
      rw[check_def, assert_def, Abbr`b`]
      \\ drule eval_exprs_length
      \\ gvs[check_def, assert_def] )
    \\ rw[] )
  \\ conj_tac >- rw[eval_expr_cps_def, evaluate_def, raise_def]
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def,
       no_recursion_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    \\ reverse CASE_TAC
    >- CASE_TAC
    \\ reverse CASE_TAC
    \\ reverse CASE_TAC
    >- CASE_TAC
    \\ CASE_TAC
    \\ reverse CASE_TAC
    >- CASE_TAC
    \\ CASE_TAC
    \\ rw[return_def]
    \\ gvs[]
    \\ first_assum drule \\ simp_tac std_ss [] \\ disch_then kall_tac
    \\ CASE_TAC
    \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_vals_def, bind_def]
    \\ CASE_TAC
    \\ reverse CASE_TAC
    \\ reverse CASE_TAC
    >- (
      CASE_TAC
      \\ rw[Once OWHILE_THM, stepk_def, SimpRHS]
      \\ gvs[apply_exc_def] \\ rw[Once OWHILE_THM] )
    \\ reverse CASE_TAC
    >- (
      rw[Once OWHILE_THM, stepk_def, SimpRHS]
      \\ gvs[apply_exc_def] \\ rw[Once OWHILE_THM] )
    \\ reverse CASE_TAC
    \\ reverse CASE_TAC
    >- (
      rw[Once OWHILE_THM, stepk_def, SimpRHS]
      \\ gvs[apply_exc_def] \\ rw[Once OWHILE_THM] )
    \\ rw[return_def, finally_def, try_def, bind_def]
    \\ last_x_assum drule \\ simp_tac std_ss [] \\ disch_then kall_tac
    \\ reverse CASE_TAC
    \\ reverse CASE_TAC
    >- (
      rw[Once OWHILE_THM, stepk_def, apply_exc_def, liftk1, finally_def]
      \\ CASE_TAC \\ CASE_TAC \\ CASE_TAC \\ CASE_TAC
      \\ gvs[ignore_bind_def, bind_def, pop_function_def, return_def,
             set_scopes_def, lift_option_def, option_CASE_rator, CaseEq"option",
             raise_def, push_function_def, o_DEF] )
    \\ rw[Once OWHILE_THM, stepk_def, apply_def, liftk1]
    \\ CASE_TAC
    \\ reverse CASE_TAC
    \\ gvs[push_function_def, return_def, o_DEF] )
  \\ conj_tac >- rw[eval_expr_cps_def, evaluate_def, return_def]
  \\ rw[eval_expr_cps_def, evaluate_def, bind_def]
  \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
  >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
  >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
  \\ CASE_TAC \\ reverse CASE_TAC
  >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
  >> rw[Once OWHILE_THM, stepk_def, apply_val_def]
  \\ CASE_TAC \\ reverse CASE_TAC
  >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
  \\ rw[return_def]
  >> rw[Once OWHILE_THM, stepk_def, apply_vals_def]
  >> rw[Once OWHILE_THM, SimpRHS, stepk_def, apply_vals_def]
  \\ gvs[apply_vals_def]
  \\ rw[Once OWHILE_THM, stepk_def]
QED

Definition type_env_def:
  type_env [] = FEMPTY ∧
  type_env (StructDef id args :: ts) =
    type_env ts |+ (string_to_num id, args) ∧
  type_env (_ :: ts) = type_env ts
End

val () = cv_auto_trans type_env_def;

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
    scopes := []
  |>
End

val () = cv_trans empty_state_def;

Definition fromk_def[simp]:
  fromk (SOME (AK cx Apply st DoneK)) = (INL (), st) ∧
  fromk (SOME (AK cx (ApplyExc ex) st DoneK)) = (INR ex, st) ∧
  fromk _ = (INR $ Error "fromk", empty_state)
End

val () = cv_trans fromk_def;

Theorem cont_tr:
  cont ak = if nextk ak = DoneK then SOME ak else cont (stepk ak)
Proof
  simp[Once cont_def]
  \\ simp[Once OWHILE_THM]
  \\ IF_CASES_TAC \\ gs[]
  \\ simp[Once cont_def]
QED

val cont_tr_pre_def = cv_trans_pre cont_tr;

Theorem IS_SOME_cont:
  IS_SOME (cont ak) ⇔
  ∃n. nextk (FUNPOW stepk n ak) = DoneK
Proof
  rw[cont_def, OWHILE_def]
QED

Theorem cont_pre_IS_SOME_cont:
  cont_pre ak ⇔ IS_SOME (cont ak)
Proof
  EQ_TAC
  >- (
    qid_spec_tac`ak`
    \\ ho_match_mp_tac (theorem "cont_pre_ind")
    \\ rw[cont_def, OWHILE_def] \\ gs[]
    >- (
      first_x_assum(qspec_then`SUC n`mp_tac)
      \\ rw[FUNPOW] )
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ rw[] )
  \\ rw[IS_SOME_cont]
  \\ pop_assum mp_tac
  \\ qid_spec_tac`ak`
  \\ Induct_on`n` \\ rw[]
  >- rw[cont_tr_pre_def]
  \\ rw[Once cont_tr_pre_def]
  \\ first_x_assum irule
  \\ gs[FUNPOW]
QED

Theorem eval_stmts_eq_cont_cps:
  eval_stmts cx body st = fromk $ cont (eval_stmts_cps cx body st DoneK)
Proof
  Cases_on`eval_stmts cx body st`
  \\ qmatch_goalsub_rename_tac`res,st1`
  \\ qspecl_then[`cx`,`body`,`st`,`DoneK`]mp_tac(cj 2 eval_cps_eq)
  \\ simp[cont_def] \\ strip_tac
  \\ simp[Once OWHILE_THM]
  \\ IF_CASES_TAC
  >- (Cases_on `res` \\ gvs[])
  \\ CASE_TAC \\ simp[]
QED

val call_external_function_pre_def = call_external_function_def
     |> SRULE [eval_stmts_eq_cont_cps]
     |> cv_auto_trans_pre;

Theorem call_external_function_pre[cv_pre]:
  call_external_function_pre am cx args vals body
Proof
  rw[call_external_function_pre_def]
  \\ rw[cont_pre_IS_SOME_cont]
  \\ qmatch_goalsub_abbrev_tac`eval_stmts_cps cx ss st k`
  \\ qspecl_then[`cx`,`ss`,`st`,`k`]mp_tac  $ cj 2 eval_cps_eq
  \\ rw[]
  \\ CASE_TAC
  \\ CASE_TAC
  \\ rw[Abbr`k`, cont_def]
  \\ rw[Once OWHILE_THM]
QED

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

val () = cv_auto_trans call_external_def;

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

val () = cv_auto_trans load_contract_def;

val () = export_theory();
