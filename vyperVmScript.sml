open HolKernel boolLib bossLib Parse wordsLib dep_rewrite
open listTheory alistTheory finite_mapTheory arithmeticTheory
     numposrepTheory stringTheory combinTheory pred_setTheory
     cv_typeTheory cv_stdTheory cv_transLib
open vyperAstTheory vfmTypesTheory vfmContextTheory

val () = new_theory "vyperVm";

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

val () = cv_auto_trans sptreeTheory.size_def;

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

(* -- *)

Definition string_to_num_def:
  string_to_num s = l2n 257 (MAP (SUC o ORD) s)
End

Definition MAP_CHR_o_PRE_def:
  MAP_CHR_o_PRE [] acc = REVERSE acc ∧
  MAP_CHR_o_PRE (x::xs) acc =
  MAP_CHR_o_PRE xs (CHR(PRE x)::acc)
End

val MAP_CHR_o_PRE_pre_def = cv_auto_trans_pre MAP_CHR_o_PRE_def;

Theorem MAP_CHR_o_PRE_pre:
  EVERY ($> 257) v ==>
  MAP_CHR_o_PRE_pre v acc
Proof
  qid_spec_tac`acc` \\ Induct_on`v`
  \\ rw[Once MAP_CHR_o_PRE_pre_def]
QED

Theorem MAP_CHR_o_PRE:
  MAP_CHR_o_PRE ls acc = REVERSE acc ++ (MAP (CHR o PRE) ls)
Proof
  qid_spec_tac`acc` \\ Induct_on`ls`
  \\ rw[MAP_CHR_o_PRE_def]
QED

Definition num_to_string_def:
  num_to_string n =
  if n = 0 then "" else
  MAP (CHR o PRE) (n2l 257 n)
End

Theorem string_to_num_to_string:
  num_to_string (string_to_num s) = s
Proof
  simp[num_to_string_def, string_to_num_def, l2n_eq_0]
  \\ rw[EVERY_MAP]
  >- (
    qmatch_assum_abbrev_tac`EVERY P s`
    \\ `P = K F`
    by (
      rw[Abbr`P`, FUN_EQ_THM]
      \\ DEP_REWRITE_TAC[LESS_MOD]
      \\ rw[SUC_LT]
      \\ qexists_tac`256`
      \\ simp[ORD_BOUND] )
    \\ Cases_on`s` \\ gvs[] )
  \\ DEP_REWRITE_TAC[n2l_l2n]
  \\ simp[l2n_eq_0, EVERY_MAP]
  \\ DEP_REWRITE_TAC[LOG_l2n]
  \\ simp[EVERY_MAP, GREATER_DEF, MAP_TAKE, MAP_MAP_o, o_DEF]
  \\ Cases_on`s = []` \\ gvs[]
  \\ rw[SUC_LT, EVERY_MEM]
  \\ qexists_tac`256`
  \\ simp[ORD_BOUND]
QED

val () = cv_auto_trans string_to_num_def;

val num_to_string_pre_def = cv_auto_trans_pre (
  num_to_string_def
 |> REWRITE_RULE[
      MAP_CHR_o_PRE |> Q.GEN`acc` |> Q.SPEC`[]`
      |> SIMP_RULE std_ss [APPEND, REVERSE_DEF] |> SYM
    ] )

Theorem num_to_string_pre[cv_pre]:
  num_to_string_pre n
Proof
  rw[num_to_string_pre_def]
  \\ irule MAP_CHR_o_PRE_pre
  \\ irule n2l_BOUND
  \\ rw[]
QED

(*
Theorem num_to_string_inj:
  (* this is false because of 0 digits *)
  num_to_string x = num_to_string y ==> x = y
Proof
  simp[num_to_string_def]
  \\ qmatch_goalsub_abbrev_tac`n2l b`
  \\ pop_assum mp_tac
  \\ simp[markerTheory.Abbrev_def]
  \\ qid_spec_tac`y`
  \\ qid_spec_tac`x`
  \\ qid_spec_tac`b`
  \\ ho_match_mp_tac n2l_ind
  \\ rpt gen_tac \\ strip_tac
  \\ rpt gen_tac \\ strip_tac
  \\ gvs[]
  \\ rw[]
  >- rw[Once n2l_def]
  >- rw[Once n2l_def]
  \\ pop_assum mp_tac
  \\ rw[Once n2l_def]
  >- (
    Cases_on`x` \\ gvs[]
    \\ qpat_x_assum`n2l _ _ = _`mp_tac
    \\ rw[Once n2l_def]
    >- ( Cases_on`x0` \\ gvs[] )
    \\ rw[Once n2l_def] )
  \\ pop_assum mp_tac
  \\ simp[Once n2l_def, SimpRHS]
  \\ rw[]
  >- rw[Once n2l_def]
  \\ gs[]
  \\ qspec_then`257`mp_tac DIVISION
  \\ impl_tac >- rw[]
  \\ disch_then(fn th => qspec_then`x`mp_tac th \\ qspec_then`y`mp_tac th)
  \\ ntac 2 strip_tac
  \\ qpat_x_assum`x = _`SUBST1_TAC
  \\ qpat_x_assum`y = _`SUBST1_TAC
  \\ qmatch_goalsub_abbrev_tac`xd * _ + xm = yd * _ + ym`
  \\ `xd = yd ∧ xm = ym` suffices_by rw[]
  \\ `PRE xm < 256` by (Cases_on`xm` \\ gvs[])
  \\ `PRE ym < 256` by (Cases_on`ym` \\ gvs[])
  \\ gs[]
  \\ Cases_on`xm = 0` >- (
    gvs[Abbr`xm`, MOD_EQ_0_IFF]

  m``PRE 0``

*)

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

val from_to_value = cv_typeLib.from_to_thm_for “:value”;

Datatype:
  toplevel_value = Value value | HashMap ((value, toplevel_value) alist)
End

Type hmap = “:(value, toplevel_value) alist”

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
  default_value env (BaseT AddressT) = BytesV (Fixed 20) (REPLICATE 20 0w) ∧
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

val () = cv_trans_rec default_value_def (
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

val from_to_value_thm = cv_typeLib.from_to_thm_for “:value”;
val from_value = from_to_value_thm |> concl |> rator |> rand
val to_value = from_to_value_thm |> concl |> rand

(*
Definition from_scope_def:
  from_scope env = from_fmap ^from_value (env f_o num_to_string)
End

Definition to_scope_def:
  to_scope cv = to_fmap ^to_value cv f_o string_to_num
End

Theorem from_to_scope[cv_from_to]:
  from_to from_scope to_scope
Proof
  mp_tac $ MATCH_MP from_to_fmap from_to_value_thm
  \\ rw[from_to_def, from_scope_def, to_scope_def]
  \\ DEP_REWRITE_TAC[f_o_ASSOC]
  \\ rw[EQ_IMP_THM]
  >- cheat
  >- metis_tac[string_to_num_to_string]
  \\ irule (iffLR fmap_EQ_THM)
  \\ DEP_REWRITE_TAC[FDOM_f_o]
  \\ simp[o_DEF, string_to_num_to_string]
  \\ rw[]
  \\ DEP_REWRITE_TAC[FAPPLY_f_o]
  \\ simp[]
QED
*)

Definition lookup_scopes_def:
  lookup_scopes id [] = NONE ∧
  lookup_scopes id ((env: scope)::rest) =
  case FLOOKUP env id of NONE =>
    lookup_scopes id rest
  | SOME v => SOME v
End

Datatype:
  expr_continuation
  = StartExpr expr
  (*
  | NamedExprK1 expr_continuation expr
  | NamedExprK2 value expr_continuation
  *)
  | IfExpK expr_continuation expr expr
  | ArrayLitK bound (value list) expr_continuation (expr list)
  | SubscriptK1 expr_continuation expr
  | SubscriptK2 value expr_continuation
  | SubscriptMapK hmap expr_continuation
  | AttributeK expr_continuation identifier
  | BuiltinK builtin (value list) expr_continuation (expr list)
  | CallK call_target (value list) expr_continuation (expr list)
  | LiftCall call_target (value list) expr_continuation
  | DoneExpr value
  | DoneExprMap hmap
  | ReturnExpr
  | ErrorExpr string
End

Type containing_scope = “: scope list # scope # scope list”;

Datatype:
  location
  = ScopedVar containing_scope identifier
  | Global identifier
End

Datatype:
  subscript
  = IntSubscript int
  | StrSubscript string
  | AttrSubscript identifier
End

Datatype:
  assignment_value
  = BaseTargetV location (subscript list)
  | TupleTargetV (assignment_value list)
End

Datatype:
  base_tgt_continuation
  = StartBaseTgt base_assignment_target
  | SubscriptTargetK1 base_tgt_continuation expr
  | SubscriptTargetK2 location (subscript list) expr_continuation
  | AttributeTargetK base_tgt_continuation identifier
  | LiftCallBaseTgt call_target (value list) base_tgt_continuation
  | DoneBaseTgt location (subscript list)
  | ErrorBaseTgt string
End

Datatype:
  tgt_continuation
  = StartTgt assignment_target
  | TupleTargetK (assignment_value list) tgt_continuation (assignment_target list)
  | BaseTargetK base_tgt_continuation
  | LiftCallTgt call_target (value list) tgt_continuation
  | DoneTgt assignment_value
  | ErrorTgt string
End

Datatype:
  exception
  = RaiseException string
  | AssertException string
  | Error string
  | ExternalReturn value
End

Datatype:
  stmt_continuation
  = StartK stmt
  | ExprK expr_continuation
  | IfK expr_continuation (stmt list) (stmt list)
  | AssertK expr_continuation string
  | ReturnSomeK expr_continuation
  | AssignK1 tgt_continuation expr
  | AssignK2 assignment_value expr_continuation
  | AugAssignK1 base_tgt_continuation binop expr
  | AugAssignK2 location (subscript list) binop expr_continuation
  | AnnAssignK identifier type expr_continuation
  | ForK identifier type expr_continuation num (stmt list)
  | DoneK
  | ExceptionK exception
End

Definition evaluate_literal_def:
  evaluate_literal (BoolL b)   = BoolV b ∧
  evaluate_literal (StringL n s) = StringV n s ∧
  evaluate_literal (BytesL b bs) = BytesV b bs ∧
  evaluate_literal (IntL i)    = IntV i
End

val () = cv_auto_trans evaluate_literal_def;

Definition evaluate_binop_def:
  evaluate_binop (Add:binop) (IntV i1) (IntV i2) = DoneExpr (IntV (i1 + i2)) ∧
  evaluate_binop Sub (IntV i1) (IntV i2) = DoneExpr (IntV (i1 - i2)) ∧
  evaluate_binop Mul (IntV i1) (IntV i2) = DoneExpr (IntV (i1 * i2)) ∧
  evaluate_binop _ _ _ = ErrorExpr "binop"
End

val () = cv_auto_trans evaluate_binop_def;

Definition evaluate_builtin_def:
  evaluate_builtin Len [BytesV _ ls] = DoneExpr (IntV &(LENGTH ls)) ∧
  evaluate_builtin Len [StringV _ ls] = DoneExpr (IntV &(LENGTH ls)) ∧
  evaluate_builtin Len [ArrayV _ ls] = DoneExpr (IntV &(LENGTH ls)) ∧
  evaluate_builtin Eq [StringV _ s1; StringV _ s2] = DoneExpr (BoolV (s1 = s2)) ∧
  evaluate_builtin Eq [BytesV _ s1; BytesV _ s2] = DoneExpr (BoolV (s1 = s2)) ∧
  evaluate_builtin Eq [BoolV b1; BoolV b2] = DoneExpr (BoolV (b1 = b2)) ∧
  evaluate_builtin Eq  [IntV i1; IntV i2] = DoneExpr (BoolV (i1 = i2)) ∧
  evaluate_builtin Lt  [IntV i1; IntV i2] = DoneExpr (BoolV (i1 < i2)) ∧
  evaluate_builtin Not [BoolV b] = DoneExpr (BoolV (¬b)) ∧
  evaluate_builtin (Bop bop) [v1; v2] = evaluate_binop bop v1 v2 ∧
  evaluate_builtin _ _ = ErrorExpr "builtin"
End

val () = cv_auto_trans evaluate_builtin_def;

Definition extract_elements_def:
  extract_elements (ArrayV _ vs) = SOME vs ∧
  extract_elements _ = NONE
End

val () = cv_auto_trans extract_elements_def;

Definition replace_elements_def:
  replace_elements (ArrayV b _) vs = SOME (ArrayV b vs) ∧
  replace_elements _ _ = NONE
End

val () = cv_auto_trans replace_elements_def;

Definition integer_index_def:
  integer_index vs i =
   if Num i < LENGTH vs then
     SOME $ if 0 ≤ i then Num i else LENGTH vs - Num i
   else NONE
End

val () = cv_auto_trans integer_index_def;

Definition evaluate_subscript_def:
  evaluate_subscript av (IntV i) =
  (case extract_elements av of SOME vs =>
    (case integer_index vs i of SOME j => DoneExpr (EL j vs)
     | _ => ErrorExpr "integer_index")
   | _ => ErrorExpr "extract_elements") ∧
  evaluate_subscript _ _ = ErrorExpr "evaluate_subscript"
End

val evaluate_subscript_pre_def = cv_auto_trans_pre evaluate_subscript_def;

Theorem evaluate_subscript_pre[cv_pre]:
  evaluate_subscript_pre av v
Proof
  rw[evaluate_subscript_pre_def, integer_index_def]
  \\ rw[]
  \\ qmatch_asmsub_rename_tac`0i ≤ v0`
  \\ Cases_on`v0` \\ gs[]
QED

Definition evaluate_attribute_def:
  evaluate_attribute (StructV kvs) id =
  (case ALOOKUP kvs id of SOME v => DoneExpr v
   | _ => ErrorExpr "attribute") ∧
  evaluate_attribute _ _ = ErrorExpr "evaluate_attribute"
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
  builtin_args_length_ok (Msg _) n = (n = 0)
End

val () = cv_auto_trans builtin_args_length_ok_def;

Definition step_expr_def:
  step_expr gbs env (StartExpr (Literal l)) =
    DoneExpr (evaluate_literal l) ∧
  step_expr gbs env (StartExpr (ArrayLit b [])) = (
    if compatible_bound b 0
    then DoneExpr (ArrayV b [])
    else ErrorExpr "ArrayLit [] bound" ) ∧
  step_expr gbs env (StartExpr (ArrayLit b (e::es))) = (
    if compatible_bound b (LENGTH (e::es))
    then ArrayLitK b [] (StartExpr e) es
    else ErrorExpr "ArrayLit :: bound" ) ∧
  step_expr gbs env (StartExpr (Name id)) =
    (case lookup_scopes (string_to_num id) env
     of SOME v => DoneExpr v
      | _ => ErrorExpr "lookup_scopes") ∧
  step_expr gbs env (StartExpr (GlobalName id)) =
    (case FLOOKUP gbs (string_to_num id)
     of SOME (Value v) => DoneExpr v
      | SOME (HashMap ls) => DoneExprMap ls
      | _ => ErrorExpr "lookup gbs") ∧
  step_expr gbs env (StartExpr (Subscript e1 e2)) =
    SubscriptK1 (StartExpr e1) e2 ∧
  step_expr gbs env (StartExpr (Attribute e id)) =
    AttributeK (StartExpr e) id ∧
  step_expr gbs env (StartExpr (IfExp e1 e2 e3)) =
    IfExpK (StartExpr e1) e2 e3 ∧
  (* TODO: handle Msg builtins *)
  step_expr gbs env (StartExpr (Builtin bt [])) =
    ErrorExpr "builtin no args" ∧
  step_expr gbs env (StartExpr (Builtin bt (e::es))) = (
    if builtin_args_length_ok bt (LENGTH (e::es))
    then BuiltinK bt [] (StartExpr e) es
    else ErrorExpr "builtin args length" ) ∧
  step_expr gbs env (StartExpr (Call id [])) =
    LiftCall id [] ReturnExpr ∧
  step_expr gbs env (StartExpr (Call id (e::es))) =
    CallK id [] (StartExpr e) es ∧
  (*
  step_expr gbs env (NamedExprK1 k e) =
    (case step_expr gbs env k
     of ErrorExpr => ErrorExpr
      | DoneExpr v => NamedExprK2 v (StartExpr e)
      | LiftCall id vs k => LiftCall id vs (NamedExprK1 k e)
      | k => NamedExprK1 k e) ∧
  step_expr gbs env (NamedExprK2 v1 k) =
    (case step_expr gbs env k
     of ErrorExpr => ErrorExpr
      | DoneExpr v2 =>
  *)
  step_expr gbs env (IfExpK k e2 e3) =
  (case step_expr gbs env k
   of ErrorExpr msg => ErrorExpr msg
    | DoneExpr v1 => (case v1 of BoolV b => StartExpr (if b then e2 else e3)
                               | _ => ErrorExpr "IfExpK value")
    | LiftCall id vs k => LiftCall id vs (IfExpK k e2 e3)
    | k => IfExpK k e2 e3) ∧
  step_expr gbs env (ArrayLitK b vs k es) =
  (case step_expr gbs env k
   of ErrorExpr msg => ErrorExpr msg
    | DoneExpr v =>
        (case es of (e::es) => ArrayLitK b (SNOC v vs) (StartExpr e) es
                  | [] => DoneExpr (ArrayV b (SNOC v vs)))
    | LiftCall id as k => LiftCall id as (ArrayLitK b vs k es)
    | k => ArrayLitK b vs k es) ∧
  step_expr gbs env (SubscriptK1 k e) =
  (case step_expr gbs env k
   of ErrorExpr msg => ErrorExpr msg
    | DoneExpr v => SubscriptK2 v (StartExpr e)
    | DoneExprMap hm => SubscriptMapK hm (StartExpr e)
    | LiftCall id vs k => LiftCall id vs (SubscriptK1 k e)
    | k => SubscriptK1 k e) ∧
  step_expr gbs env (SubscriptK2 v1 k) =
  (case step_expr gbs env k
   of ErrorExpr msg => ErrorExpr msg
    | DoneExpr v2 => evaluate_subscript v1 v2
    | LiftCall id vs k => LiftCall id vs (SubscriptK2 v1 k)
    | k => SubscriptK2 v1 k) ∧
  step_expr gbs env (SubscriptMapK hm k) =
  (case step_expr gbs env k
   of ErrorExpr msg => ErrorExpr msg
    | DoneExpr v2 => (case ALOOKUP hm v2 of
                           SOME (Value v) => DoneExpr v
                           (* TODO: more hashmaps *)
                         | _ => ErrorExpr "SubscriptMapK lookup")
    | LiftCall id vs k => LiftCall id vs (SubscriptMapK hm k)
    | k => SubscriptMapK hm k) ∧
  step_expr gbs env (AttributeK k id) =
  (case step_expr gbs env k
   of ErrorExpr msg => ErrorExpr msg
    | DoneExpr v => evaluate_attribute v id
    | LiftCall fn vs k => LiftCall fn vs (AttributeK k id)
    | k => AttributeK k id) ∧
  step_expr gbs env (BuiltinK bt vs k es) =
  (case step_expr gbs env k
   of ErrorExpr msg => ErrorExpr msg
    | DoneExpr v1 =>
        (let vs = SNOC v1 vs in
         case es of (e::es) =>
           BuiltinK bt vs (StartExpr e) es
          | [] => evaluate_builtin bt vs)
    | LiftCall id ws k => LiftCall id ws (BuiltinK bt vs k es)
    | k => BuiltinK bt vs k es) ∧
  step_expr gbs env (CallK id vs k es) =
  (case step_expr gbs env k
   of ErrorExpr msg => ErrorExpr msg
    | DoneExpr v =>
        (let vs = SNOC v vs in
         case es of (e::es) => CallK id vs (StartExpr e) es
                  | [] => LiftCall id vs ReturnExpr)
    | LiftCall id ws k => LiftCall id ws (CallK id vs k es)
    | k => CallK id vs k es) ∧
  step_expr gbs env (LiftCall id vs k) = LiftCall id vs k ∧
  step_expr gbs env (DoneExpr v) = DoneExpr v ∧
  step_expr gbs env (DoneExprMap ls) = DoneExprMap ls ∧
  step_expr gbs env ReturnExpr = ReturnExpr ∧
  step_expr gbs env (ErrorExpr msg) = ErrorExpr msg
End

val () = cv_auto_trans step_expr_def;

Datatype:
  loop_info = <|
    loop_var: (* identifier *) num
  ; loop_first_stmt: stmt
  ; loop_rest_stmts: stmt list
  ; remaining_values: value list
  |>
End

Datatype:
  function_or_loop = Fn identifier | Loop loop_info
End

Datatype:
  function_context =
  <| scopes: scope list
   ; current_stmt: stmt_continuation
   ; remaining_stmts: stmt list
   ; name: function_or_loop
   |>
End

Definition initial_function_context_def:
  initial_function_context fn args ss = <|
    scopes := [args]
  ; current_stmt := (case ss of s::_ => StartK s
                        | _ => ExceptionK (Error "initial_function_context"))
  ; remaining_stmts := TL ss
  ; name := Fn fn
  |>
End

val () = cv_auto_trans initial_function_context_def;

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

Datatype:
  contract = <|
    src: toplevel list
  ; globals: (* identifier *) num |-> toplevel_value
  |>
End

Datatype:
  execution_context = <|
    current_fc : function_context
  ; call_stack : function_context list
  ; current_contract: contract
  |>
End

Datatype:
  machine_state = <|
    contracts : (address, contract) alist (* TODO: use a function (sptree under cv) *)
  |>
End

Definition initial_machine_state_def:
  initial_machine_state = <| contracts := [] |>
End

val () = cv_auto_trans initial_machine_state_def;

Definition type_env_def:
  type_env [] = FEMPTY ∧
  type_env (StructDef id args :: ts) =
    type_env ts |+ (string_to_num id, args) ∧
  type_env (_ :: ts) = type_env ts
End

val () = cv_auto_trans type_env_def;

Definition load_contract_def:
  load_contract ms a ts =
  (* TODO: take args and run Deploy function if any *)
  ms with contracts updated_by
    CONS (a, <|src := ts; globals := initial_globals (type_env ts) ts |>)
End

val () = cv_auto_trans load_contract_def;

Definition initial_execution_context_def:
  initial_execution_context c fc = <|
    current_fc := fc
  ; call_stack := []
  ; current_contract := c
  |>
End

val () = cv_auto_trans initial_execution_context_def;

Definition raise_def:
  raise err ctx = ctx with current_fc updated_by
    (λfc. fc with current_stmt := ExceptionK err)
End

val () = cv_auto_trans raise_def;

Definition push_scope_def:
  push_scope ctx =
    ctx with current_fc updated_by (λfc. fc with scopes updated_by CONS FEMPTY)
End

val () = cv_auto_trans push_scope_def;

Definition pop_scope_def:
  pop_scope ctx =
  case ctx.current_fc.scopes
    of [] => raise (Error "pop_scope") ctx
     | (_::rest) => ctx with current_fc updated_by (λfc. fc with scopes := rest)
End

val () = cv_auto_trans pop_scope_def;

Definition new_variable_def:
  new_variable id typ ctx =
  let tenv = type_env ctx.current_contract.src in
  case ctx.current_fc.scopes
    of [] => raise (Error "new_variable") ctx
     | env::rest =>
         if id ∈ FDOM env then raise (Error "var exists") ctx
         else ctx with current_fc updated_by
           (λfc. fc with scopes := (env |+ (id, default_value tenv typ))::rest)
End

val () = cv_auto_trans (REWRITE_RULE[TO_FLOOKUP]new_variable_def);

Definition find_containing_scope_def:
  find_containing_scope id [] = NONE : containing_scope option ∧
  find_containing_scope id (env::rest) =
  if id ∈ FDOM env then SOME ([], env, rest)
  else OPTION_MAP (λ(p,q). (env::p, q)) (find_containing_scope id rest)
End

val () = cv_auto_trans (REWRITE_RULE[TO_FLOOKUP]find_containing_scope_def);

Definition step_base_target_def:
  step_base_target gbs env (StartBaseTgt (NameTarget id)) =
    (case find_containing_scope (string_to_num id) env
     of SOME cs => DoneBaseTgt (ScopedVar cs id) []
      | _ => ErrorBaseTgt "step_base_target find_containing_scope" ) ∧
  step_base_target gbs env (StartBaseTgt (GlobalNameTarget id)) =
    DoneBaseTgt (Global id) [] ∧
  step_base_target gbs env (StartBaseTgt (SubscriptTarget t e)) =
    SubscriptTargetK1 (StartBaseTgt t) e ∧
  step_base_target gbs env (StartBaseTgt (AttributeTarget t id)) =
    AttributeTargetK (StartBaseTgt t) id ∧
  step_base_target gbs env (SubscriptTargetK1 k e) =
    (case step_base_target gbs env k of
     | DoneBaseTgt l s => SubscriptTargetK2 l s (StartExpr e)
     | LiftCallBaseTgt fn vs k => LiftCallBaseTgt fn vs (SubscriptTargetK1 k e)
     | ErrorBaseTgt msg => ErrorBaseTgt msg
     | k => SubscriptTargetK1 k e) ∧
  step_base_target gbs env (SubscriptTargetK2 l s k) =
   (case step_expr gbs env k
    of DoneExpr (IntV i) => DoneBaseTgt l ((IntSubscript i)::s)
     | DoneExpr _ => ErrorBaseTgt "SubscriptTargetK2 DoneExpr"
     | ErrorExpr msg => ErrorBaseTgt msg
     | LiftCall fn vs k => LiftCallBaseTgt fn vs (SubscriptTargetK2 l s k)
     | k => SubscriptTargetK2 l s k) ∧
  step_base_target gbs env (AttributeTargetK k id) =
  (case step_base_target gbs env k
   of ErrorBaseTgt msg => ErrorBaseTgt msg
    | DoneBaseTgt l s => DoneBaseTgt l ((AttrSubscript id)::s)
    | LiftCallBaseTgt fn vs k => LiftCallBaseTgt fn vs (AttributeTargetK k id)
    | k => AttributeTargetK k id) ∧
  step_base_target gbs env (LiftCallBaseTgt fn vs k) = LiftCallBaseTgt fn vs k ∧
  step_base_target gbs env (DoneBaseTgt l s) = DoneBaseTgt l s ∧
  step_base_target gbs env (ErrorBaseTgt msg) = ErrorBaseTgt msg
End

val () = cv_auto_trans step_base_target_def;

Definition step_target_def:
  step_target gbs env (StartTgt (BaseTarget b)) =
    BaseTargetK (StartBaseTgt b) ∧
  step_target gbs env (StartTgt (TupleTarget [])) =
    DoneTgt (TupleTargetV []) ∧
  step_target gbs env (StartTgt (TupleTarget (t::ts))) =
    TupleTargetK [] (StartTgt t) ts ∧
  step_target gbs env (TupleTargetK vs k ts) =
  (case step_target gbs env k
   of DoneTgt v =>
     (case ts of [] => DoneTgt (TupleTargetV (SNOC v vs))
               | (t::ts) => TupleTargetK (SNOC v vs) (StartTgt t) ts)
    | LiftCallTgt fn as k =>
        LiftCallTgt fn as (TupleTargetK vs k ts)
    | ErrorTgt msg => ErrorTgt msg
    | k => TupleTargetK vs k ts) ∧
  step_target gbs env (BaseTargetK k) =
  (case step_base_target gbs env k
   of DoneBaseTgt l s => DoneTgt $ BaseTargetV l s
    | LiftCallBaseTgt fn vs k => LiftCallTgt fn vs (BaseTargetK k)
    | ErrorBaseTgt msg => ErrorTgt msg
    | k => BaseTargetK k) ∧
  step_target gbs env (LiftCallTgt fn vs k) = LiftCallTgt fn vs k ∧
  step_target gbs env (DoneTgt v) = DoneTgt v ∧
  step_target gbs env (ErrorTgt msg) = ErrorTgt msg
End

val () = cv_auto_trans step_target_def;

Definition set_variable_def:
  set_variable id v ctx =
  case find_containing_scope id ctx.current_fc.scopes
    of NONE => raise (Error "find_containing_scope") ctx
     | SOME (pre, env, rest) =>
         (* check that v has same type as current value here ? *)
         ctx with current_fc updated_by
           (λfc. fc with scopes := pre ++ (env |+ (id, v))::rest)
End

val () = cv_auto_trans set_variable_def;

Datatype:
  assign_operation = Replace value | Update binop value
End

Definition assign_subscripts_def:
  assign_subscripts a [] (Replace v) = SOME v ∧
  assign_subscripts a [] (Update bop v) =
  (case evaluate_binop bop a v
     of DoneExpr w => SOME w
      | _ => NONE) ∧
  assign_subscripts a ((IntSubscript i)::is) ao =
  (case extract_elements a of SOME vs =>
   (case integer_index vs i of SOME j =>
    (case assign_subscripts (EL j vs) is ao of SOME vj =>
       replace_elements a (TAKE j vs ++ [vj] ++ DROP (SUC j) vs)
     | _ => NONE)
    | _ => NONE)
   | _ => NONE) ∧
  assign_subscripts _ _ _ = NONE (* TODO: handle AttrSubscript *)
End

val assign_subscripts_pre_def = cv_auto_trans_pre assign_subscripts_def;

Theorem assign_subscripts_pre[cv_pre]:
  !a b c. assign_subscripts_pre a b c
Proof
  ho_match_mp_tac assign_subscripts_ind
  \\ rw[Once assign_subscripts_pre_def]
  \\ rw[Once assign_subscripts_pre_def]
  \\ gvs[integer_index_def] \\ rw[]
  \\ qmatch_asmsub_rename_tac`0i ≤ v0`
  \\ Cases_on`v0` \\ gs[]
QED

Definition assign_target_def:
  assign_target (BaseTargetV (ScopedVar (pre,env,rest) id) is) ao ctx =
    (let nid = string_to_num id in
    (case FLOOKUP env nid of SOME a =>
     (case assign_subscripts a is ao of SOME a' =>
        ctx with current_fc updated_by
          (λfc. fc with scopes := pre ++ (env |+ (nid, a'))::rest)
      | _ => raise (Error "assign_subscripts ScopedVar") ctx)
     | _ => raise (Error "assign_target lookup") ctx)) ∧
  assign_target (BaseTargetV (Global id) is) ao ctx =
  (let nid = string_to_num id in
  (* TODO: add assignment to hashmaps *)
  (case FLOOKUP ctx.current_contract.globals nid of SOME (Value a) =>
   (case assign_subscripts a is ao of SOME a' =>
     ctx with current_contract updated_by
       (λcc. cc with globals := cc.globals |+ (nid, Value a'))
    | _ => raise (Error "assign_subscripts Global") ctx)
   | _ => raise (Error "assign_target globals lookup") ctx)) ∧
  assign_target _ _ ctx = raise (Error "TODO: TupleTargetV") ctx
End

val () = cv_auto_trans assign_target_def;

(* TODO: check types? *)
Definition bind_arguments_def:
  bind_arguments ([]: argument list) [] = SOME (FEMPTY: scope) ∧
  bind_arguments ((id, typ)::params) (v::vs) =
    OPTION_MAP (λm. m |+ (string_to_num id, v)) (bind_arguments params vs) ∧
  bind_arguments _ _ = NONE
End

val () = cv_auto_trans bind_arguments_def;

Definition is_ArrayT_def[simp]:
  is_ArrayT (ArrayT _ _) = T ∧
  is_ArrayT _ = F
End

Definition lookup_function_def:
  lookup_function name vis [] = NONE ∧
  lookup_function name vis (FunctionDef fv fm id args ret body :: ts) =
  (if id = name ∧ vis = fv then SOME (args, ret, body)
   else lookup_function name vis ts) ∧
  lookup_function name External (VariableDecl Public _ id typ :: ts) =
  (if id = name ∧ ¬is_ArrayT typ then SOME ([], typ, [Return (SOME (GlobalName id))])
   else lookup_function name External ts) ∧
 (* TODO: handle arrays, array of array, hashmap of array, etc. *)
 (* TODO
  lookup_function name External (HashMapDecl Public id kt vt :: ts) =
  (if id = name then SOME ([("], typ, [Return (SOME (GlobalName "id"))])
   else lookup_function name External ts) ∧
 *)
  lookup_function name vis (_ :: ts) =
    lookup_function name vis ts
End

val () = cv_auto_trans lookup_function_def;

Definition push_call_def:
  push_call ct args ctx =
  case ct of GlobalFn fn =>
    if ctx.current_fc.name = Fn fn ∨
       EXISTS (λfc. fc.name = Fn fn) ctx.call_stack
    then raise (Error "recursive call") ctx else (
    case lookup_function fn Internal ctx.current_contract.src of
    | SOME (params, ret, body) =>
      (case bind_arguments params args of
       | SOME env =>
           let fc = initial_function_context fn env body in
           ctx with <|
             call_stack updated_by CONS ctx.current_fc
           ; current_fc := fc |>
       | _ => raise (Error "bind_arguments") ctx)
    | _ => raise (Error "lookup_function Internal") ctx )
  | _ => raise (Error "unsupported call") ctx
End

val () = cv_auto_trans push_call_def;

Definition update_current_stmt_def:
  update_current_statement st ctx =
  ctx with current_fc updated_by
    (λfc. fc with current_stmt := st)
End

val () = cv_auto_trans update_current_stmt_def;

Definition return_expr_def:
  return_expr v (StartExpr _) = ErrorExpr "return StartExpr" ∧
  return_expr v (IfExpK k e1 e2) = IfExpK (return_expr v k) e1 e2  ∧
  return_expr v (ArrayLitK b vs k es) = ArrayLitK b vs (return_expr v k) es ∧
  return_expr v (SubscriptK1 k e) = SubscriptK1 (return_expr v k) e ∧
  return_expr v (SubscriptK2 w k) = SubscriptK2 w (return_expr v k) ∧
  return_expr v (SubscriptMapK h k) = SubscriptMapK h (return_expr v k) ∧
  return_expr v (AttributeK k id) = AttributeK (return_expr v k) id ∧
  return_expr v (BuiltinK bt vs k es) = BuiltinK bt vs (return_expr v k) es ∧
  return_expr v (CallK id vs k es) = CallK id vs (return_expr v k) es ∧
  return_expr v (LiftCall fn vs k) = LiftCall fn vs (return_expr v k) ∧
  return_expr v (DoneExpr _) = ErrorExpr "return DoneExpr" ∧
  return_expr v (DoneExprMap _) = ErrorExpr "return DoneExprMap" ∧
  return_expr v ReturnExpr = DoneExpr v ∧
  return_expr v (ErrorExpr msg) = ErrorExpr msg
End

val () = cv_auto_trans return_expr_def;

Definition return_base_tgt_def:
  return_base_tgt v (StartBaseTgt _) = ErrorBaseTgt "return_base_tgt Start" ∧
  return_base_tgt v (SubscriptTargetK1 k e) =
    SubscriptTargetK1 (return_base_tgt v k) e ∧
  return_base_tgt v (SubscriptTargetK2 l s k) =
    SubscriptTargetK2 l s (return_expr v k) ∧
  return_base_tgt v (AttributeTargetK k id) =
    AttributeTargetK (return_base_tgt v k) id ∧
  return_base_tgt v (LiftCallBaseTgt fn vs k) =
    LiftCallBaseTgt fn vs (return_base_tgt v k) ∧
  return_base_tgt _ (DoneBaseTgt _ _) = ErrorBaseTgt "return_base_tgt Done" ∧
  return_base_tgt _ (ErrorBaseTgt msg) = ErrorBaseTgt msg
End

val () = cv_auto_trans return_base_tgt_def;

Definition return_tgt_def:
  return_tgt v (StartTgt _) = ErrorTgt "return StartTgt" ∧
  return_tgt v (TupleTargetK vs k as) =
    TupleTargetK vs (return_tgt v k) as ∧
  return_tgt v (BaseTargetK t) =
    (case return_base_tgt v t of ErrorBaseTgt msg => ErrorTgt msg
        | t => BaseTargetK t) ∧
  return_tgt v (LiftCallTgt fn vs k) =
    LiftCallTgt fn vs (return_tgt v k) ∧
  return_tgt v (DoneTgt _) = ErrorTgt "return DoneTgt" ∧
  return_tgt v (ErrorTgt msg) = ErrorTgt msg
End

val () = cv_auto_trans return_tgt_def;

Definition return_def:
  return v (ForK id typ k n ss) = ForK id typ (return_expr v k) n ss ∧
  return v (IfK k s1 s2) = IfK (return_expr v k) s1 s2 ∧
  return v (AssertK k s) = AssertK (return_expr v k) s ∧
  return v (ReturnSomeK k) = ReturnSomeK (return_expr v k) ∧
  return v (AssignK1 t e) = AssignK1 (return_tgt v t) e ∧
  return v (AssignK2 a k) = AssignK2 a (return_expr v k) ∧
  return v (AugAssignK1 bt op e) = AugAssignK1 (return_base_tgt v bt) op e ∧
  return v (AugAssignK2 l sl op k) = AugAssignK2 l sl op (return_expr v k) ∧
  return v (AnnAssignK id typ k) = AnnAssignK id typ (return_expr v k) ∧
  return v (StartK _) = ExceptionK (Error "return StartK") ∧
  return v (ExprK k) = ExprK (return_expr v k) ∧
  return v (DoneK) = ExceptionK (Error "return DoneK") ∧
  return v (ExceptionK err) = ExceptionK (Error "return ExceptionK")
End

val () = cv_auto_trans return_def;

Definition pop_call_def:
  pop_call v ctx =
  case ctx.call_stack of fc::fcs =>
    if case fc.name of Loop _ => T | _ => F then
      pop_call v (ctx with call_stack := fcs)
    else
      ctx with <|
          current_fc := fc with current_stmt updated_by return v
        ; call_stack := fcs
        |>
  | _ => raise (ExternalReturn v) ctx
Termination
  WF_REL_TAC`measure (λx. LENGTH (SND x).call_stack)` \\ rw[]
End

val pop_call_pre_def = cv_auto_trans_pre pop_call_def;

Theorem pop_call_pre[cv_pre]:
  ∀v ctx. pop_call_pre v ctx
Proof
  ho_match_mp_tac pop_call_ind
  \\ rw[]
  \\ rw[Once pop_call_pre_def]
  \\ fs[]
  \\ qmatch_assum_abbrev_tac`pop_call_pre v c1`
  \\ qmatch_goalsub_abbrev_tac`pop_call_pre v c2`
  \\ `c1 = c2` suffices_by (rw[] \\ fs[])
  \\ rw[Abbr`c1`, Abbr`c2`]
  \\ CASE_TAC
  \\ rw[ theorem"execution_context_component_equality"]
QED

Definition set_stmt_def:
  set_stmt k ctx =
    ctx with current_fc updated_by (λfc. fc with current_stmt := k)
End

val () = cv_auto_trans set_stmt_def;

Definition exception_raised_def:
  exception_raised ctx <=>
  case ctx.current_fc.current_stmt of ExceptionK _ => T | _ => F
End

val () = cv_auto_trans exception_raised_def;

Definition push_loop_def:
  push_loop id typ (v::vs) (s::ss) ctx =
    ctx with <|
      call_stack updated_by CONS ctx.current_fc
    ; current_fc := <|
        scopes := (FEMPTY |+ (id,v))::ctx.current_fc.scopes
      ; current_stmt := (StartK s)
      ; remaining_stmts := ss
      ; name := Loop <|
          loop_var := id
        ; remaining_values := vs
        ; loop_first_stmt := s
        ; loop_rest_stmts := ss
        |>
      |>
    |> ∧
  push_loop _ _ [] (_::_) ctx = set_stmt DoneK ctx ∧
  push_loop _ _ _ _ ctx = raise (Error "push_loop") ctx
End

val () = cv_auto_trans push_loop_def;

Definition pop_loop_def:
  pop_loop ctx =
  case ctx.call_stack of
     | [] => raise (Error "pop_loop") ctx
     | fc::fcs => ctx with <|
         current_fc := (fc with <|
           current_stmt := DoneK (* check it was ForK? *)
         ; scopes := ctx.current_fc.scopes
             (* TODO: is this a reason to maybe not have a loop context?  *)
         |>)
       ; call_stack := fcs |>
End

val () = cv_auto_trans pop_loop_def;

Definition next_iteration_def:
  next_iteration lp ctx =
  case lp.remaining_values of [] => pop_loop ctx
     | v::vs => ctx with current_fc updated_by (λfc.
        fc with <| scopes updated_by CONS (FEMPTY |+ (lp.loop_var, v))
                 ; current_stmt := StartK lp.loop_first_stmt
                 ; remaining_stmts := lp.loop_rest_stmts
                 ; name := Loop (lp with remaining_values := vs) |>)
End

val () = cv_auto_trans next_iteration_def;

Definition continue_loop_def:
  continue_loop ctx =
  case ctx.current_fc.name of Loop lp => (
    let ctx = pop_scope ctx in
      if exception_raised ctx then ctx else
        next_iteration lp ctx
  ) | _ => raise (Error "continue_loop") ctx
End

val () = cv_auto_trans continue_loop_def;

Definition break_loop_def:
  break_loop ctx =
  case ctx.current_fc.name of Loop lp => (
    let ctx = pop_scope ctx in
      if exception_raised ctx then ctx else
        pop_loop ctx
  ) | _ => raise (Error "break_loop") ctx
End

val () = cv_auto_trans break_loop_def;

Definition next_stmt_def:
  next_stmt ctx =
  case ctx.current_fc.remaining_stmts of s::ss =>
    ctx with current_fc updated_by (λfc.
      fc with <| current_stmt := StartK s
               ; remaining_stmts := ss |>)
  | _ => (case ctx.current_fc.name
            of Fn _ => pop_call NoneV ctx
             | Loop lp =>
                 let ctx = pop_scope ctx in
                   if exception_raised ctx then ctx
                   else next_iteration lp ctx)
End

val () = cv_auto_trans next_stmt_def;

Definition step_stmt_def:
  step_stmt ctx =
  let fc = ctx.current_fc in
  let gbs = ctx.current_contract.globals in
  (case fc.current_stmt of
      | StartK Pass => set_stmt DoneK ctx
      | StartK Continue => continue_loop ctx
      | StartK Break => break_loop ctx
      | StartK (Expr e) => set_stmt (ExprK (StartExpr e)) ctx
      | StartK (Raise s) => raise (RaiseException s) ctx
      | StartK (Assert e s) => set_stmt (AssertK (StartExpr e) s) ctx
      | StartK (Return NONE) => pop_call NoneV ctx
      | StartK (Return (SOME e)) =>
          set_stmt (ReturnSomeK (StartExpr e)) ctx
      | StartK (AnnAssign id typ e) =>
          set_stmt (AnnAssignK id typ (StartExpr e)) ctx
      | StartK (AugAssign bt bop e) =>
          set_stmt (AugAssignK1 (StartBaseTgt bt) bop e) ctx
      | StartK (Assign tgt e) =>
          set_stmt (AssignK1 (StartTgt tgt) e) ctx
      | StartK (If e s1 s2) =>
          set_stmt (IfK (StartExpr e) s1 s2) ctx
      | StartK (For id typ e n s) =>
          set_stmt (ForK id typ (StartExpr e) n s) ctx
      | ExprK (DoneExpr _) => set_stmt DoneK ctx
      | ExprK (DoneExprMap _) => raise (Error "ExprK Map") ctx
      | ExprK (ErrorExpr msg) => raise (Error "ExprK err") ctx
      | ExprK (LiftCall fn vs k) =>
          push_call fn vs (set_stmt (ExprK k) ctx)
      | ExprK k => set_stmt (ExprK (step_expr gbs fc.scopes k)) ctx
      | IfK (DoneExpr (BoolV b)) s1 s2 => (
          case (if b then s1 else s2) of s::ss =>
            ctx with current_fc := fc with
              <| current_stmt := StartK s
               ; remaining_stmts updated_by (λx. ss ++ x) |>
          | _ => set_stmt DoneK ctx)
      | IfK (DoneExpr _) _ _ => raise (Error "IfK DoneExpr") ctx
      | IfK (DoneExprMap _) _ _ => raise (Error "IfK DoneExprMap") ctx
      | IfK (ErrorExpr msg) _ _ => raise (Error ("IfK " ++ msg)) ctx
      | IfK ReturnExpr _ _ => raise (Error "IfK ReturnExpr") ctx
      | IfK (LiftCall fn vs k) s1 s2 =>
          push_call fn vs
            (set_stmt (IfK k s1 s2) ctx)
      | IfK k s1 s2 =>
          set_stmt
            (IfK (step_expr gbs fc.scopes k) s1 s2) ctx
      | AssertK (DoneExpr (BoolV b)) s => (
          if b then set_stmt DoneK ctx
          else raise (AssertException s) ctx)
      | AssertK (DoneExpr _) _ => raise (Error "AssertK DoneExpr") ctx
      | AssertK (DoneExprMap _) _ => raise (Error "AssertK DoneExprMap") ctx
      | AssertK (ErrorExpr msg) _ => raise (Error "AssertK ErrorExpr") ctx
      | AssertK ReturnExpr _ => raise (Error "AssertK ReturnExpr") ctx
      | AssertK (LiftCall fn vs k) s =>
          push_call fn vs
            (set_stmt (AssertK k s) ctx)
      | AssertK k s =>
          set_stmt (AssertK (step_expr gbs fc.scopes k) s) ctx
      | ReturnSomeK (DoneExpr v) => pop_call v ctx
      | ReturnSomeK (DoneExprMap _) => raise (Error "ReturnSomeK Map") ctx
      | ReturnSomeK (ErrorExpr msg) => raise (Error ("ReturnSomeK " ++ msg)) ctx
      | ReturnSomeK ReturnExpr => raise (Error "ReturnSomeK ReturnExpr") ctx
      | ReturnSomeK (LiftCall fn vs k) =>
          push_call fn vs
            (set_stmt (ReturnSomeK k) ctx)
      | ReturnSomeK k =>
          set_stmt
            (ReturnSomeK (step_expr gbs fc.scopes k)) ctx
      | AssignK1 (DoneTgt av) e =>
          set_stmt (AssignK2 av (StartExpr e)) ctx
      | AssignK1 (ErrorTgt msg) e => raise (Error "AssignK1 err") ctx
      | AssignK1 (LiftCallTgt fn vs tk) e =>
          push_call fn vs
            (set_stmt (AssignK1 tk e) ctx)
      | AssignK1 tk e =>
          set_stmt
            (AssignK1 (step_target gbs fc.scopes tk) e) ctx
      | AssignK2 tv (DoneExpr v) =>
          let ctx = assign_target tv (Replace v) ctx in
            if exception_raised ctx then ctx else
              set_stmt DoneK ctx
      | AssignK2 tv (DoneExprMap _) => raise (Error "AssignK2 Map") ctx
      | AssignK2 tv (ErrorExpr msg) => raise (Error "AssignK2 err") ctx
      | AssignK2 tv ReturnExpr => raise (Error "AssignK2 ReturnExpr") ctx
      | AssignK2 tv (LiftCall fn vs k) =>
          push_call fn vs
            (set_stmt (AssignK2 tv k) ctx)
      | AssignK2 tv k =>
          set_stmt
            (AssignK2 tv (step_expr gbs fc.scopes k)) ctx
      | AugAssignK1 (DoneBaseTgt l sl) bop e =>
          set_stmt (AugAssignK2 l sl bop (StartExpr e)) ctx
      | AugAssignK1 (LiftCallBaseTgt fn vs bk) bop e =>
          push_call fn vs (set_stmt (AugAssignK1 bk bop e) ctx)
      | AugAssignK1 bk bop e =>
          set_stmt
            (AugAssignK1 (step_base_target gbs fc.scopes bk) bop e) ctx
      | AugAssignK2 l sl bop (DoneExpr v2) =>
          let ctx = assign_target (BaseTargetV l sl) (Update bop v2) ctx in
            if exception_raised ctx then ctx else set_stmt DoneK ctx
      | AugAssignK2 _ _ bop (DoneExprMap _) => raise (Error "AugAssignK Map") ctx
      | AugAssignK2 _ _ bop (ErrorExpr msg) => raise (Error "AugAssignK err") ctx
      | AugAssignK2 _ _ bop ReturnExpr => raise (Error "AugAssignK ReturnExpr") ctx
      | AugAssignK2 l sl bop (LiftCall fn vs k) =>
          push_call fn vs
            (set_stmt (AugAssignK2 l sl bop k) ctx)
      | AugAssignK2 l sl bop k =>
          set_stmt
            (AugAssignK2 l sl bop (step_expr gbs fc.scopes k)) ctx
      | AnnAssignK id typ (DoneExpr v) => (
          let nid = string_to_num id in
          let ctx = new_variable nid typ ctx in
            if exception_raised ctx then ctx else
              set_stmt DoneK (set_variable nid v ctx))
      | AnnAssignK id typ (DoneExprMap _) => raise (Error "AnnAssignK Map") ctx
      | AnnAssignK id typ (ErrorExpr msg) => raise (Error "AnnAssignK err") ctx
      | AnnAssignK id typ ReturnExpr => raise (Error "AnnAssignK ReturnExpr") ctx
      | AnnAssignK id typ (LiftCall fn vs k) =>
          push_call fn vs
            (set_stmt (AnnAssignK id typ k) ctx)
      | AnnAssignK id typ k =>
          set_stmt (AnnAssignK id typ (step_expr gbs fc.scopes k)) ctx
      | ExceptionK err => ctx
      | DoneK => next_stmt ctx
      | ForK id typ (DoneExpr (ArrayV _ [])) n (st::ss) =>
          set_stmt DoneK ctx
      | ForK id typ (DoneExpr (ArrayV _ vs)) n ss =>
          if LENGTH vs ≤ n then
            push_loop (string_to_num id) typ vs ss ctx
          else raise (Error "ForK bound") ctx
      | ForK id typ (DoneExpr _) _ _ => raise (Error "ForK DoneExpr") ctx
      | ForK id typ (DoneExprMap _) _ _ => raise (Error "ForK DoneExprMap") ctx
      | ForK id typ (ErrorExpr msg) _ _ => raise (Error "ForK err") ctx
      | ForK id typ ReturnExpr _ _ => raise (Error "ForK ReturnExpr") ctx
      | ForK id typ (LiftCall fn vs k) n ss =>
          push_call fn vs
            (set_stmt (ForK id typ k n ss) ctx)
      | ForK id typ k n ss =>
          set_stmt (ForK id typ (step_expr gbs fc.scopes k) n ss) ctx)
End

val () = cv_auto_trans step_stmt_def;

Definition expr_bound_def[simp]:
  expr_bound (Name _, fns) = (0n, fns) ∧
  expr_bound (GlobalName _, fns) = (0, fns) ∧
  expr_bound (IfExp e1 e2 e3, fns) = (
    let (n1, fns) = expr_bound (e1, fns) in
    let (n2, fns) = expr_bound (e2, fns) in
    let (n3, fns) = expr_bound (e3, fns) in
      (1 + n1 + MAX n2 n3, fns) ) ∧
  expr_bound (Literal _, fns) = (0, fns) ∧
  expr_bound (ArrayLit _ es, fns) = (
  let (ns, fns) = expr_bound_list (es, fns) in
    (1 + ns, fns) ) ∧
  expr_bound (Subscript e1 e2, fns) = (
  let (n1, fns) = expr_bound (e1, fns) in
  let (n2, fns) = expr_bound (e2, fns) in
    (1 + n1 + n2, fns) ) ∧
  expr_bound (Attribute e _, fns) = (
  let (n, fns) = expr_bound (e, fns) in
    (1 + n, fns) ) ∧
  expr_bound (Builtin _ es, fns) = (
  let (ns, fns) = expr_bound_list (es, fns) in
    (1 + ns, fns) ) ∧
  expr_bound (Call ct es, fns) = (
  let (ns, fns) = expr_bound_list (es, fns) in
    (1 + ns, (case ct of GlobalFn fn => fn INSERT fns | _ => fns)) ) ∧
  expr_bound_list ([], fns) = (0, fns) ∧
  expr_bound_list (e::es, fns) = (
  let (n, fns) = expr_bound (e, fns) in
  let (ns, fns) = expr_bound_list (es, fns) in
    (1 + n + ns, fns) )
Termination
  WF_REL_TAC`measure (λx.
    case x of INL (e, _) => expr_size e
            | INR (es, _) => expr1_size es)`
End

Definition exprk_bound_def[simp]:
  exprk_bound (StartExpr e, fns) = (
    let (n, fns) = expr_bound (e, fns) in
      (2 + n, fns)) ∧
  exprk_bound (IfExpK k e1 e2, fns) = (
    let (n, fns) = exprk_bound (k, fns) in
    let (n1, fns) = expr_bound (e1, fns) in
    let (n2, fns) = expr_bound (e2, fns) in
      (1 + n + n2 + n2, fns)) ∧
  exprk_bound (ArrayLitK _ _ k es, fns) = (
    let (n, fns) = exprk_bound (k, fns) in
    let (ns, fns) = expr_bound_list (es, fns) in
      (1 + n + ns, fns)) ∧
  exprk_bound (SubscriptK1 k e, fns) = (
    let (n, fns) = exprk_bound (k, fns) in
    let (ne, fns) = expr_bound (e, fns) in
      (1 + n + ne, fns)) ∧
  exprk_bound (SubscriptK2 _ k, fns) = (
    let (n, fns) = exprk_bound (k, fns) in
      (1 + n, fns)) ∧
  exprk_bound (SubscriptMapK _ k, fns) = (
    let (n, fns) = exprk_bound (k, fns) in
      (1 + n, fns)) ∧
  exprk_bound (AttributeK k _, fns) = (
    let (n, fns) = exprk_bound (k, fns) in
      (1 + n, fns)) ∧
  exprk_bound (BuiltinK _ _ k es, fns) = (
    let (n, fns) = exprk_bound (k, fns) in
    let (ns, fns) = expr_bound_list (es, fns) in
      (1 + n + ns, fns)) ∧
  exprk_bound (CallK _ _ k es, fns) = (
    let (n, fns) = exprk_bound (k, fns) in
    let (ns, fns) = expr_bound_list (es, fns) in
      (1 + n + ns, fns)) ∧
  exprk_bound (LiftCall _ _ k, fns) = (
    let (n, fns) = exprk_bound (k, fns) in
      (1 + n, fns)) ∧
  exprk_bound (DoneExpr _, fns) = (1, fns) ∧
  exprk_bound (DoneExprMap _, fns) = (1, fns) ∧
  exprk_bound (ReturnExpr, fns) = (1, fns) ∧
  exprk_bound (ErrorExpr _, fns) = (1, fns)
End

Definition base_tgt_bound_def[simp]:
  base_tgt_bound (AttributeTarget t _, fns) =(
  let (nt, fns) = base_tgt_bound (t, fns) in
    (1 + nt, fns)) ∧
  base_tgt_bound (SubscriptTarget t e, fns) = (
  let (nt, fns) = base_tgt_bound (t, fns) in
  let (ne, fns) = expr_bound (e, fns) in
    (1 + nt + ne, fns)) ∧
  base_tgt_bound (_, fns) = (1n, fns)
End

Definition tgt_bound_def[simp]:
  tgt_bound (BaseTarget t, fns) = (
  let (n, fns) = base_tgt_bound (t, fns) in
    (1 + n, fns)) ∧
  tgt_bound (TupleTarget ts, fns) = (
  let (ns, fns) = tgt_bound_list (ts, fns) in
    (1 + ns, fns)) ∧
  tgt_bound_list ([], fns) = (0, fns) ∧
  tgt_bound_list ((t::ts), fns) = (
  let (n, fns) = tgt_bound (t, fns) in
  let (ns, fns) = tgt_bound_list (ts, fns) in
    (1 + n + ns, fns))
Termination
  WF_REL_TAC`measure (λx.
    case x of INR (x, _) => assignment_target1_size x
       | INL (x, _) => assignment_target_size x)`
End

Definition base_tgtk_bound_def[simp]:
  base_tgtk_bound (StartBaseTgt t, fns) = (
  let (n, fns) = base_tgt_bound (t, fns) in
    (2 + n, fns)) ∧
  base_tgtk_bound (SubscriptTargetK1 k e, fns) = (
  let (n, fns) = base_tgtk_bound (k, fns) in
  let (ne, fns) = expr_bound (e, fns) in
    (1 + n + ne, fns)) ∧
  base_tgtk_bound (SubscriptTargetK2 _ _ k, fns) = (
  let (n, fns) = exprk_bound (k, fns) in
    (1 + n, fns)) ∧
  base_tgtk_bound (AttributeTargetK k _, fns) = (
  let (n, fns) = base_tgtk_bound (k, fns) in
    (1 + n, fns)) ∧
  base_tgtk_bound (LiftCallBaseTgt _ _ k, fns) = (
  let (n, fns) = base_tgtk_bound (k, fns) in
    (1 + n, fns)) ∧
  base_tgtk_bound (_, fns) = (1, fns)
End

Definition tgtk_bound_def[simp]:
  tgtk_bound (StartTgt t, fns) = (
  let (n, fns) = tgt_bound (t, fns) in
    (2 + n, fns)) ∧
  tgtk_bound (TupleTargetK _ k ts, fns) = (
  let (n, fns) = tgtk_bound (k, fns) in
  let (ns, fns) = tgt_bound_list (ts, fns) in
    (1 + n + ns, fns)) ∧
  tgtk_bound (BaseTargetK bk, fns) = (
  let (n, fns) = base_tgtk_bound (bk, fns) in
    (1 + n, fns)) ∧
  tgtk_bound (LiftCallTgt _ _ k, fns) = (
  let (n, fns) = tgtk_bound (k, fns) in
    (1 + n, fns)) ∧
  tgtk_bound (_, fns) = (1, fns)
End

Definition stmt_bound_def[simp]:
  stmt_bound (Pass, fns) = (1n, fns) ∧
  stmt_bound (Continue, fns) = (1, fns) ∧
  stmt_bound (Break, fns) = (1, fns) ∧
  stmt_bound (Expr e, fns) = (
    let (ne, fns) = expr_bound (e, fns) in
      (1 + ne, fns)) ∧
  stmt_bound (For _ _ e n ss, fns) = (
    let (ne, fns) = expr_bound (e, fns) in
    let (ns, fns) = stmt_bound_list (ss, fns) in
      (1 + ne + n * ns, fns)) ∧
  stmt_bound (If e s1 s2, fns) = (
    let (ne, fns) = expr_bound (e, fns) in
    let (n1, fns) = stmt_bound_list (s1, fns) in
    let (n2, fns) = stmt_bound_list (s2, fns) in
      (1 + ne + n1 + n2, fns)) ∧
  stmt_bound (Assert e _, fns) = (
    let (ne, fns) = expr_bound (e, fns) in
      (1 + ne, fns)) ∧
  stmt_bound (Raise _, fns) = (1, fns) ∧
  stmt_bound (Return NONE, fns) = (1, fns) ∧
  stmt_bound (Return (SOME e), fns) = (
    let (ne, fns) = expr_bound (e, fns) in
      (1 + ne, fns)) ∧
  stmt_bound (Assign tgt e, fns) = (
    let (ne, fns) = expr_bound (e, fns) in
    let (nt, fns) = tgt_bound (tgt, fns) in
      (1 + ne + nt, fns)) ∧
  stmt_bound (AugAssign bt _ e, fns) = (
    let (ne, fns) = expr_bound (e, fns) in
    let (nb, fns) = base_tgt_bound (bt, fns) in
      (1 + ne + nb, fns)) ∧
  stmt_bound (AnnAssign _ _ e, fns) = (
    let (ne, fns) = expr_bound (e, fns) in
      (1 + ne, fns)) ∧
  stmt_bound_list ([], fns) = (0, fns) ∧
  stmt_bound_list (s::ss, fns) = (
    let (n, fns) = stmt_bound (s, fns) in
    let (ns, fns) = stmt_bound_list (ss, fns) in
      (1 + n + ns, fns))
Termination
  WF_REL_TAC`measure (λx.
    case x of INL (e, _) => stmt_size e
            | INR (es, _) => stmt1_size es)`
End

Definition stmtk_bound_def[simp]:
  stmtk_bound (StartK s, fns) = (
    let (n, fns) = stmt_bound (s, fns) in
      (3 + n, fns)) ∧
  stmtk_bound (ExprK k, fns) = (
    let (n, fns) = exprk_bound (k, fns) in
      (1 + n, fns)) ∧
  stmtk_bound (IfK k s1 s2, fns) = (
    let (n, fns) = exprk_bound (k, fns) in
    let (n1, fns) = stmt_bound_list (s1, fns) in
    let (n2, fns) = stmt_bound_list (s2, fns) in
      (1 + n + n1 + n2, fns)) ∧
  stmtk_bound (AssertK k _, fns) = (
    let (n, fns) = exprk_bound (k, fns) in
      (1 + n, fns)) ∧
  stmtk_bound (ReturnSomeK k, fns) = (
    let (n, fns) = exprk_bound (k, fns) in
      (1 + n, fns)) ∧
  stmtk_bound (AssignK1 tk e, fns) = (
    let (nt, fns) = tgtk_bound (tk, fns) in
    let (ne, fns) = expr_bound (e, fns) in
      (1 + nt + ne, fns)) ∧
  stmtk_bound (AssignK2 _ k, fns) = (
    let (n, fns) = exprk_bound (k, fns) in
      (1 + n, fns)) ∧
  stmtk_bound (AugAssignK1 k _ e, fns) = (
    let (n, fns) = base_tgtk_bound (k, fns) in
    let (ne, fns) = expr_bound (e, fns) in
      (1 + n + ne, fns)) ∧
  stmtk_bound (AugAssignK2 _ _ _ k, fns) = (
    let (n, fns) = exprk_bound (k, fns) in
      (1 + n, fns)) ∧
  stmtk_bound (AnnAssignK _ _ k, fns) = (
    let (n, fns) = exprk_bound (k, fns) in
      (1 + n, fns)) ∧
  stmtk_bound (ForK _ _ k n s, fns) = (
    let (nk, fns) = exprk_bound (k, fns) in
    let (ns, fns) = stmt_bound_list (s, fns) in
      (1 + nk + n * ns, fns)) ∧
  stmtk_bound (_, fns) = (1, fns)
End

Definition fns_from_context_def:
  fns_from_context fc =
  case fc.name of Fn fn => {fn} | _ => {}
End

Definition all_fns_def[simp]:
  all_fns [] = {} ∧
  all_fns (FunctionDef fv fm id args ret body :: ts) =
    id INSERT (all_fns ts) ∧
  all_fns (_ :: ts) = all_fns ts
End

Definition fn_bound_def:
  fn_bound ts all seen fns =
  if FINITE all ∧ DISJOINT seen fns ∧ fns ⊆ all ∧ seen ⊆ all then
    if fns = {} then 0 else
      let fn = CHOICE fns in
      let rest = REST fns in
      let seen = fn INSERT seen in
        case lookup_function fn Internal ts of
           | NONE => fn_bound ts all seen rest
           | SOME (_, _, body) =>
             let (n, x) = stmt_bound_list (body, {}) in
               n + fn_bound ts all seen (rest UNION (x DIFF seen))
  else 0
Termination
  WF_REL_TAC`measure (λ(_,all,seen,_). CARD (all DIFF seen))`
  \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`CARD s1 < CARD s2`
  \\ `s2 = CHOICE fns INSERT s1`
  by (
    simp[Abbr`s1`, Abbr`s2`, EXTENSION]
    \\ gs[IN_DISJOINT, SUBSET_DEF]
    \\ rw[EQ_IMP_THM]
    \\ metis_tac[CHOICE_DEF] )
  \\ `FINITE s1` by rw[Abbr`s1`]
  \\ rw[CARD_INSERT, Abbr`s1`]
End

Definition step_bound_def:
  step_bound ctx =
  let current_fns =
    fns_from_context ctx.current_fc ∪
    BIGUNION (IMAGE fns_from_context (set ctx.call_stack)) in
  let ts = ctx.current_contract.src in
  let (ns, fns) = stmtk_bound (ctx.current_fc.current_stmt, {}) in
  let (nr, fns) = stmt_bound_list (ctx.current_fc.remaining_stmts, fns) in
    ns + nr +
      fn_bound ts (all_fns ts) current_fns (fns DIFF current_fns)
End

Theorem set_stmt_simps[simp]:
  (set_stmt k ctx).current_contract = ctx.current_contract ∧
  (set_stmt k ctx).call_stack = ctx.call_stack ∧
  (set_stmt k ctx).current_fc.current_stmt = k ∧
  (set_stmt k ctx).current_fc.remaining_stmts = ctx.current_fc.remaining_stmts
Proof
  rw[set_stmt_def]
QED

Theorem fns_from_context_set_stmt[simp]:
  fns_from_context (set_stmt k ctx).current_fc =
  fns_from_context ctx.current_fc
Proof
  rw[set_stmt_def, fns_from_context_def]
QED

Theorem raise_simps[simp]:
  (raise e ctx).current_contract = ctx.current_contract ∧
  (raise e ctx).call_stack = ctx.call_stack ∧
  (raise e ctx).current_fc = ctx.current_fc with current_stmt := ExceptionK e
Proof
  rw[raise_def]
QED

Theorem exception_raised_raise[simp]:
  exception_raised (raise e ctx)
Proof
  rw[exception_raised_def]
QED

Theorem pop_loop_simps[simp]:
  (pop_loop ctx).current_contract = ctx.current_contract
Proof
  rw[pop_loop_def]
  \\ CASE_TAC \\ rw[]
QED

Theorem next_iteration_current_contract[simp]:
  (next_iteration lp ctx).current_contract = ctx.current_contract
Proof
  rw[next_iteration_def]
  \\ CASE_TAC \\ rw[]
QED

Definition step_stmt_till_exception_def:
  step_stmt_till_exception ctx =
  if exception_raised ctx then ctx
  else step_stmt_till_exception (step_stmt ctx)
Termination
  cheat
  (*
  WF_REL_TAC`measure step_bound`
  \\ rw[step_stmt_def]
  \\ CASE_TAC
  >- (
    CASE_TAC
    >- ( rw[step_bound_def] \\ pairarg_tac \\ fs[])
    >- ( rw[step_bound_def]
      \\ pairarg_tac \\ gvs[]
      \\ gs[continue_loop_def]
      \\ Cases_on`ctx.current_fc.name` \\ gs[]
      >- (
        gs[fns_from_context_def]
        \\ pairarg_tac \\ gvs[] )
      \\ pairarg_tac \\ gvs[]
      \\ pairarg_tac \\ gvs[]
      \\ gs[pop_scope_def]
      \\ Cases_on`ctx.current_fc.scopes` \\ gvs[]
      >- gs[fns_from_context_def]
      \\ IF_CASES_TAC
      >- gs[exception_raised_def]
      \\ cheat )
    >- ( rw[step_bound_def]
      \\ pairarg_tac \\ gs[]
      \\ gs[break_loop_def]
      \\ Cases_on`ctx.current_fc.name` \\ gs[]
      >- (
        gs[fns_from_context_def]
        \\ pairarg_tac \\ gvs[] )
      \\ pairarg_tac \\ gvs[]


    \\ cheat )
    >- ( rw[step_bound_def] \\ rpt(pairarg_tac \\ gvs[]))
    >- ( rw[step_bound_def] \\ rpt(pairarg_tac \\ gvs[]))
    >- ( rw[step_bound_def] \\ rpt(pairarg_tac \\ gvs[]))
    >- ( rw[step_bound_def] \\ rpt(pairarg_tac \\ gvs[]))
    >- ( rw[step_bound_def] \\ rpt(pairarg_tac \\ gvs[raise_def]))
    *)
End

val () = cv_auto_trans step_stmt_till_exception_def;

Definition external_call_contract_def:
 external_call_contract ctr name args =
 case lookup_function name External ctr.src of
   NONE => (INR "lookup_function External", ctr)
 | SOME (params, _, body) =>
   (case bind_arguments params args of
      SOME env =>
      (let fc = initial_function_context name env body in
       let ctx = initial_execution_context ctr fc in
       let ctx = step_stmt_till_exception ctx in
       let ctr = ctx.current_contract in
       (case ctx.current_fc.current_stmt
          of ExceptionK (ExternalReturn v) => (INL v, ctr)
           | ExceptionK (Error msg) => (INR msg, ctr)
           | _ => (INR "current_stmt", ctr)))
    | _ => (INR "external bind_arguments", ctr))
End

val () = cv_auto_trans external_call_contract_def;

Definition external_call_def:
  external_call ms addr name args =
  case ALOOKUP ms.contracts addr of NONE => (INR "no contract at addr", ms)
     | SOME ctr =>
  case external_call_contract ctr name args of
       (res, ctr) =>
       (res, ms with contracts updated_by CONS (addr, ctr))
End

val () = cv_auto_trans external_call_def;

val () = export_theory();
