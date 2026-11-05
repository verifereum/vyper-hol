(* Structural module-constant inlining. Replacements are already expanded by
   module_consts_env: substitution never recursively chases its own output.
   Assignment names and qualified module references are deliberately retained. *)
Theory constSubst
Ancestors
  vyperAST alist list pair vyperContext
Libs
  cv_transLib

(* Only the initializer producer invokes this normalization. Runtime
   substitution below remains purely structural. *)
Definition fold_const_builtin_def:
  fold_const_builtin ty bi es =
    case (bi,es) of
      (Sha256,[Literal aty (BytesL bs)]) =>
        Literal ty (BytesL (word_to_bytes (SHA_256_bytes bs : bytes32) T))
    | (Sha256,[Literal aty (StringL s)]) =>
        Literal ty (BytesL
          (word_to_bytes (SHA_256_bytes (string_to_bytes s) : bytes32) T))
    | _ => Builtin ty bi es
End

Definition fold_const_expr_def:
  fold_const_expr (Name ty id) = Name ty id /\
  fold_const_expr (TopLevelName ty ns) = TopLevelName ty ns /\
  fold_const_expr (FlagMember ty ns id) = FlagMember ty ns id /\
  fold_const_expr (Literal ty l) = Literal ty l /\
  fold_const_expr (IfExp ty a b c) =
    IfExp ty (fold_const_expr a) (fold_const_expr b) (fold_const_expr c) /\
  fold_const_expr (StructLit ty ns fs) =
    StructLit ty ns (fold_const_fields fs) /\
  fold_const_expr (Subscript ty a b) =
    Subscript ty (fold_const_expr a) (fold_const_expr b) /\
  fold_const_expr (Attribute ty a id) = Attribute ty (fold_const_expr a) id /\
  fold_const_expr (Builtin ty bi es) =
    fold_const_builtin ty bi (fold_const_exprs es) /\
  fold_const_expr (TypeBuiltin ty bi t es) =
    TypeBuiltin ty bi t (fold_const_exprs es) /\
  fold_const_expr (Pop ty tgt) = Pop ty (fold_const_btarget tgt) /\
  fold_const_expr (Call ty ct es d) =
    Call ty ct (fold_const_exprs es) (fold_const_opt d) /\
  fold_const_btarget (NameTarget id) = NameTarget id /\
  fold_const_btarget (TopLevelNameTarget ns) = TopLevelNameTarget ns /\
  fold_const_btarget (SubscriptTarget tgt e) =
    SubscriptTarget (fold_const_btarget tgt) (fold_const_expr e) /\
  fold_const_btarget (AttributeTarget tgt id) =
    AttributeTarget (fold_const_btarget tgt) id /\
  fold_const_exprs [] = [] /\
  fold_const_exprs (e::es) = fold_const_expr e :: fold_const_exprs es /\
  fold_const_opt NONE = NONE /\
  fold_const_opt (SOME e) = SOME (fold_const_expr e) /\
  fold_const_fields [] = [] /\
  fold_const_fields ((id,e)::fs) = (id,fold_const_expr e)::fold_const_fields fs
Termination
  qexists_tac `measure (\(x : expr + base_assignment_target + expr list +
      expr option + (identifier # expr) list).
    case x of
      INL e => expr_size e
    | INR (INL t) => base_assignment_target_size t
    | INR (INR (INL es)) => list_size expr_size es
    | INR (INR (INR (INL opt))) => option_size expr_size opt
    | INR (INR (INR (INR fs))) =>
        list_size (pair_size (list_size char_size) expr_size) fs)` >>
  conj_tac >- MATCH_ACCEPT_TAC prim_recTheory.WF_measure >>
  PURE_REWRITE_TAC [prim_recTheory.measure_thm, sumTheory.sum_case_def,
                    pairTheory.pair_case_def] >>
  simp[expr_size_def, list_size_def, basicSizeTheory.pair_size_def,
       basicSizeTheory.option_size_def, bnfPrelimsTheory.option_size_map,
       bnfPrelimsTheory.pair_size_map, list_size_map, SF ETA_ss]
End

Definition no_sha256_expr_def:
  no_sha256_expr (Name ty id) = T /\
  no_sha256_expr (TopLevelName ty ns) = T /\
  no_sha256_expr (FlagMember ty ns id) = T /\
  no_sha256_expr (Literal ty l) = T /\
  no_sha256_expr (IfExp ty a b c) =
    (no_sha256_expr a /\ no_sha256_expr b /\ no_sha256_expr c) /\
  no_sha256_expr (StructLit ty ns fs) = no_sha256_fields fs /\
  no_sha256_expr (Subscript ty a b) = (no_sha256_expr a /\ no_sha256_expr b) /\
  no_sha256_expr (Attribute ty a id) = no_sha256_expr a /\
  no_sha256_expr (Builtin ty bi es) = (bi <> Sha256 /\ no_sha256_exprs es) /\
  no_sha256_expr (TypeBuiltin ty bi t es) = no_sha256_exprs es /\
  no_sha256_expr (Pop ty tgt) = no_sha256_btarget tgt /\
  no_sha256_expr (Call ty ct es d) = (no_sha256_exprs es /\ no_sha256_opt d) /\
  no_sha256_btarget (NameTarget id) = T /\
  no_sha256_btarget (TopLevelNameTarget ns) = T /\
  no_sha256_btarget (SubscriptTarget tgt e) =
    (no_sha256_btarget tgt /\ no_sha256_expr e) /\
  no_sha256_btarget (AttributeTarget tgt id) = no_sha256_btarget tgt /\
  no_sha256_exprs [] = T /\
  no_sha256_exprs (e::es) = (no_sha256_expr e /\ no_sha256_exprs es) /\
  no_sha256_opt NONE = T /\
  no_sha256_opt (SOME e) = no_sha256_expr e /\
  no_sha256_fields [] = T /\
  no_sha256_fields ((id,e)::fs) = (no_sha256_expr e /\ no_sha256_fields fs)
Termination
  qexists_tac `measure (\(x : expr + base_assignment_target + expr list +
      expr option + (identifier # expr) list).
    case x of
      INL e => expr_size e
    | INR (INL t) => base_assignment_target_size t
    | INR (INR (INL es)) => list_size expr_size es
    | INR (INR (INR (INL opt))) => option_size expr_size opt
    | INR (INR (INR (INR fs))) =>
        list_size (pair_size (list_size char_size) expr_size) fs)` >>
  conj_tac >- MATCH_ACCEPT_TAC prim_recTheory.WF_measure >>
  PURE_REWRITE_TAC [prim_recTheory.measure_thm, sumTheory.sum_case_def,
                    pairTheory.pair_case_def] >>
  simp[expr_size_def, list_size_def, basicSizeTheory.pair_size_def,
       basicSizeTheory.option_size_def, bnfPrelimsTheory.option_size_map,
       bnfPrelimsTheory.pair_size_map, list_size_map, SF ETA_ss]
End

Theorem fold_const_builtin_type[simp]:
  expr_type (fold_const_builtin ty bi es) = ty
Proof
  Cases_on `bi` >> simp[fold_const_builtin_def, expr_type_def] >>
  Cases_on `es` >> simp[expr_type_def] >>
  Cases_on `t` >> simp[expr_type_def] >>
  Cases_on `h` >> simp[expr_type_def] >>
  rename1 `Literal aty l` >> Cases_on `l` >> simp[expr_type_def]
QED

Theorem fold_const_expr_type[simp]:
  expr_type (fold_const_expr e) = expr_type e
Proof
  Cases_on `e` >>
  simp[fold_const_expr_def, expr_type_def, fold_const_builtin_type]
QED

Theorem fold_const_collections:
  fold_const_exprs es = MAP fold_const_expr es /\
  fold_const_opt d = OPTION_MAP fold_const_expr d /\
  fold_const_fields fs = MAP (\(id,e). (id,fold_const_expr e)) fs
Proof
  rpt conj_tac
  >- (Induct_on `es` >> simp[fold_const_expr_def])
  >- (Cases_on `d` >> simp[fold_const_expr_def])
  >> Induct_on `fs` >> simp[fold_const_expr_def] >>
  Cases_on `h` >> simp[fold_const_expr_def]
QED

Theorem no_sha256_collections:
  no_sha256_exprs es = EVERY no_sha256_expr es /\
  no_sha256_opt d = (case d of NONE => T | SOME e => no_sha256_expr e) /\
  no_sha256_fields fs = EVERY (no_sha256_expr o SND) fs
Proof
  rpt conj_tac
  >- (Induct_on `es` >> simp[no_sha256_expr_def])
  >- (Cases_on `d` >> simp[no_sha256_expr_def])
  >> Induct_on `fs` >> simp[no_sha256_expr_def] >>
  Cases_on `h` >> simp[no_sha256_expr_def]
QED

Definition subst_consts_expr_def:
  subst_consts_expr env (Name ty id) = Name ty id /\
  subst_consts_expr env (TopLevelName ty (ns,id)) =
    (case ns of
       SOME m => TopLevelName ty (SOME m,id)
     | NONE => case ALOOKUP env id of
                 NONE => TopLevelName ty (NONE,id) | SOME e => e) /\
  subst_consts_expr env (FlagMember ty ns id) = FlagMember ty ns id /\
  subst_consts_expr env (Literal ty l) = Literal ty l /\
  subst_consts_expr env (IfExp ty a b c) =
    IfExp ty (subst_consts_expr env a) (subst_consts_expr env b)
             (subst_consts_expr env c) /\
  subst_consts_expr env (StructLit ty ns fs) =
    StructLit ty ns (subst_consts_fields env fs) /\
  subst_consts_expr env (Subscript ty a b) =
    Subscript ty (subst_consts_expr env a) (subst_consts_expr env b) /\
  subst_consts_expr env (Attribute ty a id) =
    Attribute ty (subst_consts_expr env a) id /\
  subst_consts_expr env (Builtin ty bi es) =
    Builtin ty bi (subst_consts_exprs env es) /\
  subst_consts_expr env (TypeBuiltin ty bi t es) =
    TypeBuiltin ty bi t (subst_consts_exprs env es) /\
  subst_consts_expr env (Pop ty tgt) = Pop ty (subst_consts_btarget env tgt) /\
  subst_consts_expr env (Call ty ct es d) =
    Call ty ct (subst_consts_exprs env es) (subst_consts_opt env d) /\
  subst_consts_btarget env (NameTarget id) = NameTarget id /\
  subst_consts_btarget env (TopLevelNameTarget ns) = TopLevelNameTarget ns /\
  subst_consts_btarget env (SubscriptTarget tgt e) =
    SubscriptTarget (subst_consts_btarget env tgt) (subst_consts_expr env e) /\
  subst_consts_btarget env (AttributeTarget tgt id) =
    AttributeTarget (subst_consts_btarget env tgt) id /\
  subst_consts_exprs env [] = [] /\
  subst_consts_exprs env (e::es) =
    subst_consts_expr env e :: subst_consts_exprs env es /\
  subst_consts_opt env NONE = NONE /\
  subst_consts_opt env (SOME e) = SOME (subst_consts_expr env e) /\
  subst_consts_fields env [] = [] /\
  subst_consts_fields env ((id,e)::fs) =
    (id,subst_consts_expr env e)::subst_consts_fields env fs
Termination
  qexists_tac `measure (\(x : (identifier # expr) list # expr +
      (identifier # expr) list # base_assignment_target +
      (identifier # expr) list # expr list +
      (identifier # expr) list # expr option +
      (identifier # expr) list # (identifier # expr) list).
    case x of
      INL (_,e) => expr_size e
    | INR (INL (_,t)) => base_assignment_target_size t
    | INR (INR (INL (_,es))) => list_size expr_size es
    | INR (INR (INR (INL (_,opt)))) => option_size expr_size opt
    | INR (INR (INR (INR (_,fs)))) =>
        list_size (pair_size (list_size char_size) expr_size) fs)` >>
  conj_tac >- MATCH_ACCEPT_TAC prim_recTheory.WF_measure >>
  PURE_REWRITE_TAC [prim_recTheory.measure_thm, sumTheory.sum_case_def,
                    pairTheory.pair_case_def] >>
  simp[expr_size_def, list_size_def, basicSizeTheory.pair_size_def,
       basicSizeTheory.option_size_def, bnfPrelimsTheory.option_size_map,
       bnfPrelimsTheory.pair_size_map, list_size_map, SF ETA_ss]
End

Definition subst_consts_target_def:
  subst_consts_target env (BaseTarget tgt) =
    BaseTarget (subst_consts_btarget env tgt) /\
  subst_consts_target env (TupleTarget ts) =
    TupleTarget (subst_consts_targets env ts) /\
  subst_consts_targets env [] = [] /\
  subst_consts_targets env (t::ts) =
    subst_consts_target env t :: subst_consts_targets env ts
End

Definition subst_consts_iter_def:
  subst_consts_iter env (Array e) = Array (subst_consts_expr env e) /\
  subst_consts_iter env (Range a b) =
    Range (subst_consts_expr env a) (subst_consts_expr env b)
End

Definition subst_consts_error_def:
  subst_consts_error env (CustomError ns es fs) =
    CustomError ns (subst_consts_exprs env es) (subst_consts_fields env fs)
End

Definition subst_consts_areason_def:
  subst_consts_areason env AssertBare = AssertBare /\
  subst_consts_areason env AssertUnreachable = AssertUnreachable /\
  subst_consts_areason env (AssertReason e) = AssertReason (subst_consts_expr env e) /\
  subst_consts_areason env (AssertCustomError e) =
    AssertCustomError (subst_consts_error env e)
End

Definition subst_consts_rreason_def:
  subst_consts_rreason env RaiseBare = RaiseBare /\
  subst_consts_rreason env RaiseUnreachable = RaiseUnreachable /\
  subst_consts_rreason env (RaiseReason e) = RaiseReason (subst_consts_expr env e) /\
  subst_consts_rreason env (RaiseCustomError e) =
    RaiseCustomError (subst_consts_error env e)
End

Definition subst_consts_stmt_def:
  subst_consts_stmt env Pass = Pass /\
  subst_consts_stmt env Continue = Continue /\
  subst_consts_stmt env Break = Break /\
  subst_consts_stmt env (Expr e) = Expr (subst_consts_expr env e) /\
  subst_consts_stmt env (For id ty it n body) =
    For id ty (subst_consts_iter env it) n (subst_consts_stmts env body) /\
  subst_consts_stmt env (If e a b) =
    If (subst_consts_expr env e) (subst_consts_stmts env a) (subst_consts_stmts env b) /\
  subst_consts_stmt env (Assert e r) =
    Assert (subst_consts_expr env e) (subst_consts_areason env r) /\
  subst_consts_stmt env (Log ns es) = Log ns (subst_consts_exprs env es) /\
  subst_consts_stmt env (Raise r) = Raise (subst_consts_rreason env r) /\
  subst_consts_stmt env (Return e) = Return (subst_consts_opt env e) /\
  subst_consts_stmt env (Assign t e) =
    Assign (subst_consts_target env t) (subst_consts_expr env e) /\
  subst_consts_stmt env (AugAssign ty t bi e) =
    AugAssign ty (subst_consts_btarget env t) bi (subst_consts_expr env e) /\
  subst_consts_stmt env (Append t e) =
    Append (subst_consts_btarget env t) (subst_consts_expr env e) /\
  subst_consts_stmt env (AnnAssign id ty e) = AnnAssign id ty (subst_consts_expr env e) /\
  subst_consts_stmts env [] = [] /\
  subst_consts_stmts env (s::ss) =
    subst_consts_stmt env s :: subst_consts_stmts env ss
End

Definition module_consts_env_def:
  module_consts_env [] acc = acc /\
  module_consts_env (VariableDecl vis (Constant e) id ty slot :: rest) acc =
    module_consts_env rest (acc ++ [(id,fold_const_expr (subst_consts_expr acc e))]) /\
  module_consts_env (_::rest) acc = module_consts_env rest acc
End

Definition subst_consts_fn_def:
  subst_consts_fn env (mut,nr,rr,id,args,dflts,ret,body) =
    (mut,nr,rr,id,args,subst_consts_exprs env dflts,ret,subst_consts_stmts env body)
End

Theorem subst_consts_expr_empty:
  (!env e. env = [] ==> subst_consts_expr env e = e) /\
  (!env t. env = [] ==> subst_consts_btarget env t = t) /\
  (!env es. env = [] ==> subst_consts_exprs env es = es) /\
  (!env opt. env = [] ==> subst_consts_opt env opt = opt) /\
  (!env fs. env = [] ==> subst_consts_fields env fs = fs)
Proof
  ho_match_mp_tac subst_consts_expr_ind >>
  simp[subst_consts_expr_def] >> rpt gen_tac >>
  Cases_on `ns` >> simp[]
QED

Theorem subst_consts_target_empty:
  (!env t. env = [] ==> subst_consts_target env t = t) /\
  (!env ts. env = [] ==> subst_consts_targets env ts = ts)
Proof
  ho_match_mp_tac subst_consts_target_ind >>
  simp[subst_consts_target_def, subst_consts_expr_empty]
QED

Theorem subst_consts_iter_empty[simp]:
  subst_consts_iter [] it = it
Proof
  Cases_on `it` >> simp[subst_consts_iter_def, subst_consts_expr_empty]
QED

Theorem subst_consts_error_empty[simp]:
  subst_consts_error [] err = err
Proof
  Cases_on `err` >> simp[subst_consts_error_def, subst_consts_expr_empty]
QED

Theorem subst_consts_areason_empty[simp]:
  subst_consts_areason [] r = r
Proof
  Cases_on `r` >> simp[subst_consts_areason_def, subst_consts_expr_empty]
QED

Theorem subst_consts_rreason_empty[simp]:
  subst_consts_rreason [] r = r
Proof
  Cases_on `r` >> simp[subst_consts_rreason_def, subst_consts_expr_empty]
QED

Theorem subst_consts_stmt_empty:
  (!env s. env = [] ==> subst_consts_stmt env s = s) /\
  (!env ss. env = [] ==> subst_consts_stmts env ss = ss)
Proof
  ho_match_mp_tac subst_consts_stmt_ind >>
  simp[subst_consts_stmt_def, subst_consts_expr_empty,
       subst_consts_target_empty]
QED

Theorem subst_consts_fn_empty[simp]:
  subst_consts_fn [] fn = fn
Proof
  PairCases_on `fn` >>
  simp[subst_consts_fn_def, subst_consts_expr_empty, subst_consts_stmt_empty]
QED

(* Inlining changes only defaults and bodies, never dispatch metadata. *)
Theorem subst_consts_fn_metadata:
  subst_consts_fn env (mut,nr,rr,id,args,dflts,ret,body) =
    (mut,nr,rr,id,args,subst_consts_exprs env dflts,ret,subst_consts_stmts env body)
Proof
  simp[subst_consts_fn_def]
QED

val () = cv_auto_trans fold_const_builtin_def;
val () = cv_auto_trans fold_const_expr_def;
val () = cv_auto_trans no_sha256_expr_def;
val () = cv_auto_trans subst_consts_expr_def;
val () = cv_auto_trans subst_consts_target_def;
val () = cv_auto_trans subst_consts_iter_def;
val () = cv_auto_trans subst_consts_error_def;
val () = cv_auto_trans subst_consts_areason_def;
val () = cv_auto_trans subst_consts_rreason_def;
val () = cv_auto_trans subst_consts_stmt_def;
val () = cv_auto_trans module_consts_env_def;
val () = cv_auto_trans subst_consts_fn_def;

(* Executable coverage regressions: declaration order, single-step replacement,
   qualified references, nested lvalue indices and expression-bearing reasons. *)
Theorem module_consts_env_chain[local]:
  module_consts_env
    [VariableDecl Private (Constant (Literal (BaseT (UintT 256)) (IntL 7)))
       "A" (BaseT (UintT 256)) NONE;
     VariableDecl Private (Constant (TopLevelName (BaseT (UintT 256)) (NONE,"A")))
       "B" (BaseT (UintT 256)) NONE] [] =
    [("A", Literal (BaseT (UintT 256)) (IntL 7));
     ("B", Literal (BaseT (UintT 256)) (IntL 7))]
Proof
  EVAL_TAC
QED

Theorem subst_consts_reference_boundaries[local]:
  subst_consts_expr
    [("A",TopLevelName NoneT (NONE,"B")); ("B",Literal NoneT (IntL 7))]
    (TopLevelName NoneT (NONE,"A")) = TopLevelName NoneT (NONE,"B") /\
  subst_consts_expr [("A",Literal NoneT (IntL 7))]
    (TopLevelName NoneT (SOME 1,"A")) = TopLevelName NoneT (SOME 1,"A") /\
  subst_consts_expr [("A",Literal NoneT (IntL 7))]
    (Name NoneT "A") = Name NoneT "A"
Proof
  EVAL_TAC
QED

Theorem subst_consts_nested_targets[local]:
  subst_consts_target [("A",Literal NoneT (IntL 7))]
    (TupleTarget [BaseTarget
      (SubscriptTarget (AttributeTarget
        (SubscriptTarget (TopLevelNameTarget (NONE,"A"))
          (TopLevelName NoneT (NONE,"A"))) "x")
        (TopLevelName NoneT (NONE,"A")))]) =
    TupleTarget [BaseTarget
      (SubscriptTarget (AttributeTarget
        (SubscriptTarget (TopLevelNameTarget (NONE,"A"))
          (Literal NoneT (IntL 7))) "x") (Literal NoneT (IntL 7)))]
Proof
  EVAL_TAC
QED

Theorem subst_consts_defaults_bodies_reasons[local]:
  subst_consts_fn [("A",Literal NoneT (IntL 7))]
    (View,F,F,"__default__",[],[TopLevelName NoneT (NONE,"A")],NoneT,
      [For "i" NoneT (Range (TopLevelName NoneT (NONE,"A"))
        (TopLevelName NoneT (NONE,"A"))) 8
        [Assert (TopLevelName NoneT (NONE,"A"))
           (AssertCustomError (CustomError (NONE,"E")
             [TopLevelName NoneT (NONE,"A")]
             [("x",TopLevelName NoneT (NONE,"A"))]));
         Raise (RaiseReason (TopLevelName NoneT (NONE,"A")))];
       Return (SOME (TopLevelName NoneT (NONE,"A")))]) =
    (View,F,F,"__default__",[],[Literal NoneT (IntL 7)],NoneT,
      [For "i" NoneT (Range (Literal NoneT (IntL 7))
        (Literal NoneT (IntL 7))) 8
        [Assert (Literal NoneT (IntL 7))
           (AssertCustomError (CustomError (NONE,"E")
             [Literal NoneT (IntL 7)] [("x",Literal NoneT (IntL 7))]));
         Raise (RaiseReason (Literal NoneT (IntL 7)))];
       Return (SOME (Literal NoneT (IntL 7)))])
Proof
  EVAL_TAC
QED

(* Symbolic regressions: exercise the fold interface without evaluating a
   concrete cryptographic hash inside the proof. *)
Theorem fold_const_literal_sha256[local]:
  fold_const_expr (Builtin ty Sha256 [Literal aty (BytesL bs)]) =
    Literal ty (BytesL (word_to_bytes (SHA_256_bytes bs : bytes32) T)) /\
  fold_const_expr (Builtin ty Sha256 [Literal aty (StringL s)]) =
    Literal ty (BytesL
      (word_to_bytes (SHA_256_bytes (string_to_bytes s) : bytes32) T))
Proof
  simp[fold_const_expr_def, fold_const_builtin_def]
QED

Theorem fold_const_nested_sha256[local]:
  fold_const_expr
    (Builtin ty Sha256 [Builtin aty Sha256 [Literal bty (BytesL bs)]]) =
  Literal ty (BytesL (word_to_bytes
    (SHA_256_bytes (word_to_bytes (SHA_256_bytes bs : bytes32) T) : bytes32) T))
Proof
  simp[fold_const_expr_def, fold_const_builtin_def]
QED

Theorem fold_const_nonliteral_sha256[local]:
  fold_const_expr (Builtin ty Sha256 [TopLevelName aty (NONE,id)]) =
    Builtin ty Sha256 [TopLevelName aty (NONE,id)] /\
  ~no_sha256_expr
    (fold_const_expr (Builtin ty Sha256 [TopLevelName aty (NONE,id)]))
Proof
  simp[fold_const_expr_def, fold_const_builtin_def, no_sha256_expr_def]
QED

Theorem no_sha256_hidden_children[local]:
  ~no_sha256_expr (StructLit ty ns [(id,Builtin aty Sha256 [])]) /\
  ~no_sha256_expr (Builtin ty Len [Builtin aty Sha256 []]) /\
  ~no_sha256_expr (Call ty ct [] (SOME (Builtin aty Sha256 []))) /\
  ~no_sha256_expr
    (Pop ty (SubscriptTarget (NameTarget id) (Builtin aty Sha256 [])))
Proof
  simp[no_sha256_expr_def]
QED

Theorem subst_consts_runtime_sha256[local]:
  subst_consts_expr [] (Builtin ty Sha256 [Literal aty (BytesL bs)]) =
    Builtin ty Sha256 [Literal aty (BytesL bs)]
Proof
  simp[subst_consts_expr_def]
QED
