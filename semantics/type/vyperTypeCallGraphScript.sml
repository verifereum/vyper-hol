(*
 * Executable internal-call graph analysis for checked Vyper contracts.
 *
 * TOP-LEVEL:
 * - int_calls_expr / int_calls_stmt: syntactic internal-call extraction
 * - contract_call_edges: whole-contract call graph
 * - contract_call_graph_acyclic: bounded executable cycle check
 *)

Theory vyperTypeCallGraph
Ancestors
  list rich_list vyperAST
Libs
  cv_transLib

(* ===== Internal calls in expressions and assignment targets ===== *)

Definition int_calls_expr_def:
  int_calls_expr (Name _ _) = [] /\
  int_calls_expr (TopLevelName _ _) = [] /\
  int_calls_expr (FlagMember _ _ _) = [] /\
  int_calls_expr (IfExp _ c x y) =
    int_calls_expr c ++ int_calls_expr x ++ int_calls_expr y /\
  int_calls_expr (Literal _ _) = [] /\
  int_calls_expr (StructLit _ _ kes) = int_calls_named_exprs kes /\
  int_calls_expr (Subscript _ x y) = int_calls_expr x ++ int_calls_expr y /\
  int_calls_expr (Attribute _ x _) = int_calls_expr x /\
  int_calls_expr (Builtin _ _ es) = int_calls_exprs es /\
  int_calls_expr (TypeBuiltin _ _ _ es) = int_calls_exprs es /\
  int_calls_expr (Pop _ tgt) = int_calls_target tgt /\
  int_calls_expr (Call _ (IntCall callee) es _) =
    callee :: int_calls_exprs es /\
  int_calls_expr (Call _ (ExtCall _ _) es default_ret) =
    int_calls_exprs es ++ int_calls_opt default_ret /\
  int_calls_expr (Call _ _ es _) = int_calls_exprs es /\

  int_calls_target (NameTarget _) = [] /\
  int_calls_target (TopLevelNameTarget _) = [] /\
  int_calls_target (SubscriptTarget tgt e) =
    int_calls_target tgt ++ int_calls_expr e /\
  int_calls_target (AttributeTarget tgt _) = int_calls_target tgt /\

  int_calls_exprs [] = [] /\
  int_calls_exprs (e::es) = int_calls_expr e ++ int_calls_exprs es /\

  int_calls_opt NONE = [] /\
  int_calls_opt (SOME e) = int_calls_expr e /\

  int_calls_named_exprs [] = [] /\
  int_calls_named_exprs ((_,e)::kes) =
    int_calls_expr e ++ int_calls_named_exprs kes
Termination
  WF_REL_TAC `measure (\(x : expr + base_assignment_target + expr list +
                                      expr option + (identifier # expr) list).
    case x of
    | INL e => expr_size e
    | INR (INL tgt) => base_assignment_target_size tgt
    | INR (INR (INL es)) => expr4_size es
    | INR (INR (INR (INL opt))) => expr3_size opt
    | INR (INR (INR (INR kes))) => expr1_size kes)` >>
  simp[expr_size_def] >>
  qsuff_tac
    `(!es. expr4_size es = list_size expr_size es) /\
     (!opt. expr3_size opt = option_size expr_size opt) /\
     (!kes. expr1_size kes =
       list_size (pair_size (list_size char_size) expr_size) kes)`
  >- (strip_tac >> asm_rewrite_tac[] >> DECIDE_TAC) >>
  rpt conj_tac >>
  TRY (Induct >> simp[expr_size_def, listTheory.list_size_def,
        basicSizeTheory.pair_size_def]) >>
  Cases >> simp[expr_size_def, basicSizeTheory.option_size_def]
End

(* ===== Internal calls in statements ===== *)

Definition int_calls_atarget_def:
  int_calls_atarget (BaseTarget tgt) = int_calls_target tgt /\
  int_calls_atarget (TupleTarget tgts) = int_calls_atargets tgts /\
  int_calls_atargets [] = [] /\
  int_calls_atargets (t::ts) = int_calls_atarget t ++ int_calls_atargets ts
Termination
  WF_REL_TAC `measure (\x. case x of
    | INL tgt => assignment_target_size tgt
    | INR tgts => assignment_target1_size tgts)` >>
  simp[]
End

Definition int_calls_iterator_def:
  int_calls_iterator (Array e) = int_calls_expr e /\
  int_calls_iterator (Range x y) = int_calls_expr x ++ int_calls_expr y
End

Definition int_calls_assert_reason_def:
  int_calls_assert_reason AssertBare = [] /\
  int_calls_assert_reason AssertUnreachable = [] /\
  int_calls_assert_reason (AssertReason e) = int_calls_expr e
End

Definition int_calls_raise_reason_def:
  int_calls_raise_reason RaiseBare = [] /\
  int_calls_raise_reason RaiseUnreachable = [] /\
  int_calls_raise_reason (RaiseReason e) = int_calls_expr e
End

Definition int_calls_stmt_def:
  int_calls_stmt Pass = [] /\
  int_calls_stmt Continue = [] /\
  int_calls_stmt Break = [] /\
  int_calls_stmt (Expr e) = int_calls_expr e /\
  int_calls_stmt (For _ _ iter _ body) =
    int_calls_iterator iter ++ int_calls_stmts body /\
  int_calls_stmt (If e yes no) =
    int_calls_expr e ++ int_calls_stmts yes ++ int_calls_stmts no /\
  int_calls_stmt (Assert e reason) =
    int_calls_expr e ++ int_calls_assert_reason reason /\
  int_calls_stmt (Log _ es) = int_calls_exprs es /\
  int_calls_stmt (Raise reason) = int_calls_raise_reason reason /\
  int_calls_stmt (Return opt) = int_calls_opt opt /\
  int_calls_stmt (Assign tgt e) = int_calls_atarget tgt ++ int_calls_expr e /\
  int_calls_stmt (AugAssign _ tgt _ e) =
    int_calls_target tgt ++ int_calls_expr e /\
  int_calls_stmt (Append tgt e) = int_calls_target tgt ++ int_calls_expr e /\
  int_calls_stmt (AnnAssign _ _ e) = int_calls_expr e /\

  int_calls_stmts [] = [] /\
  int_calls_stmts (s::ss) = int_calls_stmt s ++ int_calls_stmts ss
Termination
  WF_REL_TAC `measure (\x. case x of
    | INL s => stmt_size s
    | INR ss => list_size stmt_size ss)` >>
  simp[]
End

(* ===== Contract graph construction ===== *)

Definition function_int_calls_def:
  function_int_calls dflts body = int_calls_exprs dflts ++ int_calls_stmts body
End

Definition toplevel_call_edges_def:
  toplevel_call_edges src
    (FunctionDecl _ _ _ _ fn _ dflts _ body) =
      MAP (\callee. ((src,fn),callee)) (function_int_calls dflts body) /\
  toplevel_call_edges _ _ = []
End

Definition module_call_edges_def:
  module_call_edges (src,tls) = FLAT (MAP (toplevel_call_edges src) tls)
End

Definition contract_call_edges_def:
  contract_call_edges mods = FLAT (MAP module_call_edges mods)
End

Definition contract_call_nodes_def:
  contract_call_nodes mods =
    nub (MAP FST (contract_call_edges mods) ++ MAP SND (contract_call_edges mods))
End

(* ===== Executable bounded reachability and acyclicity ===== *)

Definition direct_callees_def:
  direct_callees edges caller = MAP SND (FILTER (\edge. FST edge = caller) edges)
End

Definition reachable_nodes_def:
  reachable_nodes edges 0 caller = nub (direct_callees edges caller) /\
  reachable_nodes edges (SUC fuel) caller =
    let reached = reachable_nodes edges fuel caller in
      nub (reached ++ FLAT (MAP (direct_callees edges) reached))
End

Definition call_graph_acyclic_def:
  call_graph_acyclic nodes edges <=>
    EVERY (\node. ~MEM node (reachable_nodes edges (LENGTH nodes) node)) nodes
End

Definition contract_call_graph_acyclic_def:
  contract_call_graph_acyclic mods <=>
    call_graph_acyclic (contract_call_nodes mods) (contract_call_edges mods)
End

