(*
 * The read/write overlap check of an array subscript whose base passes
 * through a dynamic-array element.  When it holds, Vyper 0.5.0b1 copies the
 * base before evaluating the index, since the index could resize the array
 * the base was derived from: the interpreter reads the base there, and the
 * lowering copies it.
 *
 * Mirrors Python: codegen_venom/expr.py _lower_array_subscript (overlap),
 * _subscript_read_write_overlap and _contains_risky_call.
 *
 * Main definitions:
 * - expr_accesses: the variables an expression reads and writes, and
 *   whether it makes a risky call, including in the internal functions it
 *   reaches (vyperTypeCallGraph's reachable_nodes)
 * - subscript_overlap: the check itself
 *)

Theory vyperSubscriptOverlap
Ancestors
  list alist vyperAST vyperTypeCallGraph
Libs
  cv_transLib

Datatype:
  var_ref = LocalRef identifier | StateRef nsid
End

Datatype:
  var_access = ReadAcc var_ref | WriteAcc var_ref | RiskyAcc
End

(* Builtins lowered to call-family opcodes.  Python skips a sha256 its
   constant folder removed; this check has no folder, so such a sha256
   still counts as risky here (vyper-hol#1303).
   Mirrors Python: expr.py _RISKY_BUILTINS *)
Definition risky_builtin_def:
  risky_builtin Sha256 = T ∧
  risky_builtin ECRecover = T ∧
  risky_builtin ECAdd = T ∧
  risky_builtin ECMul = T ∧
  risky_builtin _ = F
End

val () = cv_auto_trans risky_builtin_def;

(* extcall, staticcall, send, raw_call and the create builtins.
   Mirrors Python: expr.py _contains_risky_call, _RISKY_BUILTINS *)
Definition risky_call_target_def:
  risky_call_target (ExtCall _ _ _ _) = T ∧
  risky_call_target (Send _) = T ∧
  risky_call_target (RawCallTarget _) = T ∧
  risky_call_target (RawCallCalldataTarget _) = T ∧
  risky_call_target (CreateTarget _ _ _) = T ∧
  risky_call_target _ = F
End

val () = cv_auto_trans risky_call_target_def;

(* A written variable is also read, as Python logs every assignment target
   as a read (local.py ExprVisitor.visit). *)
Definition accesses_expr_def:
  accesses_expr (Name _ id) = [ReadAcc (LocalRef id)] ∧
  accesses_expr (TopLevelName _ nsid) = [ReadAcc (StateRef nsid)] ∧
  accesses_expr (FlagMember _ _ _) = [] ∧
  accesses_expr (IfExp _ c x y) =
    accesses_expr c ++ accesses_expr x ++ accesses_expr y ∧
  accesses_expr (Literal _ _) = [] ∧
  accesses_expr (StructLit _ _ kes) = accesses_named_exprs kes ∧
  accesses_expr (Subscript _ x y) = accesses_expr x ++ accesses_expr y ∧
  accesses_expr (Attribute _ x _) = accesses_expr x ∧
  accesses_expr (Builtin _ bt es) =
    (if risky_builtin bt then [RiskyAcc] else []) ++
    accesses_exprs es ∧
  accesses_expr (TypeBuiltin _ _ _ es) = accesses_exprs es ∧
  accesses_expr (Pop _ tgt) = accesses_target tgt ∧
  accesses_expr (Call _ t es drv) =
    (if risky_call_target t then [RiskyAcc] else []) ++
    accesses_exprs es ++ accesses_opt drv ∧

  accesses_target (NameTarget id) =
    [ReadAcc (LocalRef id); WriteAcc (LocalRef id)] ∧
  accesses_target (TopLevelNameTarget nsid) =
    [ReadAcc (StateRef nsid); WriteAcc (StateRef nsid)] ∧
  accesses_target (SubscriptTarget tgt e) =
    accesses_target tgt ++ accesses_expr e ∧
  accesses_target (AttributeTarget tgt _) = accesses_target tgt ∧

  accesses_exprs [] = [] ∧
  accesses_exprs (e::es) = accesses_expr e ++ accesses_exprs es ∧

  accesses_opt NONE = [] ∧
  accesses_opt (SOME e) = accesses_expr e ∧

  accesses_named_exprs [] = [] ∧
  accesses_named_exprs ((_,e)::kes) =
    accesses_expr e ++ accesses_named_exprs kes
Termination
  qexists_tac `measure (\(x : expr + base_assignment_target + expr list +
                                      expr option + (identifier # expr) list).
    case x of
    | INL e => expr_size e
    | INR (INL tgt) => base_assignment_target_size tgt
    | INR (INR (INL es)) => list_size expr_size es
    | INR (INR (INR (INL opt))) => option_size expr_size opt
    | INR (INR (INR (INR kes))) =>
        list_size (pair_size (list_size char_size) expr_size) kes)` >>
  conj_tac >- MATCH_ACCEPT_TAC prim_recTheory.WF_measure >>
  PURE_REWRITE_TAC [prim_recTheory.measure_thm, sumTheory.sum_case_def] >>
  simp[expr_size_def, listTheory.list_size_def,
       basicSizeTheory.pair_size_def, basicSizeTheory.option_size_def,
       bnfPrelimsTheory.option_size_map, bnfPrelimsTheory.pair_size_map,
       listTheory.list_size_map, SF ETA_ss]
End

val () = cv_auto_trans accesses_expr_def;

Definition accesses_atarget_def:
  accesses_atarget (BaseTarget tgt) = accesses_target tgt ∧
  accesses_atarget (TupleTarget tgts) = accesses_atargets tgts ∧
  accesses_atargets [] = [] ∧
  accesses_atargets (t::ts) = accesses_atarget t ++ accesses_atargets ts
Termination
  WF_REL_TAC `measure (\x. case x of
    | INL tgt => assignment_target_size tgt
    | INR tgts => list_size assignment_target_size tgts)` >>
  simp[assignment_target_size_def, listTheory.list_size_def]
End

val () = cv_auto_trans accesses_atarget_def;

Definition accesses_iterator_def:
  accesses_iterator (Array e) = accesses_expr e ∧
  accesses_iterator (Range x y) = accesses_expr x ++ accesses_expr y
End

val () = cv_auto_trans accesses_iterator_def;

Definition accesses_assert_reason_def:
  accesses_assert_reason AssertBare = [] ∧
  accesses_assert_reason AssertUnreachable = [] ∧
  accesses_assert_reason (AssertReason e) = accesses_expr e ∧
  accesses_assert_reason (AssertCustomError err) =
    accesses_exprs (custom_error_exprs err)
End

val () = cv_auto_trans accesses_assert_reason_def;

Definition accesses_raise_reason_def:
  accesses_raise_reason RaiseBare = [] ∧
  accesses_raise_reason RaiseUnreachable = [] ∧
  accesses_raise_reason (RaiseReason e) = accesses_expr e ∧
  accesses_raise_reason (RaiseCustomError err) =
    accesses_exprs (custom_error_exprs err)
End

val () = cv_auto_trans accesses_raise_reason_def;

Definition accesses_stmt_def:
  accesses_stmt Pass = [] ∧
  accesses_stmt Continue = [] ∧
  accesses_stmt Break = [] ∧
  accesses_stmt (Expr e) = accesses_expr e ∧
  accesses_stmt (For _ _ iter _ body) =
    accesses_iterator iter ++ accesses_stmts body ∧
  accesses_stmt (If e yes no) =
    accesses_expr e ++ accesses_stmts yes ++ accesses_stmts no ∧
  accesses_stmt (Assert e reason) =
    accesses_expr e ++ accesses_assert_reason reason ∧
  accesses_stmt (Log _ es) = accesses_exprs es ∧
  accesses_stmt (Raise reason) = accesses_raise_reason reason ∧
  accesses_stmt (Return opt) = accesses_opt opt ∧
  accesses_stmt (Assign tgt e) = accesses_atarget tgt ++ accesses_expr e ∧
  accesses_stmt (AugAssign _ tgt _ e) = accesses_target tgt ++ accesses_expr e ∧
  accesses_stmt (Append tgt e) = accesses_target tgt ++ accesses_expr e ∧
  accesses_stmt (AnnAssign _ _ e) = accesses_expr e ∧

  accesses_stmts [] = [] ∧
  accesses_stmts (s::ss) = accesses_stmt s ++ accesses_stmts ss
Termination
  WF_REL_TAC `measure (\x. case x of
    | INL s => stmt_size s
    | INR ss => list_size stmt_size ss)` >>
  simp[]
End

val () = cv_auto_trans accesses_stmt_def;

Definition find_function_def:
  find_function name [] = NONE ∧
  find_function name (FunctionDecl _ _ _ _ name' _ dflts _ body :: tls) =
    (if name' = name then SOME (dflts, body) else find_function name tls) ∧
  find_function name (_ :: tls) = find_function name tls
End

val () = cv_auto_trans find_function_def;

(* A callee's own locals are not the caller's variables. *)
Definition callee_accesses_def:
  callee_accesses [] = [] ∧
  callee_accesses (ReadAcc (LocalRef _) :: accs) = callee_accesses accs ∧
  callee_accesses (WriteAcc (LocalRef _) :: accs) = callee_accesses accs ∧
  callee_accesses (a :: accs) = a :: callee_accesses accs
End

val () = cv_auto_trans callee_accesses_def;

(* The accesses of the internal function name of module src. *)
Definition function_accesses_def:
  function_accesses mods (src, name) =
    case ALOOKUP mods src of
      NONE => []
    | SOME tls =>
        case find_function name tls of
          NONE => []
        | SOME (dflts, body) =>
            callee_accesses (accesses_exprs dflts ++ accesses_stmts body)
End

val () = cv_auto_trans function_accesses_def;

val () = cv_auto_trans int_calls_expr_def;
val () = cv_auto_trans int_calls_atarget_def;
val () = cv_auto_trans int_calls_iterator_def;
val () = cv_auto_trans int_calls_assert_reason_def;
val () = cv_auto_trans int_calls_raise_reason_def;
val () = cv_auto_trans int_calls_stmt_def;
val () = cv_auto_trans function_int_calls_def;
val () = cv_auto_trans toplevel_call_edges_def;
val () = cv_auto_trans module_call_edges_def;
val () = cv_auto_trans contract_call_edges_def;
val () = cv_auto_trans contract_call_nodes_def;
val () = cv_auto_trans direct_callees_def;
val () = cv_auto_trans reachable_nodes_def;

(* The internal functions e calls, directly or through other internal calls.
   Calls form an acyclic graph (Vyper forbids recursion), so no call chain is
   longer than the number of functions. *)
Definition reached_functions_def:
  reached_functions mods e =
    let edges = contract_call_edges mods;
        direct = int_calls_expr e in
      nub (direct ++
           FLAT (MAP (reachable_nodes edges (LENGTH (contract_call_nodes mods)))
                     direct))
End

val () = cv_auto_trans reached_functions_def;

(* What e reads and writes, and its risky calls, including those of the
   internal functions it reaches: a callee's state-variable reads and writes,
   and its risky calls, are its callers' too.
   Mirrors Python: local.py ExprVisitor.visit_Call adds an internal callee's
   state-variable reads and writes to the call; expr.py
   _function_contains_risky_call.
   Differs from Python for a call to an abstract function: the AST names its
   concrete override, whose writes count here, while Python takes the
   abstract function's (empty) writes (verifereum/vyper-hol#1291). *)
Definition expr_accesses_def:
  expr_accesses mods e =
    accesses_expr e ++
    FLAT (MAP (function_accesses mods) (reached_functions mods e))
End

val () = cv_auto_trans expr_accesses_def;

Definition constant_decl_def:
  constant_decl id [] = F ∧
  constant_decl id (VariableDecl _ (Constant _) id' _ _ :: tls) =
    (id' = id ∨ constant_decl id tls) ∧
  constant_decl id (_ :: tls) = constant_decl id tls
End

val () = cv_auto_trans constant_decl_def;

(* The variables read, other than constants.
   Mirrors Python: expr.py _subscript_read_write_overlap (base_reads) *)
Definition nonconstant_reads_def:
  nonconstant_reads mods [] = [] ∧
  nonconstant_reads mods (ReadAcc (StateRef (src, id)) :: accs) =
    (case ALOOKUP mods src of
       SOME tls => if constant_decl id tls then nonconstant_reads mods accs
                   else StateRef (src, id) :: nonconstant_reads mods accs
     | NONE => StateRef (src, id) :: nonconstant_reads mods accs) ∧
  nonconstant_reads mods (ReadAcc v :: accs) = v :: nonconstant_reads mods accs ∧
  nonconstant_reads mods (_ :: accs) = nonconstant_reads mods accs
End

val nonconstant_reads_pre_def =
  cv_auto_trans_pre "nonconstant_reads_pre" nonconstant_reads_def;

Theorem nonconstant_reads_pre[cv_pre]:
  ∀mods accs. nonconstant_reads_pre mods accs
Proof
  ho_match_mp_tac nonconstant_reads_ind \\ rw[]
  \\ rw[Once nonconstant_reads_pre_def]
  \\ gvs[]
QED

Definition any_written_def:
  any_written [] accs = F ∧
  any_written (v :: vs) accs = (MEM (WriteAcc v) accs ∨ any_written vs accs)
End

val () = cv_auto_trans any_written_def;

(* Whether array subscript base[idx] copies its base before the index, in a
   contract whose modules are mods: the base passes through a dynamic-array
   element, reads a variable other than a constant, and the index writes a
   variable the base reads or makes a risky call.
   Mirrors Python: expr.py _lower_array_subscript (overlap) *)
Definition subscript_overlap_def:
  subscript_overlap mods base idx ⇔
    is_ArrayT (expr_type base) ∧ base_through_dynarray base ∧
    let reads = nonconstant_reads mods (expr_accesses mods base) in
      reads ≠ [] ∧
      let idx_as = expr_accesses mods idx in
        any_written reads idx_as ∨ MEM RiskyAcc idx_as
End

val () = cv_auto_trans subscript_overlap_def;

Theorem subscript_overlap_through_dynarray:
  subscript_overlap mods base idx ⇒
  is_ArrayT (expr_type base) ∧ base_through_dynarray base
Proof
  simp[subscript_overlap_def]
QED
