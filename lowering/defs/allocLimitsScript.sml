(*
 * Python's allocation limit: Context.allocate_buffer
 * (vyper/codegen_venom/context.py) raises MemoryAllocationException for a
 * buffer of 2 ** 64 bytes or more.  The lowering's ALLOCA takes its size as
 * a word literal and cannot fail, so lower_vyper_runtime_unit checks the
 * limit up front, for every function (compileVyper's fn_allocs_ok), as it
 * does return_buffer_ok.
 *
 * TOP-LEVEL:
 *   alloc_limits_expr, literal_alloc_ok -- every static buffer the lowering
 *                                          allocates for an expression
 *   alloc_limits_stmt(s) -- the same for every expression of a statement,
 *                           and every local it declares
 *)
Theory allocLimits
Ancestors
  compileEnv vyperAST vfmConstants list pair

(* The buffer the lowering allocates for a bytes or string literal, its
   length word and its data rounded up to whole words, is below 2 ** 64
   bytes.  A bytesN or address literal has at most 32 bytes and no buffer,
   and the bound holds of it all the same. *)
Definition literal_alloc_ok_def:
  literal_alloc_ok (BytesL bs) = (32 + 32 * word_size (LENGTH bs) < 2 ** 64) /\
  literal_alloc_ok (StringL str) =
    (32 + 32 * word_size (LENGTH str) < 2 ** 64) /\
  literal_alloc_ok _ = T
End

(* Every static buffer the lowering allocates for a node of the expression
   is below Python's allocation limit, 2 ** 64 bytes: the buffers of bytes
   and string literals, struct and array literals, empty(T) of a type that
   is not a word, and the output of a calldata slice.  The same recursion
   as byte_widths_expr. *)
Definition alloc_limits_expr_def:
  alloc_limits_expr cenv (Name t _) = T /\
  alloc_limits_expr cenv (TopLevelName t _) = T /\
  alloc_limits_expr cenv (FlagMember t _ _) = T /\
  alloc_limits_expr cenv (IfExp t c x y) =
    (alloc_limits_expr cenv c /\ alloc_limits_expr cenv x /\
     alloc_limits_expr cenv y) /\
  alloc_limits_expr cenv (Literal t l) = literal_alloc_ok l /\
  alloc_limits_expr cenv (StructLit t nsid kes) =
    (type_memory_bytes cenv (StructT nsid) < 2 ** 64 /\
     alloc_limits_named_exprs cenv kes) /\
  alloc_limits_expr cenv (Subscript t x y) =
    (alloc_limits_expr cenv x /\ alloc_limits_expr cenv y) /\
  alloc_limits_expr cenv (Attribute t x _) = alloc_limits_expr cenv x /\
  alloc_limits_expr cenv (Builtin t bi es) =
    ((case bi of
        MakeArray NONE _ =>
          SUM (MAP (type_memory_bytes cenv o expr_type) es) < 2 ** 64
      | MakeArray (SOME _) _ => type_memory_bytes cenv t < 2 ** 64
      | CalldataSlice n => 32 + 32 * word_size n < 2 ** 64
      | _ => T) /\
     alloc_limits_exprs cenv es) /\
  alloc_limits_expr cenv (TypeBuiltin t tb ty es) =
    ((tb = Empty /\ ~is_word_type ty ==> type_memory_bytes cenv ty < 2 ** 64) /\
     alloc_limits_exprs cenv es) /\
  alloc_limits_expr cenv (Pop t tgt) = alloc_limits_target cenv tgt /\
  alloc_limits_expr cenv (Call t _ es dflt) =
    (alloc_limits_exprs cenv es /\ alloc_limits_opt cenv dflt) /\

  alloc_limits_target cenv (NameTarget _) = T /\
  alloc_limits_target cenv (TopLevelNameTarget _) = T /\
  alloc_limits_target cenv (SubscriptTarget tgt e) =
    (alloc_limits_target cenv tgt /\ alloc_limits_expr cenv e) /\
  alloc_limits_target cenv (AttributeTarget tgt _) =
    alloc_limits_target cenv tgt /\

  alloc_limits_exprs cenv [] = T /\
  alloc_limits_exprs cenv (e::es) =
    (alloc_limits_expr cenv e /\ alloc_limits_exprs cenv es) /\

  alloc_limits_opt cenv NONE = T /\
  alloc_limits_opt cenv (SOME e) = alloc_limits_expr cenv e /\

  alloc_limits_named_exprs cenv [] = T /\
  alloc_limits_named_exprs cenv ((_,e)::kes) =
    (alloc_limits_expr cenv e /\ alloc_limits_named_exprs cenv kes)
Termination
  (* container sizes, not the package's per-instance size functions. *)
  qexists_tac `measure (\(x : compile_env # expr + compile_env #
                              base_assignment_target + compile_env # expr list +
                              compile_env # expr option +
                              compile_env # (identifier # expr) list).
    case x of
    | INL (_, e) => expr_size e
    | INR (INL (_, tgt)) => base_assignment_target_size tgt
    | INR (INR (INL (_, es))) => list_size expr_size es
    | INR (INR (INR (INL (_, opt)))) => option_size expr_size opt
    | INR (INR (INR (INR (_, kes)))) =>
        list_size (pair_size (list_size char_size) expr_size) kes)` >>
  conj_tac >- MATCH_ACCEPT_TAC prim_recTheory.WF_measure >>
  PURE_REWRITE_TAC [prim_recTheory.measure_thm, sumTheory.sum_case_def,
                    pairTheory.pair_case_def] >>
  simp[expr_size_def, listTheory.list_size_def,
       basicSizeTheory.pair_size_def, basicSizeTheory.option_size_def,
       bnfPrelimsTheory.option_size_map, bnfPrelimsTheory.pair_size_map,
       listTheory.list_size_map, SF ETA_ss]
End

Definition alloc_limits_assignment_def:
  alloc_limits_assignment cenv (BaseTarget tgt) = alloc_limits_target cenv tgt ∧
  alloc_limits_assignment cenv (TupleTarget gs) =
    alloc_limits_assignments cenv gs ∧
  alloc_limits_assignments cenv [] = T ∧
  alloc_limits_assignments cenv (g::gs) =
    (alloc_limits_assignment cenv g ∧ alloc_limits_assignments cenv gs)
Termination
  WF_REL_TAC `measure (λx. case x of
    INL (_,g) => assignment_target_size g
  | INR (_,gs) => list_size assignment_target_size gs)` >>
  simp[assignment_target_size_def, list_size_def]
End

Definition alloc_limits_iterator_def:
  alloc_limits_iterator cenv (Array e) = alloc_limits_expr cenv e ∧
  alloc_limits_iterator cenv (Range e1 e2) =
    (alloc_limits_expr cenv e1 ∧ alloc_limits_expr cenv e2)
End

Definition alloc_limits_assert_def:
  alloc_limits_assert cenv (AssertReason e) = alloc_limits_expr cenv e ∧
  alloc_limits_assert cenv (AssertCustomError err) =
    alloc_limits_exprs cenv (custom_error_exprs err) ∧
  alloc_limits_assert cenv AssertBare = T ∧
  alloc_limits_assert cenv AssertUnreachable = T
End

Definition alloc_limits_raise_def:
  alloc_limits_raise cenv (RaiseReason e) = alloc_limits_expr cenv e ∧
  alloc_limits_raise cenv (RaiseCustomError err) =
    alloc_limits_exprs cenv (custom_error_exprs err) ∧
  alloc_limits_raise cenv RaiseBare = T ∧
  alloc_limits_raise cenv RaiseUnreachable = T
End

(* alloc_limits_expr of every expression of a statement, targets' keys
   included, and the limit for every local it declares: Python allocates a
   declared local and a loop variable with Context.new_variable. *)
Definition alloc_limits_stmt_def:
  alloc_limits_stmt cenv Pass = T ∧
  alloc_limits_stmt cenv Break = T ∧
  alloc_limits_stmt cenv Continue = T ∧
  alloc_limits_stmt cenv (Expr e) = alloc_limits_expr cenv e ∧
  alloc_limits_stmt cenv (Return eo) = alloc_limits_opt cenv eo ∧
  alloc_limits_stmt cenv (AnnAssign id ty e) =
    (type_memory_bytes cenv ty < 2 ** 64 ∧ alloc_limits_expr cenv e) ∧
  alloc_limits_stmt cenv (Assign g e) =
    (alloc_limits_assignment cenv g ∧ alloc_limits_expr cenv e) ∧
  alloc_limits_stmt cenv (AugAssign ty tgt op e) =
    (alloc_limits_target cenv tgt ∧ alloc_limits_expr cenv e) ∧
  alloc_limits_stmt cenv (Append tgt e) =
    (alloc_limits_target cenv tgt ∧ alloc_limits_expr cenv e) ∧
  alloc_limits_stmt cenv (Log id es) = alloc_limits_exprs cenv es ∧
  alloc_limits_stmt cenv (Assert c reason) =
    (alloc_limits_expr cenv c ∧ alloc_limits_assert cenv reason) ∧
  alloc_limits_stmt cenv (Raise reason) = alloc_limits_raise cenv reason ∧
  alloc_limits_stmt cenv (If c ss1 ss2) =
    (alloc_limits_expr cenv c ∧ alloc_limits_stmts cenv ss1 ∧
     alloc_limits_stmts cenv ss2) ∧
  alloc_limits_stmt cenv (For id ty it n body) =
    (type_memory_bytes cenv ty < 2 ** 64 ∧ alloc_limits_iterator cenv it ∧
     alloc_limits_stmts cenv body) ∧
  alloc_limits_stmts cenv [] = T ∧
  alloc_limits_stmts cenv (s::ss) =
    (alloc_limits_stmt cenv s ∧ alloc_limits_stmts cenv ss)
Termination
  WF_REL_TAC `measure (λx. case x of
    INL (_,s) => stmt_size s | INR (_,ss) => list_size stmt_size ss)` >>
  simp[stmt_size_def, list_size_def]
End
