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
 *                           every local it declares, and a log's buffers
 *)
Theory allocLimits
Ancestors
  stmtLowering compileEnv vyperAST vfmConstants list pair

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

(* A value of type t that is not a word fits below Python's allocation
   limit, 2 ** 64 bytes, in memory.  unwrap_value copies an aggregate held
   in storage, transient storage or code into a buffer of this size. *)
Definition type_alloc_ok_def:
  type_alloc_ok cenv t <=>
    (~is_word_type t ==> type_memory_bytes cenv t < 2 ** 64)
End

(* Every static buffer the lowering allocates for a node of the expression
   is below Python's allocation limit, 2 ** 64 bytes: the buffers of bytes
   and string literals, struct and array literals, empty(T) of a type that
   is not a word, a convert to a bytestring (the copy of a widening cast),
   the output of a calldata slice, and the copy unwrap_value makes of the
   node's value when it is not in memory, which every node's type_alloc_ok
   bounds.  The same recursion as byte_widths_expr. *)
Definition alloc_limits_expr_def:
  alloc_limits_expr cenv (Name t _) = type_alloc_ok cenv t /\
  alloc_limits_expr cenv (TopLevelName t _) = type_alloc_ok cenv t /\
  alloc_limits_expr cenv (FlagMember t _ _) = type_alloc_ok cenv t /\
  alloc_limits_expr cenv (IfExp t c x y) =
    (type_alloc_ok cenv t /\ alloc_limits_expr cenv c /\
     alloc_limits_expr cenv x /\ alloc_limits_expr cenv y) /\
  alloc_limits_expr cenv (Literal t l) =
    (type_alloc_ok cenv t /\ literal_alloc_ok l) /\
  alloc_limits_expr cenv (StructLit t nsid kes) =
    (type_alloc_ok cenv t /\
     type_memory_bytes cenv (StructT nsid) < 2 ** 64 /\
     alloc_limits_named_exprs cenv kes) /\
  alloc_limits_expr cenv (Subscript t x y) =
    (type_alloc_ok cenv t /\ alloc_limits_expr cenv x /\
     alloc_limits_expr cenv y) /\
  alloc_limits_expr cenv (Attribute t x _) =
    (type_alloc_ok cenv t /\ alloc_limits_expr cenv x) /\
  alloc_limits_expr cenv (Builtin t bi es) =
    (type_alloc_ok cenv t /\
     (case bi of
        MakeArray NONE _ =>
          SUM (MAP (type_memory_bytes cenv o expr_type) es) < 2 ** 64
      | MakeArray (SOME _) _ => type_memory_bytes cenv t < 2 ** 64
      | CalldataSlice n => 32 + 32 * word_size n < 2 ** 64
      | _ => T) /\
     alloc_limits_exprs cenv es) /\
  alloc_limits_expr cenv (TypeBuiltin t tb ty es) =
    (type_alloc_ok cenv t /\
     (case tb of
        Empty => (~is_word_type ty ==> type_memory_bytes cenv ty < 2 ** 64)
      | Convert => (~is_word_type ty ==> type_memory_bytes cenv ty < 2 ** 64)
      | AbiEncode ensure mid =>
          (let single = (LENGTH es = 1 /\ ~ensure) in
           let enc_ty = if single then expr_type (HD es)
                        else TupleT (MAP expr_type es) in
           let mid_size = case mid of NONE => 0 | SOME _ => 4 in
           32 + 32 * word_size
             (abi_size_bound cenv.ce_struct_fields enc_ty + mid_size) < 2 ** 64 /\
           (~single ==> type_memory_bytes cenv enc_ty < 2 ** 64))
      | AbiDecode unwrap =>
          type_memory_bytes cenv
            (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) <
          2 ** 64
      | _ => T) /\
     alloc_limits_exprs cenv es) /\
  alloc_limits_expr cenv (Pop t tgt) =
    (type_alloc_ok cenv t /\ alloc_limits_target cenv tgt) /\
  alloc_limits_expr cenv (Call t _ es dflt) =
    (type_alloc_ok cenv t /\ alloc_limits_exprs cenv es /\
     alloc_limits_opt cenv dflt) /\

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
   declared local and a loop variable with Context.new_variable.  A tuple
   assignment from a memory view (is_memory_view) needs a buffer of the
   source's size: a memory source may be staged in one (compile_tuple_unpack;
   Python's _lower_tuple_unpack allocates it with
   Context.new_temporary_value), and a storage, transient or immutable source
   is read into one (compile_ensure_in_memory; Python's Context.unwrap).  The
   check covers both, so don't narrow it to the staging condition alone. *)
(* A log's two buffers are below Python's allocation limit, as lower_Log
   allocates them through allocate_buffer: the data of its non-indexed
   arguments, and their ABI encoding.  An event the compile env doesn't
   know has none, since compile_stmt emits INVALID for it. *)
Definition log_alloc_ok_def:
  log_alloc_ok cenv id es ⇔
    case cenv.ce_event_info (nsid_to_string id) of
      NONE => T
    | SOME (_, _, flags) =>
        let tys = log_non_indexed_types flags (MAP expr_type es) in
          SUM (MAP (type_memory_bytes cenv) tys) < 2 ** 64 ∧
          abi_size_bound cenv.ce_struct_fields (TupleT tys) < 2 ** 64
End

Definition alloc_limits_stmt_def:
  alloc_limits_stmt cenv Pass = T ∧
  alloc_limits_stmt cenv Break = T ∧
  alloc_limits_stmt cenv Continue = T ∧
  alloc_limits_stmt cenv (Expr e) = alloc_limits_expr cenv e ∧
  alloc_limits_stmt cenv (Return eo) = alloc_limits_opt cenv eo ∧
  alloc_limits_stmt cenv (AnnAssign id ty e) =
    (type_memory_bytes cenv ty < 2 ** 64 ∧ alloc_limits_expr cenv e) ∧
  alloc_limits_stmt cenv (Assign g e) =
    (alloc_limits_assignment cenv g ∧ alloc_limits_expr cenv e ∧
     (case g of
        TupleTarget _ =>
          is_memory_view e ⇒ type_memory_bytes cenv (expr_type e) < 2 ** 64
      | _ => T)) ∧
  alloc_limits_stmt cenv (AugAssign ty tgt op e) =
    (alloc_limits_target cenv tgt ∧ alloc_limits_expr cenv e) ∧
  alloc_limits_stmt cenv (Append tgt e) =
    (alloc_limits_target cenv tgt ∧ alloc_limits_expr cenv e) ∧
  alloc_limits_stmt cenv (Log id es) =
    (alloc_limits_exprs cenv es ∧ log_alloc_ok cenv id es) ∧
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

(* ABI allocations are physical capacities, not just used byte counts. *)
Theorem alloc_limits_abi_encode_output:
  alloc_limits_expr ce (TypeBuiltin t (AbiEncode ensure mid) ty es) ==>
  32 + 32 * word_size
    (abi_size_bound ce.ce_struct_fields
      (if LENGTH es = 1 /\ ~ensure then expr_type (HD es)
       else TupleT (MAP expr_type es)) +
     (case mid of NONE => 0 | SOME _ => 4)) < 2 ** 64
Proof
  simp[Once alloc_limits_expr_def, LET_THM]
QED

Theorem alloc_limits_abi_encode_staging:
  alloc_limits_expr ce (TypeBuiltin t (AbiEncode ensure mid) ty es) /\
  ~(LENGTH es = 1 /\ ~ensure) ==>
  type_memory_bytes ce (TupleT (MAP expr_type es)) < 2 ** 64
Proof
  Cases_on `LENGTH es = 1 /\ ~ensure` >>
  simp[Once alloc_limits_expr_def, LET_THM]
QED

Theorem alloc_limits_abi_decode_output:
  alloc_limits_expr ce (TypeBuiltin t (AbiDecode unwrap) ty es) ==>
  type_memory_bytes ce
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) < 2 ** 64
Proof
  simp[Once alloc_limits_expr_def]
QED

Theorem alloc_limits_abi_rounded_regressions:
  32 + 32 * word_size (32+4) = 96 /\
  32 + 32 * word_size (32+4) <> 68 /\
  32 + 32 * word_size 32 = 64 /\
  EVERY (\n. n <= 32 * word_size n) [0;1;31;32;33;36] /\
  32 + 32 * word_size (2 ** 64 - 64) < 2 ** 64 /\
  ~(32 + 32 * word_size (2 ** 64 - 63) < 2 ** 64)
Proof
  EVAL_TAC
QED
