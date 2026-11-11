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
 *
 * alloc_limits_expr also carries two more codegen-time rejections, checked
 * up front the same way, both Python's "risky overlap" panic:
 * pop_subscript_overlap for a subscript of a pop() result
 * (vyperlang/vyper#5350), and target_subscript_overlap for a target
 * subscript whose base passes through a dynamic-array element
 * (vyperlang/vyper#5280).
 *)
Theory allocLimits
Ancestors
  stmtLowering compileEnv vyperAST vyperSubscriptOverlap vfmConstants list pair

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

(* The buffers _lower_external_call allocates for an external call: the
   argument tuple in memory (new_temporary_value) and the call buffer, the
   larger of the argument and return ABI size bounds plus the method id word
   (allocate_buffer).  Their sizes are sums over the arguments, which no
   node's type_alloc_ok bounds. *)
Definition ext_call_alloc_ok_def:
  ext_call_alloc_ok cenv (ExtCall _ _ (_, arg_tys, ret) _) es =
    (let tys = MAP (lowered_value_type cenv) (TAKE (LENGTH arg_tys) (DROP 1 es));
         wrapped = if needs_external_call_wrap ret then TupleT [ret] else ret in
       SUM (MAP (type_memory_bytes cenv) tys) < 2 ** 64 /\
       MAX (abi_size_bound cenv.ce_struct_fields (TupleT tys))
           (abi_size_bound cenv.ce_struct_fields wrapped) + 32 < 2 ** 64) /\
  ext_call_alloc_ok cenv _ _ = T
End

(* A slice's .code source, replaced by its address, is smaller. *)
val is_extcode_def = exprLoweringTheory.is_extcode_def;
val extcode_addr_expr_def = exprLoweringTheory.extcode_addr_expr_def;

Theorem extcode_operands_size[local]:
  !es. es <> [] /\ is_extcode (HD es) ==>
       list_size expr_size (extcode_addr_expr (HD es) :: TL es) <
       list_size expr_size es
Proof
  Cases >> simp[] >> rename1 `is_extcode h` >>
  Cases_on `h` >> simp[is_extcode_def] >>
  rename1 `Builtin _ b l` >> Cases_on `b` >> simp[is_extcode_def] >>
  rename1 `Acc a` >> Cases_on `a` >> simp[is_extcode_def] >>
  Cases_on `l` >> simp[is_extcode_def] >>
  rename1 `_ :: tl` >> Cases_on `tl` >>
  simp[is_extcode_def, extcode_addr_expr_def, expr_size_def,
       listTheory.list_size_def]
QED

(* Whether the expression is a pop() result, or a member or element of one.
   Mirrors Python: expr.py _is_derived_from_pop (vyperlang/vyper#5350) *)
Definition base_from_pop_def:
  base_from_pop (Pop _ _) = T /\
  base_from_pop (Subscript _ e _) = base_from_pop e /\
  base_from_pop (Attribute _ e _) = base_from_pop e /\
  base_from_pop _ = F
End

(* Whether array subscript base[idx] is rejected, in a contract whose
   modules are mods: the base is derived from a pop() result, reads a
   variable other than a constant, and the index writes a variable the base
   reads or makes a risky call.  The popped element lies past the array's
   new length, so the index could overwrite it before the base is read.
   The same test as subscript_overlap, with base_from_pop in place of
   base_through_dynarray.
   Mirrors Python: expr.py _lower_array_subscript (vyperlang/vyper#5350) *)
Definition pop_subscript_overlap_def:
  pop_subscript_overlap mods base idx <=>
    is_ArrayT (expr_type base) /\ base_from_pop base /\
    let reads = nonconstant_reads mods (expr_accesses mods base) in
      reads <> [] /\
      let idx_as = expr_accesses mods idx in
        any_written reads idx_as \/ MEM RiskyAcc idx_as
End

(* The place type of an assignment target: a local's from ce_var_type,
   a module variable's from its hashmap or declared type, and an element
   or member's from its base's.  NONE when a type is unknown. *)
Definition target_place_type_def:
  target_place_type cenv (NameTarget id) =
    OPTION_MAP ValPT (cenv.ce_var_type id) /\
  target_place_type cenv (TopLevelNameTarget nsid) =
    (case cenv.ce_hashmap_info nsid of
       SOME (_, kt, vt) => SOME (MapPT kt vt)
     | NONE => OPTION_MAP ValPT (cenv.ce_module_var_type nsid)) /\
  target_place_type cenv (SubscriptTarget bt _) =
    OPTION_MAP (\pt. case pt of
                       MapPT _ vt => value_type_place vt
                     | ValPT (ArrayT t _) => ValPT t
                     | _ => ValPT (BaseT (UintT 256)))
      (target_place_type cenv bt) /\
  target_place_type cenv (AttributeTarget bt fld) =
    (case target_place_type cenv bt of
       SOME (ValPT (StructT sn)) =>
         (case ALOOKUP (get_struct_fields cenv.ce_struct_fields
                          (nsid_to_string sn)) fld of
            SOME (fty, _) => SOME (ValPT fty)
          | NONE => NONE)
     | _ => NONE)
End

(* Whether the target passes through an element of a dynamic array, whose
   resizing can leave a pointer to it stale.
   Mirrors Python: expr.py _subscript_base_length_can_stale
   (vyperlang/vyper#5280) *)
Definition target_through_dynarray_def:
  target_through_dynarray cenv (SubscriptTarget bt _) =
    ((case target_place_type cenv bt of
        SOME (ValPT (ArrayT _ (Dynamic _))) => T
      | _ => F) \/
     target_through_dynarray cenv bt) /\
  target_through_dynarray cenv (AttributeTarget bt _) =
    target_through_dynarray cenv bt /\
  target_through_dynarray cenv _ = F
End

(* Whether target subscript bt[idx] is rejected: bt passes through a
   dynamic-array element, reads a variable other than a constant, and the
   index writes a variable bt reads or makes a risky call.  The write must
   reach the live element, so bt cannot be snapshotted.  The same test as
   pop_subscript_overlap, on a target.
   Mirrors Python: expr.py check_target_overlap (vyperlang/vyper#5280) *)
Definition target_subscript_overlap_def:
  target_subscript_overlap cenv bt idx <=>
    target_through_dynarray cenv bt /\
    let mods = cenv.ce_modules;
        reads = nonconstant_reads mods (expr_accesses mods (target_to_expr bt)) in
      reads <> [] /\
      let idx_as = expr_accesses mods idx in
        any_written reads idx_as \/ MEM RiskyAcc idx_as
End

(* Every static buffer the lowering allocates for a node of the expression
   is below Python's allocation limit, 2 ** 64 bytes: the buffers of bytes
   and string literals, struct and array literals, empty(T) of a type that
   is not a word, a convert to a bytestring (the copy of a widening cast),
   the output of a calldata slice, an external call's argument and call
   buffers, and the copy unwrap_value makes of the node's value when it is
   not in memory, which every node's type_alloc_ok bounds.  The same
   recursion as byte_widths_expr. *)
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
     alloc_limits_expr cenv y /\
     ~pop_subscript_overlap cenv.ce_modules x y) /\
  alloc_limits_expr cenv (Attribute t x _) =
    (type_alloc_ok cenv t /\ alloc_limits_expr cenv x) /\
  (* Python's codegen rejects an address's .code anywhere but as slice()'s
     source (CompilerPanic ".code requires slice() context",
     codegen_venom/expr.py:672), where compile_slice reads it with
     EXTCODECOPY and lowers only its address.  The check does the same:
     Acc Code fails, and a slice's .code source is checked through its
     address (extcode_addr_expr). *)
  alloc_limits_expr cenv (Builtin t bi es) =
    (type_alloc_ok cenv t /\ bi <> Acc Code /\
     (case bi of
        MakeArray NONE _ =>
          SUM (MAP (type_memory_bytes cenv o expr_type) es) < 2 ** 64
      | MakeArray (SOME _) _ => type_memory_bytes cenv t < 2 ** 64
      | CalldataSlice n => 32 + 32 * word_size n < 2 ** 64
      | Concat _ => concat_alloc_size (MAP expr_type es) < 2 ** 64
      | _ => T) /\
     alloc_limits_exprs cenv
       (if (?n. bi = Slice n) /\ es <> [] /\ is_extcode (HD es)
        then extcode_addr_expr (HD es) :: TL es else es)) /\
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
  alloc_limits_expr cenv (Call t ct es dflt) =
    (type_alloc_ok cenv t /\ ext_call_alloc_ok cenv ct es /\
     alloc_limits_exprs cenv es /\ alloc_limits_opt cenv dflt) /\

  alloc_limits_target cenv (NameTarget _) = T /\
  alloc_limits_target cenv (TopLevelNameTarget _) = T /\
  alloc_limits_target cenv (SubscriptTarget tgt e) =
    (alloc_limits_target cenv tgt /\ alloc_limits_expr cenv e /\
     ~target_subscript_overlap cenv tgt e) /\
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
       listTheory.list_size_map, SF ETA_ss] >>
  rw[] >> drule_all extcode_operands_size >> simp[]
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

(* For a target in storage or transient storage, SOME of the place type
   compile_get_target_ptr gives it; NONE for any other target.  It reads
   only the module's variables and struct fields, so a local's frame
   doesn't change it. *)
Definition target_store_place_def:
  target_store_place cenv (NameTarget id) = NONE ∧
  target_store_place cenv (TopLevelNameTarget nsid) =
    (let pt = (case cenv.ce_hashmap_info nsid of
                 SOME (_, kt, vt) => SOME (MapPT kt vt)
               | NONE => OPTION_MAP ValPT (cenv.ce_module_var_type nsid)) in
     case FLOOKUP cenv.ce_module_vars nsid of
       SOME (StorageLoc _) => SOME pt
     | SOME (TransientLoc _) => SOME pt
     | _ => NONE) ∧
  target_store_place cenv (SubscriptTarget bt idx_e) =
    OPTION_MAP (λpt. case pt of
                       SOME (MapPT kt vt) => SOME (value_type_place vt)
                     | SOME (ValPT (ArrayT t _)) => SOME (ValPT t)
                     | _ => SOME (ValPT (BaseT (UintT 256))))
      (target_store_place cenv bt) ∧
  target_store_place cenv (AttributeTarget bt fld) =
    OPTION_MAP (λpt. case ALOOKUP (get_struct_fields cenv.ce_struct_fields
                                     (case pt of
                                        SOME (ValPT (StructT sn)) =>
                                          nsid_to_string sn
                                      | _ => "")) fld of
                       SOME (fty, _) => SOME (ValPT fty)
                     | NONE => NONE)
      (target_store_place cenv bt)
End

(* Assigning e to a storage or transient target of another type first
   converts the value to the target's layout in a buffer of the target's
   size (compile_assign_value; Python's _store_complex_type allocates it
   with Context.new_temporary_value), so that buffer is below the limit.
   No other assignment allocates it, so no other is checked. *)
Definition assign_alloc_ok_def:
  assign_alloc_ok cenv bt e ⇔
    (case target_store_place cenv bt of
      SOME (SOME (ValPT dty)) =>
        (let sty = lowered_value_type cenv e in
           ¬is_word_type dty ∧ dty ≠ sty ∧
           ¬(is_bytestring_type dty ∧ is_bytestring_type sty) ∧
           ¬(has_length_word (expr_type e) ∧ is_empty_value_expr e) ⇒
           type_memory_bytes cenv dty < 2 ** 64)
    | _ => T) ∧
    (* The snapshot of the RHS taken before an effectful target's indices
       (compile_snapshot_vv) copies a composite into a temporary of its
       lowered type's size. *)
    (expr_can_mutate cenv (target_to_expr bt) ∧
     ¬(has_length_word (expr_type e) ∧ is_empty_value_expr e) ⇒
     type_alloc_ok cenv (lowered_value_type cenv e))
End

(* The local types after statement s, as compile_stmts threads them
   (declare_stmt_local): an AnnAssign declares its local, for the rest of
   its block.  A name reused at another type in a sibling block keeps each
   block's own type.  A For's loop variable is declared for its body only. *)
Definition decl_var_type_def:
  decl_var_type cenv (AnnAssign id ty _) =
    cenv with ce_var_type updated_by (id =+ SOME ty) ∧
  decl_var_type cenv _ = cenv
End

(* alloc_limits_expr of every expression of a statement, targets' keys
   included, and the limit for every local it declares: Python allocates a
   declared local and a loop variable with Context.new_variable.  A tuple
   assignment from a memory view (is_memory_view) needs a buffer of the
   source's size: a memory source may be staged in one (compile_tuple_unpack;
   Python's _lower_tuple_unpack allocates it with
   Context.new_temporary_value), and a storage, transient or immutable source
   is read into one (compile_ensure_in_memory; Python's Context.unwrap).  The
   check covers both, so don't narrow it to the staging condition alone.
   A log's two buffers are bounded by log_alloc_ok.  Local types follow the
   declarations as compile_stmt sees them: the statements after an AnnAssign
   see its local (decl_var_type), a For's body sees its loop variable, and
   an AnnAssign's value is lowered with its local declared.  The value is
   checked without the local too: it cannot name the local it initialises,
   so the two agree on any program the front end accepts, and the proofs
   read the value both before and after the declaration. *)
Definition alloc_limits_stmt_def:
  alloc_limits_stmt cenv Pass = T ∧
  alloc_limits_stmt cenv Break = T ∧
  alloc_limits_stmt cenv Continue = T ∧
  alloc_limits_stmt cenv (Expr e) = alloc_limits_expr cenv e ∧
  alloc_limits_stmt cenv (Return eo) = alloc_limits_opt cenv eo ∧
  alloc_limits_stmt cenv (AnnAssign id ty e) =
    (type_memory_bytes cenv ty < 2 ** 64 ∧ alloc_limits_expr cenv e ∧
     alloc_limits_expr (cenv with ce_var_type updated_by (id =+ SOME ty)) e) ∧
  alloc_limits_stmt cenv (Assign g e) =
    (alloc_limits_assignment cenv g ∧ alloc_limits_expr cenv e ∧
     (case g of
        TupleTarget _ =>
          is_memory_view e ⇒ type_memory_bytes cenv (expr_type e) < 2 ** 64
      | BaseTarget bt => assign_alloc_ok cenv bt e)) ∧
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
     alloc_limits_stmts (cenv with ce_var_type updated_by (id =+ SOME ty))
       body) ∧
  alloc_limits_stmts cenv [] = T ∧
  alloc_limits_stmts cenv (s::ss) =
    (alloc_limits_stmt cenv s ∧ alloc_limits_stmts (decl_var_type cenv s) ss)
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
