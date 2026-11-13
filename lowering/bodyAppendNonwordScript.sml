(* S1 cases for Append to a local, subscript or attribute target whose element
   is not a full word (struct, tuple, array, bytes, string, or a narrow word).

   The lowering resolves the target's array pointer (compile_get_target_ptr),
   lowers the element, stages a non-word element through a fresh buffer with
   compile_store_memory (relayout from the lowered type to the array's element
   type), then appends it (compile_dynarray_append): compile_store_memory into a
   memory array, compile_store_slots into a storage or transient array.

   body_append_nonword_local: the target's root is a local, so the array is in
   memory.  The element type comes from the typing (type_place_target); the
   gate's bindings-based target info isn't tied to it, so the element may be
   wider than expr_type e.

   body_append_nonword_nested: the root is a top-level storage or transient
   variable, below a subscript or attribute.  The gate's target info is then
   computed from the module's declarations, so the element type is exactly
   expr_type e.

   With the full-word case (stmtSimAppendResolved) these partition the
   non-top-level Append targets of body_append_case. *)
Theory bodyAppendNonword
Ancestors
  bodySim targetPlaceSim supportedTypes

Theorem body_append_nonword_local:
  !cx bt e.
    (!s'' p t'. eval_target_place cx bt s'' = (INL p,t') ==> body_expr_ok cx e) /\
    body_base_target_ok cx bt /\
    (?id. target_root bt = NameTarget id) /\
    ~supported_full_word_type (expr_type e) ==>
    body_stmt_ok cx (Append bt e)
Proof
  cheat
QED

Theorem body_append_nonword_nested:
  !cx bt e.
    (!s'' p t'. eval_target_place cx bt s'' = (INL p,t') ==> body_expr_ok cx e) /\
    body_base_target_ok cx bt /\
    (!id. bt <> TopLevelNameTarget id) /\
    (?id. target_root bt = TopLevelNameTarget id) /\
    ~supported_full_word_type (expr_type e) ==>
    body_stmt_ok cx (Append bt e)
Proof
  cheat
QED
