(* Delayed capture is a proposed proof interface, not an operand hypothesis. *)
Theory exprSimExtCallOperands
Ancestors
  exprSim exprSimHyps compileEnv context finite_map list arithmetic
  venomState vyperState vyperValueOperation

Definition operand_frame_def:
  operand_frame cenv es s cut es' s' <=>
    (!x w. not_fresh_at cut x /\ lookup_var x s = SOME w ==>
       lookup_var x s' = SOME w) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
       FLOOKUP s'.vs_allocas aid = SOME b) /\
    (!aid off sz.
       FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < cut.cs_next_id /\
       (!n b sz'. local_region cenv es.scopes s n b sz' ==>
          off + sz <= b \/ b + sz' <= off) ==>
       mem_bytes_at off sz s'.vs_memory = mem_bytes_at off sz s.vs_memory) /\
    locals_kept cenv es s s'
End

Definition delayed_capture_def:
  delayed_capture ctx func cenv cx ty tv vv lo hi es s <=>
    !es' s' hi' v.
      stmt_state_rel ctx func cenv cx es' s' /\
      MAP FDOM es.scopes = MAP FDOM es'.scopes /\
      hi.cs_next_var <= hi'.cs_next_var /\ hi.cs_next_id <= hi'.cs_next_id /\
      operand_frame cenv es s hi es' s' /\
      read_result cx tv es' = (INL v,es') ==>
      vv_holds cenv cx ty tv vv es' s' /\
      vv_at cenv cx ty lo hi' es' tv vv s'
End

Theorem delayed_capture_holds[local]:
  delayed_capture ctx func cenv cx ty tv vv lo hi es s /\
  stmt_state_rel ctx func cenv cx es' s' /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  hi.cs_next_var <= hi'.cs_next_var /\ hi.cs_next_id <= hi'.cs_next_id /\
  operand_frame cenv es s hi es' s' /\
  read_result cx tv es' = (INL v,es') ==>
  vv_holds cenv cx ty tv vv es' s'
Proof
  simp[delayed_capture_def] >> metis_tac[]
QED

Theorem delayed_capture_at[local]:
  delayed_capture ctx func cenv cx ty tv vv lo hi es s /\
  stmt_state_rel ctx func cenv cx es' s' /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  hi.cs_next_var <= hi'.cs_next_var /\ hi.cs_next_id <= hi'.cs_next_id /\
  operand_frame cenv es s hi es' s' /\
  read_result cx tv es' = (INL v,es') ==>
  vv_at cenv cx ty lo hi' es' tv vv s'
Proof
  simp[delayed_capture_def] >> metis_tac[]
QED

Theorem vv_post_operand_frame[local]:
  vv_post ctx func cenv cx e es lo hi s0 es' tv vv s ==>
  operand_frame cenv es s0 lo es' s
Proof
  simp[vv_post_def, operand_frame_def] >> strip_tac >> simp[]
QED

Theorem vv_post_equal_state[local]:
  vv_post ctx func cenv cx e es lo hi s0 es' tv vv s ==>
  vv_holds cenv cx (expr_type e) tv vv es' s /\
  vv_at cenv cx (expr_type e) lo hi es' tv vv s
Proof
  simp[vv_post_def] >> metis_tac[]
QED

(* A stack witness records the value at capture time, not its provenance.
   If a place later reads a different word, the same literal is invalid. *)
Theorem changed_read_invalidates_stack[local]:
  read_result cx tv es' = (INL v,es') /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\
  is_word_type ty /\ typed_val_to_w256 tvt v <> w ==>
  ~vv_holds ce cx ty tv (StackValue ty (Lit w)) es' s'
Proof
  simp[vv_holds_def, expr_val_rel_def, eval_operand_def] >>
  metis_tac[]
QED

Theorem storage_capture_read[local]:
  read_result cx (PlaceR (StoragePlace tr slot tvt)) es =
  read_storage_slot cx tr slot tvt es
Proof
  simp[read_result_def, read_place_def]
QED

Theorem memory_capture_read[local]:
  read_result cx (PlaceR (MemoryPlace name []))
    (es with scopes := [FEMPTY |+ (name,entry)]) =
  (INL entry.value, es with scopes := [FEMPTY |+ (name,entry)])
Proof
  simp[read_result_def, read_place_def, get_scopes_def, bind_def,
       lookup_scopes_def, lift_option_type_def, return_def,
       read_memory_path_def, evaluate_subscripts_def, lift_sum_def,
       FLOOKUP_UPDATE]
QED

Theorem memory_mutation_probe[local]:
  read_result cx (PlaceR (MemoryPlace name []))
    (es with scopes := [FEMPTY |+ (name,
      <| assignable := T; type := BaseTV BoolT; value := BoolV F; popped := [] |> )]) =
    (INL (BoolV F), es with scopes := [FEMPTY |+ (name,
      <| assignable := T; type := BaseTV BoolT; value := BoolV F; popped := [] |> )]) /\
  read_result cx (PlaceR (MemoryPlace name []))
    (es with scopes := [FEMPTY |+ (name,
      <| assignable := T; type := BaseTV BoolT; value := BoolV T; popped := [] |> )]) =
    (INL (BoolV T), es with scopes := [FEMPTY |+ (name,
      <| assignable := T; type := BaseTV BoolT; value := BoolV T; popped := [] |> )]) /\
  read_result cx (Value (BoolV F)) es = (INL (BoolV F),es)
Proof
  simp[memory_capture_read, read_result_def, return_def]
QED

Theorem storage_mutation_probe[local]:
  read_result cx (PlaceR (StoragePlace T 0w (BaseTV BoolT)))
    (es with tStorage := (\a. (\k. 0w))) =
    (INL (BoolV F), es with tStorage := (\a. (\k. 0w))) /\
  read_result cx (PlaceR (StoragePlace T 0w (BaseTV BoolT)))
    (es with tStorage := (\a. (\k. 1w))) =
    (INL (BoolV T), es with tStorage := (\a. (\k. 1w)))
Proof
  simp[storage_capture_read, read_storage_slot_def, get_storage_backend_def,
       get_transient_storage_def, bind_def, return_def,
       vfmExecutionTheory.lookup_transient_storage_def,
       vyperStorageTheory.decode_value_def, vyperStorageTheory.read_slot_def,
       vyperStorageTheory.decode_base_from_slot_def, lift_option_def,
       vyperStorageTheory.slot_to_bool_def, vfmStateTheory.lookup_storage_def]
QED

(* This implication applies to PlaceR as well as Value.  Thus the
   current-state holds interface admits a literal witness for a place. *)
Theorem bool_read_stack_probe[local]:
  read_result cx tv es = (INL (BoolV b),es) ==>
  (vv_holds ce cx (BaseT BoolT) tv
     (StackValue (BaseT BoolT) (Lit 0w)) es s <=> ~b)
Proof
  strip_tac >>
  simp[vv_holds_def, expr_val_rel_def, eval_operand_def,
       vyperValueTheory.evaluate_type_def, is_word_type_def,
       valueEncodingTheory.typed_val_to_w256_def] >>
  Cases_on `b` >> simp[valueEncodingTheory.val_to_w256_def]
QED

Theorem compile_name_ptr_probe[local]:
  FLOOKUP ce.ce_vars name = SOME (PtrVar ptr_op sz) ==>
  compile_name_vv ce ty name st =
    (LocatedValue ty (mk_ptr ptr_op LocMemory),st)
Proof
  simp[exprLoweringTheory.compile_name_vv_def, compileEnvTheory.comp_return_def]
QED

(* Producer audit (C1.P.2.1; not a proved capture theorem).

   Source paths returning PlaceR, and compiler paths (line references refer
   to vyperInterpreterScript, vyperStateScript, exprLoweringScript):
   - Name: interpreter 1502-1505 -> MemoryPlace id [].  Lowering 2766,
     1481-1493 -> LocatedValue LocMemory, literal MemLoc or PtrVar operand.
     Needs local layout/region correspondence from stmt_state_rel.
   - TopLevelName: interpreter 1507-1508, state 465-483 -> StoragePlace,
     ImmutablePlace, or HashMapRef (not itself readable). Lowering 2820-2829
     -> literal Storage/Transient/Code pointer from ce_module_vars.
     Needs module layout and immutable sub-layout correspondence.
   - IfExp: interpreter 1510-1513, state 1054-1068 -> retains ONLY memory
     aggregate places; other places are forced to Value. Lowering 2767-2789
     -> nonword LocatedValue LocMemory PHI, word StackValue PHI.
     Needs chosen-branch provenance for a retained place, and branch operand
     stability; condition/branch vv_post alone only relates current values.
   - Subscript: interpreter 1524-1528, state 1166-1203 -> extends a place
     (or HashMapRef), but selects Value from immediate Value bases.
     Lowering 2268-2316 -> LocatedValue at the base location (memory default
     for StackValue); pointer is tuple offset, hashed mapping key, or
     array element pointer. Needs base provenance, captured index value,
     and correct per-location offset/stride/metadata. Dynamic bounds are
     checked at capture time, not rechecked in a future state.
   - Attribute: interpreter 1530-1533 uses the same select_result; lowering
     2321-2342 adds field offset to the recursively compiled base pointer.
     Needs base provenance and correct field layout; Value bases instead
     need snapshot-buffer framing, not mutable-place transport.
   - Pop: interpreter 1548-1551, state 1217-1260 -> retained storage element
     address or MemoryPlace path to the removed element, backed by popped
     history; immutable pop returns Value. Lowering 2832 onwards uses target
     pointer, loads/decrements length, returns LocatedValue element pointer.
     Needs target provenance and old length, plus retained element bytes /
     popped-history agreement after later operations.
   Literal, FlagMember, StructLit, Builtin (including Len), TypeBuiltin and
   Calls do not introduce PlaceR: interpreter 1509,1515-1522,1534-1546,
   1552-1556,1558-1692 and their call helpers return Value or exceptions.

   Recursive trace: Subscript(Name a, Name i) first captures MemoryPlace a[],
   then reads i and appends ValueSubscript v to the captured path.  Compilation
   first obtains a's pointer, then lower_value of i, then computes an element
   pointer with the captured index and a capture-time length check.  Replaying
   the expression in a future state is invalid if i changes.  The missing
   induction premise must relate the retained a pointer and captured path,
   not merely the current value of a or a future evaluation of this syntax.

   Candidate boundary (UNPROVED): under expr_body_pre and existing operand
   judgments, actual successful eval_expr/compile_expr fragment execution
   admits a relational post containing source-place/compiled-address identity
   (or framed Value snapshot), with frozen selection indices and base
   metadata.  Eliminating that relation in future related states would give
   delayed_capture.  stmt_state_rel supplies root layouts and vv_post supplies
   current reads/frames; neither supplies recursive path identity.  For
   Subscript/Attribute/IfExp/Pop a structural producer premise for the base,
   chosen branch or target remains unproved. Existing expr_vv_case/results_case
   supply no such recursive premise. No global induction or strengthened IH
   is asserted here. Changing lengths and popped history must be covered by
   the producer relation, not silently excluded as equal-state transport.
*)
