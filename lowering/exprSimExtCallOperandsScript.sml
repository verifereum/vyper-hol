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
