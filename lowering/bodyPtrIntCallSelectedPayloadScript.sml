(* Task-local design interface, not a compiler-production theorem.
   A copied IfExp arm is a snapshot even when its source result is a
   MemoryPlace. Pop aliases retain their complete extended place path;
   captured Pop reads use the complete post-pop state (including history).
   Pointer validity and taint remain separate, existing ptr predicates. *)
Theory bodyPtrIntCallSelectedPayload
Ancestors
  bodyPtrIntCallIdentityProbe loweringPosts vyperInterpreter vyperState
  vyperAST finite_map venomState

Datatype:
  intcall_payload_mode = IntcallAlias | IntcallSnapshot
End

Definition intcall_alias_valid_def:
  intcall_alias_valid cenv cx t result op s <=>
    ?w. eval_operand op s = SOME w /\
        place_ptr_rel cenv cx s result w (SOME LocMemory) (Type t)
End

Definition intcall_snapshot_valid_def:
  intcall_snapshot_valid cx t result op capture v s <=>
    read_result cx result capture = (INL v,capture) /\
    expr_val_rel cx t v op s
End

Definition intcall_read_compatible_def:
  intcall_read_compatible cx result v es <=>
    read_result cx result es = (INL v,es)
End

(* capture and v are explicit parameters, not hidden existential witnesses. *)
Definition intcall_selected_payload_def:
  intcall_selected_payload mode cenv cx t result op capture v es s <=>
    case mode of
      IntcallAlias => intcall_alias_valid cenv cx t result op s
    | IntcallSnapshot => intcall_snapshot_valid cx t result op capture v s /\
                         intcall_read_compatible cx result v es
End

Theorem intcall_alias_name:
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME b /\
  cenv.ce_var_type id = SOME ann /\
  evaluate_type (get_tenv cx) ann = SOME tv ==>
  intcall_alias_valid cenv cx ann (PlaceR (MemoryPlace id [])) (Var p) s
Proof
  strip_tac >> drule_all intcall_name_place_identity >>
  strip_tac >> simp[intcall_alias_valid_def, eval_operand_def] >>
  metis_tac[]
QED

Theorem intcall_snapshot_intro:
  read_result cx result capture = (INL v,capture) /\
  expr_val_rel cx t v op s ==>
  intcall_snapshot_valid cx t result op capture v s
Proof
  simp[intcall_snapshot_valid_def]
QED

Theorem intcall_alias_operand:
  eval_operand op' s = eval_operand op s ==>
  (intcall_alias_valid cenv cx t result op' s <=>
   intcall_alias_valid cenv cx t result op s)
Proof
  simp[intcall_alias_valid_def]
QED

Theorem intcall_snapshot_transport:
  intcall_snapshot_valid cx t result op capture v s /\
  eval_operand op' s' = eval_operand op s /\
  s'.vs_memory = s.vs_memory ==>
  intcall_snapshot_valid cx t result op' capture v s'
Proof
  simp[intcall_snapshot_valid_def, expr_val_rel_def]
QED

Theorem intcall_snapshot_delayed_read:
  intcall_snapshot_valid cx t result op capture v s /\
  intcall_read_compatible cx result v es ==>
  read_result cx result es = (INL v,es) /\ expr_val_rel cx t v op s
Proof
  simp[intcall_snapshot_valid_def, intcall_read_compatible_def]
QED

Theorem intcall_selected_snapshot:
  intcall_selected_payload IntcallSnapshot cenv cx t result op capture v es s <=>
  intcall_snapshot_valid cx t result op capture v s /\
  intcall_read_compatible cx result v es
Proof
  simp[intcall_selected_payload_def]
QED

Theorem intcall_selected_alias:
  intcall_selected_payload IntcallAlias cenv cx t result op capture v es s <=>
  intcall_alias_valid cenv cx t result op s
Proof
  simp[intcall_selected_payload_def]
QED

val _ = export_theory ();
