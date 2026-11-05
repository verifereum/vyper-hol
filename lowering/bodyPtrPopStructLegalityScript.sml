Theory bodyPtrPopStructLegality
Ancestors
  bodyPtrPopDynAssignProbe supportedStmts supportedProgram vyperTypeSystem
  vyperTypeContract finite_map vyperValue

(* Bounded source-contract fixture. A named struct permits field projection
   unlike the tuple diagnostic; its sole field has three array levels. *)
Definition pop_struct_ty_def:
  pop_struct_ty = StructT (NONE,"Box")
End
Definition pop_struct_fields_def:
  pop_struct_fields = [("a", pop_dyn_assign_ty)]
End
Definition pop_struct_env_def:
  pop_struct_env = <|
    current_src := NONE;
    var_types := FEMPTY |+ ("replacement",pop_struct_ty);
    var_assignable := FEMPTY |+ ("replacement",T);
    bare_globals := FEMPTY;
    bare_global_assignable := FEMPTY |+ ((NONE,"A"),pop_struct_ty);
    toplevel_vtypes := FEMPTY;
    type_defs := FEMPTY |+ ((NONE,"Box"),StructArgs pop_struct_fields);
    fn_sigs := FEMPTY; flag_members := FEMPTY |>
End
Definition pop_struct_root_def:
  pop_struct_root = TopLevelNameTarget (NONE,"A")
End
Definition pop_struct_field_def:
  pop_struct_field = AttributeTarget pop_struct_root "a"
End
Definition pop_struct_body_def:
  pop_struct_body =
    [Assign (BaseTarget pop_struct_root) (Name pop_struct_ty "replacement");
     Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))]
End

Theorem pop_struct_field_typing:
  type_place_target pop_struct_env pop_struct_field =
    SOME (Type pop_dyn_assign_ty)
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_struct_saved_typing:
  type_place_target pop_struct_env
    (SubscriptTarget pop_struct_field (Literal (BaseT (UintT 256)) (IntL 0))) =
    SOME (Type (ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 1)) (Dynamic 1)))
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_struct_assign_typing:
  type_stmt pop_struct_env (BaseT (UintT 256))
    (Assign (BaseTarget pop_struct_root) (Name pop_struct_ty "replacement")) =
    SOME pop_struct_env
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_struct_return_typing:
  type_stmt pop_struct_env (BaseT (UintT 256))
    (Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))) =
    SOME pop_struct_env
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

(* The preceding assignment typing uses an existing local. A zero-argument
   callee with only Assign;Return has no such local: push_function supplies
   bound arguments, not its caller's local scopes. This is an exact missing
   source-contract condition, not an exclusion of all struct replacements. *)
Theorem pop_struct_no_local_assignment_rejected:
  type_stmt (pop_struct_env with <| var_types := FEMPTY;
                                  var_assignable := FEMPTY |>)
    (BaseT (UintT 256))
    (Assign (BaseTarget pop_struct_root) (Name pop_struct_ty "replacement")) = NONE
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED
