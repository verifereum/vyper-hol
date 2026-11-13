(* TOP-LEVEL: supported_target_info, supported_target_pure.
   Resolve each target layer from its immediate base descriptor. Local names
   consult local bindings; module names consult declarations. Whole-map and
   tuple writes remain outside this interface. *)
Theory supportedTargets
Ancestors
  supportedExprs supportedExprForms supportedTypes supportedDecls
  exprLowering vyperAST list alist

Definition supported_target_info_def:
  supported_target_info tops bindings (NameTarget name) =
    (case ALOOKUP bindings name of
       SOME ty => if supported_place_type tops ty then SOME (ValPT ty) else NONE
     | NONE => NONE) /\
  supported_target_info tops bindings (TopLevelNameTarget id) =
    (if supported_place_root tops id then
       case supported_hashmap_decl tops id of
         SOME (_, _, kt, vt, _) => SOME (MapPT kt vt)
       | NONE =>
           (case supported_variable_decl tops id of
              SOME (_, _, ty, _) => SOME (ValPT ty)
            | NONE => NONE)
     else NONE) /\
  supported_target_info tops bindings (SubscriptTarget base key) =
    (if supported_expr tops key then
       case supported_target_info tops bindings base of
         SOME (MapPT kt vt) => SOME (value_type_place vt)
       | SOME (ValPT (ArrayT elem bound)) => SOME (ValPT elem)
       | _ => NONE
     else NONE) /\
  supported_target_info tops bindings (AttributeTarget base field) =
    (case supported_target_info tops bindings base of
       SOME (ValPT (StructT id)) =>
         (case supported_struct_fields tops id of
            SOME fields => OPTION_MAP ValPT (ALOOKUP fields field)
          | NONE => NONE)
     | _ => NONE)
End

Definition supported_target_pure_def:
  supported_target_pure tops (NameTarget name) = T /\
  supported_target_pure tops (TopLevelNameTarget id) = T /\
  supported_target_pure tops (SubscriptTarget base key) =
    (supported_target_pure tops base /\ supported_pure_expr tops key) /\
  supported_target_pure tops (AttributeTarget base field) =
    supported_target_pure tops base
End

(* Until #550 changes Assign evaluation order, an effectful target may only
   precede an RHS whose lowering has no child computations. Name values keep
   their location until the final store; word literals are immediate values. *)
Definition supported_uncomputed_rhs_def:
  supported_uncomputed_rhs (Name ty name) = T /\
  supported_uncomputed_rhs (TopLevelName ty id) = T /\
  supported_uncomputed_rhs (Literal ty lit) = supported_word_type ty /\
  supported_uncomputed_rhs e = F
End

Theorem supported_target_array:
  supported_target_info tops bindings target_base = SOME (ValPT (ArrayT elem bound)) /\
  supported_expr tops key ==>
  supported_target_info tops bindings (SubscriptTarget target_base key) = SOME (ValPT elem)
Proof
  simp[supported_target_info_def]
QED

Theorem supported_target_map:
  supported_target_info tops bindings target_base = SOME (MapPT kt vt) /\
  supported_expr tops key ==>
  supported_target_info tops bindings (SubscriptTarget target_base key) =
    SOME (value_type_place vt)
Proof
  simp[supported_target_info_def]
QED

Theorem supported_target_field:
  supported_target_info tops bindings target_base = SOME (ValPT (StructT id)) /\
  supported_struct_fields tops id = SOME fields ==>
  supported_target_info tops bindings (AttributeTarget target_base field_name) =
    OPTION_MAP ValPT (ALOOKUP fields field_name)
Proof
  simp[supported_target_info_def]
QED
