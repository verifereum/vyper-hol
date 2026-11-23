(* TOP-LEVEL: supported_target_info, supported_target_pure.
   Local names consult local bindings; module names consult declarations.
   Whole-map and tuple writes remain outside this interface. *)
Theory supportedTargets
Ancestors
  supportedExprs supportedExprForms supportedExprTraverse supportedTypes supportedDecls
  exprLowering vyperAST list alist

(* Only definedness matters to the gate: a local root is bound, a storage
   root is a supported place root, and every index is supported. The
   lowering resolves each layer's type from its own scoped environment, so
   a local's binding type is not consulted (sibling scopes may redeclare a
   name at another type). The marker for a qualified root carries no type
   information. The linked lookup supplies its descriptor. *)
Definition supported_target_info_def:
  supported_target_info tops bindings (NameTarget name) =
    OPTION_MAP ValPT (ALOOKUP bindings name) /\
  supported_target_info tops bindings (TopLevelNameTarget id) =
    (if FST id <> NONE then SOME (ValPT NoneT)
     else if supported_place_root tops id then
       case supported_hashmap_decl tops id of
         SOME (_, _, kt, vt, _) => SOME (MapPT kt vt)
       | NONE =>
           (case supported_variable_decl tops id of
              SOME (_, _, ty, _) => SOME (ValPT ty)
            | NONE => NONE)
     else NONE) /\
  supported_target_info tops bindings (SubscriptTarget base key) =
    (if supported_expr tops key then supported_target_info tops bindings base
     else NONE) /\
  supported_target_info tops bindings (AttributeTarget base field) =
    supported_target_info tops bindings base
End

Definition supported_target_pure_def:
  supported_target_pure tops (NameTarget name) = T /\
  supported_target_pure tops (TopLevelNameTarget id) = T /\
  supported_target_pure tops (SubscriptTarget base key) =
    (supported_target_pure tops base /\ supported_pure_expr tops key) /\
  supported_target_pure tops (AttributeTarget base field) =
    supported_target_pure tops base
End

Theorem supported_target_pure_expr_exclusion:
  (!e. supported_pure_expr tops e ==> ~supported_expr_exists p e) /\
  supported_target_pure tops target ==> ~supported_target_exists p target
Proof
  `(!e:expr. T) /\
   !target. (!e. supported_pure_expr tops e ==> ~supported_expr_exists p e) /\
     supported_target_pure tops target ==> ~supported_target_exists p target`
    suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  rw[supported_target_pure_def, supported_expr_exists_def] >> metis_tac[]
QED

(* Until #550 changes Assign evaluation order, an effectful target may only
   precede an RHS whose lowering has no child computations. Name values keep
   their location until the final store; word literals are immediate values. *)
Definition supported_uncomputed_rhs_def:
  supported_uncomputed_rhs (Name ty name) = T /\
  supported_uncomputed_rhs (TopLevelName ty id) = T /\
  supported_uncomputed_rhs (Literal ty lit) = supported_word_type ty /\
  supported_uncomputed_rhs e = F
End
