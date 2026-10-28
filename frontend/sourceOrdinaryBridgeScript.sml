Theory sourceOrdinaryBridge
Ancestors
  sourceExprElaborate sourceExprProps sourceExprDefs sourceSyntax sourceConstEval
  jsonToVyperExpr jsonAST vyperAST list pair

(* Small feasibility kernel for the ordinary bridge, NOT a program frontend.
   A residual node is selected BEFORE elaboration. Its children carry original
   syntax and normalization results, not compiler replacement JSON literals.
   See sourceOrdinaryBridge.md for the remaining whole-program boundary. *)

(* Only original named/qualified designators are admitted by this adapter.
   In particular JE_Folded is NOT a designator and cannot affect dispatch.
   Type/source/import fields remain explicit inherited legacy claims. *)
Definition source_ordinary_designator_def:
  source_ordinary_designator (SX_Name name) (JE_Name id tc src ty) =
    (name = id) /\
  source_ordinary_designator (SX_Attribute base name)
    (JE_Attribute annotated attr tc btn btc src ty) =
    (name = attr /\ source_ordinary_designator base annotated) /\
  source_ordinary_designator _ _ = F
End

(* The common strict expression route, reused unchanged. No runtime expression
   supplied by JSON is substituted for the result of this computation. *)
Definition source_ordinary_verified_def:
  source_ordinary_verified fuel env scopes table constants bindings ty original =
    source_expr_elaborate fuel env scopes table constants bindings ty original
End

(* A one-layer residual adapter for ordinary calls with no pop receiver or
   calldata shortcut. It consumes RUNTIME child ASTs directly via the existing
   legacy translate_call helper. It does NOT implement a new builtin rule.
   The caller still owes certified child equations and the explicit residual
   policy decision. These are NOT established just by this adapter succeeding.
   This function is deliberately not a fallback after Source failure. *)
Definition source_ordinary_call_layer_def:
  source_ordinary_call_layer ctx original func arguments keywords ret_ty src =
    case original of
      SX_Call callee source_args source_keywords =>
        if source_ordinary_designator callee func /\
           source_args = MAP FST arguments /\
           source_keywords = MAP (\(key,(syntax,result)). (key,syntax)) keywords then
          source_const_combine (\args kws.
            SC_Value (translate_call ctx func args kws ret_ty src NONE))
            (source_const_collect (MAP SND arguments))
            (source_const_collect
              (MAP (\(key,(syntax,result)).
                source_const_then result (\e. SC_Value (key,e))) keywords))
        else SC_Invalid SCErr_Domain
    | _ => SC_Invalid SCErr_Domain
End

Theorem source_ordinary_verified_equation:
  source_ordinary_verified fuel env scopes table constants bindings ty original =
  source_expr_elaborate fuel env scopes table constants bindings ty original
Proof
  simp[source_ordinary_verified_def]
QED

Theorem source_ordinary_verified_typed:
  source_ordinary_verified fuel env scopes table constants bindings ty original = SC_Value e ==>
  expr_type e = ty /\ well_typed_expr env e
Proof
  simp[source_ordinary_verified_def] >>
  MATCH_ACCEPT_TAC source_expr_elaborate_typed
QED

Theorem source_ordinary_call_layer_original_mismatch:
  source_args <> MAP FST arguments ==>
  source_ordinary_call_layer ctx (SX_Call callee source_args source_keywords)
    func arguments keywords ret_ty src = SC_Invalid SCErr_Domain
Proof
  simp[source_ordinary_call_layer_def]
QED

Theorem source_ordinary_call_layer_folded_designator:
  source_ordinary_call_layer ctx (SX_Call callee source_args source_keywords)
    (JE_Folded original replacement) arguments keywords ret_ty src =
  SC_Invalid SCErr_Domain
Proof
  Cases_on `callee` >>
  simp[source_ordinary_call_layer_def, source_ordinary_designator_def]
QED

(* The positive equation is polymorphic in the legacy callable, its inherited
   result/signature claims and the already-normalized children. No encoding of
   e back into JSON, inferred literal type, or trusted folded branch is needed. *)
Theorem source_ordinary_call_layer_values:
  source_ordinary_designator callee func ==>
  source_ordinary_call_layer ctx
    (SX_Call callee (MAP FST children) []) func
    (MAP (\(syntax,e). (syntax,SC_Value e)) children) [] ret_ty src =
  SC_Value (translate_call ctx func (MAP SND children) [] ret_ty src NONE)
Proof
  strip_tac >>
  `MAP FST (MAP (\(syntax,e). (syntax,SC_Value e)) children) = MAP FST children` by
    (Induct_on `children` >> simp[FORALL_PROD]) >>
  `source_const_collect
     (MAP SND (MAP (\(syntax,e). (syntax,SC_Value e)) children)) =
     SC_Value (MAP SND children)` by
    (Induct_on `children` >>
     simp[source_const_collect_def, source_const_combine_def, FORALL_PROD]) >>
  simp[source_ordinary_call_layer_def, source_const_collect_def,
       source_const_combine_def]
QED
