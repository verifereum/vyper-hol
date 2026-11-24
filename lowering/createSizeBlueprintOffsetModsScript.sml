(* Apply the shared literal-offset rules to the operand of a blueprint call. *)
Theory createSizeBlueprintOffsetMods
Ancestors
  createSizeBlueprintOffset createExprSizeExitDefsMods
  alist constSubstModsCorrect blueprintLiteralOffsetProps createSizeOperandPreMods exprBodyPreProps
  exprLowering exprSimHypsDefs integer_word list vyperAST vyperCreate
  vyperInterpreter vyperOriginFold vyperPinFold vyperState vyperTypeSystem vyperValue words

Theorem blueprint_offset_literal_bit_mods:
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALL_DISTINCT (MAP FST mods) /\
  expr_body_pre_mods mods cenv cx env offset es /\
  LENGTH salts = (if salted then 1 else 0) ==>
  blueprint_literal_offset cx salted (target::amount::(salts ++ offset::ctor)) =
    IS_SOME (expr_int_literal (origin_fold_value offset))
Proof
  cheat
QED

Theorem create_blueprint_offset_bridge_mods:
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  expr_body_pre_mods mods cenv cx env
    (Call ty (CreateTarget (CreateFromBlueprint raw) hs rof ks) args d) es /\
  args = target::value::((if hs then [salt] else []) ++ (off::ctors)) ==>
  (blueprint_literal_offset cx hs args = is_int_literal (origin_fold_value off)) /\
  (!oty i. origin_fold_value off = Literal oty (IntL i) ==>
     (!st. bind (eval_expr cx off) (read_result cx) st = (INL (IntV i), st)) /\
     dest_NumV (IntV i) = SOME (w2n (i2w i : bytes32)))
Proof
  cheat
QED
