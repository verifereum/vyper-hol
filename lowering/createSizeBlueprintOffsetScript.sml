(* Apply the shared literal-offset rules to the operand of a blueprint call. *)
Theory createSizeBlueprintOffset
Ancestors
  blueprintLiteralOffsetProps createSizeOperandPre exprBodyPreProps
  exprLowering exprSimHypsDefs integer_word list vyperAST vyperCreate
  vyperInterpreter vyperOriginFold vyperPinFold vyperState vyperTypeSystem vyperValue words

Theorem create_blueprint_offset_bridge:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env
    (Call ty (CreateTarget (CreateFromBlueprint raw) hs rof ks) args d) es /\
  args = target::value::((if hs then [salt] else []) ++ (off::ctors)) ==>
  (blueprint_literal_offset cx hs args = is_int_literal (origin_fold_value off)) /\
  (!oty i. origin_fold_value off = Literal oty (IntL i) ==>
     (!st. bind (eval_expr cx off) (read_result cx) st = (INL (IntV i), st)) /\
     dest_NumV (IntV i) = SOME (w2n (i2w i : bytes32)))
Proof
  strip_tac >> drule expr_body_pre_static_facts >> strip_tac >>
  `MEM off args /\ expr_type off = BaseT (UintT 256)` by
    (Cases_on `hs` >> gvs[well_typed_expr_def,create_arg_types_ok_def]) >>
  `expr_body_pre cenv cx env off es` by
    metis_tac[create_call_operand_body_pre] >>
  conj_tac
  >- (mp_tac (Q.INST [`tops` |-> `tops`, `ctx` |-> `ctx`,
          `salted` |-> `hs`, `offset` |-> `off`,
          `salts` |-> `if hs then [salt] else []`,
          `target` |-> `target`, `amount` |-> `value`, `ctor` |-> `ctors`]
          blueprint_offset_literal_bit) >>
      Cases_on `hs` >> simp[blueprint_offset_form]) >>
  rpt strip_tac >>
  `expr_int_literal (origin_fold_value off) = SOME i` by simp[expr_int_literal_def] >>
  metis_tac[blueprint_literal_offset_read,blueprint_literal_offset_word]
QED
