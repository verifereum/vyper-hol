Theory bodyCreateRawLayoutMods
Ancestors
  bodyCreateRawLayoutProjection bodyCreateOperandPreMods exprBodyPreProps
  exprSimHypsDefs allocLimits vyperTypeSystem vyperAST vyperCreate list rich_list

Theorem raw_create_layout_mods:
  expr_body_pre_mods mods ce cx env (Call ann (CreateTarget RawCreate salted rof ks) args dflt) es ==>
  ann = BaseT AddressT /\
  ?code amount ctor salts bound.
    args = code :: amount :: (ctor ++ salts) /\
    expr_type code = BaseT (BytesT (Dynamic bound)) /\ bound <= 49152 /\
    expr_type amount = BaseT (UintT 256) /\
    LENGTH salts = (if salted then 1 else 0) /\
    EVERY (\e. expr_type e = BaseT (BytesT (Fixed 32))) salts /\
    create_operand_order RawCreate salted args = code :: (ctor ++ amount :: salts) /\
    EVERY (\e. expr_body_pre_mods mods ce cx env e es) args /\
    (ctor <> [] ==> bound + abi_size_bound ce.ce_struct_fields (TupleT (MAP expr_type ctor)) < 2 ** 64)
Proof
  strip_tac >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  `EVERY (\e. expr_body_pre_mods mods ce cx env e es) args` by
    (simp[EVERY_MEM] >> rpt strip_tac >> drule_all create_operand_pre_mods >> simp[]) >>
  `alloc_limits_expr ce (Call ann (CreateTarget RawCreate salted rof ks) args dflt)` by
    fs[expr_body_pre_mods_def] >>
  drule expr_body_pre_mods_well_typed >>
  simp[well_typed_expr_def] >> strip_tac >>
  drule raw_create_args_type_layout >> strip_tac >>
  qexistsl [`code`, `amount`, `ctor`, `salts`, `bound`] >>
  Cases_on `salted` >>
  gvs[MAP_EQ_CONS, MAP_EQ_NIL, alloc_limits_expr_def, ext_call_alloc_ok_def,
      bytelike_type_bound_def, create_operand_order_def, FRONT_APPEND,
      DROP_LENGTH_APPEND, TAKE_LENGTH_APPEND]
QED
