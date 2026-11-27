Theory bodyCreateRawLayoutProjection
Ancestors
  vyperTypeSystem vyperAST list rich_list

Theorem raw_create_args_type_layout:
  create_arg_types_ok RawCreate salted (MAP expr_type args) ==>
  ?code amount ctor salts bound.
    args = code :: amount :: (ctor ++ salts) /\
    expr_type code = BaseT (BytesT (Dynamic bound)) /\ bound <= 49152 /\
    expr_type amount = BaseT (UintT 256) /\
    MAP expr_type salts = (if salted then [BaseT (BytesT (Fixed 32))] else [])
Proof
  Cases_on `args` >- simp[create_arg_types_ok_def] >>
  rename1 `code::tail` >> Cases_on `tail` >- simp[create_arg_types_ok_def] >>
  rename1 `code::amount::rest` >>
  reverse (Cases_on `salted`)
  >- (simp[create_arg_types_ok_def] >> strip_tac >>
      rename1 `bound <= 49152` >>
      qexists_tac `bound` >> simp[]) >>
  Cases_on `rest` using listTheory.SNOC_CASES
  >- simp[create_arg_types_ok_def] >>
  rename1 `SNOC salt ctor` >>
  simp[create_arg_types_ok_raw_create, SNOC_APPEND, FRONT_APPEND,
       FRONT_CONS_NOT_NIL, LAST_CONS_cond, LAST_APPEND] >>
  strip_tac >> rename1 `bound <= 49152` >>
  qexistsl_tac [`ctor`,`[salt]`,`bound`] >> fs[GSYM APPEND_ASSOC, FRONT_APPEND]
QED
