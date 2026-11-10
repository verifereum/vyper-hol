Theory convertScalarTyping
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts
  exprSimConvert exprSimHypsDefs exprSimHyps exprLowering compileEnv vyperAST
  vyperTypeSystem vyperValue exprLoweringProps emitHelper exprBopLowering
Libs
  pairLib

Theorem scalar_conversion_to_bytes:
  !src m. valid_conversion src (BaseT (BytesT (Fixed m))) /\
    ~is_bytestring_type src ==>
    (?n. src = BaseT (BytesT (Fixed n))) \/
    (src = BaseT AddressT /\ 20 <= m /\ m <= 32) \/
    (?n. src = BaseT (UintT n) /\ n <= 8 * m) \/
    (?n. src = BaseT (IntT n) /\ n <= 8 * m) \/
    (?name. src = FlagT name /\ m = 32)
Proof
  Cases_on `src` >> simp[valid_conversion_def, is_bytestring_type_def] >>
  rename1 `valid_conversion (BaseT bt) _` >> Cases_on `bt` >>
  simp[valid_conversion_def, is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[valid_conversion_def, is_bytestring_type_def]
QED

Theorem scalar_conversion_to_flag:
  !src name. valid_conversion src (FlagT name) ==>
    src = BaseT (UintT 256)
Proof
  Cases_on `src` >> simp[valid_conversion_def] >>
  rename1 `valid_conversion (BaseT bt) _` >> Cases_on `bt` >> simp[valid_conversion_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >> simp[valid_conversion_def]
QED

Theorem scalar_conversion_from_fixed:
  !m t. valid_conversion (BaseT (BytesT (Fixed m))) t /\
    ~is_bytestring_type t ==>
    t = BaseT BoolT \/ (?n. t = BaseT (IntT n)) \/
    (?n. t = BaseT (UintT n)) \/ t = BaseT AddressT \/
    t = BaseT DecimalT \/ (?k. t = BaseT (BytesT (Fixed k)))
Proof
  Cases_on `t` >> simp[valid_conversion_def, is_bytestring_type_def] >>
  rename1 `valid_conversion _ (BaseT bt)` >> Cases_on `bt` >>
  simp[valid_conversion_def, is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[valid_conversion_def, is_bytestring_type_def]
QED

Theorem scalar_conversion_from_address:
  !t. valid_conversion (BaseT AddressT) t /\ ~is_bytestring_type t ==>
    (?n. t = BaseT (UintT n)) \/
    (?m. t = BaseT (BytesT (Fixed m)) /\ 20 <= m /\ m <= 32)
Proof
  Cases_on `t` >> simp[valid_conversion_def, is_bytestring_type_def] >>
  rename1 `valid_conversion _ (BaseT bt)` >> Cases_on `bt` >>
  simp[valid_conversion_def, is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[valid_conversion_def, is_bytestring_type_def]
QED

Theorem scalar_conversion_from_decimal:
  !t. valid_conversion (BaseT DecimalT) t ==>
    (?n. t = BaseT (IntT n)) \/ (?n. t = BaseT (UintT n))
Proof
  Cases_on `t` >> simp[valid_conversion_def] >>
  rename1 `valid_conversion _ (BaseT bt)` >> Cases_on `bt` >> simp[valid_conversion_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >> simp[valid_conversion_def]
QED

Theorem scalar_conversion_from_flag:
  !name t. valid_conversion (FlagT name) t ==>
    (?n. t = BaseT (IntT n)) \/ (?n. t = BaseT (UintT n)) \/
    t = BaseT (BytesT (Fixed 32))
Proof
  Cases_on `t` >> simp[valid_conversion_def] >>
  rename1 `valid_conversion _ (BaseT bt)` >> Cases_on `bt` >> simp[valid_conversion_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >> simp[valid_conversion_def]
QED

Theorem scalar_conversion_from_uint:
  !n t. valid_conversion (BaseT (UintT n)) t /\
    ~is_bytestring_type t /\ ~int_convert_pair (BaseT (UintT n)) t ==>
    (?m. t = BaseT (BytesT (Fixed m)) /\ n <= 8 * m) \/
    t = BaseT AddressT \/ t = BaseT DecimalT \/
    (?name. t = FlagT name /\ n = 256)
Proof
  Cases_on `t` >> simp[valid_conversion_def, is_bytestring_type_def,
    int_convert_pair_def] >>
  rename1 `valid_conversion _ (BaseT bt)` >> Cases_on `bt` >>
  simp[valid_conversion_def, is_bytestring_type_def, int_convert_pair_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[valid_conversion_def, is_bytestring_type_def, int_convert_pair_def]
QED

Theorem scalar_conversion_from_int:
  !n t. valid_conversion (BaseT (IntT n)) t /\
    ~is_bytestring_type t /\ ~int_convert_pair (BaseT (IntT n)) t ==>
    (?m. t = BaseT (BytesT (Fixed m)) /\ n <= 8 * m) \/
    t = BaseT AddressT \/ t = BaseT DecimalT
Proof
  Cases_on `t` >> simp[valid_conversion_def, is_bytestring_type_def,
    int_convert_pair_def] >>
  rename1 `valid_conversion _ (BaseT bt)` >> Cases_on `bt` >>
  simp[valid_conversion_def, is_bytestring_type_def, int_convert_pair_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[valid_conversion_def, is_bytestring_type_def, int_convert_pair_def]
QED

Theorem scalar_conversion_source:
  !src t. valid_conversion src t /\ ~is_bytestring_type src /\
    ~is_bytestring_type t /\ ~int_convert_pair src t ==>
    (?m. src = BaseT (BytesT (Fixed m))) \/
    src = BaseT AddressT \/ (?n. src = BaseT (IntT n)) \/
    (?n. src = BaseT (UintT n)) \/ src = BaseT DecimalT \/
    (?name. src = FlagT name)
Proof
  rpt gen_tac >> Cases_on `src` >> Cases_on `t` >>
  simp[valid_conversion_def, is_bytestring_type_def, int_convert_pair_def] >>
  rename1 `valid_conversion (BaseT bt) _` >> Cases_on `bt` >>
  simp[valid_conversion_def, is_bytestring_type_def, int_convert_pair_def]
  >- (rename1 `valid_conversion _ (BaseT bt)` >> Cases_on `bt` >>
      simp[valid_conversion_def, is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >> simp[valid_conversion_def]) >>
  rpt strip_tac >> rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[is_bytestring_type_def]
QED

Theorem scalar_flag_member_count:
  !cenv cx env es name m.
    expr_sim_inv cenv cx env es /\
    FLOOKUP (get_tenv cx) name = SOME (FlagArgs m) ==>
    cenv.ce_flag_n_members (nsid_to_string name) = m
Proof
  simp[expr_sim_inv_def] >> metis_tac[]
QED

Theorem expr_body_pre_scalar_convert:
  !cenv cx env ann t e1 es.
    expr_body_pre cenv cx env (TypeBuiltin ann Convert t [e1]) es ==>
    ann = t /\ valid_conversion (expr_type e1) t /\
    expr_body_pre cenv cx env e1 es /\
    IS_SOME (evaluate_type (get_tenv cx) (expr_type e1)) /\
    IS_SOME (evaluate_type (get_tenv cx) t)
Proof
  rpt strip_tac >>
  drule expr_body_pre_type_evaluates >> simp[expr_type_def] >> strip_tac >>
  drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  drule expr_body_pre_type_evaluates >> simp[]
QED
