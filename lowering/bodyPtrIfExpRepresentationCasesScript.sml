Theory bodyPtrIfExpRepresentationCases
Ancestors
  exprLowering vyperAST

Theorem lowered_value_type_exceptions:
  lowered_value_type ce e <> expr_type e ==>
  (?n s. e = Literal (BaseT (StringT n)) (StringL s)) \/
  (?n bs. e = Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)) \/
  (?ty n args. e = Builtin ty (Concat n) args) \/
  (?ann ensure method_id tys args.
     e = TypeBuiltin ann (AbiEncode ensure method_id) tys args) \/
  (?ann fid args dret. e = Call ann (IntCall fid) args dret)
Proof
  Cases_on `e` >> simp[lowered_value_type_def]
  >~ [`Literal t l`]
  >- (Cases_on `t` >> simp[lowered_value_type_def] >>
      rename1 `BaseT bt` >> Cases_on `bt` >>
      Cases_on `l` >> simp[lowered_value_type_def] >>
      rename1 `BytesT bound` >> Cases_on `bound` >> simp[lowered_value_type_def])
  >~ [`Builtin t b l`]
  >- (Cases_on `b` >> simp[lowered_value_type_def])
  >~ [`TypeBuiltin ann tb tys args`]
  >- (Cases_on `tb` >> simp[lowered_value_type_def]) >>
  rename1 `Call ann target args dret` >> Cases_on `target` >>
  simp[lowered_value_type_def]
QED

Theorem lowered_value_type_ordinary:
  ~(?n s. e = Literal (BaseT (StringT n)) (StringL s)) /\
  ~(?n bs. e = Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)) /\
  ~(?ty n args. e = Builtin ty (Concat n) args) /\
  ~(?ann ensure method_id tys args.
     e = TypeBuiltin ann (AbiEncode ensure method_id) tys args) /\
  ~(?ann fid args dret. e = Call ann (IntCall fid) args dret) ==>
  lowered_value_type ce e = expr_type e
Proof
  metis_tac[lowered_value_type_exceptions]
QED
