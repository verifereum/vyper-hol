Theory deployOutcomesFreeSelectors
Ancestors
  vyperTypeSystem list supportedExprTraverse exprCallbackContracts exprLowering

(* Diagnostic boundary: a real typing premise supplies the indices used by
   binary lowering. P can carry both exclusion and recursive selector safety. *)
Theorem outcomes_free_binary_selectors:
  well_typed_builtin_app ty (Bop op) (MAP expr_type args) /\
  EVERY P args ==>
  P (HD args) /\ P (HD (TL args)) /\
  MEM (HD args) args /\ MEM (HD (TL args)) args
Proof
  simp[well_typed_builtin_app_def] >> strip_tac >>
  Cases_on `args` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[]
QED

Theorem outcomes_free_select:
  EVERY Q args /\ k < LENGTH args ==>
  Q (EL k args) /\ MEM (EL k args) args
Proof
  metis_tac[EVERY_EL, MEM_EL]
QED

Theorem outcomes_free_head:
  EVERY Q args /\ args <> [] ==> Q (HD args) /\ MEM (HD args) args
Proof
  Cases_on `args` >> simp[]
QED

Theorem outcomes_free_second:
  EVERY Q args /\ 2 <= LENGTH args ==>
  Q (HD (TL args)) /\ MEM (HD (TL args)) args
Proof
  Cases_on `args` >> simp[] >> Cases_on `t` >> simp[]
QED

Theorem outcomes_free_builtin_arities:
  well_typed_builtin_app ty bi (MAP expr_type args) ==>
  ((?op. bi = Bop op) ==> LENGTH args = 2) /\
  ((bi = AddMod \/ bi = MulMod \/ (?n. bi = Slice n)) ==> LENGTH args = 3) /\
  ((bi = PowMod256 \/ bi = ECAdd \/ bi = ECMul) ==> LENGTH args = 2) /\
  (bi = ECRecover ==> LENGTH args = 4) /\
  ((bi = Not \/ bi = Neg \/ bi = Abs \/ (?item. bi = Acc item) \/
    bi = Keccak256 \/ bi = Sha256 \/ (?n. bi = CalldataSlice n) \/
    bi = Len \/ bi = BlockHash \/ bi = BlobHash \/ bi = Ceil \/
    bi = Floor \/ (?n. bi = Uint2Str n) \/
    (?denom. bi = AsWeiValue denom) \/ bi = MethodId) ==> LENGTH args = 1)
Proof
  Cases_on `bi` >> simp[well_typed_builtin_app_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `MAP _ _ = _` (mp_tac o AP_TERM ``LENGTH : type list -> num``) >> simp[]
QED

Theorem outcomes_free_type_builtin_arities:
  well_typed_type_builtin_args tb target_ty (MAP expr_type args) ==>
  ((tb = Convert \/ (?unwrap. tb = AbiDecode unwrap)) ==> LENGTH args = 1) /\
  (tb = Extract32 ==> LENGTH args = 2)
Proof
  Cases_on `tb` >> simp[well_typed_type_builtin_args_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem outcomes_free_typed_children:
  !es. well_typed_exprs env es /\ ~supported_exprs_exists p es ==>
  EVERY (\e. well_typed_expr env e /\ ~supported_expr_exists p e) es
Proof
  Induct >> simp[well_typed_expr_def, supported_expr_exists_def]
QED

Theorem outcomes_free_make_array_children:
  well_typed_expr env (Builtin ty (MakeArray a b) elems) /\
  ~supported_expr_exists p (Builtin ty (MakeArray a b) elems) ==>
  EVERY (\e. well_typed_expr env e /\ ~supported_expr_exists p e) elems
Proof
  simp[well_typed_expr_def, supported_expr_exists_def] >>
  metis_tac[outcomes_free_typed_children]
QED

Theorem outcomes_free_extcode_address:
  is_extcode e /\ well_typed_expr env e /\ ~supported_expr_exists p e ==>
  well_typed_expr env (extcode_addr_expr e) /\
  ~supported_expr_exists p (extcode_addr_expr e)
Proof
  simp[is_extcode_characterization] >> rpt strip_tac >>
  gvs[well_typed_expr_def, supported_expr_exists_def, extcode_addr_expr_def]
QED
