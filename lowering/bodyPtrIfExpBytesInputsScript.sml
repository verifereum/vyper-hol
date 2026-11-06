Theory bodyPtrIfExpBytesInputs
Ancestors
  memoryLocalRhsProps exprSimHypsDefs exprSimDefs vyperTypeArgFits
  vyperInterpreter vyperState context compileEnv valueCopyBytes
  valueEncodingTyping exprSimProps vyperTyping valueEncoding vfmConstants words arithmetic
  bodyPtrIfExpResidual vyperTypeSystem allocLimits vyperAST
Libs monadsyntax

Theorem ifexp_arm_annotation_typed:
  expr_body_pre ce cx env e es /\
  eval_expr cx e es = (INL raw,ee) /\ read_result cx raw ee = (INL v,er) ==>
  ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    value_has_type tv v /\ type_memory_bytes ce (expr_type e) = type_memory_size tv
Proof
  strip_tac >>
  `value_runtime_typed env (expr_type e) v` by
    (irule memory_rhs_read_destination_typed >>
     goal_assum (drule_at Any) >> simp[bind_def]) >>
  `expr_sim_inv ce cx env es` by gvs[expr_body_pre_def] >>
  drule_all memory_rhs_runtime_layout >> simp[]
QED

Theorem bytes_typed_padded_size:
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v /\ type_memory_bytes ce ty = type_memory_size tv ==>
  ?len. ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
         (?str. v = StringV str /\ len = LENGTH str)) /\
    val_store_size tv v = 32 + 32 * ((len+31) DIV 32) /\
    32 + 32 * ((len+31) DIV 32) <= type_memory_bytes ce ty
Proof
  strip_tac >>
  `val_wf tv v` by metis_tac[value_has_type_val_wf] >>
  drule val_store_size_le >> strip_tac >>
  drule_all bytestring_type_value >> strip_tac >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def, val_store_size_def, word_size_def]
QED

Theorem bytes_padded_word_bounds:
  n = 32 + 32 * ((len+31) DIV 32) /\ n <= capacity /\ capacity < 2 ** 64 ==>
  len+31 < dimword(:256) /\ n < dimword(:256)
Proof
  strip_tac >>
  qspec_then `32` mp_tac DIVISION >> simp[] >>
  disch_then (qspec_then `len+31` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `len+31 = _ + residue` >>
  `residue < 32` by simp[Abbr `residue`] >>
  gvs[dimword_def] >> decide_tac
QED

Theorem ifexp_residual_noncall_bytes:
  expr_body_pre ce cx env (IfExp ty cond a b) es /\
  (arm = a \/ arm = b) /\
  compile_expr ce ret_ty arm sa = (vv,sb) /\
  vv_post ctx fn ce cx arm es_arm sa sb s0 ee tv vv t /\
  ~same_memory_layout ce (lowered_value_type ce arm) ty /\
  ~(?ann fid args dret. arm = Call ann (IntCall fid) args dret) ==>
  is_bytestring_type ty
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_type arm = ty /\ well_typed_expr env arm` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  drule_all ifexp_allocating_arm_exceptions >> strip_tac >>
  gvs[expr_type_def, is_bytestring_type_def, well_typed_expr_def,
      type_builtin_result_ok_def]
QED

Theorem ifexp_bytes_caller_inputs:
  expr_body_pre ce cx env e es /\ is_bytestring_type (expr_type e) /\
  type_alloc_ok ce (expr_type e) /\
  eval_expr cx e es = (INL raw,ee) /\ read_result cx raw ee = (INL v,er) ==>
  ?tv len. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    value_has_type tv v /\
    ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
     (?str. v = StringV str /\ len = LENGTH str)) /\
    val_store_size tv v = 32 + 32 * ((len+31) DIV 32) /\
    32 + 32 * ((len+31) DIV 32) <= type_memory_bytes ce (expr_type e) /\
    len+31 < dimword(:256) /\ 32 + 32 * ((len+31) DIV 32) < dimword(:256)
Proof
  strip_tac >> drule_all ifexp_arm_annotation_typed >> strip_tac >>
  drule_all bytes_typed_padded_size >> strip_tac >>
  `type_memory_bytes ce (expr_type e) < 2 ** 64` by
    metis_tac[type_alloc_ok_def, is_bytestring_word_type] >>
  `len+31 < dimword(:256) /\ 32 + 32 * ((len+31) DIV 32) < dimword(:256)` by
    (irule bytes_padded_word_bounds >> simp[] >>
     qexists_tac `type_memory_bytes ce (expr_type e)` >> gvs[]) >>
  qexistsl_tac [`tv`, `len`] >> simp[]
QED

Theorem ifexp_selected_bytes_inputs:
  expr_body_pre ce cx env (IfExp ty cond a b) es /\
  (arm = a \/ arm = b) /\
  expr_body_pre ce cx env_arm arm es_arm /\
  compile_expr ce ret_ty arm sa = (vv,sb) /\
  vv_post ctx fn ce cx arm es_arm sa sb s0 ee raw vv t /\
  ~same_memory_layout ce (lowered_value_type ce arm) ty /\
  ~(?ann fid args dret. arm = Call ann (IntCall fid) args dret) /\
  eval_expr cx arm es_arm = (INL raw,ee) /\ read_result cx raw ee = (INL v,er) ==>
  is_bytestring_type ty /\
  ?tv len. evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
     (?str. v = StringV str /\ len = LENGTH str)) /\
    val_store_size tv v = 32 + 32 * ((len+31) DIV 32) /\
    32 + 32 * ((len+31) DIV 32) <= type_memory_bytes ce ty /\
    len+31 < dimword(:256) /\ 32 + 32 * ((len+31) DIV 32) < dimword(:256)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `is_bytestring_type ty` by metis_tac[ifexp_residual_noncall_bytes] >>
  `expr_type arm = ty /\ type_alloc_ok ce ty` by
    gvs[expr_body_pre_def, well_typed_expr_def, alloc_limits_expr_def] >>
  gvs[] >> drule_all ifexp_bytes_caller_inputs >> simp[]
QED
