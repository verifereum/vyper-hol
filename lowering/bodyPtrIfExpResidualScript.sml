Theory bodyPtrIfExpResidual
Ancestors
  bodyPtrIfExpRepresentationCases bodyPtrIfExpLayoutRefl
  bodyPtrIfExpCallAlignment bodyPtrIfExpCallShape bodyPtrIfExpUnwrapNoop
  bodyPtrIfExpUnwrapContract exprSimHypsDefs vyperTypeSystem
  exprLowering compileEnv context vyperAST vyperTypeCallGraph

Theorem ifexp_allocating_lowered_differs:
  expr_body_pre ce cx env (IfExp ty cond a b) es /\
  (arm = a \/ arm = b) /\
  ~same_memory_layout ce (lowered_value_type ce arm) ty ==>
  lowered_value_type ce arm <> expr_type arm
Proof
  strip_tac >>
  `expr_type arm = ty` by gvs[expr_body_pre_def, well_typed_expr_def] >>
  metis_tac[same_memory_layout_reflexive]
QED


Theorem ifexp_allocating_arm_exceptions:
  expr_body_pre ce cx env (IfExp ty cond a b) es /\
  (arm = a \/ arm = b) /\
  (int_calls_expr arm = [] \/
   same_memory_layout ce (lowered_value_type ce arm) (expr_type arm)) /\
  post_value_type ce arm = expr_type arm /\
  compile_expr ce ret_ty arm sa = (vv,sb) /\
  vv_post ctx fn ce cx arm es_arm sa sb s0 ee tv vv t /\
  ~same_memory_layout ce (lowered_value_type ce arm) ty ==>
  (?n s. arm = Literal (BaseT (StringT n)) (StringL s)) \/
  (?n bs. arm = Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)) \/
  (?t n args. arm = Builtin t (Concat n) args) \/
  (?ann ensure method_id tys args.
    arm = TypeBuiltin ann (AbiEncode ensure method_id) tys args) \/
  (?ann fid args dret pvs. arm = Call ann (IntCall fid) args dret /\
    ce.ce_func_info (nsid_to_string fid) = (0,0,pvs))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `lowered_value_type ce arm <> expr_type arm` by
    metis_tac[ifexp_allocating_lowered_differs] >>
  `expr_type arm = ty` by gvs[expr_body_pre_def, well_typed_expr_def] >>
  `int_calls_expr arm = []` by metis_tac[] >>
  drule lowered_value_type_exceptions >> strip_tac >> gvs[int_calls_expr_def]
QED

Theorem ifexp_zero_call_result:
  compile_expr ce ret_ty (Call ann (IntCall fid) args dret) sa = (vv,sb) /\
  ce.ce_func_info (nsid_to_string fid) = (0,0,pvs) ==>
  vv = StackValue (ce.ce_func_return_type (nsid_to_string fid)) (Lit 0w)
Proof
  strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_component_eq] >> strip_tac >>
  drule_all compile_call_intcall_zero_shape >> strip_tac >> gvs[]
QED

Theorem ifexp_string_literal_memory_result:
  compile_expr ce ret_ty
    (Literal (BaseT (StringT n)) (StringL payload)) sa = (vv,sb) ==>
  ?p. vv = LocatedValue (BaseT (StringT n)) p /\ p.ptr_location = LocMemory
Proof
  simp[compile_expr_component_eq, expr_type_def, compile_literal_vv_def,
       comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[base_ptr_def, mk_ptr_def, expr_type_def]
QED

Theorem ifexp_bytes_literal_memory_result:
  compile_expr ce ret_ty
    (Literal (BaseT (BytesT (Dynamic n))) (BytesL payload)) sa = (vv,sb) ==>
  ?p. vv = LocatedValue (BaseT (BytesT (Dynamic n))) p /\ p.ptr_location = LocMemory
Proof
  simp[compile_expr_component_eq, expr_type_def, compile_literal_vv_def,
       comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[base_ptr_def, mk_ptr_def, expr_type_def]
QED

Theorem ifexp_abi_encode_memory_result:
  compile_expr ce ret_ty (TypeBuiltin ann (AbiEncode ensure method_id) tys args) sa = (vv,sb) ==>
  ?p. vv = LocatedValue ann p /\ p.ptr_location = LocMemory
Proof
  simp[Once compile_expr_component_eq] >>
  pure_rewrite_tac[Once compile_type_builtin_dispatch_component_eq] >>
  pure_rewrite_tac[Once compile_type_builtin_dispatch_body_def] >>
  simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt IF_CASES_TAC >>
  rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[expr_type_def] >>
  qmatch_asmsub_abbrev_tac `as_ptr_val _ LocMemory result` >>
  PairCases_on `result` >> gvs[as_ptr_val_def, mk_ptr_def]
QED

Theorem ifexp_concat_memory_result:
  compile_expr ce ret_ty (Builtin t (Concat n) args) sa = (vv,sb) ==>
  ?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory
Proof
  `!bt es. names_builtin bt es ==> !k. bt <> Concat k` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `~names_builtin (Concat n) args` by metis_tac[] >>
  simp[compile_expr_builtin_dispatch,
       Once compile_builtin_dispatch_component_eq] >>
  rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[base_ptr_def, mk_ptr_def]
QED

Theorem ifexp_allocating_noop_representation:
  expr_body_pre ce cx env (IfExp ty cond a b) es /\
  (arm = a \/ arm = b) /\
  (int_calls_expr arm = [] \/
   same_memory_layout ce (lowered_value_type ce arm) (expr_type arm)) /\
  post_value_type ce arm = expr_type arm /\
  compile_expr ce ret_ty arm sa = (vv,sb) /\
  vv_post ctx fn ce cx arm es_arm sa sb s0 ee tv vv t /\
  ~is_word_type ty /\
  ~same_memory_layout ce (lowered_value_type ce arm) ty ==>
  (?tag op. vv = StackValue tag op) \/
  (?tag p. vv = LocatedValue tag p /\ ~is_word_type tag /\ p.ptr_location = LocMemory)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_type arm = ty` by gvs[expr_body_pre_def, well_typed_expr_def] >>
  `!tag p. vv = LocatedValue tag p ==> ~is_word_type tag` by
    metis_tac[exprPtrUnwrapMarkedTheory.vv_post_located_type,
              valueCopyBytesTheory.is_bytestring_word_type] >>
  drule_all ifexp_allocating_arm_exceptions >> strip_tac >> gvs[] >>
  FIRST [drule ifexp_string_literal_memory_result,
         drule ifexp_bytes_literal_memory_result,
         drule ifexp_concat_memory_result,
         drule ifexp_abi_encode_memory_result,
         drule_all ifexp_zero_call_result] >> metis_tac[]
QED

Theorem ifexp_allocating_unwrap_noop:
  expr_body_pre ce cx env (IfExp ty cond a b) es /\
  (arm = a \/ arm = b) /\
  (int_calls_expr arm = [] \/
   same_memory_layout ce (lowered_value_type ce arm) (expr_type arm)) /\
  post_value_type ce arm = expr_type arm /\
  compile_expr ce ret_ty arm sa = (vv,sb) /\
  vv_post ctx fn ce cx arm es_arm sa sb s0 ee tv vv t /\
  ~is_word_type ty /\
  ~same_memory_layout ce (lowered_value_type ce arm) ty /\
  unwrap_value ce vv sc = (op,sn) ==>
  sn = sc /\ op = vv_operand vv
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ifexp_allocating_noop_representation >> strip_tac >>
  metis_tac[unwrap_value_noop_endpoint]
QED
