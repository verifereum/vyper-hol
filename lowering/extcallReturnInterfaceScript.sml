(* Caller-side typing and allocation projections for the return seam. *)
Theory extcallReturnInterface
Ancestors
  exprSimHypsDefs allocLimits vyperTypeSystem arithmetic typedMemoryCopy words
  compileEnv

Theorem extcall_return_type_bounds:
  expr_body_pre cenv cx env
    (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt) es ==>
  ann = ret_type /\
  well_formed_type env.type_defs ret_type /\
  (ret_type <> NoneT ==> assignable_type env.type_defs ret_type) /\
  abi_decode_bytes_widths env.type_defs ret_type /\
  type_alloc_ok cenv ret_type /\
  abi_size_bound cenv.ce_struct_fields
    (if needs_external_call_wrap ret_type then TupleT [ret_type] else ret_type)
    + 32 < 2 ** 64
Proof
  simp_tac (srw_ss()) [expr_body_pre_def, well_typed_expr_def,
    alloc_limits_expr_def, ext_call_alloc_ok_def, LET_THM] >>
  rpt strip_tac >> gvs[] >>
  irule LESS_EQ_LESS_TRANS >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem extcall_return_memory_size:
  expr_body_pre cenv cx env
    (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt) es /\
  evaluate_type (get_tenv cx) ret_type = SOME tv ==>
  type_memory_bytes cenv ret_type = type_memory_size tv
Proof
  strip_tac >> irule typedMemoryCopyTheory.typed_copy_memory_size >>
  qexists_tac `get_tenv cx` >>
  gvs[expr_body_pre_def, expr_sim_inv_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem extcall_return_store_bound:
  expr_body_pre cenv cx env
    (Call ann (ExtCall stat skip (fname,arg_types,ret_type) opts) args dflt) es /\
  evaluate_type (get_tenv cx) ret_type = SOME tv ==>
  type_memory_size tv + 64 < dimword (:256)
Proof
  strip_tac >> drule_all extcall_return_memory_size >> strip_tac >>
  drule extcall_return_type_bounds >> strip_tac >>
  Cases_on `is_word_type ret_type`
  >- (Cases_on `ret_type` >>
      gvs[is_word_type_def, type_memory_bytes_def, wordsTheory.dimword_def] >>
      Cases_on `b` >>
      gvs[is_word_type_def, type_memory_bytes_def] >>
      Cases_on `b'` >> gvs[is_word_type_def, type_memory_bytes_def]) >>
  gvs[type_alloc_ok_def, wordsTheory.dimword_def]
QED
