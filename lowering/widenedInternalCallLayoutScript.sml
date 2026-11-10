(* Memory location of a positive-sized internal-call return buffer. *)
Theory widenedInternalCallLayout
Ancestors
  internalReturnMetadata intCallStep bodySim supportedExprs
  memoryLocalRhsProps exprLowering valueEncoding compileEnv

Theorem positive_internal_call_memory_layout:
  body_inv tops ctx ce cx /\
  supported_expr tops (Call ann (IntCall fid) args drv) /\
  0 < type_memory_bytes ce (lowered_value_type ce (Call ann (IntCall fid) args drv)) /\
  compile_expr ce ty (Call ann (IntCall fid) args drv) sa = (vv,sb) ==>
  ?p. vv = LocatedValue (lowered_value_type ce (Call ann (IntCall fid) args drv)) p /\
      p.ptr_location = LocMemory
Proof
  strip_tac >>
  `supported_program tops /\
   ce.ce_func_return_type = build_func_return_type tops /\
   ce.ce_func_info = build_func_info (get_struct_fields (make_struct_fields_map tops)) tops /\
   ce.ce_struct_fields = make_struct_fields_map tops` by fs[body_inv_def] >>
  qpat_x_assum `supported_expr _ _` mp_tac >>
  simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def] >>
  Cases_on `drv` >> simp[supported_effect_expr_def, optionTheory.IS_SOME_EXISTS] >>
  strip_tac >> PairCases_on `x` >>
  drule_all supported_internal_return_type >> strip_tac >>
  drule_all supported_internal_call_info >> strip_tac >>
  `lowered_value_type ce (Call ann (IntCall fid) args NONE) = x5` by
    simp[lowered_value_type_def] >>
  `x5 <> NoneT` by (strip_tac >> gvs[type_memory_bytes_def]) >>
  namedCases_on `ce.ce_func_info (nsid_to_string fid)` ["ret_count rbs pvs"] >>
  `0 < type_memory_bytes ce x5` by metis_tac[] >>
  `0 < ret_count \/ 0 < rbs` by (irule positive_compute_func_info >> metis_tac[]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def] >> strip_tac >>
  drule_all compile_call_intcall_shape >> strip_tac >>
  Cases_on `ret_count = 0` >> gvs[contextTheory.base_ptr_def]
QED
