Theory externalReturnIntcallProducer
Ancestors
  externalReturnVvPrefixProbe exprLoweringProps localPtrsProps
  fragExec compileEnv exprLowering vyperAST context
Libs
  pairLib

Theorem return_compile_intcall_output:
  compile_expr ce ct (Call ann (IntCall fid) args drv) sa = (vv,sm) ==>
  (?p. vv = LocatedValue (ce.ce_func_return_type (nsid_to_string fid)) p /\
       p.ptr_location = LocMemory) \/
  (?pvs. vv = StackValue (ce.ce_func_return_type (nsid_to_string fid)) (Lit 0w) /\
         ce.ce_func_info (nsid_to_string fid) = (0,0,pvs))
Proof
  namedCases_on `ce.ce_func_info (nsid_to_string fid)` ["nret bs pvs"] >>
  simp[Once compile_expr_def, expr_type_def, compile_call_def] >>
  Cases_on `nret > 0` >> simp[] >>
  Cases_on `bs > 0` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[base_ptr_def, mk_ptr_def] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem return_lower_value_code_slices:
  lower_value compile_expr ce ct e sa = (op,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa ==>
  ?vv sm. compile_expr ce ct e sa = (vv,sm) /\
    unwrap_value ce vv sm = (op,sb) /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    sa.cs_next_var <= sm.cs_next_var /\ local_ptrs_reserved ce sm
Proof
  simp[lower_value_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_expr ce ct e sa = (vv,sm)` >>
  `ci_mono sa sm` by
    (drule (cj 1 compile_expr_grows) >> simp[ci_mono_def]) >>
  `ci_mono sm sb` by
    (mp_tac ci_mono_unwrap_value >>
     disch_then (qspecl_then [`ce`,`vv`,`sm`] mp_tac) >> simp[]) >>
  gvs[ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  metis_tac[local_ptrs_reserved_next_var]
QED
