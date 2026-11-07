Theory bodyPtrPopTraversalBoundary
Ancestors bodyPtrPopMaterialization bodyPtrPopCompilerBoundary
  bodyPtrPopArithmeticBoundary bodyPtrPopAllocationBoundary
  bodyPtrPopCopyBoundary bodyPtrPopTypedCopyBoundary
  exprLowering compileEnv emitHelper list

Theorem pop_compile_multi_vvs_boundary:
  !es sa r sb.
  (!e aty s v t. MEM e es /\ pop_comp_boundary s /\
    cfn cenv aty e s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\ compile_multi_vvs cfn cenv es sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Induct >> simp[compile_multi_vvs_def, comp_return_def] >> rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!e aty s v t. _` (qspec_then `h` mp_tac) >>
      simp[] >> disch_then drule_all >> simp[]) >>
  rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!sa r sb. _ /\ _ /\ compile_multi_vvs _ _ _ _ = _ ==> _` irule >>
      reverse conj_tac >- (goal_assum (drule_at Any) >> simp[]) >>
      rpt strip_tac >> qpat_x_assum `!e aty s v t. _` (qspec_then `e` mp_tac) >>
      simp[] >> disch_then drule_all >> simp[]) >>
  rpt strip_tac >> gvs[comp_return_def]
QED

Theorem pop_store_multi_results_boundary:
  !ops off sa r sb.
  pop_comp_boundary sa /\ store_multi_results buf ops off sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Induct >> simp[store_multi_results_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]) >>
  rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]) >>
  rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem pop_compile_extcall_store_values_boundary:
  !vs off sa r sb.
  pop_comp_boundary sa /\ compile_extcall_store_values cenv vs buf off sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Induct >> simp[compile_extcall_store_values_def, comp_return_def] >> rpt strip_tac >>
  PairCases_on `h` >> gvs[compile_extcall_store_values_def, comp_ignore_bind_def] >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]) >>
  rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all pop_unwrap_value_boundary >> simp[]) >>
  rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (Cases_on `is_word_type h1` >> simp[]
      >- (rpt strip_tac >> drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]) >>
      Cases_on `is_bytestring_type h1` >> simp[] >> rpt strip_tac
      >- (drule_all pop_compile_store_bytestring_boundary >> simp[]) >>
      drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]) >>
  rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem pop_compile_materialize_vv_boundary:
  pop_comp_boundary sa /\ compile_materialize_vv cenv ty vv sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_materialize_vv_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_at (Pat `compile_alloc_buffer _ _ = _`) pop_compile_alloc_buffer_boundary,
         drule_all pop_unwrap_value_boundary,
         drule_all pop_compile_store_memory_boundary,
         (gvs[comp_return_def]) ] >> simp[]
QED

Theorem pop_compile_ext_call_kwarg_boundary:
  (!aty s v t. pop_comp_boundary s /\ cfn cenv aty e s = (v,t) ==>
    pop_comp_boundary t) /\ pop_comp_boundary sa /\
  compile_ext_call_kwarg cfn cenv rt k e sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `k = EKDefault /\ ~is_word_type rt` >>
  simp[compile_ext_call_kwarg_def] >> rpt strip_tac
  >- (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
      disch_then irule >> simp[] >> conj_tac
      >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
      rpt strip_tac >>
      dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
      disch_then irule >> simp[] >> conj_tac
      >- (rpt strip_tac >> drule_all pop_compile_materialize_vv_boundary >> simp[]) >>
      rpt strip_tac >> gvs[comp_return_def]) >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_at (Pat `lower_value _ _ _ _ _ = _`)
        pop_lower_value_boundary >> disch_then irule >> simp[] >>
      rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  rpt strip_tac >> gvs[comp_return_def]
QED

Theorem pop_compile_ext_call_kwargs_boundary:
  !es ks sa r sb.
  (!e aty s v t. MEM e es /\ pop_comp_boundary s /\
    cfn cenv aty e s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\ compile_ext_call_kwargs cfn cenv rt ks es sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Induct
  >- (Cases_on `ks` >> simp[compile_ext_call_kwargs_def, comp_return_def] >> metis_tac[]) >>
  qx_gen_tac `arg` >> Cases_on `ks` >>
  simp[compile_ext_call_kwargs_def, comp_return_def] >> rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_at (Pat `compile_ext_call_kwarg _ _ _ _ _ _ = _`)
        pop_compile_ext_call_kwarg_boundary >> disch_then irule >> simp[] >>
      rpt strip_tac >> qpat_x_assum `!e aty s v t. _` (qspec_then `arg` mp_tac) >>
      simp[] >> disch_then drule_all >> simp[]) >>
  rpt strip_tac >> pairarg_tac >> gvs[] >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!ks sa r sb. _ /\ _ /\ compile_ext_call_kwargs _ _ _ _ _ _ = _ ==> _` irule >>
      reverse conj_tac >- (goal_assum (drule_at Any) >> simp[]) >>
      rpt strip_tac >> qpat_x_assum `!e aty s v t. _` (qspec_then `e` mp_tac) >>
      simp[] >> disch_then drule_all >> simp[]) >>
  rpt strip_tac >> pairarg_tac >> gvs[comp_return_def]
QED

Theorem pop_compile_struct_lit_boundary:
  !fields buf off sa r sb.
  (!nm e aty s v t. MEM (nm,e) fields /\ pop_comp_boundary s /\
    cfn cenv aty e s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\ compile_struct_lit cfn cenv ty fields buf off sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Induct
  >- (simp[compile_struct_lit_def, comp_return_def] >> metis_tac[]) >>
  qx_gen_tac `fld` >> PairCases_on `fld` >>
  simp[compile_struct_lit_def, comp_ignore_bind_def] >> rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!nm e aty s v t. _`
        (qspecl_then [`fld0`, `fld1`] mp_tac) >>
      simp[] >> disch_then drule_all >> simp[]) >>
  rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[]) >>
  rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all pop_unwrap_value_boundary >> simp[]) >>
  rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all pop_compile_store_memory_boundary >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!buf off sa r sb. _ /\ _ /\ compile_struct_lit _ _ _ _ _ _ _ = _ ==> _` irule >>
  reverse conj_tac >- (goal_assum (drule_at Any) >> simp[]) >>
  rpt strip_tac >> qpat_x_assum `!nm e aty s v t. _`
    (qspecl_then [`nm`, `e`] mp_tac) >> simp[] >> disch_then drule_all >> simp[]
QED

Theorem pop_compile_stage_intcall_args_boundary:
  !cenv vals flags tys sa r sb.
  pop_comp_boundary sa /\ compile_stage_intcall_args cenv vals flags tys sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  recInduct compile_stage_intcall_args_ind >>
  simp[compile_stage_intcall_args_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all pop_unwrap_value_boundary >> simp[]) >>
  rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_all pop_unwrap_value_boundary,
         drule_all pop_compile_alloc_buffer_boundary,
         (qpat_x_assum `!sa r sb. _ /\ compile_stage_intcall_args _ _ _ _ _ = _ ==> _` drule_all >> simp[]),
         (gvs[comp_return_def] >> NO_TAC),
         (Cases_on `is_word_type ty` >> gvs[]
          >- (drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]) >>
          qmatch_asmsub_abbrev_tac `if bs then _ else _` >> Cases_on `bs` >> gvs[]
          >- (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
              disch_then irule >> simp[] >> conj_tac
              >- (rpt strip_tac >> drule_all pop_compile_store_bytestring_boundary >> simp[]) >>
              rpt strip_tac >> gvs[comp_return_def]) >>
          drule_all pop_compile_store_memory_boundary >> simp[])] >> simp[]
QED
