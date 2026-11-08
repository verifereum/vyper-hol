Theory bodyPtrBytestringBuiltinsSliceAbortPath
Ancestors
  bodyPtrBytestringBuiltinsSliceGuardAbort
  bodyPtrBytestringBuiltinsAllocationEntry bodyPtrBytestringBuiltinsZeroCheck
  bodyPtrBytestringBuiltinsExternalSlice fragExec compileEnv emitHelper
  exprLowering exprLoweringProps exprSimUnopProps convertScalarProps exprSimConvert
  fragGasPathPtr venomState ptrDiscipline words arithmetic emitHelperProps

Theorem slice_guard_suffix_extends:
  as_ptr_val ann LocMemory
    (compile_slice_extcode addr start len root data sa) = (vv,sb) ==>
  cs_extends sa sb
Proof
  Cases_on `compile_slice_extcode addr start len root data sa` >>
  simp[as_ptr_val_def] >> strip_tac >> gvs[] >>
  drule compile_slice_extcode_stages >> strip_tac >>
  metis_tac[cs_extends_trans]
QED

Theorem slice_guard_checker_embedding:
  lower_value compile_expr order_ptr_env ty
    (extcode_addr_expr slice_guard_source) sa = (op,sb) /\
  fn_has_code sa sb fn ==>
  ?z s1 nz s2 sc.
    emit_op ISZERO [Lit 0w] sa = (Var z,s1) /\
    emit_op ISZERO [Var z] s1 = (Var nz,s2) /\
    emit_void ASSERT [Var nz] s2 = ((),sc) /\ fn_has_code sa sc fn
Proof
  strip_tac >> drule slice_guard_address_cut >> strip_tac >>
  drule slice_guard_division_emission >> strip_tac >>
  `cs_extends s3 sm` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends sm sb` by
    (irule (cj 1 (INST_TYPE [alpha |-> ``:operand``] straight_fresh_cs_extends)) >>
     qexistsl_tac [`compile_type_convert x (mk_convert_op (BaseT (UintT 256)) (BaseT AddressT))`, `op`] >>
     simp[mk_convert_op_def, is_bytestring_type_def, straight_fresh_convert]) >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends sa s3` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s3 fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `?v. z = Var v` by metis_tac[emitted_insts_emit_op] >>
  `?v. nz = Var v` by metis_tac[emitted_insts_emit_op] >>
  gvs[] >> metis_tac[]
QED

Theorem slice_guard_counted_abort:
  compile_expr order_ptr_env ty slice_guard_expr sa = (vv,sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?H tm t. gas_path_ptr D 0 ctx fn PG G tn s 0 H tm
    (Abort Revert_abort t)
Proof
  strip_tac >> drule slice_guard_compile_prefix >> strip_tac >>
  `cs_extends s3 s4` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends s4 sb` by metis_tac[slice_guard_suffix_extends] >>
  `cs_extends s3 sb` by metis_tac[cs_extends_trans] >>
  `32 <= 64 /\ 64 < dimword (:256)` by simp[dimword_def] >>
  drule_all slice_allocation_continuation_entry >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `fn_has_code s3 s4 fn` by metis_tac[fn_has_code_split] >>
  drule_all slice_guard_checker_embedding >> strip_tac >>
  `eval_operand (Lit 0w) t = SOME 0w /\
   op_taint tn2 (Lit 0w) = {} /\ op_prov G2 (Lit 0w) = NONE` by simp[] >>
  drule_all zero_check_emit_abort_counted >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all gas_path_ptr_then >> simp[] >>
  strip_tac >> goal_assum drule
QED
