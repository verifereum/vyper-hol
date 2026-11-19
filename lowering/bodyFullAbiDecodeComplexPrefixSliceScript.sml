Theory bodyFullAbiDecodeComplexPrefixSlice
Ancestors
  exprSimWordBuiltins[qualified,ignore_grammar]
  bodyPtrBopScalarOutcome
  bodyFullAbiDecodeInterface bodyFullAbiDecodeFiniteGuard
  bodyFullAbiDecodeBytesArithmetic abiDecodePtrPrims abiDecoderCoherence abiDecoderMemberInfos vyperABI valueEncoding
  abiDecoderReentry bodyPtrTypeBuiltinsBounds loweringStateRelDefs
  emitHelper compileEnv emitHelperProps exprLowering exprLoweringProps abiEncoder venomExecSemantics
  venomInst venomState words list rich_list finite_map
  bodyFullAbiDecodeScalarObserved bodyPtrBopScalarSeq
  bodyPtrBopScalarDynamic genBlockSim fragExec fragGasOriginPtr fragGasPathPtr
  fragGasPath gasPathPtrExec stateFrame bodyFullAbiDecodeLeafCases
  bodyFullAbiDecodeComplexPrefix bodyFullAbiDecodeFiniteObserved externalEntryShape
Libs
  bodyFullAbiDecodeComplexPrefixSyntaxLib

Theorem abi_decode_complex_prefix_observed_slice:
  !finish.
  (^guarded_to_buf_entry) dst src opc base_op hi (DecComplex dyn infos)
    env sf ty tv live protected start finish s G tn d ==>
  (?t Gf tnf. (!H. V H ==> gas_origin_ptr_path
    (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (Abort Revert_abort t,Gf,tnf)) /\
    (!obs. fn_has_code start finish obs ==> gas_path ctx obs s 0 (Abort Revert_abort t)) /\
    (?e sm sb.
      emit_op ADD [src;Lit (n2w (FOLDR (\(_,asz,_) acc. asz+acc) 0 infos))]
        start = (e,sm) /\
      compile_abi_decode_range_check src e hi sm = ((),sb) /\
      cs_extends start sb /\ cs_extends sb finish /\
      (!obs. fn_has_code start sb obs ==> gas_path ctx obs s 0 (Abort Revert_abort t)))) \/
  (?env' sf' tys tvs e sm sb t Gf tnf.
    infos = abi_decoder_member_infos sf' ce tys /\
    type_memory_size tv = SUM (MAP (type_memory_bytes ce) tys) /\
    emit_op ADD [src;Lit (n2w (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) tys)))]
      start = (e,sm) /\
    compile_abi_decode_range_check src e hi sm = ((),sb) /\
    (!H. V H ==> gas_origin_ptr_path
      (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    (!x. not_fresh_at start x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (^empty_member_entry) dst src opc base_op hi infos env' sf' tys tvs live protected
      sb finish t Gf tnf d /\
    (!obs. fn_has_code start sb obs ==> gas_path ctx obs s 0 (OK t)) /\
    tnf.t_mem = tn.t_mem /\ t.vs_allocas = s.vs_allocas)
Proof
  BETA_TAC >> gen_tac >>
  disch_then (fn th =>
    mp_tac (MATCH_MP (SPEC_ALL (BETA_RULE
      bodyFullAbiDecodeComplexPrefixTheory.abi_decode_complex_prefix_raw_endpoint_effect)) th) >>
    map_every assume_tac (CONJUNCTS th)) >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)))
  >- suspend "reject" >>
  qpat_x_assum `?raw. run_inst_seq _ _ = OK raw /\ _` strip_assume_tac >>
  suspend "success"
QED

Resume abi_decode_complex_prefix_observed_slice[reject]:
  `cs_extends start sb` by
    (irule cs_extends_trans >> qexists_tac `sm` >>
     conj_tac
     >- (drule exprSimAccountsTheory.emit_op_extends_next_var >> simp[]) >>
     mp_tac (Q.SPECL [`src`, `e`, `hi`, `sm`, `K T`]
       externalEntryShapeTheory.compile_abi_decode_range_check_labels) >> simp[]) >>
  `cs_extends sb finish'` by
    (drule_all abi_decode_complex_bounded_split >> strip_tac >>
     `sb = sb'` by gvs[] >>
     mp_tac (Q.SPECL [`dst`, `src`, `opc`, `base_op`, `hi`, `infos`, `0`, `0`, `sb`]
       (cj 2 externalEntryShapeTheory.compile_abi_decode_labels)) >> gvs[]) >>
  `fn_has_code start sb fn` by metis_tac[fn_has_code_split] >>
  drule_all abi_decode_complex_header_shape >> strip_tac >>
  `?B. bop_scalar_seq {x | not_fresh_at start x}
    {src;hi;Lit (n2w (FOLDR (\(_,asz,_) acc. asz+acc) 0 infos))}
    (emitted_insts start sb) B` by
    (irule abi_decode_complex_header_scalar >>
     conj_tac >- simp[] >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  pop_assum strip_assume_tac >>
  `!op. op IN {src;hi;Lit (n2w (FOLDR (\(_,asz,_) acc. asz+acc) 0 infos))} ==>
     op_prov G op = NONE /\ op_taint tn op = {}` by
    (pure_rewrite_tac [pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY] >>
     rpt strip_tac >> gvs[] >>
     simp[ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.op_taint_def]) >>
  `allocas_from lo s` by
    (qpat_x_assum `?H. V H` strip_assume_tac >>
     qpat_assum `!H. V H ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def] >>
     metis_tac[bodyPtrDefsTheory.ghost_inv_at_def]) >>
  drule_all bodyFullAbiDecodeScalarObservedTheory.member_scalar_revert_observed >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `t = u` by
    (qpat_x_assum `?H. V H` strip_assume_tac >>
     qpat_assum `!H. V H ==> gas_origin_ptr_path _ _ _ (Abort Revert_abort t,_,_)`
       (qspec_then `H` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ _ _ (Abort Revert_abort u,_,_)`
       (qspec_then `DF H` mp_tac) >>
     qpat_assum `V H` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[] >> rpt strip_tac >>
     imp_res_tac gas_origin_ptr_path_projections >>
     `Abort Revert_abort t = Abort Revert_abort u` suffices_by simp[] >>
     irule (cj 3 gas_path_ptr_exit_unique) >> simp[exit_result_def] >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  disj1_tac >> qexistsl_tac [`t`, `Gf`, `tnf`] >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac
  >- (rpt strip_tac >> metis_tac[fn_has_code_split]) >>
  qexistsl_tac [`e`, `sm`, `sb`] >> asm_rewrite_tac[]
QED

Resume abi_decode_complex_prefix_observed_slice[success]:
  drule_all abi_decode_complex_header_shape >> strip_tac >>
  `?B. bop_scalar_seq {x | not_fresh_at start x}
    {src;hi;Lit (n2w (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) tys)))}
    (emitted_insts start sb) B` by
    (irule abi_decode_complex_header_scalar >>
     conj_tac >- simp[] >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  pop_assum strip_assume_tac >>
  `t.vs_allocas = s.vs_allocas` by
    (drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
     simp[] >> qpat_x_assum `raw = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `!obs. fn_has_code start sb obs ==> gas_path ctx obs s 0 (OK t)` by
    (qpat_assum `t = _` (fn th => once_rewrite_tac[th]) >>
     `sb.cs_current_insts = start.cs_current_insts ++ emitted_insts start sb` by
       gvs[inst_extends_def] >>
     drule bop_scalar_seq_opcodes >> strip_tac >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (emitted_insts start sb)` by gs[EVERY_MEM] >>
     `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts start sb)) = 0` by
       gs[EVERY_MEM, FILTER_EQ_NIL] >>
     rpt strip_tac >>
     drule_all bodyFullAbiDecodeFiniteObservedTheory.abi_decode_finite_success_observed >>
     disch_then (qspec_then `ctx` mp_tac) >> simp[]) >>
  disj2_tac >>
  qexistsl_tac [`env'`, `sf'`, `tys`, `tvs`, `e`, `sm`, `sb`, `t`, `Gf`, `tnf`] >>
  asm_rewrite_tac[]
QED

Finalise abi_decode_complex_prefix_observed_slice
