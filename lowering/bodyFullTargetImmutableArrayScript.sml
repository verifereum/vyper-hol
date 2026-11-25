(* Constructor immutable array selection at the state after the index. *)
Theory bodyFullTargetImmutableArray
Ancestors
  bodyFullTargetImmutableArraySelected
  bodyFullTargetDefs bodyFullTargetRoots bodyFullSubscriptLiveImmSelect
  bodyFullPathHistory bodyFullGhostFrame bodyFullUnwrapRun bodyFullHashKeccakFixed
  exprSimSubscriptArrayLiveImmutableView exprSimSubscriptArrayLiveImmutableSuffix
  exprSimSubscriptArraySuffix exprSimSubscriptArraySource exprSimArrayIndex
  exprSimProps exprSimHypsDefs loweringStateRelDefs vyperValue vyperInterpreter
  fragGasOriginPtr fragExec venomInst context gasContext exprLowering emitHelper exprSimCopy
  bodyFullExtCallPosTransport targetSubscriptMemory exprOperandVar[qualified,ignore_grammar]
  gasOutcomeFull gasOutcomeFullCompose gasSummary exprSimDefs bodyPtrDefs loweringPosts compileEnv
  exprLoweringProps emitHelperProps freshWrites typedCopyOriginPtrBase
  ptrDiscipline vyperArray vyperTypeValues vyperValueOperation vyperTyping
  vyperFixedShapePath vyperPlaceResultTyping vyperState vyperStorageFootprint valueEncoding
  valueEncodingProps exprSimFieldLayout vyperAST venomState list finite_map words

Theorem immutable_target_array_tail:
  body_inv tops ctx cenv cx /\ cenv.ce_is_ctor /\ cenv.ce_module = NONE /\
  expr_sim_inv cenv cx env ee /\ ee.gas_obs = [] /\
  storage_trace_domain cx st0 ee.storage_trace /\
  FLOOKUP cenv.ce_module_vars (NONE,id) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables NONE imms) id = SOME (itv,iv) /\
  off + type_memory_size itv < dimword (:256) /\
  mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  evaluate_subscripts itv iv path = INL (ArrayV av) /\
  compile_array_subscript arg iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0) 32
    (type_memory_size etv) sgn
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode) sn = (dst,sb) /\
  eval_operand arg s = SOME (n2w (off+k)) /\ copy_old_operand sn arg /\
  op_taint tn arg = {} /\ op_prov G arg = NONE /\
  eval_operand iop s = SOME iw /\ copy_old_operand sn iop /\
  op_taint tn iop = {} /\ op_prov G iop = NONE /\
  (!l. arg <> Label l /\ iop <> Label l) /\
  i = (if sgn then w2i iw else &(w2n iw)) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sn /\
  sa.cs_next_var <= sn.cs_next_var /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    wb_frame cenv es ee sa s0 s /\ ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (bind (extend_place cx (PlaceR (ImmutablePlace NONE id path))
             (ValueSubscript (IntV i))) get_place) (ee,s,G,tn)
    (\H res fin G' tn' q.
       res = INL (ImmutablePlace NONE id (path ++ [ValueSubscript (IntV i)])) /\
       imm_target_post H ctx func cenv cx es sa sb s0 fin id
         (path ++ [ValueSubscript (IntV i)]) et (dst,SOME LocCode,SOME (ValPT et)) q /\
       q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts /\
       alloca_history func q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
       s0.vs_alloca_next <= q.vs_alloca_next /\
       ghost_inv_at (DF H) lo d cenv cx fin G' tn' q /\
       target_ptr_ok cenv (PlaceR (ImmutablePlace NONE id (path ++ [ValueSubscript (IntV i)])))
         (dst,SOME LocCode,SOME (ValPT et)) G' tn' q /\
       op_prov G' dst = NONE /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')
    (\H res fin gt r. expr_exit res r /\ halt_exit H cx fin res r /\
      (ctx_has_dalloca ctx ==> !q. r = Halt q ==> allocas_below_fmp q))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule (SIMP_RULE (srw_ss()) [gas_explicit_def]
    (Q.INST [`marks` |-> `[]:bool list`] gas_outcome_full_intro)) >>
  mp_tac (REWRITE_RULE [] (BETA_RULE
    (Q.INST [`observe_result` |-> `\r. T`] immutable_target_array_tail_selected_by))) >>
  (impl_tac >-
    (asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
     irule (REWRITE_RULE [wordsTheory.n2w_w2n]
       (Q.INST [`i` |-> `w2n (iw:bytes32)`] live_code_select_joint)) >>
     simp[] >> qexistsl [`arg`,`T`,`iop`,`cenv.ce_imm_alloca`] >>
     fs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM])) >>
  disch_then (qx_choosel_then [`res`,`fin`,`r`,`Gf`,`tnf`] strip_assume_tac) >>
  qexistsl [`Gf`,`fin`,`r`,`res`,`tnf`] >> gvs[] >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  simp[]
QED
