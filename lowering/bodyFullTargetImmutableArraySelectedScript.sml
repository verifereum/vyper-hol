(* Source and frame facts at the result chosen by the immutable array selector. *)
Theory bodyFullTargetImmutableArraySelected
Ancestors
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

Theorem immutable_target_array_tail_selected_by:
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
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) /\
  (!dyn cnt.
    compile_array_subscript arg iop dyn (if dyn then 0 else cnt) 32
      (type_memory_size etv) sgn
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode) sn = (dst,sb) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    (dyn ==> immutable_copy_read cenv.ce_is_ctor (n2w (off+k)) s = n2w cnt /\
      w2n (n2w (off+k):bytes32) + 32 <= lo /\
      mem_word_taint tn.t_mem (w2n (n2w (off+k):bytes32)) = {} /\
      (!region. cenv.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w /\
        copy_old_operand sn region /\ op_taint tn region = {} /\ op_prov G region = NONE)) ==>
    ?Gf tnf q.
      observe_result (if idx_in_range sgn iw (n2w cnt) then OK q else Abort Revert_abort q) /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        ((if idx_in_range sgn iw (n2w cnt) then OK q else Abort Revert_abort q),Gf,tnf)) /\
      q.vs_immutables = s.vs_immutables /\ q.vs_memory = s.vs_memory /\
      q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
      q.vs_fmp = s.vs_fmp /\ q.vs_accounts = s.vs_accounts /\
      q.vs_transient = s.vs_transient /\ q.vs_call_ctx = s.vs_call_ctx /\
      q.vs_requests = s.vs_requests /\
      tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
      (!v. not_fresh_at sn v ==> lookup_var v q = lookup_var v s /\
        FLOOKUP Gf v = FLOOKUP G v /\ op_taint tnf (Var v) = op_taint tn (Var v)) /\
      (idx_in_range sgn iw (n2w cnt) ==>
        q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~q.vs_halted /\
        eval_operand dst q = SOME (n2w (off+k) + n2w ((if dyn then 32 else 0) + w2n iw * type_memory_size etv)) /\
        op_taint tnf dst = {} /\ op_prov Gf dst = NONE /\
        !(H:(bool # bytes32 # type_value) list # num list) cenv cx es.
          stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sn ==>
          stmt_state_rel H ctx func cenv cx es q)) ==>
  ?res fin r G' tn'.
    observe_result r /\
    (!tail. bind (extend_place cx (PlaceR (ImmutablePlace NONE id path))
              (ValueSubscript (IntV i))) get_place (ee with gas_obs := tail) =
            (res,fin with gas_obs := tail)) /\
    storage_trace_domain cx st0 fin.storage_trace /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (r,G',tn') /\
      ((?q. r = OK q /\
         res = INL (ImmutablePlace NONE id (path ++ [ValueSubscript (IntV i)])) /\
         imm_target_post H ctx func cenv cx es sa sb s0 (fin with gas_obs := []) id
           (path ++ [ValueSubscript (IntV i)]) et (dst,SOME LocCode,SOME (ValPT et)) q /\
         q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts /\
         alloca_history func q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
         s0.vs_alloca_next <= q.vs_alloca_next /\
         ghost_inv_at (DF H) lo d cenv cx (fin with gas_obs := []) G' tn' q /\
         target_ptr_ok cenv (PlaceR (ImmutablePlace NONE id (path ++ [ValueSubscript (IntV i)])))
           (dst,SOME LocCode,SOME (ValPT et)) G' tn' q /\
         op_prov G' dst = NONE /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn') \/
       (exit_result r /\ expr_exit res r /\ halt_exit H cx (fin with gas_obs := []) res r /\
        (ctx_has_dalloca ctx ==> !q. r = Halt q ==> allocas_below_fmp q))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by
    simp[Abbr `H0`,GSYM storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `immutable_holds cenv cx (ArrayT et bd) (PlaceR (ImmutablePlace NONE id path))
      (n2w (off+k)) ee s` by
    (qpat_assum `cenv.ce_module = NONE`
       (fn eq => irule (REWRITE_RULE[eq] (INST_TYPE [``:'a`` |-> ``:256``] live_immutable_path_holds))) >>
     simp[] >> conj_tac >- (qexists_tac `env` >> simp[]) >>
     qexistsl [`H0`,`ctx`,`func`] >> simp[]) >>
  drule_all_then strip_assume_tac imm_place_at_value_type >>
  `val_wf (ArrayTV etv bd) (ArrayV av)` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  qabbrev_tac `cnt = array_length (ArrayTV etv bd) av` >>
  qabbrev_tac `dyn = case bd of Fixed _ => F | Dynamic _ => T` >>
  `cnt < dimword (:256)` by
    (simp[Abbr `cnt`] >> drule_all target_memory_array_length_bound >> simp[]) >>
  `valid_index (ArrayTV etv bd) av i <=> idx_in_range sgn iw (n2w cnt)` by
    (mp_tac (Q.INST [`et` |-> `etv`,`w` |-> `iw:bytes32`] array_index_word_bounds) >>
     fs[Abbr `cnt`]) >>
  `compile_array_subscript arg iop dyn (if dyn then 0 else cnt) 32
     (type_memory_size etv) sgn
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode) sn = (dst,sb)` by
    (Cases_on `bd` >> fs[Abbr `dyn`,Abbr `cnt`,array_length_def] >>
     Cases_on `av` >> gvs[value_has_type_def,array_length_def]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    drule_then ACCEPT_TAC stmt_state_rel_allocas_below_fmp >>
  `dyn ==> immutable_copy_read cenv.ce_is_ctor (n2w (off+k)) s = n2w cnt /\
    w2n (n2w (off+k):bytes32) + 32 <= lo /\
    mem_word_taint tn.t_mem (w2n (n2w (off+k):bytes32)) = {} /\
    (!region. cenv.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w /\
       copy_old_operand sn region /\ op_taint tn region = {} /\ op_prov G region = NONE)` by
    suspend "header" >>
  qpat_x_assum `!dyn cnt. _ ==> ?Gf tnf q. _` (qspecl_then [`dyn`,`cnt`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`Gf`,`tnf`,`q`] strip_assume_tac) >>
  Cases_on `idx_in_range sgn iw (n2w cnt)`
  >- suspend "in_range" >>
  suspend "out_of_range"
QED

Resume immutable_target_array_tail_selected_by[header]:
  Cases_on `bd` >> simp[Abbr `dyn`,Abbr `cnt`] >>
  `read_result cx (PlaceR (ImmutablePlace NONE id path)) ee = (INL (ArrayV av),ee)` by
    (Cases_on `ALOOKUP ee.immutables cx.txn.target` >> gvs[] >>
     simp[read_result_def,read_place_def,get_immutables_def,
          get_address_immutables_def,bind_def,lift_option_type_def,
          lift_sum_def,return_def]) >>
  `(mk_ptr arg LocCode).ptr_location = LocCode` by simp[contextTheory.mk_ptr_def] >>
  `vv_holds cenv cx (ArrayT et (Dynamic n)) (PlaceR (ImmutablePlace NONE id path))
     (LocatedValue (ArrayT et (Dynamic n)) (mk_ptr arg LocCode)) ee s` by
    (simp[vv_holds_def,contextTheory.mk_ptr_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `dead_lo_ok H0 (DF H0) lo cenv cx` by simp[] >>
  `!rt w. evaluate_type (get_tenv cx) (ArrayT et (Dynamic n)) = SOME rt /\
         eval_operand (mk_ptr arg LocCode).ptr_operand s = SOME w ==>
         w2n w + type_memory_size rt <= lo /\
         (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
            val_in_memory rt (ArrayV av) (w2n w) mem)` by
    (MATCH_MP_TAC (Q.INST [`entry` |-> `ee`, `H` |->
       `H0:((bool # bytes32 # type_value) list # num list)`,
       `D` |-> `DF (H0:((bool # bytes32 # type_value) list # num list))`,
       `env` |-> `env`, `tops` |-> `tops`, `ctx` |-> `ctx`,
       `func` |-> `func`, `d` |-> `d`, `G` |-> `G`]
       (INST_TYPE [alpha |-> ``:256``] extcall_request_saved_ctor_read)) >>
     asm_rewrite_tac[] >> simp[] >>
     qexists_tac `PlaceR (ImmutablePlace NONE id path)` >> simp[]) >>
  pop_assum (qspecl_then [`ArrayTV etv (Dynamic n)`,`n2w (off+k):bytes32`] mp_tac) >>
  simp[contextTheory.mk_ptr_def] >> strip_tac >>
  mp_tac (Q.INST [`H` |-> `H0:((bool # bytes32 # type_value) list # num list)`,
    `fin` |-> `ee`,`cap` |-> `n`,`w` |-> `n2w (off+k):bytes32`,
    `raw` |-> `PlaceR (ImmutablePlace NONE id path)`]
    (INST_TYPE [alpha |-> ``:256``] current_immutable_dynamic_header)) >>
  (impl_tac >- simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  strip_tac >>
  rpt strip_tac >>
  `lo <> 0` by decide_tac >>
  `eval_operand region s = SOME 0w` by
    metis_tac[bodyPtrBopInRepresentationTheory.membership_immutable_base_value] >>
  Cases_on `region` >>
  gvs[copy_old_operand_def,eval_operand_def,ghost_inv_at_def,op_taint_def,op_prov_def] >>
  metis_tac[local_ptrs_reserved_imm_base]
QED

Resume immutable_target_array_tail_selected_by[in_range]:
  `valid_index (ArrayTV etv bd) av i` by metis_tac[] >>
  `Num i = w2n iw` by
    (`0 <= i` by fs[vyperArrayTheory.valid_index_def,IgnAsm `i = _`] >>
     Cases_on `sgn` >> gvs[overflowElimHelpersTheory.nonneg_w2i_eq_w2n]) >>
  qpat_x_assum `i = if sgn then _ else _` kall_tac >>
  drule_then (qx_choose_then `v` assume_tac)
    (REWRITE_RULE [optionTheory.IS_SOME_EXISTS] array_index_valid) >>
  qpat_assum `idx_in_range _ _ _ ==> _` (drule_then strip_assume_tac) >>
  drule_all_then assume_tac array_element_step_offset >>
  drule_all_then strip_assume_tac exprSimPropsTheory.mem_path_offset_snoc >>
  `evaluate_subscripts (ArrayTV etv bd) (ArrayV av) [ValueSubscript (IntV i)] = INL v` by
    simp[evaluate_subscripts_def] >>
  `subscripts_type itv path = SOME (ArrayTV etv bd)` by
    metis_tac[exprSimPropsTheory.mem_path_offset_sound] >>
  `evaluate_subscripts itv iv (path ++ [ValueSubscript (IntV i)]) = INL v` by
    (drule_all evaluate_subscripts_append >> simp[]) >>
  `!gs. bind (extend_place cx (PlaceR (ImmutablePlace NONE id path))
      (ValueSubscript (IntV i))) get_place (ee with gas_obs := gs) =
    (INL (ImmutablePlace NONE id (path ++ [ValueSubscript (IntV i)])),
     ee with gas_obs := gs)` by
    (gen_tac >> Cases_on `ALOOKUP ee.immutables cx.txn.target` >> gvs[] >>
     mp_tac (Q.INST [`es` |-> `ee with gas_obs := gs`, `path` |-> `path`,
       `src` |-> `NONE`, `imms` |-> `x`, `ptv` |-> `ArrayTV etv bd`,
       `value` |-> `ArrayV av`, `sb` |-> `ValueSubscript (IntV i)`]
       immutable_target_extend) >>
     gvs[]) >>
  drule_then assume_tac
    (CONJUNCT2 (CONJUNCT2 exprOperandVarTheory.compiler_subscript_ops_var)) >>
  qexistsl [`INL (ImmutablePlace NONE id (path ++ [ValueSubscript (IntV i)]))`,
    `ee`,`OK q`,`Gf`,`tnf`] >>
  simp[exit_result_def] >> conj_tac >- fs[] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK q,Gf,tnf)` by
    (qpat_assum `idx_in_range sgn iw (n2w cnt)` (fn in_range =>
     qpat_assum `!D. gas_origin_ptr_path _ _ [] _`
       (qspec_then `DF H` (ACCEPT_TAC o REWRITE_RULE [in_range])))) >>
  `alloca_inv s` by
    drule_then (ACCEPT_TAC o CONJUNCT2) stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >>
  drule_all_then assume_tac body_full_path_alloca_history >>
  `stmt_state_rel H ctx func cenv cx ee q` by
    (qpat_assum `!K ce c e. stmt_state_rel K ctx func ce c e s /\
       local_ptrs_reserved ce sn ==> stmt_state_rel K ctx func ce c e q` irule >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sn x` by metis_tac[not_fresh_at_mono] >>
  `ghost_inv_at (DF H) lo d cenv cx ee Gf tnf q` by
    (irule ghost_inv_at_exterior_frame >>
     qexistsl [`G`,`ee`,`s`,`sn`,`tn`] >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf` by
    (irule ghost_kept_at_clean_suffix >> qexistsl [`G`,`tn`] >> simp[]) >>
  fs[wb_frame_def] >>
  `locals_kept cenv es ee s0 q` by
    (irule locals_kept_mem_tail >> qexists_tac `s` >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp q` by
    drule_then ACCEPT_TAC stmt_state_rel_allocas_below_fmp >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  Cases_on `bd` >>
  simp[imm_target_post_def,target_ptr_ok_def,Abbr `dyn`,
       wordsTheory.word_add_n2w,AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM,
       arithmeticTheory.MULT_COMM] >>
  metis_tac[]
QED

Resume immutable_target_array_tail_selected_by[out_of_range]:
  `~valid_index (ArrayTV etv bd) av i` by metis_tac[] >>
  qpat_x_assum `i = if sgn then _ else _` kall_tac >>
  `!al. av = SArrayV al ==> ?n. bd = Fixed n` by
    (rpt strip_tac >> Cases_on `bd` >> gvs[value_has_type_def]) >>
  `evaluate_subscripts (ArrayTV etv bd) (ArrayV av) [ValueSubscript (IntV i)] =
    INR (RuntimeError "evaluate_subscripts array_index")` by
    metis_tac[evaluate_array_subscript_oob] >>
  `subscripts_type itv path = SOME (ArrayTV etv bd)` by
    metis_tac[exprSimPropsTheory.mem_path_offset_sound] >>
  `!gs. bind (extend_place cx (PlaceR (ImmutablePlace NONE id path))
      (ValueSubscript (IntV i))) get_place (ee with gas_obs := gs) =
    (INR (Error (RuntimeError "evaluate_subscripts array_index")),ee with gas_obs := gs)` by
    (gen_tac >> Cases_on `ALOOKUP ee.immutables cx.txn.target` >> gvs[] >>
     mp_tac (Q.INST [`es` |-> `ee with gas_obs := gs`, `path` |-> `path`,
       `src` |-> `NONE`, `imms` |-> `x`, `ptv` |-> `ArrayTV etv bd`,
       `value` |-> `ArrayV av`, `sb` |-> `ValueSubscript (IntV i)`]
       immutable_target_extend) >>
     simp[]) >>
  qexistsl [`INR (Error (RuntimeError "evaluate_subscripts array_index"))`,
    `ee`,`Abort Revert_abort q`,`Gf`,`tnf`] >>
  simp[exit_result_def,expr_exit_def,halt_exit_def] >>
  rpt strip_tac >>
  qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (assume_tac o Q.SPEC `DF H`) >> gvs[]
QED

Finalise immutable_target_array_tail_selected_by
