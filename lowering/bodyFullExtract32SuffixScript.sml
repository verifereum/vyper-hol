(* Joint finite-horizon execution of the read-only Extract32 suffix. *)
Theory bodyFullExtract32Suffix
Ancestors
  typeBuiltinPrereqs
  bodyFullExtract32Certificate bodyFullUnwrapRun bodyFullGhostFrame
  fragGasCopyLoop varsExt freshWrites
  exprSimExtract32Run exprSimExtract32Read
   exprSimExtract32Source bodySimFull gasOutcomeFullCompose
  extract32Certificate exprLoweringProps exprSimMemDefs loweringPosts
  bodyPtrDefs ptrDiscipline compileEnv venomState venomInst
  builtinBytes vyperInterpreter vyperTypeSystem vyperState loweringStateRelDefs list words

Theorem extract32_suffix_success_frame[local]:
  compile_extract32_load l dp offset st3 = (raw,st4) /\
  compile_clamp_basetype raw (BaseT bt) st4 = (op,sb) /\
  fn_has_code st3 sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv st3 /\ sa.cs_next_var <= st3.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st3 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st3 x) /\
  s.vs_current_bb = st3.cs_current_bb /\
  s.vs_inst_idx = LENGTH st3.cs_current_insts /\
  alloca_history func s /\ alloca_inv s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  stmt_state_rel H ctx func cenv cx ee s /\
  storage_well_formed_on cx ee (FST H) /\
  wb_frame cenv es ee sa s0 s /\
  (~expr_has_effect e ==> pure_frame cenv func es sa s0 s) /\
  ghost_inv_at D lo d cenv cx ee G tn s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  expr_type e = BaseT bt /\ post_value_type cenv e = BaseT bt /\
  is_word_type (BaseT bt) /\
  run_inst_seq (emitted_insts st3 sb) s = OK t /\
  eval_operand op t = SOME (typed_val_to_w256 (BaseTV bt) v) /\
  op_prov HG op = NONE /\ op_taint th op = {} /\
  th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
  th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
  (!x. not_fresh_at st3 x ==> FLOOKUP HG x = FLOOKUP G x /\
    op_taint th (Var x) = op_taint tn (Var x)) ==>
  vv_post H ctx func cenv cx e es sa sb s0 ee (Value v)
    (StackValue (BaseT bt) op) (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee (Value v)
    (StackValue (BaseT bt) op) (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  t.vs_current_bb = sb.cs_current_bb /\
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at D lo d cenv cx ee HG th
    (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  ptr_vv_ok cx (post_value_type cenv e) (Value v) (StackValue (BaseT bt) op)
    ee HG th (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 HG th
Proof
  strip_tac >>
  drule_all extract32_tail_straight_noext >> strip_tac >>
  drule_all extract32_tail_code_cuts >> strip_tac >>
  `emitted_insts st3 sb = emitted_insts st3 st4 ++ emitted_insts st4 sb` by
    metis_tac[] >>
  `sb.cs_current_insts = st3.cs_current_insts ++ emitted_insts st3 sb` by
    (qpat_x_assum `emitted_insts st3 sb = _` kall_tac >>
     gvs[rich_listTheory.IS_PREFIX_APPEND, emitted_insts_def, DROP_APPEND]) >>
  `t = s with vs_vars := t.vs_vars` by
    (irule (cj 1 extract32_suffix_readonly_frame) >> simp[] >>
     metis_tac[]) >>
  `!x. not_fresh_at st3 x ==> lookup_var x t = lookup_var x s` by
    metis_tac[extract32_suffix_lookup_kept] >>
  `vv_post H ctx func cenv cx e es sa sb s0 ee (Value v)
     (StackValue (BaseT bt) op) (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
   vv_store_bound cx (BaseT bt) (lowered_value_type cenv e) ee (Value v)
     (StackValue (BaseT bt) op) (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule extract32_suffix_word_post >> simp[] >> qexistsl_tac [`s`,`st3`] >> simp[]) >>
  `alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule emitted_alloca_history >> simp[] >>
     qexistsl_tac [`emitted_insts st3 sb`,`s`,`st3`] >> simp[] >>
     gvs[EVERY_APPEND, EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `sb.cs_current_insts = _` kall_tac >>
  simp[] >>
  conj_tac >- (qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[] >> metis_tac[]) >>
  conj_tac >- (qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  conj_tac
  >- (irule ghost_inv_at_exterior_frame >>
      qexistsl_tac [`G`,`ee`,`s`,`st3`,`tn`] >> simp[] >>
      conj_tac >- gvs[lookup_var_def] >>
      qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  conj_tac
  >- simp[ptr_vv_ok_def, ptr_val_ok_def, read_result_def, vyperStateTheory.return_def] >>
  irule ghost_kept_at_clean_suffix >> simp[] >>
  qexistsl_tac [`G`,`tn`] >> simp[] >> rpt strip_tac >>
  `not_fresh_at st3 x` by (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  metis_tac[]
QED

(* The inputs transported from the normal source and offset landings. *)
Definition extract32_suffix_ready_def:
  extract32_suffix_ready (DF,lo,d,ctx,func) cenv cx st0 (src,off,bt)
    (es,sa,s0,G0,tn0) (st3,sb,op) (ee,s,G,tn)
    (bs,m,p,i,len,data,offset,raw,st4,srcop) <=>
  extract32_result_base_ok bt /\
  (case bt of UintT k => k <= 256 | IntT k => 0 < k /\ k <= 256 |
    BytesT (Fixed k) => k <= 32 | _ => T) /\
  val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p s.vs_memory /\
  LENGTH bs < dimword(:256) /\ Num i < dimword(:256) /\
  p+32+LENGTH bs < dimword(:256) /\
  eval_operand (Var len) s = SOME (n2w (LENGTH bs)) /\
  eval_operand (Var data) s = SOME (n2w (p+32)) /\
  eval_operand offset s = SOME (n2w (Num i)) /\
  (!z. Var len = Var z \/ Var data = Var z \/ offset = Var z ==> not_fresh_at st3 z) /\
  compile_extract32_load (Var len) (Var data) offset st3 = (raw,st4) /\
  compile_clamp_basetype raw (BaseT bt) st4 = (op,sb) /\
  0 <= i /\ expr_type src = BaseT (BytesT (Dynamic m)) /\
  is_int_type (expr_type off) /\
  (!l. offset <> Label l) /\
  op_prov G offset = NONE /\ op_taint tn offset = {} /\
  op_prov G (Var len) = NONE /\ op_taint tn (Var len) = {} /\
  ptr_mem_ok cx (expr_type src) (BytesV bs) srcop G tn s /\
  evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m))) /\
  eval_operand srcop s = SOME (n2w p) /\
  (!span. 0 < LENGTH bs /\ span <= LENGTH bs ==> ptr_covers G tn data s span) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  fn_has_code st3 sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv st3 /\ sa.cs_next_var <= st3.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st3 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st3 x) /\
  ~s.vs_halted /\ s.vs_current_bb = st3.cs_current_bb /\
  s.vs_inst_idx = LENGTH st3.cs_current_insts /\
  alloca_history func s /\ alloca_inv s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  p+32+LENGTH bs <= s.vs_alloca_next /\
  ee.gas_obs = [] /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    wb_frame cenv es ee sa s0 s /\
    (~expr_has_effect (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]) ==>
      pure_frame cenv func es sa s0 s) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
End

Theorem extract32_suffix_landing:
  extract32_suffix_ready (DF,lo,d,ctx,func) cenv cx st0 (src,off,bt)
    (es,sa,s0,G0,tn0) (st3,sb,op) (ee,s,G,tn)
    (bs,m,p,i,len,data,offset,raw,st4,srcop) ==>
  ?res r HG th.
    (!tail. bind (lift_sum (evaluate_type_builtin cx Extract32 (BaseT bt)
      [expr_type src;expr_type off] [BytesV bs;IntV i]))
      (\v. return (Value v)) (ee with gas_obs := tail) =
          (res,ee with gas_obs := tail)) /\
    ((?t. run_inst_seq (emitted_insts st3 sb) s = OK t /\
          r = OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) \/
     (?t j. run_inst_seq (emitted_insts st3 sb) s = Abort Revert_abort t /\
            r = Abort Revert_abort (t with vs_inst_idx := j))) /\
    !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (r,HG,th) /\
      ((?t tv. r = OK t /\ res = INL tv /\
        vv_post H ctx func cenv cx
          (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]) es sa sb s0 ee tv
          (StackValue (BaseT bt) op) t /\
        vv_store_bound cx (BaseT bt)
          (lowered_value_type cenv (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]))
          ee tv (StackValue (BaseT bt) op) t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee HG th t /\
        ptr_vv_ok cx (BaseT bt) tv (StackValue (BaseT bt) op) ee HG th t /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 HG th) \/
       (exit_result r /\ expr_exit res r))
Proof
  rewrite_tac[extract32_suffix_ready_def] >> strip_tac >>
  `not_fresh_at st3 len /\ not_fresh_at st3 data` by metis_tac[] >>
  `!z. offset = Var z ==> not_fresh_at st3 z` by metis_tac[] >>
  drule_all extract32_suffix_certificate >>
  disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >>
  drule_all extract32_tail_code_cuts >> strip_tac >>
  `emitted_insts st3 sb = emitted_insts st3 st4 ++ emitted_insts st4 sb` by metis_tac[] >>
  `EVERY (\ins. ins.inst_opcode <> DALLOCA) (emitted_insts st3 sb)` by
    (simp[EVERY_APPEND] >> conj_tac
     >- (mp_tac (Q.SPECL [`Var len`,`Var data`,`offset`] extract32_read_load) >>
         simp[extract32_straight_read_frame_def] >> disch_then drule >>
         simp[EVERY_MEM] >> strip_tac >> rpt strip_tac >> first_x_assum drule >>
         gvs[fresh_write_op_def]) >>
     mp_tac (Q.SPECL [`raw`,`BaseT bt`] extract32_read_clamp_basetype) >>
     simp[extract32_straight_read_frame_def] >> disch_then drule >>
     simp[EVERY_MEM] >> strip_tac >> rpt strip_tac >> first_x_assum drule >>
     gvs[fresh_write_op_def]) >>
  `(ctx_has_dalloca ctx ==>
    !pre ins post u. emitted_insts st3 sb = pre ++ ins::post /\
      run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap ins u)` by
    (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     qpat_x_assum `EVERY (\ins. ins.inst_opcode <> DALLOCA) _` mp_tac >>
     simp[EVERY_APPEND]) >>
  `eval_operand (Var len) (drop_fresh st3 s) = SOME (n2w (LENGTH bs)) /\
   eval_operand (Var data) (drop_fresh st3 s) = SOME (n2w (p+32)) /\
   eval_operand offset (drop_fresh st3 s) = SOME (n2w (Num i))` by
    metis_tac[eval_operand_drop_fresh] >>
  `val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p
    (drop_fresh st3 s).vs_memory` by simp[drop_fresh_def] >>
  `(?t. run_inst_seq (emitted_insts st3 sb) (drop_fresh st3 s) = OK t) \/
   (?a t. run_inst_seq (emitted_insts st3 sb) (drop_fresh st3 s) = Abort a t)` by
    (drule_all extract32_tail_run_any >>
     Cases_on `evaluate_extract32 bs (Num i) bt` >> simp[] >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts st3 sb) s` by
    (`w2n (n2w (p+32):bytes32) + w2n (n2w (LENGTH bs):bytes32) <= s.vs_alloca_next` by
       (simp[w2n_n2w] >> metis_tac[arithmeticTheory.MOD_LESS, arithmeticTheory.LESS_EQ_TRANS]) >>
     drule extract32_suffix_separated_mem_ok >>
     disch_then drule >> simp[] >>
     disch_then irule >> simp[] >> metis_tac[]) >>
  qpat_x_assum `run_inst_seq _ (drop_fresh _ _) = _` kall_tac >>
  qpat_x_assum `val_in_memory _ _ _ (drop_fresh _ _).vs_memory` kall_tac >>
  (drule_all extract32_tail_run_any >>
   Cases_on `evaluate_extract32 bs (Num i) bt` >> gvs[]
   >- suspend "success"
   >> suspend "abort")
QED

Resume extract32_suffix_landing[success]:
  markerLib.RESUME_TAC >> strip_tac >>
  qexistsl_tac [`INL (Value x)`,`OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)`,`HG`,`th`] >>
  conj_tac
  >- (gen_tac >> simp[vyperContextTheory.evaluate_type_builtin_def, lift_sum_def, bind_def, return_def]) >>
  conj_tac >- metis_tac[] >>
  gen_tac >> strip_tac >> simp[] >> conj_tac
  >- (irule bodyFullUnwrapRunTheory.emitted_origin_ptr_path >>
      simp[] >> qexistsl_tac [`emitted_insts st3 sb`,`st3`] >> simp[EVERY_APPEND] >>
      drule_all extract32_tail_straight_noext >> strip_tac >>
      gvs[rich_listTheory.IS_PREFIX_APPEND, emitted_insts_def, DROP_APPEND, EVERY_APPEND, EVERY_MEM] >>
      metis_tac[]) >>
  `is_word_type (BaseT bt)` by
    (Cases_on `bt` >> gvs[extract32_result_base_ok_def, is_word_type_def] >>
     rename1 `BytesT b` >> Cases_on `b` >> gvs[extract32_result_base_ok_def, is_word_type_def]) >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
  simp[] >> strip_tac >>
  `op_prov HG op = NONE /\ op_taint th op = {}` by metis_tac[] >>
  `run_inst_seq (emitted_insts st3 sb) s = OK t` by metis_tac[] >>
  drule_all (extract32_suffix_success_frame |> SPEC_ALL |>
    Q.INST [`e` |-> `TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]`] |>
    SIMP_RULE (srw_ss()) [post_value_type_def, vyperASTTheory.expr_type_def] |> GEN_ALL) >>
  strip_tac >> simp[vyperASTTheory.expr_type_def, contextTheory.vv_location_def] >>
  metis_tac[]
QED
Resume extract32_suffix_landing[abort]:
  markerLib.RESUME_TAC >> strip_tac >>
  drule_all extract32_tail_straight_noext >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts st3 sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fragExecTheory.fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND,
       emitted_insts_def, DROP_APPEND] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS)
     (emitted_insts st3 st4 ++ emitted_insts st4 sb)` by simp[EVERY_APPEND] >>
  qspecl_then [`emitted_insts st3 sb`,`s`,`Revert_abort`,`t`,`ctx`,`func`,`bb`]
    mp_tac run_inst_seq_abort_origin_ptr_uniform >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `j` assume_tac) >>
  qexistsl_tac [`INR (Error y)`,`Abort Revert_abort (t with vs_inst_idx := j)`,`HG`,`th`] >>
  conj_tac
  >- (gen_tac >> simp[vyperContextTheory.evaluate_type_builtin_def, lift_sum_def, bind_def, return_def, raise_def]) >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> simp[exprSimDefsTheory.expr_exit_def, fragExecTheory.exit_result_def] >>
  first_x_assum irule >> simp[]
QED

Finalise extract32_suffix_landing

Theorem extract32_suffix_result_word:
  extract32_result_base_ok bt /\
  (case bt of UintT k => k <= 256 | IntT k => 0 < k /\ k <= 256 |
    BytesT (Fixed k) => k <= 32 | _ => T) ==> is_word_type (BaseT bt)
Proof
  Cases_on `bt` >> simp[extract32_result_base_ok_def, is_word_type_def] >>
  rename1 `BytesT b` >> Cases_on `b` >> simp[extract32_result_base_ok_def, is_word_type_def]
QED

(* The original unscoped interface is the projection of the selected run. *)
Theorem extract32_suffix_full:
  extract32_result_base_ok bt /\
  (case bt of UintT k => k <= 256 | IntT k => 0 < k /\ k <= 256 |
    BytesT (Fixed k) => k <= 32 | _ => T) /\
  val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p s.vs_memory /\
  LENGTH bs < dimword(:256) /\ Num i < dimword(:256) /\
  p+32+LENGTH bs < dimword(:256) /\
  eval_operand (Var len) s = SOME (n2w (LENGTH bs)) /\
  eval_operand (Var data) s = SOME (n2w (p+32)) /\
  eval_operand offset s = SOME (n2w (Num i)) /\
  (!z. Var len = Var z \/ Var data = Var z \/ offset = Var z ==> not_fresh_at st3 z) /\
  compile_extract32_load (Var len) (Var data) offset st3 = (raw,st4) /\
  compile_clamp_basetype raw (BaseT bt) st4 = (op,sb) /\
  0 <= i /\ expr_type src = BaseT (BytesT (Dynamic m)) /\
  is_int_type (expr_type off) /\
  (!l. offset <> Label l) /\
  op_prov G offset = NONE /\ op_taint tn offset = {} /\
  op_prov G (Var len) = NONE /\ op_taint tn (Var len) = {} /\
  ptr_mem_ok cx (expr_type src) (BytesV bs) srcop G tn s /\
  evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m))) /\
  eval_operand srcop s = SOME (n2w p) /\
  (!span. 0 < LENGTH bs /\ span <= LENGTH bs ==> ptr_covers G tn data s span) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  fn_has_code st3 sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv st3 /\ sa.cs_next_var <= st3.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st3 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st3 x) /\
  ~s.vs_halted /\ s.vs_current_bb = st3.cs_current_bb /\
  s.vs_inst_idx = LENGTH st3.cs_current_insts /\
  alloca_history func s /\ alloca_inv s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  p+32+LENGTH bs <= s.vs_alloca_next /\
  ee.gas_obs = [] /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    wb_frame cenv es ee sa s0 s /\
    (~expr_has_effect (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]) ==>
      pure_frame cenv func es sa s0 s) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (bind (lift_sum (evaluate_type_builtin cx Extract32 (BaseT bt)
      [expr_type src;expr_type off] [BytesV bs;IntV i]))
      (\v. return (Value v)))
    (ee,s,G,tn)
    (\H res ee' HG th t. ?tv. res = INL tv /\
      vv_post H ctx func cenv cx
        (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]) es sa sb s0 ee' tv
        (StackValue (BaseT bt) op) t /\
      vv_store_bound cx (expr_type (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]))
        (lowered_value_type cenv (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]))
        ee' tv (StackValue (BaseT bt) op) t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee' HG th t /\
      ptr_vv_ok cx (post_value_type cenv (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]))
        tv (StackValue (BaseT bt) op) ee' HG th t /\
      (cenv.ce_is_ctor /\ vv_location (StackValue (BaseT bt) op) = SOME LocCode ==>
        ?val. read_result cx tv ee' = (INL val,ee') /\
          !rt w. evaluate_type (get_tenv cx)
            (post_value_type cenv (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off])) = SOME rt /\
            eval_operand (vv_operand (StackValue (BaseT bt) op)) t = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside th.t_mem t.vs_memory mem ==>
              val_in_memory rt val (w2n w) mem)) /\
      (!t' op'. StackValue (BaseT bt) op = StackValue t' op' /\
        ~is_word_type (post_value_type cenv (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off])) ==>
        ptr_buf_ok cenv (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]) op' HG t) /\
      (!t' p'. StackValue (BaseT bt) op = LocatedValue t' p' /\
        p'.ptr_location = LocMemory ==>
        ptr_buf_ok cenv (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]) p'.ptr_operand HG t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 HG th)
    (\H res ee' gt r. expr_exit res r)
Proof
  strip_tac >>
  drule_all (REWRITE_RULE [extract32_suffix_ready_def] extract32_suffix_landing) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `is_word_type (BaseT bt)` by metis_tac[extract32_suffix_result_word] >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  rewrite_tac[gasOutcomeFullTheory.gas_outcome_full_def] >>
  simp[] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`,`ee`,`r`,`HG`,`th`] >>
  simp[gasSummaryTheory.gas_explicit_def, post_value_type_def, vyperASTTheory.expr_type_def,
       contextTheory.vv_location_def] >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> gvs[fragExecTheory.exit_result_def] >>
  metis_tac[]
QED
