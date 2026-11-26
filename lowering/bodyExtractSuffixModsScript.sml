(* Extract32 after its operands have returned: no child is evaluated here. *)
Theory bodyExtractSuffixMods
Ancestors
  bodyFullPostsMods bodyForRangeScalarFrameMods gasOutcomeFullPostMods
  bodyFullExtract32Certificate bodyFullUnwrapRun fragGasCopyLoop
  exprSimExtract32Read typeBuiltinPrereqs extract32Certificate haltExitProj
  exprSimMemDefs loweringPosts loweringStateRelDefs
  bodyPtrDefs ptrDiscipline freshWrites varsExt fragExec exprLoweringProps
  compileEnv venomState venomInst builtinBytes vyperInterpreter
  exprSimDefs vyperTypeSystem vyperContext vyperAST vyperState list words

Theorem extract32_suffix_mem_ok[local]:
  extract32_result_base_ok bt /\
  (case bt of UintT k => k <= 256 | IntT k => 0 < k /\ k <= 256 |
    BytesT (Fixed k) => k <= 32 | _ => T) /\
  val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p s.vs_memory /\
  LENGTH bs < dimword(:256) /\ n < dimword(:256) /\
  p+32+LENGTH bs < dimword(:256) /\
  eval_operand (Var len) s = SOME (n2w (LENGTH bs)) /\
  eval_operand (Var data) s = SOME (n2w (p+32)) /\
  eval_operand offset s = SOME (n2w n) /\
  (!z. Var len = Var z \/ Var data = Var z \/ offset = Var z ==> not_fresh_at st3 z) /\
  compile_extract32_load (Var len) (Var data) offset st3 = (raw,st4) /\
  compile_clamp_basetype raw (BaseT bt) st4 = (op,sb) /\
  p+32+LENGTH bs <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st3 sb) s
Proof
  strip_tac >> drule_all_then strip_assume_tac extract32_tail_code_cuts >>
  `eval_operand (Var len) (drop_fresh st3 s) = SOME (n2w (LENGTH bs)) /\
   eval_operand (Var data) (drop_fresh st3 s) = SOME (n2w (p+32)) /\
   eval_operand offset (drop_fresh st3 s) = SOME (n2w n)` by
    metis_tac[eval_operand_drop_fresh] >>
  `val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p
     (drop_fresh st3 s).vs_memory` by simp[drop_fresh_def] >>
  `(?t. run_inst_seq (emitted_insts st3 sb) (drop_fresh st3 s) = OK t) \/
   (?a t. run_inst_seq (emitted_insts st3 sb) (drop_fresh st3 s) = Abort a t)` by
    (drule_all (Q.INST [`s` |-> `drop_fresh st3 s`] extract32_tail_run_any) >>
     Cases_on `evaluate_extract32 bs n bt` >> simp[] >> metis_tac[]) >>
  `p+32 < dimword (:256)` by decide_tac >>
  `w2n (n2w (p+32):bytes32) + w2n (n2w (LENGTH bs):bytes32) <= s.vs_alloca_next` by
    simp[w2n_n2w, arithmeticTheory.MOD_LESS] >>
  drule extract32_suffix_separated_mem_ok >> disch_then drule >>
  simp[] >> disch_then irule >> simp[] >> metis_tac[]
QED

Theorem extract32_suffix_no_wrap[local]:
  compile_extract32_load len dp offset st3 = (raw,st4) /\
  compile_clamp_basetype raw ty st4 = (op,sb) ==>
  !pre i post u. emitted_insts st3 sb = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u
Proof
  strip_tac >> drule_all_then strip_assume_tac extract32_tail_code_cuts >>
  `EVERY (\ins. ins.inst_opcode <> DALLOCA) (emitted_insts st3 sb)` by
    (simp[EVERY_APPEND] >> conj_tac
     >- (mp_tac (Q.SPECL [`len`,`dp`,`offset`] extract32_read_load) >>
         simp[extract32_straight_read_frame_def] >> disch_then drule >>
         simp[EVERY_MEM] >> strip_tac >> rpt strip_tac >> first_x_assum drule >>
         gvs[fresh_write_op_def]) >>
     mp_tac (Q.SPECL [`raw`,`ty`] extract32_read_clamp_basetype) >>
     simp[extract32_straight_read_frame_def] >> disch_then drule >>
     simp[EVERY_MEM] >> strip_tac >> rpt strip_tac >> first_x_assum drule >>
     gvs[fresh_write_op_def]) >>
  rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
  qpat_x_assum `EVERY (\ins. ins.inst_opcode <> DALLOCA) _` mp_tac >>
  simp[EVERY_APPEND]
QED

Theorem extract32_link_word_post[local]:
  post_value_type cenv e = expr_type e /\
  immutable_frame_mods func cenv cx ee t /\
  vv_post H ctx func cenv cx e es sa sb s0 ee (Value v) (StackValue a op) t ==>
  vv_post_mods H ctx func cenv cx e es sa sb s0 ee (Value v) (StackValue a op) t
Proof
  simp[vv_post_mods_def, vv_post_def, vv_holds_mods_def, vv_place_ptr_mods_def] >>
  strip_tac >> simp[]
QED

Theorem extract32_suffix_landing[local]:
  compile_extract32_load len dp offset st3 = (raw,st4) /\
  compile_clamp_basetype raw ty st4 = (op,sb) /\
  run_inst_seq (emitted_insts st3 sb) s = OK t /\
  fn_has_code st3 sb func /\ fn_inst_ids_distinct func /\
  s.vs_current_bb = st3.cs_current_bb /\
  s.vs_inst_idx = LENGTH st3.cs_current_insts /\
  alloca_history func s /\ alloca_inv s ==>
  t = s with vs_vars := t.vs_vars /\
  (!x. not_fresh_at st3 x ==> lookup_var x t = lookup_var x s) /\
  t.vs_current_bb = sb.cs_current_bb /\
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >> drule_all_then strip_assume_tac extract32_tail_straight_noext >>
  drule_all_then strip_assume_tac extract32_tail_code_cuts >>
  `t = s with vs_vars := t.vs_vars` by
    (irule (cj 1 extract32_suffix_readonly_frame) >> simp[] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> irule extract32_suffix_lookup_kept >> metis_tac[]) >>
  conj_tac >- (qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  qpat_x_assum `emitted_insts st3 sb = _` kall_tac >>
  irule emitted_alloca_history >> simp[] >>
  qexistsl_tac [`emitted_insts st3 sb`,`s`,`st3`] >> simp[] >>
  conj_tac >- gvs[rich_listTheory.IS_PREFIX_APPEND, emitted_insts_def, DROP_APPEND] >>
  fs[EVERY_MEM]
QED

Theorem extract32_linked_landing_frames[local]:
  t = s with vs_vars := t.vs_vars /\
  (!x. not_fresh_at st3 x ==> lookup_var x t = lookup_var x s) /\
  local_ptrs_reserved cenv st3 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st3 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st3 x) /\
  immutable_frame_mods func cenv cx ee s /\
  ghost_inv_at_mods D lo d cenv cx ee G tn s /\
  th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
  th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
  (!x. not_fresh_at st3 x ==> FLOOKUP HG x = FLOOKUP G x /\
      op_taint th (Var x) = op_taint tn (Var x)) ==>
  immutable_frame_mods func cenv cx ee (t with vs_inst_idx := j) /\
  ghost_inv_at_mods D lo d cenv cx ee HG th (t with vs_inst_idx := j)
Proof
  strip_tac >>
  `!x. not_fresh_at st3 x ==> lookup_var x (t with vs_inst_idx := j) = lookup_var x s` by
    (rpt strip_tac >> simp[lookup_var_def] >> fs[lookup_var_def]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_data_section = s.vs_data_section /\
   t.vs_memory = s.vs_memory /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables` by
    (qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  conj_tac
  >- (irule immutable_frame_mods_exterior_frame >>
      qexistsl_tac [`ee`,`s`,`st3`] >> simp[]) >>
  irule ghost_inv_at_mods_exterior_frame >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem extract32_suffix_word_type[local]:
  extract32_result_base_ok bt /\
  (case bt of BytesT (Fixed k) => k <= 32 | _ => T) ==>
  is_word_type (BaseT bt)
Proof
  Cases_on `bt` >> simp[extract32_result_base_ok_def, is_word_type_def] >>
  rename1 `BytesT b` >> Cases_on `b` >> simp[extract32_result_base_ok_def, is_word_type_def]
QED

Theorem extract32_linked_word_landing[local]:
  expr_type e = BaseT bt /\ post_value_type cenv e = BaseT bt /\
  is_word_type (BaseT bt) /\
  local_ptrs_reserved cenv st3 /\ sa.cs_next_var <= st3.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st3 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st3 x) /\
  stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
  wb_frame cenv es ee sa s0 s /\
  (~expr_has_effect e ==> pure_frame cenv func es sa s0 s) /\
  immutable_frame_mods func cenv cx ee s /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  t = s with vs_vars := t.vs_vars /\
  (!x. not_fresh_at st3 x ==> lookup_var x t = lookup_var x s) /\
  eval_operand op t = SOME (typed_val_to_w256 (BaseTV bt) v) /\
  op_prov HG op = NONE /\ op_taint th op = {} /\
  th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
  th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
  (!x. not_fresh_at st3 x ==> FLOOKUP HG x = FLOOKUP G x /\
      op_taint th (Var x) = op_taint tn (Var x)) ==>
  vv_post_mods H ctx func cenv cx e es sa sb s0 ee (Value v)
    (StackValue (BaseT bt) op) (t with vs_inst_idx := j) /\
  vv_store_bound cx (BaseT bt) lt ee (Value v)
    (StackValue (BaseT bt) op) (t with vs_inst_idx := j) /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee HG th (t with vs_inst_idx := j) /\
  ptr_vv_ok cx (BaseT bt) (Value v) (StackValue (BaseT bt) op)
    ee HG th (t with vs_inst_idx := j) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 HG th
Proof
  strip_tac >> drule_all_then strip_assume_tac extract32_linked_landing_frames >>
  simp[ptr_vv_ok_def, ptr_val_ok_def, read_result_def, return_def] >>
  `vv_post H ctx func cenv cx e es sa sb s0 ee (Value v)
      (StackValue (BaseT bt) op) (t with vs_inst_idx := j) /\
   vv_store_bound cx (BaseT bt) lt ee (Value v)
      (StackValue (BaseT bt) op) (t with vs_inst_idx := j)` by
    (irule extract32_suffix_word_post >> simp[] >> qexistsl_tac [`s`,`st3`] >> simp[]) >>
  simp[] >> conj_tac >- (irule extract32_link_word_post >> simp[]) >>
  irule ghost_kept_at_clean_suffix >>
  qexistsl_tac [`G`,`tn`] >> simp[] >> rpt strip_tac >>
  `not_fresh_at st3 x` by (irule not_fresh_at_mono >> metis_tac[]) >>
  simp[]
QED

Theorem extract32_suffix_abort_path[local]:
  fn_has_code st3 sb func /\ sb.cs_current_bb = st3.cs_current_bb /\
  isPREFIX st3.cs_current_insts sb.cs_current_insts /\
  ~s.vs_halted /\ s.vs_current_bb = st3.cs_current_bb /\
  s.vs_inst_idx = LENGTH st3.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) (emitted_insts st3 sb) /\
  run_inst_seq_mem_ok (emitted_insts st3 sb) s /\
  (ctx_has_dalloca ctx ==> !pre i post u. emitted_insts st3 sb = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u) /\
  run_inst_seq (emitted_insts st3 sb) s = Abort Revert_abort t ==>
  ?j. !D lo explicit PG G tn HG th.
    inst_seq_ptr D lo ctx func PG G tn (emitted_insts st3 sb) s HG th ==>
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort Revert_abort (t with vs_inst_idx := j),HG,th)
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts st3 sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND, emitted_insts_def, DROP_APPEND] >>
     metis_tac[]) >>
  irule run_inst_seq_abort_origin_ptr_uniform >> goal_assum (drule_at Any) >>
  gvs[] >> metis_tac[APPEND]
QED

(* Saved input bytes, length and offset are from the start of this suffix.
   The success and revert paths use that same input and the same code cut. *)
val extract32_suffix_expr = ``TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]``;

Theorem extract32_suffix_mods:
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
  is_int_type (expr_type off) /\ (!l. offset <> Label l) /\
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
  s0.vs_alloca_next <= s.vs_alloca_next /\ p+32+LENGTH bs <= s.vs_alloca_next /\
  ee.gas_obs = [] /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\
    wb_frame cenv es ee sa s0 s /\
    (~expr_has_effect ^extract32_suffix_expr ==> pure_frame cenv func es sa s0 s) /\
    immutable_frame_mods func cenv cx ee s /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (bind (lift_sum (evaluate_type_builtin cx Extract32 (BaseT bt)
      [expr_type src;expr_type off] [BytesV bs;IntV i])) (\v. return (Value v)))
    (ee,s,G,tn)
    (\H res ee' HG th t. ?tv. res = INL tv /\
      vv_post_mods H ctx func cenv cx ^extract32_suffix_expr es sa sb s0 ee' tv
        (StackValue (BaseT bt) op) t /\
      vv_store_bound cx (post_value_type cenv ^extract32_suffix_expr)
        (lowered_value_type cenv ^extract32_suffix_expr) ee' tv (StackValue (BaseT bt) op) t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee' HG th t /\
      ptr_vv_ok cx (post_value_type cenv ^extract32_suffix_expr)
        tv (StackValue (BaseT bt) op) ee' HG th t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 HG th)
    (\H res ee' gt r. expr_exit res r /\ halt_exit H cx ee' res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  strip_tac >>
  `is_word_type (BaseT bt)` by
    (irule extract32_suffix_word_type >> simp[] >> Cases_on `bt` >> fs[]) >>
  `not_fresh_at st3 len /\ not_fresh_at st3 data /\
   (!z. offset = Var z ==> not_fresh_at st3 z)` by metis_tac[operand_11] >>
  drule_all extract32_suffix_certificate >>
  disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >>
  drule_all_then strip_assume_tac extract32_tail_straight_noext >>
  drule_all_then assume_tac extract32_suffix_mem_ok >>
  `(ctx_has_dalloca ctx ==> !pre ins post u. emitted_insts st3 sb = pre ++ ins::post /\
     run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap ins u)` by
    (strip_tac >> drule extract32_suffix_no_wrap >> disch_then drule >>
     disch_then (qspec_then `s` ACCEPT_TAC)) >>
  drule_all_then strip_assume_tac extract32_tail_code_cuts >>
  qpat_x_assum `emitted_insts st3 sb = _` kall_tac >>
  drule_all extract32_tail_run_any >> Cases_on `evaluate_extract32 bs (Num i) bt` >>
  simp[] >> strip_tac
  >- suspend "success" >>
  suspend "abort"
QED

Resume extract32_suffix_mods[success]:
  markerLib.RESUME_TAC >>
  drule_all_then strip_assume_tac extract32_suffix_landing >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  rename1 `evaluate_extract32 bs (Num i) bt = INL v` >>
  qexistsl_tac [`HG`,`ee`,`INL (Value v)`,
    `t with vs_inst_idx := LENGTH sb.cs_current_insts`,`th`] >>
  conj_tac >-
    simp[evaluate_type_builtin_def, lift_sum_def, bind_def, return_def] >>
  qx_gen_tac `H` >> strip_tac >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  simp[] >> conj_tac
  >- (irule emitted_origin_ptr_path >> simp[] >>
      qexistsl_tac [`emitted_insts st3 sb`,`st3`] >> simp[] >>
      (conj_tac >- gvs[rich_listTheory.IS_PREFIX_APPEND, emitted_insts_def, DROP_APPEND]) >>
      fs[EVERY_MEM] >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon cx st0 H _ ==> _` drule >> strip_tac >>
  `op_prov HG op = NONE /\ op_taint th op = {}` by
    (qpat_assum `!t. run_inst_seq _ _ = OK t ==> _` drule >> simp[]) >>
  drule_all_then (qspec_then `sb` strip_assume_tac)
    (Q.INST [`e` |-> `^extract32_suffix_expr`,
       `lt` |-> `lowered_value_type cenv ^extract32_suffix_expr`,
       `j` |-> `LENGTH sb.cs_current_insts`] extract32_linked_word_landing |>
     SIMP_RULE bool_ss [post_value_type_def, expr_type_def]) >>
  simp[post_value_type_def, expr_type_def] >>
  `t.vs_alloca_next = s.vs_alloca_next /\
   allocas_below_fmp t = allocas_below_fmp s` by
    (qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >>
     simp[allocas_below_fmp_def]) >>
  simp[ptr_vv_ok_def, ptr_val_ok_def, read_result_def, return_def]
QED

Resume extract32_suffix_mods[abort]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `_ = RuntimeError _` SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac extract32_suffix_abort_path >>
  irule gas_outcome_full_mods_exit_revert >> simp[] >>
  rename1 `evaluate_extract32 bs (Num i) bt = INR (RuntimeError msg)` >>
  qexistsl_tac [`HG`,`ee`,`INR (vyperState$Error (RuntimeError msg))`,`th`,
    `t with vs_inst_idx := j`] >>
  simp[exit_result_def] >> conj_tac
  >- simp[evaluate_type_builtin_def, lift_sum_def, bind_def, raise_def] >>
  rpt strip_tac >> simp[expr_exit_def, halt_exit_not_halt] >>
  first_x_assum irule >> simp[]
QED

Finalise extract32_suffix_mods
