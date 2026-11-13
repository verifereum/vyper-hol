(* Re-establish body state at the actual singleton word staging endpoint. *)
Theory bodyAbiEncodeWordResultMemory
Ancestors
  exprSimSource abiBuiltinEncodeCode abiBuiltinEncodeResources abiEncoderCounters
  bodyAbiEncodeWordSource exprSimWordArgs bodyAbiEncodeWordMemory bodyAbiEncodeResultMemory bodyAbiEncodeAllocationState bodyAbiEncodeWordOutputFrame abiEncoderWindowContract abiEncodeWordWindowGrowth
  abiEncoderWindowPhase abiEncoderWindowMemFrame abiEncoderRegisteredEffect
  abiBuiltinEncodeWord abiEncoderWindowChild abiEncoderWindow fragExec
  abiCallerLocalScratch exprSimAlloc loweringHalt emitHelperProps localPtrsProps exprSimProps exprLoweringProps compileEnv loweringPosts
  venomState venomInst venomMemDefs valueEncoding finite_map pred_set words list arithmetic


Theorem abi_encode_word_source_state_mem:
  is_word_type (expr_type e) /\
  lower_value cfn ce (expr_type e) e origin = (value_op,arg_st) /\
  compile_type_builtin_dispatch_body cfn ce vv_ty ty
    (AbiEncode F method_id) ret_ty [e] origin = (vv,final) /\
  fn_has_code arg_st final func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx ee s /\ local_ptrs_reserved ce arg_st /\
  eval_operand value_op s = SOME w /\
  (!x. value_op = Var x ==> not_fresh_at arg_st x) /\
  has_type at av /\ ~is_dynamic at /\ static_length at = 32 /\
  word_to_bytes w T = enc at av /\
  ~s.vs_halted /\ s.vs_current_bb = arg_st.cs_current_bb /\
  s.vs_inst_idx = LENGTH arg_st.cs_current_insts ==>
  ?buf allocated staged out t sb.
    compile_alloc_buffer 32 arg_st = (buf,allocated) /\
    emit_void MSTORE [buf.buf_operand;value_op] allocated = ((),staged) /\
    lower_abi_encode F (OPTION_MAP bytes_method_id_word method_id) buf.buf_operand
      (type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e))
      (abi_size_bound ce.ce_struct_fields (expr_type e)) staged = (out,final) /\
    vv = LocatedValue vv_ty (mk_ptr out LocMemory) /\
    fn_has_code arg_st staged func /\ fn_has_code staged final func /\
    stmt_state_rel ctx func ce cx ee t /\ local_ptrs_reserved ce staged /\
    window_phase ctx func arg_st staged {arg_st.cs_next_id} [] s t /\
    mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t /\
    wb_frame ce ee arg_st s t /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    eval_operand buf.buf_operand t = SOME (n2w sb) /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at staged x) /\
    abi_encoder_window_input
      (type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e)) at av sb 32 t.vs_memory /\
    FLOOKUP t.vs_allocas arg_st.cs_next_id = SOME (sb,32) /\
    sb+32 <= t.vs_alloca_next /\ sb+32 < dimword (:256)
Proof
  strip_tac >> drule_all compile_abi_encode_word_trace >> strip_tac >>
  drule compile_alloc_buffer_extends >> strip_tac >>
  drule window_child_void_shape >> strip_tac >>
  drule lower_abi_encode_extends >> strip_tac >>
  `cs_extends arg_st staged` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  `fn_has_code arg_st allocated func` by metis_tac[fn_has_code_split] >>
  drule_all buffer_alloc_code >> strip_tac >>
  `!b sz. FLOOKUP s.vs_allocas arg_st.cs_next_id = SOME (b,sz) ==> sz = 32` by
    (rpt strip_tac >>
     qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     simp[stmt_state_rel_def] >> rpt strip_tac >>
     first_x_assum drule >> simp[mk_inst_def, dimword_def]) >>
  `alloca_inv s /\ alloca_room ctx func s` by fs[stmt_state_rel_def] >>
  drule_all abi_encode_word_source_window_mem >> strip_tac >>
  `buf' = buf /\ allocated' = allocated` by metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `buf' = buf` SUBST_ALL_TAC >>
  qpat_x_assum `allocated' = allocated` SUBST_ALL_TAC >>
  `staged' = staged` by metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `staged' = staged` SUBST_ALL_TAC >>
  `out' = out` by metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `out' = out` SUBST_ALL_TAC >>
  `stmt_state_rel ctx func ce cx ee t` by
    (irule abi_encode_word_stage_state >> asm_rewrite_tac[] >>
     qpat_assum `MEM (mk_inst _ _ _ _) _` (irule_at Any) >>
     simp_tac (srw_ss()) [mk_inst_def] >>
     qpat_assum `window_phase _ _ _ _ _ _ _ _` (irule_at Any) >>
     qexistsl [`32`, `sb`] >> simp_tac (srw_ss()) [dimword_def] >>
     asm_rewrite_tac[] >>
     metis_tac[local_ptrs_reserved_fresh, LESS_EQ_REFL]) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `local_ptrs_reserved ce staged` by
    (irule local_ptrs_reserved_next_var >> qexists `arg_st` >>
     asm_rewrite_tac[] >> simp_tac arith_ss []) >>
  `wb_frame ce ee arg_st s t` by
    (irule abi_encode_singleton_wb_frame >>
     qpat_assum `MEM (mk_inst _ _ _ _) _` (irule_at Any) >>
     simp_tac (srw_ss()) [mk_inst_def] >>
     qpat_assum `window_phase _ _ _ _ _ _ _ _` (irule_at Any) >>
     qexists `cx` >> asm_rewrite_tac[] >>
     irule local_ptrs_reserved_fresh >> qexists `arg_st` >>
     asm_rewrite_tac[] >> simp_tac arith_ss []) >>
  qexistsl [`buf`, `allocated`, `staged`, `out`, `t`, `sb`] >>
  asm_rewrite_tac[] >> first_x_assum irule >> first_assum ACCEPT_TAC
QED

Theorem abi_encode_word_output_choice[local]:
  lower_abi_encode ensure mid src (AbiCopy 32) maxlen st = (out,final) /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx ee s /\ local_ptrs_reserved ce st /\
  32+32*word_size (maxlen+(case mid of NONE => 0 | SOME _ => 4)) < dimword (:256) ==>
  ?p. (FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas st.cs_next_id = SOME
      (p,32+32*word_size (maxlen+(case mid of NONE => 0 | SOME _ => 4)))
Proof
  strip_tac >> drule_all abi_encode_word_output_sites >>
  disch_then (qspec_then `ee.scopes` strip_assume_tac) >>
  Cases_on `FLOOKUP s.vs_allocas st.cs_next_id`
  >- (qexists `s.vs_alloca_next` >> simp[]) >>
  PairCases_on `x` >>
  `x1 = 32+32*word_size (maxlen+(case mid of NONE => 0 | SOME _ => 4))` by
    (fs[stmt_state_rel_def] >> first_x_assum drule >> simp[]) >>
  qexists `x0` >> simp[]
QED

Theorem abi_encode_word_output_mem:
  let n = 32+32*word_size (maxlen+(case mid of NONE => 0 | SOME _ => 4)) in
  let bytes = (case mid of NONE => enc at av
    | SOME m => abi_builtin_encode_method_bytes m ++ enc at av) in
  lower_abi_encode ensure mid src (AbiCopy 32) maxlen st = (out,final) /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx ee s /\ local_ptrs_reserved ce st /\
  abi_encoder_window_input (AbiCopy 32) at av sb 32 s.vs_memory /\
  LENGTH (enc at av) <= maxlen /\ eval_operand src s = SOME (n2w sb) /\
  (!x. src = Var x ==> not_fresh_at st x) /\ n < dimword (:256) /\
  FLOOKUP s.vs_allocas aid = SOME (sb,32) /\ aid < st.cs_next_id /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t p. window_phase ctx func st final
      (window_alloca_sites func (frag_ids st final)) [(p,n)] s t /\
    mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t /\
    wb_frame ce ee st s t /\
    stmt_state_rel ctx func ce cx ee t /\
    eval_operand out t = SOME (n2w p) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,n) /\
    p+n <= t.vs_alloca_next /\ p+n < dimword (:256) /\
    mem_bytes_at (p+32) (LENGTH bytes) t.vs_memory = bytes /\
    val_in_memory (BaseTV (BytesT (Dynamic
      (maxlen+(case mid of NONE => 0 | SOME _ => 4)))))
      (vyperValue$BytesV bytes) p t.vs_memory /\
    (!name b sz. local_region ce ee.scopes t name b sz ==>
      p+n <= b \/ b+sz <= p) /\
    (!i r. FLOOKUP s.vs_allocas i = SOME r ==> FLOOKUP t.vs_allocas i = SOME r) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_encode_word_output_choice >>
  disch_then (qx_choose_then `p` assume_tac) >>
  `alloca_inv s /\ alloca_room ctx func s` by fs[stmt_state_rel_def] >>
  `sb+32 <= s.vs_alloca_next` by
    metis_tac[allocaSiteResourceTheory.alloca_site_registered_below] >>
  `venomMemDefs$regions_disjoint (sb,32) (p,
    32+32*word_size (maxlen+(case mid of NONE => 0 | SOME _ => 4)))` by
    (Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >> gvs[]
     >- (simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
     `aid <> st.cs_next_id` by decide_tac >>
     metis_tac[allocaSiteResourceTheory.alloca_site_registered_disjoint]) >>
  `window_alloca_sites func (frag_ids st final) = {st.cs_next_id}` by
    metis_tac[abi_encode_word_output_sites] >>
  mp_tac (Q.INST [`cap` |-> `32`] (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
    lower_abi_encode_word_window_mem_growth))) >>
  (impl_tac >- simp[abiEncoderAdmissibleTheory.abi_encoder_admissible_def]) >>
  strip_tac >>
  `wb_frame ce ee st s t` by
    (drule_all abi_encode_word_output_sites >>
     disch_then (qspec_then `ee.scopes` strip_assume_tac) >>
     irule abi_encode_singleton_wb_frame >>
     qpat_assum `MEM inst _` (irule_at Any) >>
     qexistsl [`q`, `final`, `cx`, `ctx`] >>
     asm_rewrite_tac[] >> irule abi_encode_word_registered_phase >>
     metis_tac[]) >>
  qexistsl [`t`, `p`] >> asm_rewrite_tac[] >>
  irule abi_encode_word_output_state >>
  qpat_assum `lower_abi_encode _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `window_phase _ _ _ _ _ _ _ _` (irule_at Any) >> simp[]
QED

Theorem abi_encode_word_execution_mem[local]:
  let maxlen = abi_size_bound ce.ce_struct_fields (expr_type e) in
  let mid = OPTION_MAP bytes_method_id_word method_id in
  let capacity = maxlen+(case mid of NONE => 0 | SOME _ => 4) in
  let bytes = (case mid of NONE => enc at av
    | SOME m => abi_builtin_encode_method_bytes m ++ enc at av) in
  is_word_type (expr_type e) /\
  lower_value cfn ce (expr_type e) e origin = (value_op,arg_st) /\
  compile_type_builtin_dispatch_body cfn ce vv_ty ty
    (AbiEncode F method_id) ret_ty [e] origin = (vv,final) /\
  fn_has_code arg_st final func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx ee s /\ local_ptrs_reserved ce arg_st /\
  eval_operand value_op s = SOME w /\
  (!x. value_op = Var x ==> not_fresh_at arg_st x) /\
  has_type at av /\ ~is_dynamic at /\ static_length at = 32 /\
  word_to_bytes w T = enc at av /\ LENGTH (enc at av) <= maxlen /\
  32+32*word_size capacity < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = arg_st.cs_current_bb /\
  s.vs_inst_idx = LENGTH arg_st.cs_current_insts ==>
  ?t p staged out. mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t /\
    stmt_state_rel ctx func ce cx ee t /\ wb_frame ce ee arg_st s t /\
    ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\
    vv = LocatedValue vv_ty (mk_ptr out LocMemory) /\
    eval_operand out t = SOME (n2w p) /\
    FLOOKUP t.vs_allocas staged.cs_next_id = SOME (p,32+32*word_size capacity) /\
    arg_st.cs_next_id <= staged.cs_next_id /\ staged.cs_next_id < final.cs_next_id /\
    p+(32+32*word_size capacity) <= t.vs_alloca_next /\
    p+(32+32*word_size capacity) < dimword (:256) /\
    val_in_memory (BaseTV (BytesT (Dynamic capacity))) (vyperValue$BytesV bytes) p t.vs_memory /\
    (!name b sz. local_region ce ee.scopes t name b sz ==>
      p+(32+32*word_size capacity) <= b \/ b+sz <= p)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_encode_word_source_state_mem >> strip_tac >>
  rename1 `window_phase ctx func arg_st staged _ _ s u` >>
  drule_all abi_builtin_encode_word_context >> strip_tac >>
  `type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e) = AbiCopy 32` by
    metis_tac[abi_builtin_encode_word_info] >>
  `~u.vs_halted /\ u.vs_current_bb = staged.cs_current_bb /\
    u.vs_inst_idx = LENGTH staged.cs_current_insts` by
    metis_tac[window_phase_control] >>
  `arg_st.cs_next_id < staged.cs_next_id` by decide_tac >>
  qpat_assum `type_to_abi_enc_info _ _ _ = AbiCopy 32`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  drule_all (BETA_RULE (PURE_REWRITE_RULE [LET_THM] abi_encode_word_output_mem)) >>
  strip_tac >>
  `wb_frame ce ee arg_st s t` by
    (irule wb_frame_trans >>
     qpat_assum `wb_frame ce ee staged u t` (irule_at Any) >>
     qpat_assum `stmt_state_rel ctx func ce cx ee s` (irule_at Any) >>
     asm_rewrite_tac[] >> simp_tac arith_ss []) >>
  `~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts` by metis_tac[window_phase_control] >>
  `staged.cs_next_id < final.cs_next_id` by
    (drule lower_abi_encode_trace >> strip_tac >>
     drule abi_builtin_encode_setup_shape >> strip_tac >>
     drule abi_builtin_encode_finish_shape >> strip_tac >>
     drule abi_encoder_counters >> strip_tac >> decide_tac) >>
  qexistsl [`t`, `p`, `staged`, `out`] >> asm_rewrite_tac[] >>
  conj_tac >- metis_tac[memContinuationTheory.mem_cont_sim_trans] >>
  conj_tac >- metis_tac[window_mem_frame_trans] >> decide_tac
QED

Theorem abi_encode_word_result_mem:
  let E = TypeBuiltin ann (AbiEncode F mid) typ [e] in
  let maxlen = abi_size_bound ce.ce_struct_fields (expr_type e) in
  let bytes = (case mid of NONE => enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av
    | SOME m => abi_builtin_encode_method_bytes (bytes_method_id_word m) ++
      enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av) in
  let capacity = maxlen+(case mid of NONE => 0 | SOME _ => 4) in
  is_word_type (expr_type e) /\ expr_body_pre ce cx env e es /\
  lower_value compile_expr ce (expr_type e) e origin = (value_op,arg_st) /\
  compile_type_builtin_dispatch_body compile_expr ce (expr_type E) ty
    (AbiEncode F mid) typ [e] origin = (vv,final) /\
  fn_has_code origin final func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce origin /\
  local_ptrs_reserved ce arg_st /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  expr_post ctx func ce cx e es origin arg_st s0 ee v value_op s /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
  expr_type E = BaseT (BytesT (Dynamic declared)) /\
  evaluate_type (get_tenv cx) (expr_type E) = SOME (BaseTV (BytesT (Dynamic declared))) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce E) = SOME (BaseTV (BytesT (Dynamic capacity))) /\
  val_wf (BaseTV (BytesT (Dynamic declared))) (vyperValue$BytesV bytes) /\
  LENGTH (enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av) <= maxlen /\
  32+32*word_size capacity < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = arg_st.cs_current_bb /\
  s.vs_inst_idx = LENGTH arg_st.cs_current_insts ==>
  ?t. mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t /\
    stmt_state_rel ctx func ce cx ee t /\ wb_frame ce es origin s0 t /\
    ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\
    vv_post ctx func ce cx E es origin final s0 ee (Value (vyperValue$BytesV bytes)) vv t /\
    vv_store_bound cx (expr_type E) (lowered_value_type ce E) ee
      (Value (vyperValue$BytesV bytes)) vv t
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `stmt_state_rel ctx func ce cx ee s /\ expr_val_rel cx (expr_type e) v value_op s` by
    fs[expr_post_def] >>
  drule_all abi_encode_word_source_rep >> strip_tac >>
  `fn_has_code arg_st final func` by
    (drule_all compile_abi_encode_word_trace >> strip_tac >>
     drule compile_alloc_buffer_extends >> strip_tac >>
     drule window_child_void_shape >> strip_tac >>
     drule lower_abi_encode_extends >> strip_tac >>
     `cs_extends arg_st final` by metis_tac[cs_extends_trans] >>
     metis_tac[fn_has_code_split]) >>
  qpat_assum `enc at rv = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th]) >>
      pure_rewrite_tac[GSYM th]) >>
  drule_at (Pat `compile_type_builtin_dispatch_body _ _ _ _ _ _ _ _ = _`)
    (BETA_RULE (PURE_REWRITE_RULE [LET_THM] abi_encode_word_execution_mem)) >>
  disch_then assume_tac >> Cases_on `mid` >> fs[] >>
  qpat_x_assum `!w value_op s' func ee cx ctx av at arg_st. _` drule_all >>
  strip_tac >>
  `wb_frame ce es origin s0 s` by metis_tac[expr_post_frame] >>
  `wb_frame ce es origin s0 t` by
    (irule wb_frame_trans >>
     qpat_assum `wb_frame ce ee arg_st s t` (irule_at Any) >>
     qpat_assum `stmt_state_rel ctx func ce cx es s0` (irule_at Any) >>
     asm_rewrite_tac[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  qpat_assum `expr_type (TypeBuiltin _ _ _ _) = _`
    (fn th => pure_rewrite_tac[GSYM th]) >>
  irule abi_encode_allocated_bytes_result >>
  asm_rewrite_tac[] >>
  qpat_assum `FLOOKUP t.vs_allocas staged.cs_next_id = _` (irule_at Any) >>
  simp[] >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  fs[val_in_memory_def]
QED
