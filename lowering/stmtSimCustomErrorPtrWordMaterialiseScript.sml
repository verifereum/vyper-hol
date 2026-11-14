Theory stmtSimCustomErrorPtrWordMaterialise
Ancestors
  bodyPtrDefs exprSimPtrTopLevelForce exprSimPtrProps exprSimUnwrap
  exprSimUnwrapProps exprLoweringProps loweringPosts context compileEnv
  ptrDiscipline emitHelper emitHelperProps freshWrites venomState
  venomExecSemantics finite_map loweringStateRelDefs fragGasPathPtr
  accountsRelProps valueEncodingProps representationCleanPtr exprSimProps pred_set valueCopyBytes words exprLowering venomInst

(* A forced load changes only a fresh SSA destination.  Keep the physical
   frame explicit, so the caller can transport its tuple buffer and ADD. *)
Theorem custom_error_load_post[local]:
  vv_post ctx func ce cx e es sa sm s0 ee (Value v) (LocatedValue ty p) s /\
  is_word_type (post_value_type ce e) /\ sa.cs_next_var <= sm.cs_next_var /\
  local_ptrs_reserved ce sm /\
  out = STRING #"%" (toString sm.cs_next_var) /\
  (!x. not_fresh_at sm x ==> x <> out) /\
  (!tv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv ==>
        w = typed_val_to_w256 tv v) /\
  u = (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) ==>
  expr_post ctx func ce cx e es sa sb s0 ee v (Var out) u /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
  u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  `stmt_state_rel ctx func ce cx ee u` by
    (simp[] >> rewrite_tac[stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_update_var >> conj_tac
     >- (simp[] >> irule local_ptrs_reserved_fresh >> qexists_tac `sm` >> simp[]) >>
     gvs[vv_post_def]) >>
  `!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >> gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas` by
    simp[update_var_def] >>
  conj_tac
  >- (irule expr_post_of_vv_post_load_physical >>
      simp[] >> conj_tac
      >- (qexists_tac `w` >> simp[eval_operand_def, lookup_var_def,
                                update_var_def, FLOOKUP_UPDATE]) >>
      qexistsl_tac [`p`, `s`, `sm`, `ty`] >> simp[] >> metis_tac[]) >>
  simp[]
QED

Theorem custom_error_word_source_taint[local]:
  ptr_vv_ok cx t raw (LocatedValue ann p) es G tn s /\
  is_word_type t /\ evaluate_type (get_tenv cx) t = SOME tv /\
  eval_operand p.ptr_operand s = SOME w /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
  key_taint (if p.ptr_location = LocTransient then tn.t_trans else tn.t_stor) w = {}
Proof
  strip_tac >>
  `type_slot_size tv = 1` by metis_tac[word_type_slot_size] >>
  gvs[ptr_vv_ok_def, key_taint_def, EXTENSION] >>
  rpt strip_tac >> spose_not_then strip_assume_tac >>
  qpat_x_assum `!k b. _` (qspecl_then [`w`, `x`] mp_tac) >>
  simp[] >> metis_tac[toplevel_word_dead_bytes]
QED

Theorem custom_error_word_load_path[local]:
  unwrap_value ce (LocatedValue ty p) sm = (op,sb) /\
  is_word_type ty /\ ~ce.ce_is_ctor /\
  vv_post ctx func ce cx e es sa sm s0 ee (Value v) (LocatedValue ty p) s /\
  ptr_vv_ok cx (post_value_type ce e) raw (LocatedValue ty p) ee G tn s /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
  value_has_type tv v /\
  fn_has_code sm sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  !D PG. ?out G' tn'.
    op = Var out /\ out = STRING #"%" (toString sm.cs_next_var) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn'
      (OK (update_var out (typed_val_to_w256 tv v) s with
             vs_inst_idx := SUC s.vs_inst_idx)) /\
    op_taint tn' (Var out) = {} /\ op_prov G' (Var out) = NONE /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sm x ==> x <> out) /\
    (!x. x <> out ==> FLOOKUP G' x = FLOOKUP G x /\
                     op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> rpt gen_tac >>
  `ty = post_value_type ce e /\
   ?w. eval_operand p.ptr_operand s = SOME w` by
    (gvs[vv_post_def, vv_holds_def] >>
     metis_tac[is_bytestring_word_type]) >> gvs[] >>
  Cases_on `p.ptr_location`
  >- suspend "memory"
  >- suspend "storage"
  >- suspend "transient"
  >- suspend "code" >>
  gvs[vv_post_def, vv_holds_def]
QED

Resume custom_error_word_load_path[storage]:
  `storage_holds cx F (post_value_type ce e) (Value v) w ee s` by
    gvs[vv_post_def, vv_holds_def] >>
  `sload w s = typed_val_to_w256 tv v` by
    metis_tac[storage_holds_load] >>
  `key_taint tn.t_stor w = {}` by
    (drule custom_error_word_source_taint >> simp[]) >>
  `emit_op SLOAD [p.ptr_operand] sm = (op,sb)` by
    gvs[unwrap_value_def, compile_ptr_load_def] >>
  `step_inst_base (mk_inst sm.cs_next_id SLOAD [p.ptr_operand]
     [STRING #"%" (toString sm.cs_next_var)]) s =
   OK (update_var (STRING #"%" (toString sm.cs_next_var))
         (typed_val_to_w256 tv v) s)` by
    simp[step_inst_base_def, exec_read1_def, mk_inst_def] >>
  `op_taint tn p.ptr_operand = {}` by gvs[ptr_vv_ok_def] >>
  `MEM SLOAD [SLOAD; TLOAD; DLOAD] /\
   MEM TLOAD [SLOAD; TLOAD; DLOAD] /\ MEM DLOAD [SLOAD; TLOAD; DLOAD]` by simp[] >>
  drule_all toplevel_emit_load_path >>
  disch_then (qspecl_then [`G`, `D`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> gvs[]
QED

Resume custom_error_word_load_path[transient]:
  `storage_holds cx T (post_value_type ce e) (Value v) w ee s` by
    gvs[vv_post_def, vv_holds_def] >>
  `tload w s = typed_val_to_w256 tv v` by
    metis_tac[storage_holds_load] >>
  `key_taint tn.t_trans w = {}` by
    (drule custom_error_word_source_taint >> simp[]) >>
  `emit_op TLOAD [p.ptr_operand] sm = (op,sb)` by
    gvs[unwrap_value_def, compile_ptr_load_def] >>
  `step_inst_base (mk_inst sm.cs_next_id TLOAD [p.ptr_operand]
     [STRING #"%" (toString sm.cs_next_var)]) s =
   OK (update_var (STRING #"%" (toString sm.cs_next_var))
         (typed_val_to_w256 tv v) s)` by
    simp[step_inst_base_def, exec_read1_def, mk_inst_def] >>
  `op_taint tn p.ptr_operand = {}` by gvs[ptr_vv_ok_def] >>
  `MEM SLOAD [SLOAD; TLOAD; DLOAD] /\
   MEM TLOAD [SLOAD; TLOAD; DLOAD] /\ MEM DLOAD [SLOAD; TLOAD; DLOAD]` by simp[] >>
  drule_all toplevel_emit_load_path >>
  disch_then (qspecl_then [`G`, `D`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> gvs[]
QED

Resume custom_error_word_load_path[code]:
  `immutable_holds ce cx (post_value_type ce e) (Value v) w ee s /\
   stmt_state_rel ctx func ce cx ee s` by gvs[vv_post_def, vv_holds_def] >>
  `word_of_bytes T (0w:bytes32)
     (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w)) =
   typed_val_to_w256 tv v` by
    (drule_all immutable_holds_dload >> simp[]) >>
  `emit_op DLOAD [p.ptr_operand] sm = (op,sb)` by
    gvs[unwrap_value_def, compile_ptr_load_def, compile_imm_load_word_def] >>
  `step_inst_base (mk_inst sm.cs_next_id DLOAD [p.ptr_operand]
     [STRING #"%" (toString sm.cs_next_var)]) s =
   OK (update_var (STRING #"%" (toString sm.cs_next_var))
         (typed_val_to_w256 tv v) s)` by
    (drule step_DLOAD >> simp[]) >>
  `op_taint tn p.ptr_operand = {}` by gvs[ptr_vv_ok_def] >>
  `MEM SLOAD [SLOAD; TLOAD; DLOAD] /\
   MEM TLOAD [SLOAD; TLOAD; DLOAD] /\ MEM DLOAD [SLOAD; TLOAD; DLOAD]` by simp[] >>
  drule_all toplevel_emit_load_path >>
  disch_then (qspecl_then [`G`, `D`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> gvs[]
QED

Resume custom_error_word_load_path[memory]:
  `ptr_mem_ok cx (post_value_type ce e) v p.ptr_operand G tn s` by
    gvs[ptr_vv_ok_def] >>
  `type_memory_size tv = 32` by metis_tac[word_tv_memory_size] >>
  `32 <= val_footprint tv v /\ 32 <= val_store_size tv v` by
    (Cases_on `v` >> simp[val_footprint_def, val_store_size_def] >>
     Cases_on `tv` >> simp[] >> rename1 `BaseTV bt` >>
     Cases_on `bt` >> simp[] >> rename1 `BytesT bd` >>
     Cases_on `bd` >> simp[]) >>
  `?src b cap. p.ptr_operand = Var src /\ FLOOKUP G src = SOME (b,cap) /\
              b <= w2n w /\ w2n w + 32 <= b + cap` by
    (gvs[ptr_mem_ok_def] >> first_x_assum drule_all >> strip_tac >>
     gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
                       arithmeticTheory.LESS_EQ_LESS_EQ_MONO]) >>
  `ptr_covers G tn src s 32 /\ lookup_var src s = SOME w` by
    gvs[ptr_covers_def, ptr_vv_ok_def, eval_operand_def] >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     mem_word_at (w2n w) mem = typed_val_to_w256 tv v` by
    metis_tac[ptr_mem_ok_def, exprSimPropsTheory.val_in_memory_word] >>
  `!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem` by
    (drule robust_mem_word_at_clean >> simp[]) >>
  `mload (w2n w) s = typed_val_to_w256 tv v` by
    gvs[vv_post_def, vv_holds_def, vyperStateTheory.read_result_def,
        vyperStateTheory.return_def, mem_word_at_eq_mload] >>
  `emit_op MLOAD [Var src] sm = (op,sb)` by
    gvs[unwrap_value_def, compile_ptr_load_def] >>
  drule_all emit_mload_ptr_path >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> gvs[]
QED

Finalise custom_error_word_load_path

Theorem custom_error_word_unwrap_ptr:
  unwrap_value ce (LocatedValue ty p) sm = (op,sb) /\
  is_word_type ty /\ ~ce.ce_is_ctor /\
  vv_post ctx func ce cx e es sa sm s0 ee raw (LocatedValue ty p) s /\
  ptr_vv_ok cx (post_value_type ce e) raw (LocatedValue ty p) ee G tn s /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
  value_has_type tv v /\
  local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
  ghost_inv d ce cx ee G tn s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  fn_has_code sm sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  !D PG. ?G' tn' u.
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK u) /\
    expr_post ctx func ce cx e es sa sb s0 ee v op u /\
    ptr_val_ok cx (post_value_type ce e) v op G' tn' u /\
    ghost_inv d ce cx ee G' tn' u /\ ghost_kept ce ee sm G tn s G' tn' /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sm x ==>
         lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> rpt gen_tac >>
  `vv_post ctx func ce cx e es sa sm s0 ee (Value v) (LocatedValue ty p) s` by
    metis_tac[vv_post_read_result] >>
  `ty = post_value_type ce e` by
    (gvs[vv_post_def, vv_holds_def] >> metis_tac[is_bytestring_word_type]) >>
  drule_all custom_error_word_load_path >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qabbrev_tac `u = update_var out (typed_val_to_w256 tv v) s with
                    vs_inst_idx := SUC s.vs_inst_idx` >>
  `expr_post ctx func ce cx e es sa sb s0 ee v (Var out) u /\
   (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
   u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas` by
    (irule custom_error_load_post >> simp[Abbr `u`] >> metis_tac[]) >>
  `ghost_inv d ce cx ee G' tn' u /\ ghost_kept ce ee sm G tn s G' tn'` by
    (irule toplevel_load_ghost_post >> simp[Abbr `u`] >> metis_tac[]) >>
  `u.vs_current_bb = sb.cs_current_bb /\
   u.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     Cases_on `p.ptr_location` >>
     simp[unwrap_value_def, compile_ptr_load_def, compile_imm_load_word_def,
          emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
          fresh_id_def, emit_def, comp_return_def] >> strip_tac >>
     gvs[Abbr `u`, update_var_def]) >>
  qexistsl_tac [`G'`, `tn'`, `u`] >>
  gvs[ptr_val_ok_def, Abbr `u`, update_var_def] >> metis_tac[]
QED
