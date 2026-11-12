(* unwrap_value's word loads on one joint path: one MLOAD, SLOAD, TLOAD or
   DLOAD, or the constructor's immutable load from memory. *)
Theory bodyFullUnwrapWord
Ancestors
  bodyFullUnwrapRun exprPtrCtorImmStore bodyFieldMemoryProps
  exprPtrUnwrapLoadSegment slotCopyExecution instMemFrontier fragExecMem
  exprPtrUnwrapCode exprPtrCodeCopySegments bodyImmutableUnwrapMemory
  immutableCopyExecution memSafeRun
  exprPtrUnwrapMarked exprSimMemUnwrap fragGasOriginPtr fragGasSeqPtr
  bodyPtrEnvBuiltinsEdges bodyPtrDefs loweringPosts exprSimMemDefs
  exprSimAggregateChildren exprPtrCtorCodeLoad exprSimUnwrap exprSimUnwrapProps representationCleanPtr
  assignTuplePtrLoadStep stateFrame exprSimProps exprSimCopy
  exprLowering compileEnv context emitHelperProps venomState finite_map
  exprPtrUnwrapLoad exprPtrUnwrapStorage emitHelper venomExecSemantics
  venomInst freshWrites exprLoweringProps ptrDiscipline
  arithmetic list rich_list pred_set

(* A memory word is forced by one MLOAD. *)
Theorem unwrap_memory_word_origin_ptr:
  vv = LocatedValue t p /\ p.ptr_location = LocMemory /\ is_word_type t /\
  compile_expr cenv ty e sa = (vv,sm) /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ dead_lo_ok D lo cenv cx /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
    ~is_word_type (post_value_type cenv e) ==>
    type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  vv_post ctx func cenv cx e es sa sb s0 ee tv vv s /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ghost_inv_at D lo d cenv cx ee G tn s /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val, ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) s = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v H tf z.
    read_result cx tv ee = (INL v, ee) /\
    gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
      (s, G, tn) [] (OK z, H, tf) /\
    expr_post ctx func cenv cx e es sa sc s0 ee v op z /\
    expr_store_bound cx (post_value_type cenv e) v op z /\
    z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ghost_inv_at D lo d cenv cx ee H tf z /\
    ptr_val_ok cx (post_value_type cenv e) v op H tf z /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op H z) /\
    (~is_word_type (post_value_type cenv e) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op z = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 H tf /\
    (!x. not_fresh_at sb x ==>
         lookup_var x z = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
         op_taint tf (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee sb s z /\
    ghost_kept_at lo cenv ee sb G tn s H tf
Proof
  strip_tac >> qpat_x_assum `vv = _` SUBST_ALL_TAC >>
  `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty` by
    simp[] >>
  drule_all unwrap_memory_word_input >> strip_tac >>
  `emit_op MLOAD [Var src] sb = (op,sc)` by
    gvs[unwrap_value_def, compile_ptr_load_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sc.cs_current_bb = sb.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  qabbrev_tac `out = STRING #"%" (toString sb.cs_next_var)` >>
  qabbrev_tac `inst = mk_inst sb.cs_next_id MLOAD [Var src] [out]` >>
  qabbrev_tac `u = update_var out (mload (w2n w) s) s` >>
  `run_inst_seq [inst] s = OK u` by
    simp[run_inst_seq_def, Abbr `inst`, Abbr `u`, step_inst_base_opcode_eqs,
         mk_inst_def, exec_read1_def, eval_operand_def] >>
  `!q. not_fresh_at sb q ==> q <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `!q. not_fresh_at sa q ==> not_fresh_at sb q` by
    metis_tac[not_fresh_at_mono] >>
  `allocas_from lo s` by fs[ghost_inv_at_def] >>
  qspecl_then [`not_fresh_at sb`, `u`, `out`, `sb.cs_next_id`, `func`, `src`]
    mp_tac (Q.GENL [`P`, `t`, `out`, `id`, `fn`, `p`] ctor_mload_segment) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  `inst_seq_ptr D lo ctx func PG G tn [inst] s Gf tnf` by
    (first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >>
     `s with vs_inst_idx := s.vs_inst_idx = s` by
       simp[venom_state_component_equality] >>
     simp[]) >>
  `w2n w + 32 <= s.vs_alloca_next` by
    (`val_store_size rty v = 32` by metis_tac[word_val_store_size] >>
     fs[vv_store_bound_def] >>
     first_x_assum (qspecl_then [`t`, `Var src`, `v`, `rty`, `w`] mp_tac) >>
     simp[]) >>
  `run_inst_seq_mem_ok [inst] s` by
    metis_tac[body_word_load_prefix_mem_ok] >>
  qspecl_then [`[inst]`, `sb`, `sc`, `s`, `u`, `G`, `tn`, `Gf`, `tnf`]
    mp_tac emitted_origin_ptr_path >>
  impl_tac
  >- simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
  strip_tac >>
  `alloca_inv s` by fs[vv_post_def, stmt_state_rel_def] >>
  `alloca_history func (u with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    metis_tac[body_word_load_history] >>
  `expr_post ctx func cenv cx e es sa sc s0 ee v op
     (u with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    (drule unwrap_mload_post >>
     disch_then (qspecl_then [`w`, `v`, `sc`, `op`] mp_tac) >>
     simp[Abbr `u`, Abbr `out`, ADD1]) >>
  `mem_word_taint tn.t_mem (w2n w) = {}` by
    (simp[mem_word_taint_def, EXTENSION] >> rpt strip_tac >>
     CCONTR_TAC >> fs[] >>
     first_x_assum (qspec_then `w2n w + x` mp_tac) >> simp[]) >>
  qexistsl [`v`, `Gf`, `tnf`, `u with vs_inst_idx := LENGTH sc.cs_current_insts`] >>
  simp[expr_store_bound_word] >>
  rpt conj_tac
  >- simp[Abbr `u`, update_var_def]
  >- simp[Abbr `u`, update_var_def]
  >- (irule ghost_inv_at_register_transport >>
      qexistsl [`G`, `s`, `sa`, `tn`] >>
      simp[Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> res_tac >> res_tac >> simp[])
  >- (irule ptr_val_ok_word >> simp[])
  >- (irule ghost_kept_at_clean_suffix >> simp[] >>
      goal_assum drule >> metis_tac[SUBSET_REFL])
  >- (rpt strip_tac >> res_tac >>
      simp[Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE])
  >- (simp[wb_frame_def, Abbr `u`, update_var_def, locals_kept_mem] >>
      rpt strip_tac >> res_tac >>
      fs[lookup_var_def, FLOOKUP_UPDATE])
  >> irule ghost_kept_at_clean_suffix >>
  qexistsl [`G`, `tn`] >> simp[ghost_kept_at_def] >>
  metis_tac[SUBSET_REFL]
QED

(* A storage or transient word is forced by one SLOAD or TLOAD. *)
Theorem unwrap_slot_word_origin_ptr:
  vv = LocatedValue t p /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  is_word_type t /\
  compile_expr cenv ty e sa = (vv,sm) /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ dead_lo_ok D lo cenv cx /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
    ~is_word_type (post_value_type cenv e) ==>
    type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  vv_post ctx func cenv cx e es sa sb s0 ee tv vv s /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ghost_inv_at D lo d cenv cx ee G tn s /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val, ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) s = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v H tf z.
    read_result cx tv ee = (INL v, ee) /\
    gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
      (s, G, tn) [] (OK z, H, tf) /\
    expr_post ctx func cenv cx e es sa sc s0 ee v op z /\
    expr_store_bound cx (post_value_type cenv e) v op z /\
    z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ghost_inv_at D lo d cenv cx ee H tf z /\
    ptr_val_ok cx (post_value_type cenv e) v op H tf z /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op H z) /\
    (~is_word_type (post_value_type cenv e) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op z = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 H tf /\
    (!x. not_fresh_at sb x ==>
         lookup_var x z = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
         op_taint tf (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee sb s z /\
    ghost_kept_at lo cenv ee sb G tn s H tf
Proof
  strip_tac >> qpat_x_assum `vv = _` SUBST_ALL_TAC >>
  `post_value_type cenv e = expr_type e` by
    (CCONTR_TAC >> drule_all aggregate_unequal_post_result_location >> gvs[]) >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >>
                      REWRITE_TAC [th] >> assume_tac th) >>
  `?tr. p.ptr_location = slot_loc tr` by
    (simp[slot_loc_def] >> metis_tac[]) >>
  `evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty` by
    simp[] >>
  drule_all unwrap_storage_word_input >> strip_tac >>
  `emit_op (if tr then TLOAD else SLOAD) [p.ptr_operand] sb = (op,sc)` by
    (Cases_on `tr` >> gvs[slot_loc_def, unwrap_value_def, compile_ptr_load_def]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sc.cs_current_bb = sb.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  qabbrev_tac `out = STRING #"%" (toString sb.cs_next_var)` >>
  qabbrev_tac `inst = mk_inst sb.cs_next_id (if tr then TLOAD else SLOAD)
                        [p.ptr_operand] [out]` >>
  `!q. not_fresh_at sb q ==> q <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `!q. not_fresh_at sa q ==> not_fresh_at sb q` by
    metis_tac[not_fresh_at_mono] >>
  `allocas_from lo s` by fs[ghost_inv_at_def] >>
  qspecl_then [`if tr then TLOAD else SLOAD`, `p.ptr_operand`, `a`,
               `sb.cs_next_id`, `out`, `func`]
    mp_tac (Q.GENL [`load`, `arg`, `key`, `id`, `out`, `fn`]
              copy_slot_load_segment) >>
  impl_tac >- (Cases_on `tr` >> simp[]) >>
  strip_tac >> rename1 `run_inst_seq _ s = OK u` >>
  `step_inst_base inst s = OK u` by
    (qpat_x_assum `run_inst_seq _ s = OK u` mp_tac >>
     simp[run_inst_seq_def, Abbr `inst`] >> CASE_TAC >> simp[]) >>
  `Gf = step_prov PG G inst u /\ tnf = step_taint inst s u tn` by
    (qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[inst_seq_ptr_def, Abbr `inst`]) >>
  `slot_copy_word (if tr then TLOAD else SLOAD) s a =
     if tr then tload a s else sload a s` by
    (Cases_on `tr` >> simp[slot_copy_word_def]) >>
  `run_inst_seq_mem_ok [inst] s` by
    (simp[run_inst_seq_mem_ok_last, Abbr `inst`] >> conj_tac
     >- (irule below_frontier_no_ranges >> Cases_on `tr` >> simp[mk_inst_def])
     >> Cases_on `tr` >> simp[inst_dload_in_section_def, mk_inst_def]) >>
  qspecl_then [`[inst]`, `sb`, `sc`, `s`, `u`, `G`, `tn`, `Gf`, `tnf`]
    mp_tac emitted_origin_ptr_path >>
  impl_tac
  >- (simp[Abbr `inst`, mk_inst_def] >> Cases_on `tr` >>
      simp[is_terminator_def]) >>
  strip_tac >>
  `alloca_inv s` by fs[vv_post_def, stmt_state_rel_def] >>
  `alloca_history func (u with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    (qspecl_then [`[inst]`, `sb`, `sc`, `s`, `u`] mp_tac
       emitted_alloca_history >>
     simp[Abbr `inst`, mk_inst_def] >> Cases_on `tr` >>
     simp[is_terminator_def]) >>
  `expr_post ctx func cenv cx e es sa sc s0 ee v op
     (u with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    (drule unwrap_storage_word_post >>
     disch_then (qspecl_then [`v`, `tr`, `sc`, `op`, `a`] mp_tac) >>
     simp[Abbr `out`, ADD1]) >>
  qexistsl [`v`, `Gf`, `tnf`, `u with vs_inst_idx := LENGTH sc.cs_current_insts`] >>
  simp[expr_store_bound_word] >>
  rpt conj_tac
  >- simp[update_var_def]
  >- simp[update_var_def]
  >- (irule ghost_inv_at_register_transport >>
      qexistsl [`G`, `s`, `sa`, `tn`] >>
      simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> res_tac >> simp[])
  >- (irule ptr_val_ok_word >> simp[] >> conj_tac
      >- (Cases_on `tr` >> fs[])
      >> irule step_prov_out_none >>
      simp[Abbr `inst`, mk_inst_def] >>
      irule out_prov_other_none >> Cases_on `tr` >> simp[mk_inst_def])
  >- (irule ghost_kept_at_clean_suffix >> simp[] >>
      goal_assum drule >> metis_tac[SUBSET_REFL])
  >- (rpt strip_tac >> res_tac >>
      simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE])
  >- (simp[wb_frame_def, update_var_def, locals_kept_mem] >>
      rpt strip_tac >> res_tac >>
      fs[lookup_var_def, FLOOKUP_UPDATE])
  >> irule ghost_kept_at_clean_suffix >>
  qexistsl [`G`, `tn`] >> simp[ghost_kept_at_def] >>
  metis_tac[SUBSET_REFL]
QED

(* The constructor's word load binds only its fresh outputs. *)
Theorem ctor_load_word_shape[local]:
  compile_imm_load_word T imm arg sa = (op,sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
             ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  Cases_on `imm` >> strip_tac
  >- (gvs[compile_imm_load_word_def] >> drule emitted_insts_emit_op >>
      strip_tac >>
      gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
          comp_ignore_bind_def, comp_return_def, emit_def, mk_inst_def,
          is_terminator_def]) >>
  drule compile_imm_load_word_ctor_result >> strip_tac >>
  simp[emitted_insts_def, DROP_APPEND, mk_inst_def, is_terminator_def] >>
  gvs[compile_imm_load_word_def, emit_op_def, comp_bind_def, fresh_var_def,
      fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def]
QED

Theorem ctor_load_word_frame[local]:
  compile_imm_load_word T imm arg sa = (op,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  state_frame t = state_frame s
Proof
  Cases_on `imm` >> strip_tac
  >- (gvs[compile_imm_load_word_def] >> drule emitted_insts_emit_op >>
      strip_tac >>
      gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
          exec_read1_def, AllCaseEqs(), update_var_def, state_frame_def]) >>
  drule compile_imm_load_word_ctor_result >> strip_tac >>
  gvs[emitted_insts_def, DROP_APPEND, run_inst_seq_def,
      step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def, exec_pure2_def,
      AllCaseEqs(), update_var_def, state_frame_def]
QED

(* An immutable word is forced by DLOAD, or in a constructor by ILOAD. *)
Theorem unwrap_code_word_origin_ptr:
  vv = LocatedValue t p /\ p.ptr_location = LocCode /\ is_word_type t /\
  compile_expr cenv ty e sa = (vv,sm) /\
  unwrap_value cenv vv sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ dead_lo_ok D lo cenv cx /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
    ~is_word_type (post_value_type cenv e) ==>
    type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  vv_post ctx func cenv cx e es sa sb s0 ee tv vv s /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ghost_inv_at D lo d cenv cx ee G tn s /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val, ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                eval_operand (vv_operand vv) s = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                       val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v H tf z.
    read_result cx tv ee = (INL v, ee) /\
    gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
      (s, G, tn) [] (OK z, H, tf) /\
    expr_post ctx func cenv cx e es sa sc s0 ee v op z /\
    expr_store_bound cx (post_value_type cenv e) v op z /\
    z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ghost_inv_at D lo d cenv cx ee H tf z /\
    ptr_val_ok cx (post_value_type cenv e) v op H tf z /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op H z) /\
    (~is_word_type (post_value_type cenv e) ==>
     !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op z = SOME w ==>
            type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 H tf /\
    (!x. not_fresh_at sb x ==>
         lookup_var x z = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
         op_taint tf (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee sb s z /\
    ghost_kept_at lo cenv ee sb G tn s H tf
Proof
  strip_tac >> qpat_x_assum `vv = _` SUBST_ALL_TAC >>
  `post_value_type cenv e = expr_type e` by
    (CCONTR_TAC >> drule_all aggregate_unequal_post_result_location >> gvs[]) >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >>
                      REWRITE_TAC [th] >> assume_tac th) >>
  reverse (Cases_on `cenv.ce_is_ctor`) >- suspend "runtime" >>
  drule_all vv_post_code_source >> strip_tac >>
  `stmt_state_rel ctx func cenv cx ee s` by fs[vv_post_def] >>
  `compile_imm_load_word T cenv.ce_imm_alloca p.ptr_operand sb = (op,sc)` by
    gvs[unwrap_value_def, compile_ptr_load_def] >>
  `op_taint tn p.ptr_operand = {} /\ op_prov G p.ptr_operand = NONE` by
    fs[ptr_vv_ok_def] >>
  `is_word_type (expr_type e)` by metis_tac[] >>
  `type_memory_size rty = 32` by metis_tac[word_tv_memory_size] >>
  `w2n a + 32 <= lo /\
   !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory rty v (w2n a) mem` by
    (qpat_x_assum `cenv.ce_is_ctor /\ _ ==> _` mp_tac >>
     simp[vv_location_def, vv_operand_def] >> strip_tac >> gvs[] >>
     first_x_assum (qspecl_then [`rty`, `a`] mp_tac) >> simp[]) >>
  `mem_word_taint tn.t_mem (w2n a) = {}` by
    (`!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
            mem_word_at (w2n a) mem = typed_val_to_w256 rty v` by
       metis_tac[val_in_memory_word_type] >>
     drule robust_mem_word_at_clean >> strip_tac >>
     simp[mem_word_taint_def, EXTENSION] >> rpt strip_tac >>
     CCONTR_TAC >> fs[] >>
     first_x_assum (qspec_then `w2n a + x` mp_tac) >> simp[]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `!region. cenv.ce_imm_alloca = SOME region ==>
     eval_operand region s = SOME 0w /\ copy_old_operand sb region /\
     op_taint tn region = {} /\ op_prov G region = NONE` by
    (gen_tac >> strip_tac >>
     `immutable_base_zero cenv s` by fs[stmt_state_rel_def] >>
     fs[immutable_base_zero_alt] >> first_x_assum drule >>
     Cases_on `region` >>
     simp[eval_operand_def, lookup_var_def, copy_old_operand_def,
          op_taint_def, op_prov_def] >>
     strip_tac >> conj_tac
     >- metis_tac[local_ptrs_reserved_imm_base] >>
     `lo <> 0` by decide_tac >>
     fs[ghost_inv_at_def, op_taint_def, op_prov_def]) >>
  qspecl_then [`cenv.ce_imm_alloca`, `p.ptr_operand`, `sb`, `op`, `sc`,
               `D`, `lo`, `ctx`, `func`, `PG`, `G`, `tn`, `s`, `a`]
    mp_tac (Q.GENL [`imm`, `arg`, `sa`, `op`, `sb`, `D`, `lo`, `ctx`, `fn`,
                    `PG`, `G`, `tn`, `s`, `a`] code_copy_ctor_load) >>
  impl_tac >- fs[copy_old_operand_def, vv_operand_def] >>
  strip_tac >> rename1 `copy_runtime_frame sb s sc u` >>
  `run_inst_seq (emitted_insts sb sc) s = OK u /\
   sc.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb sc /\
   (!x. not_fresh_at sb x ==> lookup_var x u = lookup_var x s)` by
    fs[copy_runtime_frame_def] >>
  drule ctor_load_word_shape >> strip_tac >>
  `state_frame u = state_frame s` by metis_tac[ctor_load_word_frame] >>
  `u.vs_memory = s.vs_memory /\ u.vs_current_bb = s.vs_current_bb /\
   u.vs_halted = s.vs_halted /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next /\ u.vs_call_ctx = s.vs_call_ctx /\
   u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
   u.vs_immutables = s.vs_immutables` by
    fs[state_frame_def, venom_state_component_equality] >>
  `!q. not_fresh_at sa q ==> not_fresh_at sb q` by
    metis_tac[not_fresh_at_mono] >>
  `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sb sc) s Gf tnf` by
    (first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >>
     `s with vs_inst_idx := s.vs_inst_idx = s` by
       simp[venom_state_component_equality] >>
     simp[]) >>
  `w2n a + 32 <= s.vs_alloca_next` by decide_tac >>
  `run_inst_seq_mem_ok (emitted_insts sb sc) s` by
    metis_tac[body_ctor_load_mem_ok] >>
  qspecl_then [`emitted_insts sb sc`, `sb`, `sc`, `s`, `u`, `G`, `tn`,
               `Gf`, `tnf`] mp_tac emitted_origin_ptr_path >>
  impl_tac >- fs[] >> strip_tac >>
  `alloca_inv s` by fs[vv_post_def, stmt_state_rel_def] >>
  `alloca_history func (u with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    (qspecl_then [`emitted_insts sb sc`, `sb`, `sc`, `s`, `u`] mp_tac
       emitted_alloca_history >>
     fs[EVERY_MEM]) >>
  `!x n. eval_operand x (u with vs_inst_idx := n) = eval_operand x u /\
         lookup_var x (u with vs_inst_idx := n) = lookup_var x u` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  `?tvt. evaluate_type (get_tenv cx) t = SOME tvt /\
         mload (w2n a) s = typed_val_to_w256 tvt v` by
    metis_tac[immutable_holds_iload] >>
  drule vv_post_read_result >>
  disch_then (fn th => qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ tv _ _`
    (assume_tac o REWRITE_RULE [th])) >>
  `stmt_state_rel ctx func cenv cx ee
     (u with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    (irule stmt_state_rel_old_vars_frame_ptr >>
     qexistsl [`s`, `sb`] >>
     fs[state_frame_def, venom_state_component_equality]) >>
  `expr_post ctx func cenv cx e es sa sc s0 ee v op
     (u with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    (qspecl_then [`func`, `cenv`, `cx`, `e`, `es`, `sa`, `sb`, `sc`, `s0`,
                  `ee`, `v`, `t`, `p`, `op`, `s`,
                  `u with vs_inst_idx := LENGTH sc.cs_current_insts`,
                  `mload (w2n a) s`, `ctx`]
       mp_tac expr_post_of_vv_post_load_physical >>
     impl_tac >- gvs[immutable_copy_read_def] >>
     simp[]) >>
  qexistsl [`v`, `Gf`, `tnf`, `u with vs_inst_idx := LENGTH sc.cs_current_insts`] >>
  simp[expr_store_bound_word] >>
  rpt conj_tac
  >~ [`ghost_inv_at`]
  >- (irule ghost_inv_at_register_transport >>
      qexistsl [`G`, `s`, `sa`, `tn`] >> simp[] >> metis_tac[])
  >~ [`ptr_val_ok`] >- (irule ptr_val_ok_word >> simp[])
  >~ [`wb_frame`] >- (simp[wb_frame_def, locals_kept_mem] >> metis_tac[])
  >~ [`ghost_kept_at _ _ _ sa`]
  >- (irule ghost_kept_at_clean_suffix >> simp[] >>
      goal_assum drule >> metis_tac[SUBSET_REFL])
  >~ [`lookup_var`] >- metis_tac[]
  >> irule ghost_kept_at_clean_suffix >>
  qexistsl [`G`, `tn`] >> simp[ghost_kept_at_def] >>
  metis_tac[SUBSET_REFL]
QED

Resume unwrap_code_word_origin_ptr[runtime]:
  drule_all vv_post_code_source >> strip_tac >>
  `stmt_state_rel ctx func cenv cx ee s` by fs[vv_post_def] >>
  `emit_op DLOAD [p.ptr_operand] sb = (op,sc)` by
    gvs[unwrap_value_def, compile_ptr_load_def, compile_imm_load_word_def] >>
  `op_taint tn p.ptr_operand = {}` by fs[ptr_vv_ok_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sc.cs_current_bb = sb.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  qabbrev_tac `out = STRING #"%" (toString sb.cs_next_var)` >>
  qabbrev_tac `inst = mk_inst sb.cs_next_id DLOAD [p.ptr_operand] [out]` >>
  qabbrev_tac `u = update_var out (immutable_copy_read F a s) s` >>
  `run_inst_seq [inst] s = OK u` by
    simp[run_inst_seq_def, Abbr `inst`, Abbr `u`, step_inst_base_opcode_eqs,
         mk_inst_def, exec_read1_def, immutable_copy_read_def] >>
  `!q. not_fresh_at sb q ==> q <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `!q. not_fresh_at sa q ==> not_fresh_at sb q` by
    metis_tac[not_fresh_at_mono] >>
  `allocas_from lo s` by fs[ghost_inv_at_def] >>
  qspecl_then [`not_fresh_at sb`, `u`, `out`, `sb.cs_next_id`, `func`,
               `p.ptr_operand`]
    mp_tac (Q.GENL [`P`, `t`, `out`, `id`, `fn`, `arg`]
              code_copy_load_segment) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  `inst_seq_ptr D lo ctx func PG G tn [inst] s Gf tnf` by
    (first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >>
     `s with vs_inst_idx := s.vs_inst_idx = s` by
       simp[venom_state_component_equality] >>
     simp[]) >>
  `w2n a + type_memory_size rty <= LENGTH s.vs_data_section` by
    (irule runtime_immutable_data_section >> simp[] >> metis_tac[]) >>
  `run_inst_seq_mem_ok [inst] s` by
    (simp[run_inst_seq_mem_ok_last, Abbr `inst`] >> conj_tac
     >- (irule below_frontier_no_ranges >> simp[mk_inst_def])
     >> simp[inst_dload_in_section_def, mk_inst_def]) >>
  qspecl_then [`[inst]`, `sb`, `sc`, `s`, `u`, `G`, `tn`, `Gf`, `tnf`]
    mp_tac emitted_origin_ptr_path >>
  impl_tac
  >- simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
  strip_tac >>
  `alloca_inv s` by fs[vv_post_def, stmt_state_rel_def] >>
  `alloca_history func (u with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    (qspecl_then [`[inst]`, `sb`, `sc`, `s`, `u`] mp_tac
       emitted_alloca_history >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def]) >>
  `expr_post ctx func cenv cx e es sa sc s0 ee v op
     (u with vs_inst_idx := LENGTH sc.cs_current_insts)` by
    (drule unwrap_code_word_post >>
     disch_then (qspecl_then [`v`, `sc`, `op`, `a`] mp_tac) >>
     simp[Abbr `u`, Abbr `out`, ADD1, immutable_copy_read_def]) >>
  qexistsl [`v`, `Gf`, `tnf`, `u with vs_inst_idx := LENGTH sc.cs_current_insts`] >>
  simp[expr_store_bound_word] >>
  rpt conj_tac
  >- simp[Abbr `u`, update_var_def]
  >- simp[Abbr `u`, update_var_def]
  >- (irule ghost_inv_at_register_transport >>
      qexistsl [`G`, `s`, `sa`, `tn`] >>
      simp[Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> res_tac >> res_tac >> simp[])
  >- (irule ptr_val_ok_word >> simp[])
  >- (irule ghost_kept_at_clean_suffix >> simp[] >>
      goal_assum drule >> metis_tac[SUBSET_REFL])
  >- (rpt strip_tac >> res_tac >>
      simp[Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE])
  >- (simp[wb_frame_def, Abbr `u`, update_var_def, locals_kept_mem] >>
      rpt strip_tac >> res_tac >>
      fs[lookup_var_def, FLOOKUP_UPDATE])
  >> irule ghost_kept_at_clean_suffix >>
  qexistsl [`G`, `tn`] >> simp[ghost_kept_at_def] >>
  metis_tac[SUBSET_REFL]
QED

Finalise unwrap_code_word_origin_ptr
