(* Interleaved tuple heads, using the exact store arm of the extcall. *)
Theory exprExtRequestTupleHead
Ancestors
  exprExtRequestTupleStore exprExtRequestMaterialize exprExtRequestHistoryCompose
  exprExtRequestJointUnwrap stmtSimDeclGas
  exprSimHash exprSafeOperand exprLoweringProps emitHelperProps
  exprLowering compileEnv context emitHelper venomState venomInst loweringPosts
  venomInstProofs venomExecSemantics freshWrites gasSummaryCompose
Libs wordsLib

Theorem extrequest_tuple_word_head:
  comp_bind (emit_op ADD [buf; Lit (n2w off)])
    (\dst. comp_bind (unwrap_value cenv (StackValue ty src))
      (\op. emit_void MSTORE [dst;op])) sa = ((),sb) /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\ expr_val_rel cx ty v src s /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  eval_operand buf s = SOME w /\ safe_operand sa src /\
  stmt_state_rel ctx func cenv cx ee s /\ local_ptrs_reserved cenv sa /\
  (!name b sz. local_region cenv ee.scopes s name b sz ==>
    b + sz <= w2n (w + n2w off) \/
    w2n (w + n2w off) + type_memory_size tv <= b) /\
  (cenv.ce_is_ctor ==> !name itv iv io.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv)
      (w2n (w + n2w off)) (type_memory_size tv)) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    stmt_state_rel ctx func cenv cx ee q /\
    (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
    val_in_memory tv v (w2n (w + n2w off)) q.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
    (!a k. a + k <= w2n (w + n2w off) \/
       w2n (w + n2w off) + type_memory_size tv <= a ==>
       mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH q.vs_memory /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  simp[compileEnvTheory.comp_bind_def, exprLoweringTheory.unwrap_value_def,
       compileEnvTheory.comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [buf; Lit (n2w off)] sa = (dst,sn)` >>
  `ci_mono sa sn /\ ci_mono sn sb` by
    (conj_tac
     >- (qspecl_then [`ADD`, `[buf; Lit (n2w off)]`, `sa`] mp_tac ci_mono_emit_op >> simp[]) >>
     qspecl_then [`MSTORE`, `[dst;src]`, `sn`] mp_tac ci_mono_emit_void >> simp[]) >>
  `fn_has_code sa sn func /\ fn_has_code sn sb func` by
    (irule fragExecTheory.fn_has_code_split >> gvs[ci_mono_def]) >>
  qabbrev_tac `u = update_var (STRING #"%" (toString sa.cs_next_var))
    (w + n2w off) s` >>
  `run_inst_seq (emitted_insts sa sn) s = OK u` by
    (simp[Abbr `u`] >> irule buffer_emit_add_run >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    (simp[Abbr `u`, lookup_var_update_var] >> rpt strip_tac >>
     gvs[not_fresh_at_def]) >>
  `eval_operand src u = eval_operand src s` by
    (Cases_on `src` >> gvs[safe_operand_def, eval_operand_def]) >>
  `expr_val_rel cx ty v src u` by
    gvs[expr_val_rel_def] >>
  `eval_operand dst u = SOME (w + n2w off)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     simp[Abbr `u`, eval_operand_def, lookup_var_update_var]) >>
  `local_ptrs_reserved cenv sn` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> gvs[ci_mono_def]) >>
  `!x. src = Var x \/ dst = Var x ==> not_fresh_at sn x` by
    (rpt strip_tac
     >- (gvs[safe_operand_def] >> metis_tac[not_fresh_at_mono, ci_mono_def]) >>
     metis_tac[emit_op_safe_operand, safe_operand_def]) >>
  suspend "store_and_finish"
QED

Resume extrequest_tuple_word_head[store_and_finish]:
  `?q. run_inst_seq (emitted_insts sn sb) u = OK q /\
       val_in_memory tv v (w2n (w + n2w off)) q.vs_memory /\
       (q with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory|>) = u /\
       (!x. not_fresh_at sn x ==> lookup_var x q = lookup_var x u) /\
       (!a k. a + k <= w2n (w + n2w off) \/
          w2n (w + n2w off) + type_memory_size tv <= a ==>
          mem_bytes_at a k q.vs_memory = mem_bytes_at a k u.vs_memory)` by
    (irule extrequest_store_cell_encoding >> simp[] >> metis_tac[]) >>
  `LENGTH u.vs_memory <= LENGTH q.vs_memory` by
    (irule extrequest_store_cell_memory_nondecreasing >> simp[] >> metis_tac[]) >>
  `emitted_insts sa sb = emitted_insts sa sn ++ emitted_insts sn sb` by
    (irule emitted_insts_append >>
     metis_tac[emitted_insts_emit_op, emitted_insts_emit_void]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK q` by
    metis_tac[run_inst_seq_append] >>
  `(q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    q.vs_halted = s.vs_halted /\ q.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `q with <|vs_vars := _; vs_memory := _|> = u` mp_tac >>
     simp[Abbr `u`, update_var_def, venom_state_component_equality]) >>
  `!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s` by
    metis_tac[not_fresh_at_mono, ci_mono_def] >>
  `stmt_state_rel ctx func cenv cx ee q` by
    (irule exprSimBufferStoreTheory.buffer_store_state_frame >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >> simp[] >>
     qexistsl_tac [`w2n (w + n2w off)`, `type_memory_size tv`, `sa`] >>
     gvs[Abbr `u`, update_var_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `same_blocks sa sb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     drule emitted_insts_emit_void >> strip_tac >>
     `same_blocks sa sn /\ same_blocks sn sb` by
       metis_tac[emit_op_same_blocks, emit_void_same_blocks] >>
     gvs[same_blocks_def, mk_inst_def, is_terminator_def]) >>
  `(q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_inst_idx := s.vs_inst_idx|>) = s` by
    (qpat_x_assum `q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  drule_all extrequest_straight_run_path >> strip_tac >>
  qexists_tac `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx, lookup_var_def] >>
  gvs[Abbr `u`, update_var_def, same_blocks_def] >>
  fs[lookup_var_def] >> metis_tac[]
QED

Finalise extrequest_tuple_word_head

(* Compute the tuple destination before reading the captured operand.  In
   particular, the read may allocate; its history keeps the destination. *)
Theorem extrequest_tuple_head_read:
  emit_op ADD [buf; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value cenv vv sn = (op,sb) /\
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e es sa sc s0 ec r vv tc /\
  extrequest_history_frame cenv cx ec sc tc ee sm s /\
  stmt_state_rel ctx func cenv cx ec tc /\
  stmt_state_rel ctx func cenv cx ee s /\
  (case vv of StackValue ty a => safe_operand sc a
   | LocatedValue ty p => safe_operand sc p.ptr_operand) /\
  (!ty p tr w tv.
     vv = LocatedValue ty p /\ p.ptr_location = slot_loc tr /\
     eval_operand p.ptr_operand tc = SOME w /\
     evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
     storage_read_live cx tr (get_storage cx ec tr) w tv) /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
         ~is_word_type (expr_type e) ==>
         type_memory_bytes cenv (expr_type e) = type_memory_size tv /\
         type_memory_size tv < 2**64) /\
  eval_operand buf s = SOME w /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v t u. gas_marked_exec F (ctx,func) (read_result cx r) (ee,s)
      [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e ee sa sb t ee v op u /\
    eval_operand dst u = SOME (w + n2w off) /\
    safe_operand sb dst /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    extrequest_history_frame cenv cx ec sc tc ee sb u /\
    extrequest_history_frame cenv cx ee sm s ee sb u
Proof
  strip_tac >>
  `ci_mono sm sn /\ ci_mono sn sb` by
    (conj_tac
     >- (qspecl_then [`ADD`, `[buf; Lit (n2w off)]`, `sm`] mp_tac ci_mono_emit_op >> simp[]) >>
     qspecl_then [`cenv`, `vv`, `sn`] mp_tac ci_mono_unwrap_value >> simp[]) >>
  `fn_has_code sm sn func /\ fn_has_code sn sb func` by
    (irule fragExecTheory.fn_has_code_split >> gvs[ci_mono_def]) >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn` by
    (fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >>
     irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> gvs[ci_mono_def]) >>
  qabbrev_tac `t = (update_var (STRING #"%" (toString sm.cs_next_var))
    (w + n2w off) s) with vs_inst_idx := LENGTH sn.cs_current_insts` >>
  suspend "add_endpoint"
QED

Resume extrequest_tuple_head_read[add_endpoint]:
  `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s` by
    (simp[Abbr `t`, lookup_var_def, update_var_def] >>
     rpt strip_tac >> fs[not_fresh_at_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `stmt_state_rel ctx func cenv cx ee t` by
    (simp[Abbr `t`, stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_update_var >> simp[] >>
     irule local_ptrs_reserved_fresh >> qexists_tac `sm` >> simp[]) >>
  `extrequest_history_frame cenv cx ee sm s ee sn t` by
    (irule extrequest_unchanged_memory_history >>
     gvs[ci_mono_def, Abbr `t`, update_var_def]) >>
  `extrequest_history_frame cenv cx ec sc tc ee sn t` by
    metis_tac[extrequest_history_frame_trans] >>
  `eval_operand dst t = SOME (w + n2w off) /\ safe_operand sn dst` by
    (drule emitted_insts_emit_op >> strip_tac >>
     simp[Abbr `t`, eval_operand_def, lookup_var_update_var, lookup_var_def] >>
     metis_tac[emit_op_safe_operand]) >>
  `~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
   t.vs_inst_idx = LENGTH sn.cs_current_insts` by
    (drule emit_op_same_blocks >> gvs[Abbr `t`, update_var_def, same_blocks_def]) >>
  suspend "read_and_finish"
QED

Resume extrequest_tuple_head_read[read_and_finish]:
  `gas_marked_path F ctx func s 0 (OK t)` by
    (`run_inst_seq (emitted_insts sm sn) s =
        OK (update_var (STRING #"%" (toString sm.cs_next_var)) (w + n2w off) s)` by
       (irule buffer_emit_add_run >> metis_tac[]) >>
     simp[Abbr `t`] >> irule extrequest_straight_run_path >>
     simp[] >> qexists_tac `sm` >> simp[] >>
     drule emitted_insts_emit_op >> strip_tac >>
     drule emit_op_same_blocks >> strip_tac >>
     gvs[mk_inst_def, is_terminator_def]) >>
  drule_all extrequest_joint_unwrap_read >> strip_tac >>
  `eval_operand dst u = SOME (w + n2w off)` by
    (Cases_on `dst` >> gvs[safe_operand_def, eval_operand_def] >>
     fs[exprExtRequestHistoryTheory.extrequest_history_frame_def] >> metis_tac[]) >>
  `extrequest_history_frame cenv cx ee sm s ee sb u` by
    metis_tac[extrequest_history_frame_trans] >>
  `extrequest_history_frame cenv cx ec sc tc ee sb u` by
    metis_tac[extrequest_history_frame_trans] >>
  qexistsl_tac [`v`, `t`, `u`] >> simp[] >> conj_tac
  >- (irule gas_marked_exec_zero_prefix >> goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[safe_operand_mono, ci_mono_def]
QED

Finalise extrequest_tuple_head_read
