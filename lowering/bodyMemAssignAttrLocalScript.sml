(* Memory case of the body induction, assignment to a base target
   (bodyMemAssign's dispatch): a word field of a local struct (S1's body_assign_attr_local). *)
Theory bodyMemAssignAttrLocal
Ancestors
  bodySim bodyExprPreFacts supportedStmtTraverse supportedStmts supportedExprs
  vyperTypeCallGraph vyperTypeSystem vyperTypeInvariants
  bodyMemoryPreds bodyFieldMemoryProps bodyDeclMemoryCounted
  exprSimVVFrame exprOperandVar emitHelperProps gasSummary fragGasMode
  venomState venomInst venomExecSemantics compileEnv loweringStateRelDefs emitHelper fragExec
  words ASCIInumbers exprLoweringProps stmtSimAssignAttr
  gasExemptCert stmtSimForced vyperInterpreter vyperState vyperExprNoControl
  stmtSimDefs exprSimDefs gasOutcome loweringPosts gasContext exprSimMemorySource
  exprSimMemDefs context exprSimMemUnwrap exprSimWordArgs
  bodyMemAugAssignAttrLocal fragGasPath
  exprSimHypsDefs stmtSimAugAssign stmtSimDeclMem
  gasSummaryCompose stmtSimProps exprSimUnwrapProps exprSimUnwrap
  vyperLookup valueEncoding allocaFootprint bodyDeclMemoryCore bodyMemoryDefs

Theorem assign_attr_local_add_exact_mem[local]:
  emit_op ADD [Var p; Lit (n2w off)] sm = (dst,sn) /\
  lookup_var p s = SOME w /\
  fn_has_code sm sn func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_marked_path T ctx func s 0
    (OK (update_var (STRING #"%" (toString sm.cs_next_var))
          (w + n2w off) s with vs_inst_idx := LENGTH sn.cs_current_insts))
Proof
  strip_tac >>
  `run_inst_seq (emitted_insts sm sn) s =
    OK (update_var (STRING #"%" (toString sm.cs_next_var))
          (w + n2w off) s)` by
    (irule buffer_emit_add_run >> qexistsl_tac [`dst`, `Var p`] >>
     simp[eval_operand_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sm sn) s` by
    metis_tac[attr_add_prefix_mem_ok] >>
  `same_blocks sm sn /\
   sn.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sn /\
   EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) (emitted_insts sm sn)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
         fresh_var_def, emit_def, same_blocks_def, mk_inst_def,
         is_terminator_def]) >>
  drule_all body_decl_cursor_path >>
  simp[gas_marked_path_def]
QED

Theorem assign_attr_local_add_post_mem[local]:
  compile_expr cenv ty e sa = (vv,sm) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [Var p; Lit (n2w off)] sm = (dst,sn) /\
  lookup_var p s = SOME w /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  vv_post ctx func cenv cx e es sa sm s0 es' tv vv s /\
  alloca_history func s ==>
  ?q. gas_marked_path T ctx func s 0 (OK q) /\
    vv_post ctx func cenv cx e es sa sn s0 es' tv vv q /\
    eval_operand dst q = SOME (w + n2w off) /\
    alloca_history func q /\ ~q.vs_halted /\
    q.vs_current_bb = sn.cs_current_bb /\
    q.vs_inst_idx = LENGTH sn.cs_current_insts /\
    q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
    q.vs_memory = s.vs_memory /\ q.vs_labels = s.vs_labels /\
    local_ptrs_reserved cenv sn /\
    sm.cs_next_var <= sn.cs_next_var /\
    (?out. dst = Var out /\ not_fresh_at sn out) /\
    (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s)
Proof
  strip_tac >>
  drule_all assign_attr_local_add_exact_mem >> strip_tac >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sm z` by
    metis_tac[CONJUNCT1 compiler_compile_var] >>
  `alloca_inv s` by gvs[loweringPostsTheory.vv_post_def,
                       stmt_state_rel_def] >>
  `run_inst_seq (emitted_insts sm sn) s =
    OK (update_var (STRING #"%" (toString sm.cs_next_var))
          (w + n2w off) s)` by
    (irule buffer_emit_add_run >> qexistsl_tac [`dst`, `Var p`] >>
     simp[eval_operand_def]) >>
  drule_all attr_add_history >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qexists_tac `update_var (STRING #"%" (toString sm.cs_next_var))
          (w + n2w off) s with vs_inst_idx := LENGTH sn.cs_current_insts` >>
  simp[] >> conj_tac
  >- (irule vv_post_update_var >> simp[] >> qexists_tac `sm` >>
      simp[not_fresh_at_def, ASCIInumbersTheory.toString_11]) >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def, update_var_def,
      eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> gvs[not_fresh_at_def] >>
  irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]
QED

Theorem assign_attr_local_admissible_run_mem_src[local]:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es ==>
  !gs. eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)
      (es with gas_obs := gs) =
    vyperState$bind (vyperState$bind (eval_expr cx e) (read_result cx))
      (write_place cx (MemoryPlace id [AttrSubscript fld]))
      (es with gas_obs := gs)
Proof
  strip_tac >> gen_tac >>
  Cases_on `eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)
    (es with gas_obs := gs)` >>
  rename1 `_ = (res, ee)` >>
  `stmt_res_ok lctx res` by metis_tac[gas_admissible_result] >>
  drule eval_assign_attr_local >>
  impl_tac >- gvs[stmt_res_ok_def] >>
  strip_tac >> Cases_on `r` >>
  gvs[vyperStateTheory.bind_def, pairTheory.UNCURRY]
QED

Theorem assign_attr_local_admissible_rhs_mem_src[local]:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es ==>
  gas_admissible (vyperState$bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  `no_control_exc ex` by
    (qpat_x_assum `vyperState$bind _ _ _ = _` mp_tac >>
     simp[vyperStateTheory.bind_def, AllCaseEqs()] >> strip_tac >> gvs[]
     >- metis_tac[read_result_no_control]
     >> metis_tac[cj 1 eval_expr_no_control]) >>
  `stmt_res_ok lctx (INR ex)` by
    (drule gas_admissible_result >> disch_then irule >>
     qexistsl_tac [`ee`, `gs`] >>
     drule assign_attr_local_admissible_run_mem_src >>
     disch_then (qspec_then `gs` SUBST1_TAC) >>
     simp[Once vyperStateTheory.bind_def]) >>
  gvs[stmt_res_ok_def, expr_res_ok_def, no_control_exc_def]
QED

Theorem assign_attr_local_admissible_raw_mem_src[local]:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es ==>
  gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  strip_tac >> irule forced_expr_admissible_raw >>
  metis_tac[assign_attr_local_admissible_rhs_mem_src]
QED

Theorem assign_attr_local_marked_exec_mem_src[local]:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es /\
  gas_marked_exec memory (ctx,func)
    (vyperState$bind (vyperState$bind (eval_expr cx e) (read_result cx))
      (write_place cx (MemoryPlace id [AttrSubscript fld])))
    (es,s0) marks res ee r ==>
  gas_marked_exec memory (ctx,func)
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (es,s0) marks res ee r
Proof
  strip_tac >> drule assign_attr_local_admissible_run_mem_src >>
  strip_tac >> gvs[gas_marked_exec_def]
QED

Theorem assign_attr_local_continuation_success_mem_src[local]:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es /\
  vyperState$bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gs) = (INL v, ee) ==>
  ?pre env entry rest vals old.
    find_containing_scope id ee.scopes = SOME (pre, env, entry, rest) /\
    entry.value = StructV vals /\ ALOOKUP vals fld = SOME old /\
    write_place cx (MemoryPlace id [AttrSubscript fld]) v ee =
      (INL (), ee with scopes :=
        pre ++ (env |+ (id, entry with
          <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest)
Proof
  strip_tac >>
  Cases_on `eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)
    (es with gas_obs := gs)` >> rename1 `_ = (res, ff)` >>
  `stmt_res_ok lctx res` by metis_tac[gas_admissible_result] >>
  drule eval_assign_attr_local >>
  impl_tac >- gvs[stmt_res_ok_def] >> strip_tac >>
  gvs[vyperStateTheory.bind_def, pairTheory.UNCURRY] >>
  `!m. res <> INR (Error (TypeError m))` by gvs[stmt_res_ok_def] >>
  drule_all write_place_attr_local >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem assign_attr_local_continuation_all_tails_mem_src[local]:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es /\
  (!tail. vyperState$bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := prefix ++ tail) = (INL v, ee with gas_obs := tail)) ==>
  ?pre env entry rest vals old.
    find_containing_scope id ee.scopes = SOME (pre, env, entry, rest) /\
    entry.value = StructV vals /\ ALOOKUP vals fld = SOME old /\
    !tail. write_place cx (MemoryPlace id [AttrSubscript fld]) v
      (ee with gas_obs := tail) =
      (INL (), (ee with scopes :=
        pre ++ (env |+ (id, entry with
          <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest)
        with gas_obs := tail)
Proof
  strip_tac >>
  `!tail. ?pre env entry rest vals old.
    find_containing_scope id ee.scopes = SOME (pre, env, entry, rest) /\
    entry.value = StructV vals /\ ALOOKUP vals fld = SOME old /\
    write_place cx (MemoryPlace id [AttrSubscript fld]) v (ee with gas_obs := tail) =
      (INL (), (ee with scopes :=
        pre ++ (env |+ (id, entry with
          <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest)
        with gas_obs := tail)` by
    (gen_tac >> drule assign_attr_local_continuation_success_mem_src >>
     disch_then (qspecl_then [`v`, `prefix ++ tail`, `ee with gas_obs := tail`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  pop_assum (fn th => assume_tac th >> mp_tac (Q.SPEC `[]` th)) >>
  strip_tac >> qexistsl_tac [`pre`, `env`, `entry`, `rest`, `vals`, `old`] >>
  gvs[] >> gen_tac >>
  first_x_assum (qspec_then `tail` strip_assume_tac) >> gvs[]
QED

Theorem assign_attr_local_exempt_mem_src[local]:
  gas_exempt_cert memory tops (ctx, func)
    (ignore_bind (eval_expr cx e) (return ()))
    (es, s0) marks (err, ee) (leaf, fin) ==>
  gas_exempt_cert memory tops (ctx, func)
    (ignore_bind
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      (return ()))
    (es, s0) marks (err, ee) (leaf, fin)
Proof
  strip_tac >>
  `ignore_bind
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (return ()) =
   vyperState$bind (vyperState$bind (eval_expr cx e) (read_result cx))
     (\v. ignore_bind
       (vyperState$bind (eval_target_place cx (AttributeTarget (NameTarget id) fld))
         (\p. write_place cx p v))
       (return ()))` by
    simp[Once evaluate_def, ignore_bind_def, bind_assoc] >>
  pop_assum SUBST1_TAC >>
  irule gas_exempt_cert_error_value >> simp[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_result >> simp[]
QED

Theorem assign_attr_local_vv_bound_frame_mem[local]:
  vv_store_bound cx ty lt es tv vv s /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
  s.vs_alloca_next <= q.vs_alloca_next ==>
  vv_store_bound cx ty lt es tv vv q
Proof
  Cases_on `vv` >>
  simp[vv_store_bound_def, vv_operand_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >> simp[]
QED

Theorem assign_attr_local_vv_rebase_mem[local]:
  vv_post ctx func cenv cx e es sa sm s0 ee tv vv s ==>
  vv_post ctx func cenv cx e ee (sa with cs_next_var := sm.cs_next_var)
    sm s ee tv vv s
Proof
  Cases_on `vv` >>
  simp[vv_post_def, vv_at_def, expr_val_at_def, locals_kept_def]
QED

Theorem assign_attr_local_unwrap_mem[local]:
  unwrap_value cenv vv sm = (op,sb) /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ftv /\
  stmt_state_rel ctx func cenv cx es s0 /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v u. gas_marked_exec T (ctx,func) (read_result cx tv) (ee,s)
          [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
    expr_post ctx func cenv cx e ee (sa with cs_next_var := sm.cs_next_var)
      sb s ee v op u /\
    expr_store_bound cx (expr_type e) v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  drule assign_attr_local_vv_rebase_mem >> strip_tac >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_marked_read_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  impl_tac
  >- (simp[] >> irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  strip_tac >>
  `wb_frame cenv es sa s0 s` by
    (fs[vv_post_def, wb_frame_def] >> metis_tac[]) >>
  `wb_frame cenv ee (sa with cs_next_var := sm.cs_next_var) s u` by
    (fs[expr_post_def, wb_frame_def] >> metis_tac[]) >>
  `wb_frame cenv es sa s0 u` by
    (irule wb_frame_trans >> goal_assum drule >>
     conj_tac >- (goal_assum (drule_at (Pat `wb_frame _ _ _ _ _`)) >>
                  simp[]) >> metis_tac[]) >>
  qexistsl_tac [`v`, `u`] >> simp[] >>
  gvs[expr_post_def, wb_frame_def, expr_val_at_def] >> metis_tac[]
QED

Theorem assign_attr_local_store_layout_path_mem[local]:
  emit_void MSTORE [dst; op] st = ((),st') /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  stmt_state_rel ctx func cenv cx es s /\ alloca_history func s /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  find_containing_scope id es.scopes = SOME (pre,env,entry,rest) /\
  lookup_var p s = SOME wbase /\
  eval_operand dst s = SOME (wbase + n2w (struct_field_offset fields fld)) /\
  eval_operand op s = SOME (typed_val_to_w256 ftv v) /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  fields_layout fields fs /\ struct_has_type fs vals /\
  ALOOKUP fs fld = SOME ftv /\ store_lays_out ftv ftv v ==>
  ?t. stmt_state_rel ctx func cenv cx
        (es with scopes := pre ++
          (env |+ (id, entry with
            <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest) t /\
      ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\
      (!x. lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      alloca_history func t /\ gas_marked_path T ctx func s 0 (OK t)
Proof
  strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `type_memory_size ftv = 32` by fs[stmtSimDeclStoreTheory.store_lays_out_def] >>
  `w2n wbase + type_memory_size_fields fs <= s.vs_alloca_next` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> simp[type_memory_size_def] >> decide_tac) >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[stmt_state_rel_def, alloca_room_next_lt] >>
  `w2n (wbase + n2w (struct_field_offset fields fld)) =
     w2n wbase + struct_field_offset fields fld` by
    (drule_all body_field_address_no_wrap >> simp[]) >>
  `w2n (wbase + n2w (struct_field_offset fields fld)) + 32 <= s.vs_alloca_next` by
    (drule_all body_field_region_frontier >> simp[]) >>
  drule_all stmt_state_rel_write_field >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  qabbrev_tac `u = mstore (w2n (wbase + n2w (struct_field_offset fields fld)))
                          (typed_val_to_w256 ftv v) s` >>
  `run_inst_seq (emitted_insts st st') s = OK u` by
    (`step_inst_base (mk_inst st.cs_next_id MSTORE [dst; op] []) s = OK u` by
       (qunabbrev_tac `u` >> irule step_MSTORE >> simp[]) >>
     simp[run_inst_seq_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    (irule emit_mstore_mem_ok >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts st st')` by
    simp[mk_inst_def, is_terminator_def] >>
  `gas_path_mem ctx func s 0
     (OK (u with vs_inst_idx := LENGTH st'.cs_current_insts)) /\
   ~u.vs_halted /\ u.vs_current_bb = st'.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[is_terminator_def] >>
     qexists_tac `st` >> simp[is_terminator_def]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history func (u with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule body_store_memory_history >> simp[is_terminator_def] >>
     qexistsl_tac [`s`, `st`] >> simp[is_terminator_def]) >>
  `stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (env |+ (id, entry with
          <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest) u` by
    simp[Abbr `u`] >>
  qexists_tac `u with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx, gas_marked_path_def] >>
  simp[Abbr `u`, lookup_var_def, mstore_def]
QED

Theorem assign_attr_local_suffix_mem[local]:
  compile_expr cenv ty e sa = (vv,sm) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  emit_op ADD [Var p; Lit (n2w (struct_field_offset fields fld))] sm = (dst,sn) /\
  unwrap_value cenv vv sn = (op,st) /\ emit_void MSTORE [dst; op] st = ((),sb) /\
  fn_has_code sm sn func /\ fn_has_code sn st func /\ fn_has_code st sb func /\
  fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s0 /\
  vv_post ctx func cenv cx e es sa sm s0 ee (Value v) vv s /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee (Value v) vv s /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  find_containing_scope id ee.scopes = SOME (pre,env,entry,rest) /\
  lookup_var p s = SOME wbase /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  fields_layout fields fs /\ struct_has_type fs vals /\ ALOOKUP fs fld = SOME ftv /\
  is_word_type (expr_type e) /\ word_value_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ftv /\ store_lays_out ftv ftv v ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx
      (ee with scopes := pre ++
        (env |+ (id, entry with
          <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest) t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)
Proof
  strip_tac >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule (cj 1 compiler_compile_var) >>
     goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >> simp[]) >>
  drule_all assign_attr_local_add_post_mem >> strip_tac >>
  `vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee (Value v) vv q` by
    (irule assign_attr_local_vv_bound_frame_mem >> qexists_tac `s` >>
     simp[] >> Cases_on `vv_operand vv` >> simp[eval_operand_def] >>
     metis_tac[CONJUNCT1 compiler_compile_var]) >>
  `sa.cs_next_id <= sn.cs_next_id` by
    (drule emitted_insts_emit_op >> simp[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sn x` by
    (drule (CONJUNCT1 compiler_compile_var) >> strip_tac >>
     fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  drule_at (Pat `unwrap_value _ _ _ = _`) assign_attr_local_unwrap_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspec_then `ftv` mp_tac) >>
  impl_tac >- (simp[] >> decide_tac) >> strip_tac >>
  `v' = v /\ gas_marked_path T ctx func q 0 (OK u)` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, gas_explicit_def,
          read_result_def, return_def]) >>
  gvs[] >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ s` kall_tac >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ q` kall_tac >>
  `lookup_var out u = SOME (wbase + n2w (struct_field_offset fields fld))` by
    (qpat_x_assum `expr_post _ _ _ _ _ ee _ _ q _ _ _ _` mp_tac >>
     simp[expr_post_def] >> strip_tac >>
     qpat_x_assum `!x w. not_fresh_at (_ with cs_next_var := _) x /\ _ ==> _` irule >>
     simp[GSYM eval_operand_def] >> fs[not_fresh_at_def]) >>
  `not_fresh_at sa p` by
    (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `lookup_var p u = SOME wbase` by
    (`not_fresh_at sn p /\ not_fresh_at sm p` by
       (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
     `lookup_var p q = SOME wbase` by metis_tac[] >>
     qpat_x_assum `expr_post _ _ _ _ _ ee _ _ q _ _ _ _` mp_tac >>
     simp[expr_post_def] >> strip_tac >>
     qpat_x_assum `!x w. not_fresh_at (_ with cs_next_var := _) x /\ _ ==> _` irule >>
     fs[not_fresh_at_def]) >>
  `~u.vs_halted` by
    (drule gas_marked_path_exec >> strip_tac >>
     drule gas_path_normal >> simp[]) >>
  `stmt_state_rel ctx func cenv cx ee u /\
   eval_operand op u = SOME (typed_val_to_w256 ftv v)` by
    (qpat_x_assum `expr_post _ _ _ _ _ es _ _ s0 _ _ _ _` mp_tac >>
     simp[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  drule_at (Pat `emit_void _ _ _ = _`) assign_attr_local_word_store_path_mem >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `find_containing_scope _ _ = _`)) >>
  disch_then (drule_at (Pat `fields_layout _ _`)) >>
  disch_then (drule_at (Pat `ALOOKUP _ _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME (typed_val_to_w256 _ _)`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
  disch_then (qspecl_then [`wbase`, `vals`] mp_tac) >>
  impl_tac >- simp[eval_operand_def] >>
  strip_tac >>
  `gas_marked_path T ctx func q 0 (OK t)` by
    metis_tac[gas_marked_path_then, arithmeticTheory.ADD] >>
  `gas_marked_path T ctx func s 0 (OK t)` by
    metis_tac[gas_marked_path_then, arithmeticTheory.ADD] >>
  qexists_tac `t` >> simp[] >>
  qpat_x_assum `expr_post _ _ _ _ _ es _ _ s0 _ _ _ _` mp_tac >>
  simp[expr_post_def] >> metis_tac[]

QED

Theorem assign_attr_local_suffix_layout_mem[local]:
  compile_expr cenv ty e sa = (vv,sm) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  emit_op ADD [Var p; Lit (n2w (struct_field_offset fields fld))] sm = (dst,sn) /\
  unwrap_value cenv vv sn = (op,st) /\ emit_void MSTORE [dst; op] st = ((),sb) /\
  fn_has_code sm sn func /\ fn_has_code sn st func /\ fn_has_code st sb func /\
  fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s0 /\
  vv_post ctx func cenv cx e es sa sm s0 ee (Value v) vv s /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee (Value v) vv s /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  find_containing_scope id ee.scopes = SOME (pre,env,entry,rest) /\
  lookup_var p s = SOME wbase /\
  entry.type = StructTV fs /\ entry.value = StructV vals /\
  fields_layout fields fs /\ struct_has_type fs vals /\ ALOOKUP fs fld = SOME ftv /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ftv /\ store_lays_out ftv ftv v ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx
      (ee with scopes := pre ++
        (env |+ (id, entry with
          <|value := StructV (AFUPDKEY fld (K v) vals); popped := []|>)) :: rest) t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)
Proof
  strip_tac >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule (cj 1 compiler_compile_var) >>
     goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >> simp[]) >>
  drule_all assign_attr_local_add_post_mem >> strip_tac >>
  `vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee (Value v) vv q` by
    (irule assign_attr_local_vv_bound_frame_mem >> qexists_tac `s` >>
     simp[] >> Cases_on `vv_operand vv` >> simp[eval_operand_def] >>
     metis_tac[CONJUNCT1 compiler_compile_var]) >>
  `sa.cs_next_id <= sn.cs_next_id` by
    (drule emitted_insts_emit_op >> simp[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sn x` by
    (drule (CONJUNCT1 compiler_compile_var) >> strip_tac >>
     fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  drule_at (Pat `unwrap_value _ _ _ = _`) assign_attr_local_unwrap_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspec_then `ftv` mp_tac) >>
  impl_tac >- (simp[] >> decide_tac) >> strip_tac >>
  `v' = v /\ gas_marked_path T ctx func q 0 (OK u)` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, gas_explicit_def, read_result_def, return_def]) >>
  gvs[] >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ s` kall_tac >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ q` kall_tac >>
  `lookup_var out u = SOME (wbase + n2w (struct_field_offset fields fld))` by
    (qpat_x_assum `expr_post _ _ _ _ _ ee _ _ q _ _ _ _` mp_tac >>
     simp[expr_post_def] >> strip_tac >>
     qpat_x_assum `!x w. not_fresh_at (_ with cs_next_var := _) x /\ _ ==> _` irule >>
     simp[GSYM eval_operand_def] >> fs[not_fresh_at_def]) >>
  `not_fresh_at sa p` by (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `lookup_var p u = SOME wbase` by
    (`not_fresh_at sn p /\ not_fresh_at sm p` by
       (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
     `lookup_var p q = SOME wbase` by metis_tac[] >>
     qpat_x_assum `expr_post _ _ _ _ _ ee _ _ q _ _ _ _` mp_tac >>
     simp[expr_post_def] >> strip_tac >>
     qpat_x_assum `!x w. not_fresh_at (_ with cs_next_var := _) x /\ _ ==> _` irule >>
     fs[not_fresh_at_def]) >>
  `~u.vs_halted` by
    (drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `stmt_state_rel ctx func cenv cx ee u /\
   eval_operand op u = SOME (typed_val_to_w256 ftv v)` by
    (qpat_x_assum `expr_post _ _ _ _ _ es _ _ s0 _ _ _ _` mp_tac >>
     simp[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  drule_at (Pat `emit_void _ _ _ = _`) assign_attr_local_store_layout_path_mem >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `find_containing_scope _ _ = _`)) >>
  disch_then (drule_at (Pat `fields_layout _ _`)) >>
  disch_then (drule_at (Pat `ALOOKUP _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME (typed_val_to_w256 _ _)`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
  disch_then (qspecl_then [`wbase`, `vals`] mp_tac) >>
  impl_tac >- simp[eval_operand_def] >> strip_tac >>
  `gas_marked_path T ctx func q 0 (OK t)` by
    metis_tac[gas_marked_path_then, arithmeticTheory.ADD] >>
  `gas_marked_path T ctx func s 0 (OK t)` by
    metis_tac[gas_marked_path_then, arithmeticTheory.ADD] >>
  qexists_tac `t` >> simp[] >>
  qpat_x_assum `expr_post _ _ _ _ _ es _ _ s0 _ _ _ _` mp_tac >>
  simp[expr_post_def] >> metis_tac[]
QED

Theorem assign_attr_local_normal_source_mem_src[local]:
  gas_admissible
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (stmt_res_ok lctx) es /\
  expr_body_pre cenv cx env e es /\
  FLOOKUP env.var_types id = SOME (StructT sid) /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
    fld = SOME (fty,fsz) /\ is_word_type fty /\ expr_type e = fty /\
  (!tail. vyperState$bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gs ++ tail) = (INL v, ee with gas_obs := tail)) ==>
  ?pre env1 entry rest fs vals ftv.
    find_containing_scope id ee.scopes = SOME (pre,env1,entry,rest) /\
    entry.type = StructTV fs /\ entry.value = StructV vals /\
    fields_layout (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs /\
    struct_has_type fs vals /\ ALOOKUP fs fld = SOME ftv /\
    evaluate_type (get_tenv cx) fty = SOME ftv /\ store_lays_out ftv ftv v /\
    !tail. write_place cx (MemoryPlace id [AttrSubscript fld]) v
      (ee with gas_obs := tail) =
      (INL (), ee with <|scopes := pre ++
        (env1 |+ (id,entry with <|value := StructV (AFUPDKEY fld (K v) vals);
          popped := []|>)) :: rest; gas_obs := tail|>)
Proof
  strip_tac >> drule_all assign_attr_local_continuation_all_tails_mem_src >> strip_tac >>
  Cases_on `eval_stmt cx
    (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)
    (es with gas_obs := gs ++ [])` >> rename1 `_ = (res,ff)` >>
  `stmt_res_ok lctx res` by metis_tac[gas_admissible_result] >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs ++ [])` by simp[] >>
  drule_all assign_attr_local_source >> strip_tac >>
  qpat_x_assum `!tail. vyperState$bind _ _ _ = _`
    (qspec_then `[]` assume_tac) >>
  `r = INL v /\ es1 = (ee with gas_obs := [])` by
    (qpat_x_assum `(do result <- _; _ od) _ = _` mp_tac >>
     qpat_x_assum `vyperState$bind _ _ _ = _` mp_tac >>
     simp[vyperStateTheory.bind_def, pairTheory.UNCURRY]) >>
  gvs[] >> metis_tac[]
QED

Theorem assign_attr_local_frag_mem[local]:
  expr_vv_sim_mem ctx func cenv cx (expr_type e) e es /\
  expr_body_pre cenv cx env e es /\
  FLOOKUP env.var_types id = SOME (StructT sid) /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
    fld = SOME (fty,fsz) /\ is_word_type fty /\ expr_type e = fty ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty
      (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
    (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) es
Proof
  strip_tac >> simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME (StructT sid)` by fs[expr_sim_inv_def] >>
  `is_word_type (expr_type e)` by simp[] >>
  drule_all assign_attr_local_code_parts >> strip_tac >> gvs[] >>
  `cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn su /\
   cs_extends su sb` by
    (metis_tac[cj 1 compile_expr_ci_mono, ci_mono_emit_op,
       ci_mono_unwrap_value, ci_mono_emit_void, pairTheory.SND, ci_mono_def]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\
   fn_has_code sn su func /\ fn_has_code su sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `~block_is_terminated sb` by
    (drule emit_void_nonterminator_open >> simp[is_terminator_def]) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    (drule assign_attr_local_admissible_raw_mem_src >> simp[]) >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `s0`] mp_tac) >> simp[] >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN assume_tac))
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `?res es_end r. _` strip_assume_tac >> gvs[]
      >- suspend "normal"
      >> suspend "exception") >>
  qexists_tac `marks` >> disj2_tac >> pop_assum strip_assume_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule assign_attr_local_exempt_mem_src >> simp[]
QED

Resume assign_attr_local_frag_mem[exception]:
  markerLib.RESUME_TAC >> (
  Cases_on `res` >- fs[expr_exit_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >> conj_tac
  >- (irule assign_attr_local_marked_exec_mem_src >>
      (conj_tac >- (qexists_tac `lctx` >> simp[])) >>
      ntac 2 (irule gas_marked_exec_bind_exception) >> simp[]) >>
  disj2_tac >> simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type])
QED

Resume assign_attr_local_frag_mem[normal]:
  markerLib.RESUME_TAC >> (
  qpat_x_assum `stmt_env _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `lookup_scopes id es.scopes = _` kall_tac >>
  qpat_x_assum `evaluate_type _ (StructT sid) = _` kall_tac >>
  Cases_on `read_result cx tv (es_end with gas_obs := [])` >>
  rename1 `_ = (rr, ee)` >>
  `ee = es_end with gas_obs := []` by metis_tac[read_result_state] >> gvs[] >>
  reverse (Cases_on `rr`)
  >- metis_tac[vv_post_failed_read] >>
  rename1 `read_result cx tv (es_end with gas_obs := []) = (INL v, _)` >>
  `vv_store_bound cx (expr_type e) (lowered_value_type cenv e)
    (es_end with gas_obs := []) (Value v) vv t` by
    (qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
     rw[vv_store_bound_def] >> gvs[read_result_def, return_def] >>
     first_x_assum irule >> metis_tac[]) >>
  drule vv_post_read_result >> strip_tac >> gvs[] >>
  `!tail. vyperState$bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL v, es_end with gas_obs := tail)` by
    (fs[gas_marked_exec_def, vyperStateTheory.bind_def] >>
     drule read_result_gas_obs >> simp[]) >>
  drule assign_attr_local_normal_source_mem_src >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (StructT _)`)) >>
  disch_then (drule_at (Pat `ALOOKUP _ _ = _`)) >>
  simp[] >> disch_then drule >> strip_tac >>
  qpat_x_assum `!func cenv e es sa sb s0 vv s'' ctx. _` kall_tac >>
  qpat_x_assum `vv_store_bound _ _ _ _ tv _ _` kall_tac >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM (es_end with gas_obs := []).scopes` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` assume_tac) >>
     drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (drule (cj 1 compile_expr_grows) >> simp[]) >>
  `?bw. lookup_var p t = SOME bw` by
    (`local_ptrs_rel func cenv es_end.scopes t` by
       fs[vv_post_def, stmt_state_rel_def, state_rel_def] >>
     `lookup_scopes id es_end.scopes = SOME entry` by
       metis_tac[find_containing_scope_lookup] >>
     qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
     simp[local_ptrs_rel_def] >> strip_tac >>
     first_x_assum drule_all >> metis_tac[]) >>
  drule_at (Pat `emit_void _ _ _ = _`) assign_attr_local_suffix_layout_mem >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `find_containing_scope _ _ = _`) o SRULE []) >>
  disch_then (drule_at (Pat `fields_layout _ _`)) >>
  disch_then (drule_at (Pat `ALOOKUP _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_op ADD _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var p t = _`)) >>
  disch_then (qspec_then `vals` mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `stmt_state_rel ctx func cenv cx ff t'` >>
  `gas_marked_path T ctx func s0 (LENGTH marks) (OK t')` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule_all gas_marked_path_then >> simp[]) >>
  qexistsl_tac [`INL ()`, `ff`, `OK t'`] >> conj_tac
  >- (simp[gas_marked_exec_def] >> gen_tac >>
      drule assign_attr_local_admissible_run_mem_src >>
      disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings ++ tail` SUBST1_TAC) >>
      simp[Once vyperStateTheory.bind_def, Abbr `ff`]) >>
  disj1_tac >> simp[stmt_lands_def, cenv_top_ext_refl] >>
  irule return_buf_frame_frame >>
  qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  qspecl_then [`cenv`, `vv`, `sn`] mp_tac ci_mono_unwrap_value >>
  simp[] >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  fs[ci_mono_def] >> decide_tac)
QED

Finalise assign_attr_local_frag_mem

Theorem body_assign_attr_local_mem:
  !cx id fld e sid fty d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    body_expr_mem_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings
      (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    attribute_type env.type_defs (StructT sid) fld = SOME fty /\
    is_word_type fty ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) es
Proof
  rpt strip_tac >>
  `supported_expr tops e` by
    gvs[supported_stmt_def, supported_assignment_def] >>
  `well_typed_expr env e /\ expr_type e = fty` by
    (gvs[type_stmt_def, atarget_accepts_def, well_typed_expr_def,
         AllCaseEqs()] >>
     Cases_on `FLOOKUP env.var_assignable id` >> gvs[] >>
     Cases_on `x` >> gvs[] >> metis_tac[type_widens_to_word]) >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supported_assignment_exists_def, int_calls_stmt_def,
         int_calls_atarget_def, int_calls_expr_def, body_inv_def] >>
     qexists_tac `[]` >> simp[]) >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  drule attribute_type_struct_field >>
  disch_then (qspecl_then [`sid`, `fld`, `fty`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  irule assign_attr_local_frag_mem >> simp[] >>
  conj_tac
  >- (qexistsl_tac [`env`, `fsz`, `sid`] >> simp[]) >>
  fs[body_expr_mem_ok_def] >>
  first_x_assum (drule_then (drule_then strip_assume_tac)) >> simp[]
QED
