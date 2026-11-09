(*
 * Statement simulation: Assign to a word field of a storage struct (#637)
 *
 * self.x.f = e for a module variable x of struct type in storage or
 * transient storage, f a field of a word type, and e of f's type.  The
 * source evaluates e, takes the place self.x.f (x's slot plus f's slot
 * offset, struct_field_slot), reads e's value and writes its encoding at
 * f's type there.  The lowering evaluates e, adds f's slot offset
 * (struct_field_offset_slots) to x's slot, unwraps the value and stores it
 * with one SSTORE or TSTORE.  The two offsets agree by fields_layout.
 *
 * TOP-LEVEL:
 *   eval_assign_attr_toplevel          — the source run: e's forced
 *                                        value, then write_storage_slot at
 *                                        the field's slot
 *   compile_assign_attr_storage_case  — self.x.f = e, every outcome, e's
 *                                        simulation a premise
 *   compile_assign_attr_storage_stmt_frag — the same for an e with no
 *                                        internal call
 *
 * Helpers: struct_field_slot_alookup, extend_storage_place_attr,
 *   eval_target_place_attr_toplevel, assign_attr_storage_source,
 *   assign_attr_storage_code_parts, store_var_frag, assign_attr_storage_word_suffix
 *)

Theory stmtSimAssignAttrStorage
Ancestors
  exprSimFieldLayout exprSimAggregateChildren exprSimVVFrame immutableWordExecution
  fragGasSeq fragGasPath fragGasMode gasSummary exprSimUnwrap exprSimUnwrapProps
  exprSimSource exprSimMemorySource exprSimMemoryRead exprSimProps gasContext
  stmtSimProps stmtSimDeclPath vyperStorageBackend arithmetic exprOpenPrimitives
  exprSimTopLevelProps stmtSimForced exprSimDefs
  exprSimHypsDefs
  stmtSimDefs
  loweringPosts
  list rich_list finite_map pred_set alist
  fragExec exprSimHyps exprSimLeaves exprSimAttributeFields stmtSimDecl stmtSimDeclMem stmtSimAssign stmtSimAssignMem storageStoreFrame
  stmtSimAssignStorage stmtSimAssignAttr
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv loweringStateRelDefs valueEncoding accountsRelProps
  vyperInterpreter vyperState vyperStorage vyperValue vyperTyping
  vyperTypeEnv vyperTypeInvariants vyperTypeExprSoundness vyperTypeExprResult
  vyperExprNoControl
  venomExecSemantics venomInst venomState
Libs
  monadsyntax

Theorem assign_attr_add_marked[local]:
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [Lit (n2w slot); Lit (n2w off)] sm = (dst,sn) /\
  vv_post ctx func cenv cx e es sa sm s0 ee raw vv s /\
  fn_has_code sm sn func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    vv_post ctx func cenv cx e es sa sn s0 ee raw vv t /\
    eval_operand dst t = SOME (n2w slot + n2w off) /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    (?d. dst = Var d /\ not_fresh_at sn d)
Proof
  strip_tac >>
  `eval_operand (Lit (n2w slot)) s = SOME (n2w slot)` by
    simp[eval_operand_def] >>
  drule_all buffer_emit_add_vv_post >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  `sn.cs_current_bb = sm.cs_current_bb` by
    gvs[cs_extends_def, same_blocks_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sm.cs_next_id ADD [Lit (n2w slot); Lit (n2w off)]
       [STRING #"%" (toString sm.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base
    (mk_inst sm.cs_next_id ADD [Lit (n2w slot); Lit (n2w off)]
      [STRING #"%" (toString sm.cs_next_var)]) s = OK q` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  `gas_path_edge ctx func s 0
    (OK (q with vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_at (Pos last) tuple_straight_line_edge >>
     simp[mk_inst_def, is_terminator_def] >>
     disch_then irule >> simp[GSYM mk_inst_def] >> metis_tac[]) >>
  `gas_marked_path F ctx func s 0
    (OK (q with vs_inst_idx := SUC s.vs_inst_idx))` by
    (simp[gas_marked_path_def] >>
     drule gas_path_edge_normal >> simp[] >> strip_tac >>
     drule (cj 2 gas_path_rules) >>
     disch_then (qspec_then `0` mp_tac) >> simp[] >>
     disch_then irule >> irule (cj 1 gas_path_rules) >> simp[]) >>
  qexists_tac `q with vs_inst_idx := SUC s.vs_inst_idx` >>
  gvs[eval_operand_def, lookup_var_def, not_fresh_at_def] >>
  qpat_x_assum `q with vs_vars := _ = s`
    (mp_tac o Q.AP_TERM `\r. (~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb)`) >>
  simp[]
QED

Theorem assign_attr_stack_marked_read[local]:
  unwrap_value cenv (StackValue t arg) sm = (op,sb) /\
  vv_post ctx func cenv cx e es sa sm s0 ee raw (StackValue t arg) s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v u. gas_marked_exec F (ctx,func) (read_result cx raw) (ee,s)
      [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
       lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
       FLOOKUP u.vs_allocas aid = SOME b)
Proof
  strip_tac >>
  `?v. read_result cx raw ee = (INL v,ee)` by
    gvs[vv_post_def, vv_holds_def] >>
  `vv_post ctx func cenv cx e es sa sm s0 ee (Value v)
      (StackValue t arg) s` by metis_tac[vv_post_read_result] >>
  gvs[unwrap_value_def, comp_return_def] >>
  qexistsl_tac [`v`, `s`] >> simp[] >> conj_tac
  >- (simp[gas_marked_exec_def] >> conj_tac
      >- metis_tac[read_result_gas_obs] >>
      simp[gas_marked_path_def] >> irule (cj 1 gas_path_rules) >> simp[]) >>
  irule expr_post_of_vv_post_stack >> goal_assum drule
QED

Theorem assign_attr_storage_marked_read[local]:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  is_word_type (expr_type e) /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ fn_has_code sm sb func /\
  vv_post ctx func cenv cx e es sa sm s0 ee raw (LocatedValue t p) s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v u. gas_marked_exec F (ctx,func) (read_result cx raw) (ee,s)
      [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
       lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
       FLOOKUP u.vs_allocas aid = SOME b)
Proof
  strip_tac >>
  `t = expr_type e /\ ?w v. eval_operand p.ptr_operand s = SOME w /\
    read_result cx raw ee = (INL v,ee) /\
    storage_holds cx tr (expr_type e) (Value v) w ee s /\
    stmt_state_rel ctx func cenv cx ee s` by
    (Cases_on `tr` >> gvs[vv_post_def, vv_holds_def, storage_holds_def,
       read_result_def, return_def]) >>
  `vv_post ctx func cenv cx e es sa sm s0 ee (Value v)
     (LocatedValue t p) s` by metis_tac[vv_post_read_result] >>
  `emit_op (if tr then TLOAD else SLOAD) [p.ptr_operand] sm = (op,sb)` by
    (Cases_on `tr` >> gvs[unwrap_value_def, contextTheory.compile_ptr_load_def]) >>
  `!out. step_inst_base
      (mk_inst sm.cs_next_id (if tr then TLOAD else SLOAD)
        [p.ptr_operand] [out]) s =
      OK (update_var out (if tr then tload w s else sload w s) s)` by
    (Cases_on `tr` >> simp[step_inst_base_def, mk_inst_def, exec_read1_def]) >>
  `gas_path ctx func s 0
    (OK (update_var (STRING #"%" (toString sm.cs_next_var))
       (if tr then tload w s else sload w s) s
       with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule emit_op_zero_path >> simp[] >>
     qexistsl_tac [`[p.ptr_operand]`, `op`, `if tr then TLOAD else SLOAD`, `sb`] >>
     Cases_on `tr` >> simp[is_terminator_def]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    (drule emit_op_extends >> simp[same_blocks_def]) >>
  qabbrev_tac `u = update_var (STRING #"%" (toString sm.cs_next_var))
       (if tr then tload w s else sload w s) s
       with vs_inst_idx := SUC s.vs_inst_idx` >>
  `(!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
       lookup_var x u = SOME w) /\
   (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
       FLOOKUP u.vs_allocas aid = SOME b)` by
    (simp[Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >> gvs[not_fresh_at_def]) >>
  qexistsl_tac [`v`, `u`] >> conj_tac
  >- (simp[gas_marked_exec_def, gas_marked_path_def, Abbr `u`] >>
      metis_tac[read_result_gas_obs]) >>
  conj_tac
  >- (irule expr_post_of_vv_post_load >>
      goal_assum (drule_at Any) >> simp[] >> conj_tac
      >- (qexists_tac `if tr then tload w s else sload w s` >>
          simp[Abbr `u`, eval_operand_def, lookup_var_update_var, lookup_var_def,
               update_var_def, FLOOKUP_UPDATE] >>
          metis_tac[storage_holds_load]) >>
      conj_tac
      >- (simp[Abbr `u`, stmt_state_rel_inst_idx] >>
          irule stmt_state_rel_update_var >> simp[] >>
          irule local_ptrs_reserved_fresh >> qexists_tac `sm` >> simp[]) >>
      qexistsl_tac [`p`, `s`, `sm`, `t`] >> simp[Abbr `u`, update_var_def]) >>
  simp[Abbr `u`, update_var_def]
QED

Theorem assign_attr_emit_endpoint[local]:
  emit_op opc args sm = (op,sb) /\ fn_has_code sm sb func /\
  opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
  local_ptrs_reserved cenv sm /\ stmt_state_rel ctx func cenv cx ee s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!out. step_inst_base (mk_inst sm.cs_next_id opc args [out]) s =
         OK (update_var out w s)) ==>
  ?u. gas_path ctx func s 0 (OK u) /\ eval_operand op u = SOME w /\
    stmt_state_rel ctx func cenv cx ee u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x v. not_fresh_at sm x /\ lookup_var x s = SOME v ==>
       lookup_var x u = SOME v) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
       FLOOKUP u.vs_allocas aid = SOME b) /\
    u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section
Proof
  strip_tac >> drule_all emit_op_zero_path >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    (drule emit_op_extends >> simp_tac std_ss [same_blocks_def]) >>
  qexists_tac `update_var (STRING #"%" (toString sm.cs_next_var)) w s
    with vs_inst_idx := SUC s.vs_inst_idx` >>
  asm_simp_tac std_ss [eval_operand_def, lookup_var_def, update_var_def,
    venom_state_accfupds, FLOOKUP_UPDATE, stmt_state_rel_inst_idx,
    listTheory.LENGTH_APPEND, listTheory.LENGTH] >>
  conj_tac
  >- (pure_rewrite_tac [GSYM update_var_def] >>
      irule stmt_state_rel_update_var >> asm_simp_tac std_ss [] >>
      irule local_ptrs_reserved_fresh >> qexists_tac `sm` >>
      asm_simp_tac std_ss []) >>
  asm_simp_tac std_ss [update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> fs[not_fresh_at_def] >>
  `x <> STRING #"%" (toString sm.cs_next_var)` by
    (first_x_assum irule >> simp[]) >>
  simp[FLOOKUP_UPDATE]
QED

Theorem assign_attr_immutable_load_path[local]:
  compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca pop sm = (op,sb) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  stmt_state_rel ctx func cenv cx ee s /\ eval_operand pop s = SOME a /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_path ctx func s 0 (OK u) /\
    eval_operand op u = SOME
      (if cenv.ce_is_ctor then mload (w2n a) s else
       word_of_bytes T (0w:bytes32)
         (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) /\
    stmt_state_rel ctx func cenv cx ee u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x v. not_fresh_at sm x /\ lookup_var x s = SOME v ==>
       lookup_var x u = SOME v) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
       FLOOKUP u.vs_allocas aid = SOME b) /\ u.vs_memory = s.vs_memory
Proof
  strip_tac >> Cases_on `cenv.ce_is_ctor`
  >- (Cases_on `cenv.ce_imm_alloca`
      >- (gvs[contextTheory.compile_imm_load_word_def] >>
          `!out. step_inst_base (mk_inst sm.cs_next_id ILOAD [pop] [out]) s =
            OK (update_var out (mload (w2n a) s) s)` by
            simp[step_inst_base_def, mk_inst_def, exec_read1_def] >>
          drule_at (Pat `emit_op`) assign_attr_emit_endpoint >>
          simp[is_terminator_def] >> disch_then drule_all >>
          strip_tac >> qexists_tac `u` >> simp[]) >>
      gvs[contextTheory.compile_imm_load_word_def, comp_bind_def] >>
      pairarg_tac >> gvs[] >>
      rename1 `emit_op ADD [pop; ib] sm = (addr,mid)` >>
      `cs_extends sm mid /\ cs_extends mid sb` by
        (conj_tac >>
         `!opc args st op st'. emit_op opc args st = (op,st') ==>
            cs_extends st st'` by
           (rpt strip_tac >>
            `cs_appends (emit_op opc args)` by simp[cs_appends_emit_helpers] >>
            gvs[cs_appends_def] >> first_x_assum drule >> simp[]) >>
         metis_tac[]) >>
      `fn_has_code sm mid func /\ fn_has_code mid sb func` by
        metis_tac[fn_has_code_split] >>
      `eval_operand ib s = SOME 0w` by
        gvs[stmt_state_rel_def, immutable_base_zero_def] >>
      `!out. step_inst_base (mk_inst sm.cs_next_id ADD [pop; ib] [out]) s =
         OK (update_var out a s)` by
        (gen_tac >> irule immutable_word_add_zero >> simp[]) >>
      qpat_assum `emit_op ADD _ _ = _`
        (mp_then (Pat `emit_op`) mp_tac assign_attr_emit_endpoint) >>
      simp[is_terminator_def] >> disch_then drule_all >> strip_tac >>
      rename1 `gas_path ctx func s 0 (OK u1)` >>
      `sm.cs_next_var <= mid.cs_next_var` by
        (drule emitted_insts_emit_op >> simp[]) >>
      `local_ptrs_reserved cenv mid` by
        (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> simp[]) >>
      `!out. step_inst_base (mk_inst mid.cs_next_id ILOAD [addr] [out]) u1 =
         OK (update_var out (mload (w2n a) s) u1)` by
        simp[step_inst_base_def, mk_inst_def, exec_read1_def, mload_def] >>
      qpat_assum `emit_op ILOAD _ _ = _`
        (mp_then (Pat `emit_op`) mp_tac assign_attr_emit_endpoint) >>
      simp[is_terminator_def] >> disch_then drule_all >> strip_tac >>
      rename1 `gas_path ctx func u1 0 (OK u2)` >>
      qexists_tac `u2` >> simp[] >> conj_tac
      >- metis_tac[gas_path_then, arithmeticTheory.ADD_CLAUSES] >>
      metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  gvs[contextTheory.compile_imm_load_word_def] >>
  `!out. step_inst_base (mk_inst sm.cs_next_id DLOAD [pop] [out]) s =
    OK (update_var out (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) s)` by
    (gen_tac >> irule step_DLOAD >> simp[]) >>
  drule_at (Pat `emit_op`) assign_attr_emit_endpoint >>
  simp[is_terminator_def] >> disch_then drule_all >>
  strip_tac >> qexists_tac `u` >> simp[]
QED

Theorem assign_attr_immutable_marked_read[local]:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocCode /\
  is_word_type (expr_type e) /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ fn_has_code sm sb func /\
  vv_post ctx func cenv cx e es sa sm s0 ee raw (LocatedValue t p) s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v u. gas_marked_exec F (ctx,func) (read_result cx raw) (ee,s)
      [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
       lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
       FLOOKUP u.vs_allocas aid = SOME b)
Proof
  strip_tac >>
  `t = expr_type e /\ ?a v. eval_operand p.ptr_operand s = SOME a /\
    read_result cx raw ee = (INL v,ee) /\
    immutable_holds cenv cx (expr_type e) (Value v) a ee s /\
    stmt_state_rel ctx func cenv cx ee s` by
    (gvs[vv_post_def, vv_holds_def, immutable_holds_def,
         read_result_def, return_def] >>
     qexistsl_tac [`name`, `off`, `itv`, `iv`, `k`] >> simp[]) >>
  `vv_post ctx func cenv cx e es sa sm s0 ee (Value v)
     (LocatedValue t p) s` by metis_tac[vv_post_read_result] >>
  `compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca
     p.ptr_operand sm = (op,sb)` by
    gvs[unwrap_value_def, contextTheory.compile_ptr_load_def] >>
  drule_all assign_attr_immutable_load_path >> strip_tac >>
  `!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
    (if cenv.ce_is_ctor then mload (w2n a) s else
      word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) =
    typed_val_to_w256 tvt v` by
    (Cases_on `cenv.ce_is_ctor` >>
     metis_tac[immutable_holds_iload, immutable_holds_dload, optionTheory.SOME_11]) >>
  qexistsl_tac [`v`, `u`] >> conj_tac
  >- (simp[gas_marked_exec_def, gas_marked_path_def] >>
      metis_tac[read_result_gas_obs]) >>
  conj_tac
  >- (irule expr_post_of_vv_post_load >> goal_assum (drule_at Any) >>
      simp[] >> qexistsl_tac [`p`, `s`, `sm`, `t`] >> simp[]) >>
  simp[]
QED

Theorem assign_attr_ghost_regions[local]:
  local_ptrs_rel func cenv scopes s0 /\ local_ptrs_reserved cenv sa /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
    lookup_var x s = SOME w) ==>
  !n b sz. local_region cenv scopes (s0 with vs_vars := s.vs_vars) n b sz <=>
    local_region cenv scopes s0 n b sz
Proof
  strip_tac >> rpt gen_tac >> eq_tac
  >- (strip_tac >> irule local_region_frame >> conj_tac
      >- (qexists_tac `func` >> simp[]) >>
      qexistsl_tac [`sa`, `scopes`, `s`] >>
      simp[] >> gvs[local_region_def, lookup_var_def]) >>
  strip_tac >>
  `local_region cenv scopes s n b sz` by
    (irule local_region_frame_fwd >>
     qexistsl_tac [`s0`, `sa`, `scopes`] >> simp[]) >>
  gvs[local_region_def, lookup_var_def]
QED

Theorem assign_attr_ghost_vv_post[local]:
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  vv_post ctx func cenv cx e es sa sm s0 ee raw (LocatedValue t p) s ==>
  vv_post ctx func cenv cx e es (sa with cs_next_var := sm.cs_next_var)
    sm (s0 with vs_vars := s.vs_vars) ee raw (LocatedValue t p) s
Proof
  strip_tac >>
  `local_ptrs_rel func cenv es.scopes s0` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
    lookup_var x s = SOME w` by gvs[vv_post_def] >>
  drule_all assign_attr_ghost_regions >> strip_tac >>
  gvs[vv_post_def, vv_at_def, lookup_var_def, locals_kept_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem assign_attr_ghost_expr_post[local]:
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  vv_post ctx func cenv cx e es sa sm s0 ee raw (LocatedValue t p) s /\
  expr_post ctx func cenv cx e es (sa with cs_next_var := sm.cs_next_var)
    sb (s0 with vs_vars := s.vs_vars) ee v op u ==>
  expr_post ctx func cenv cx e es sa sb s0 ee v op u
Proof
  strip_tac >>
  `local_ptrs_rel func cenv es.scopes s0` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
    lookup_var x s = SOME w` by gvs[vv_post_def] >>
  drule_all assign_attr_ghost_regions >> strip_tac >>
  gvs[expr_post_def, expr_val_at_def, lookup_var_def, locals_kept_def,
      not_fresh_at_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem assign_attr_path_nonhalting[local]:
  !ctx fn s n r. gas_path ctx fn s n r ==> !u. r = OK u ==> ~u.vs_halted
Proof
  Induct_on `gas_path` >> rw[] >> gvs[exit_result_def]
QED

Theorem assign_attr_word_marked_read[local]:
  unwrap_value cenv vv sm = (op,sb) /\
  is_word_type (expr_type e) /\ local_ptrs_reserved cenv sm /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  sa.cs_next_var <= sm.cs_next_var /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\
  vv_post ctx func cenv cx e es sa sm s0 ee raw vv s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v u. gas_marked_exec F (ctx,func) (read_result cx raw) (ee,s)
      [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
       lookup_var x u = SOME w)
Proof
  strip_tac >> Cases_on `vv`
  >- (drule_all assign_attr_stack_marked_read >> strip_tac >>
      qexistsl_tac [`v`, `u`] >> simp[]) >>
  rename1 `LocatedValue t p` >> Cases_on `p.ptr_location`
  >- (drule_all assign_attr_ghost_vv_post >> strip_tac >>
      drule_at (Pat `vv_post`) unwrap_memory_marked_read >>
      simp[] >> strip_tac >>
      `expr_post ctx func cenv cx e es sa sb s0 ee v op u` by
        (irule assign_attr_ghost_expr_post >> goal_assum (drule_at Any) >>
         simp[] >> metis_tac[]) >>
      qexistsl_tac [`v`, `u`] >> simp[] >> conj_tac
      >- (gvs[gas_marked_exec_def, gas_marked_path_def] >>
          metis_tac[assign_attr_path_nonhalting]) >>
      gvs[expr_post_def, not_fresh_at_def, lookup_var_def])
  >- (mp_tac (Q.INST [`tr` |-> `F`] assign_attr_storage_marked_read) >>
      simp[] >> strip_tac >>
      qexistsl_tac [`v`, `u`] >> simp[])
  >- (mp_tac (Q.INST [`tr` |-> `T`] assign_attr_storage_marked_read) >>
      simp[] >> strip_tac >>
      qexistsl_tac [`v`, `u`] >> simp[])
  >- (drule_all assign_attr_immutable_marked_read >> strip_tac >>
      qexistsl_tac [`v`, `u`] >> simp[]) >>
  gvs[vv_post_def, vv_holds_def]
QED

(* ===== The source ===== *)

Theorem struct_field_slot_alookup[local]:
  !fs id off ftv.
    struct_field_slot fs id = SOME (off, ftv) ==> ALOOKUP fs id = SOME ftv
Proof
  Induct >> simp[struct_field_slot_def] >> PairCases >> rpt gen_tac >>
  simp[struct_field_slot_def] >> IF_CASES_TAC >> simp[] >>
  strip_tac >> gvs[] >> rename1 `struct_field_slot fs id = SOME q` >>
  PairCases_on `q` >> gvs[] >> metis_tac[]
QED

(* A field of a storage struct: the slot plus the field's slot offset, at
   the field's type; any other case is a type error. *)
Theorem extend_storage_place_attr:
  !cx tr slot tv fld es r es'.
    extend_storage_place cx tr slot tv (AttrSubscript fld) es = (r, es') /\
    (!m. r <> INR (Error (TypeError m))) ==>
    es' = es /\
    ?fs off ftv. tv = StructTV fs /\ struct_field_slot fs fld = SOME (off, ftv) /\
                 r = INL (StoragePlace tr (slot + n2w off) ftv)
Proof
  rpt gen_tac >> Cases_on `tv` >>
  simp[extend_storage_place_def, raise_def, bind_def, lift_option_type_def,
       return_def]
  >~ [`struct_field_slot l fld`]
  >- (Cases_on `struct_field_slot l fld` >> simp[raise_def, return_def] >>
      rename1 `SOME q` >> PairCases_on `q` >> simp[return_def] >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem eval_target_place_attr_toplevel:
  !cx src id fld ts tr typ id_str slot es r es'.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    eval_target_place cx (AttributeTarget (TopLevelNameTarget (src, id)) fld)
      es = (r, es') /\
    (!m. r <> INR (Error (TypeError m))) ==>
    es' = es /\
    ?fs off ftv.
      evaluate_type (get_tenv cx) typ = SOME (StructTV fs) /\
      struct_field_slot fs fld = SOME (off, ftv) /\
      r = INL (StoragePlace tr (n2w slot + n2w off) ftv)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, LET_THM] >>
  Cases_on `evaluate_type (get_tenv cx) typ` >>
  simp[raise_def, return_def, extend_place_def, bind_def] >>
  TRY (strip_tac >> gvs[] >> NO_TAC) >>
  rename1 `extend_storage_place cx tr _ tv` >>
  Cases_on `extend_storage_place cx tr (n2w slot) tv (AttrSubscript fld) es` >>
  rename1 `_ = (r1, es1)` >>
  drule extend_storage_place_attr >> strip_tac >>
  Cases_on `r1` >> simp[return_def, get_place_def] >> strip_tac >> gvs[]
QED

(* self.x.f = e, unless it fails with a type error: e's forced value r,
   and on an error that error, on a value v the write of v at f's slot. *)
Theorem eval_assign_attr_toplevel:
  !cx src id fld e es res es' ts tr typ id_str slot.
    eval_stmt cx
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld))
         e) es = (res, es') /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    (!m. res <> INR (Error (TypeError m))) ==>
    ?r es1.
      (do result <- eval_expr cx e; read_result cx result od) es = (r, es1) /\
      (!ex. r = INR ex ==> res = INR ex /\ es' = es1) /\
      (!v. r = INL v ==>
           ?fs off ftv.
             evaluate_type (get_tenv cx) typ = SOME (StructTV fs) /\
             struct_field_slot fs fld = SOME (off, ftv) /\
             write_storage_slot cx tr (n2w slot + n2w off) ftv v es1 =
               (res, es'))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `eval_expr cx e es = (r1, es1)` >>
  Cases_on `r1` >> simp[] >>
  rename1 `eval_expr cx e es = (INL pv, es1)` >>
  Cases_on `eval_target_place cx
              (AttributeTarget (TopLevelNameTarget (src, id)) fld) es1` >>
  rename1 `_ = (r2, es2)` >>
  drule eval_target_place_attr_toplevel >> rpt (disch_then drule) >>
  strip_tac >>
  Cases_on `r2` >> simp[]
  >- (gvs[] >> Cases_on `read_result cx pv es1` >>
      rename1 `read_result cx pv es1 = (r3, es3)` >>
      imp_res_tac read_result_state >> gvs[] >>
      Cases_on `r3` >> simp[write_place_def] >> metis_tac[]) >>
  strip_tac >> gvs[]
QED

Theorem eval_assign_attr_toplevel_action:
  eval_stmt cx
    (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld)) e) =
  bind (eval_expr cx e)
    (\pv. do
      p <- eval_target_place cx
        (AttributeTarget (TopLevelNameTarget (src, id)) fld);
      v <- read_result cx pv;
      write_place cx p v
    od)
Proof
  simp[Once evaluate_def]
QED

Theorem eval_target_place_attr_toplevel_action[local]:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME (StructTV fs) /\
  struct_field_slot fs fld = SOME (off, ftv) ==>
  eval_target_place cx
    (AttributeTarget (TopLevelNameTarget (src, id)) fld) =
  return (StoragePlace tr (n2w slot + n2w off) ftv)
Proof
  strip_tac >> simp[FUN_EQ_THM, Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, lookup_global_def, lift_option_type_def,
       bind_def, return_def, extend_place_def, extend_storage_place_def,
       get_place_def]
QED

Theorem assign_attr_storage_tail[local]:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME (StructTV fs) /\
  struct_field_slot fs fld = SOME (off, ftv) /\
  read_result cx raw ee = (INL v, ee) /\
  write_storage_slot cx tr (n2w slot + n2w off) ftv v ee = (res, ee') ==>
  !tail.
    (do
      p <- eval_target_place cx
        (AttributeTarget (TopLevelNameTarget (src, id)) fld);
      v <- read_result cx raw;
      write_place cx p v
    od) (ee with gas_obs := tail) = (res, ee' with gas_obs := tail)
Proof
  strip_tac >> drule_all eval_target_place_attr_toplevel_action >>
  disch_then SUBST1_TAC >>
  drule read_result_gas_obs >> strip_tac >>
  simp[bind_def, return_def, write_place_def, write_storage_slot_gas_obs]
QED

(* What self.x.f = e does on each outcome of e, with the typing that makes
   the write a one-slot store: f's slot is x's slot plus the offset the
   lowering's struct table gives, and e's value encodes there as its typed
   word. *)
Theorem assign_attr_storage_source:
  !cx cenv env lctx src id fld sid fty fsz e es res es' ts tr id_str slot.
    eval_stmt cx
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld))
         e) es = (res, es') /\
    stmt_res_ok lctx res /\ expr_body_pre cenv cx env e es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    is_word_type fty /\ expr_type e = fty ==>
    ?r es1.
      (do result <- eval_expr cx e; read_result cx result od) es = (r, es1) /\
      expr_res_ok r /\
      (!ex. r = INR ex ==> res = INR ex /\ es' = es1) /\
      (!v. r = INL v ==>
           ?ftv. evaluate_type (get_tenv cx) fty = SOME ftv /\
                 encode_value ftv v = SOME [(0, typed_val_to_w256 ftv v)] /\
                 write_storage_slot cx tr
                   (n2w slot + n2w (struct_field_offset_slots
                      (get_struct_fields cenv.ce_struct_fields
                         (nsid_to_string sid)) fld))
                   ftv v es1 = (res, es') /\
                 !u st.
                   storage_dead cx tr
                     (update_storage
                        (n2w slot + n2w (struct_field_offset_slots
                           (get_struct_fields cenv.ce_struct_fields
                              (nsid_to_string sid)) fld)) u st) =
                   storage_dead cx tr st)
Proof
  rpt gen_tac >> strip_tac >>
  `!m. res <> INR (Error (TypeError m))` by
    (rpt strip_tac >> gvs[stmt_res_ok_def]) >>
  drule_all eval_assign_attr_toplevel >> strip_tac >>
  qexistsl_tac [`r`, `es1`] >> simp[] >>
  conj_tac >- (irule expr_body_pre_res_ok >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  rename1 `struct_field_slot fs fld = SOME (off, ftv)` >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_offset_slots_eq >> strip_tac >> gvs[] >>
  drule_all struct_field_type >> strip_tac >>
  imp_res_tac struct_field_slot_alookup >> gvs[] >>
  drule_all expr_body_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  gvs[expr_result_typed_def, expr_runtime_typed_def,
      value_result_typed_def] >>
  rpt conj_tac
  >~ [`storage_dead`]
  >- (rpt gen_tac >> irule storage_dead_update_struct_word_field >>
      qexistsl_tac [`fld`, `fs`, `ftv`, `src`, `id`] >>
      simp[vyperStorageLayoutSafetyTheory.declared_storage_region_def] >>
      metis_tac[exprSimUnwrapTheory.word_type_slot_size]) >>
  irule encode_value_word_typed >> metis_tac[]
QED

Theorem assign_attr_storage_source_counted[local]:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid), id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
    fld = SOME (fty, fsz) /\
  is_word_type fty /\ expr_type e = fty /\
  expr_body_pre cenv cx env e es /\
  gas_admissible
    (eval_stmt cx
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e))
    (stmt_res_ok lctx) es /\
  eval_expr cx e (es with gas_obs := gs) = (INL raw, ee) /\
  read_result cx raw ee = (INL v, ee) ==>
  ?fs off ftv res ee'.
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    struct_field_slot fs fld = SOME (off, ftv) /\
    off = struct_field_offset_slots
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld /\
    evaluate_type (get_tenv cx) fty = SOME ftv /\
    encode_value ftv v = SOME [(0, typed_val_to_w256 ftv v)] /\
    write_storage_slot cx tr (n2w slot + n2w off) ftv v ee = (res, ee') /\
    (!tail.
      (do
        p <- eval_target_place cx
          (AttributeTarget (TopLevelNameTarget (src,id)) fld);
        v <- read_result cx raw;
        write_place cx p v
      od) (ee with gas_obs := tail) = (res, ee' with gas_obs := tail)) /\
    (!u st. storage_dead cx tr
       (update_storage (n2w slot + n2w off) u st) = storage_dead cx tr st)
Proof
  strip_tac >>
  Cases_on `eval_stmt cx
    (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e)
    (es with gas_obs := gs)` >>
  rename1 `_ = (res, ee')` >>
  `stmt_res_ok lctx res` by (drule_all gas_admissible_result >> simp[]) >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  `!m. res <> INR (Error (TypeError m))` by
    (rpt strip_tac >> gvs[stmt_res_ok_def]) >>
  drule_all eval_assign_attr_toplevel >>
  simp[bind_def] >> strip_tac >>
  drule_all assign_attr_storage_source >> simp[bind_def] >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_offset_slots_eq >> strip_tac >> gvs[] >>
  drule_all struct_field_type >> strip_tac >>
  imp_res_tac struct_field_slot_alookup >> gvs[] >>
  drule_all assign_attr_storage_tail >> simp[bind_def]
QED

(* ===== The code ===== *)

(* The code of self.x.f = e for a storage or transient struct x and f of
   a word type: e's code, the ADD of f's slot offset to x's slot, e's
   unwrap, then one SSTORE or TSTORE at the field's slot. *)
Theorem assign_attr_storage_code_parts:
  !cenv lctx ty src id fld e sa c sf tr slot sid fty fsz.
    stmt_env cenv lctx ty
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id)) fld))
         e) sa = (c, sf) /\
    FLOOKUP cenv.ce_module_vars (src, id) =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    is_word_type fty /\ is_word_type (expr_type e) ==>
    c = cenv /\
    ?vv sm dst sn op su.
      compile_expr cenv (expr_type e) e sa = (vv, sm) /\
      emit_op ADD
        [Lit slot; Lit (n2w (struct_field_offset_slots
           (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
           fld))] sm = (dst, sn) /\
      unwrap_value cenv vv sn = (op, su) /\
      emit_void (if tr then TSTORE else SSTORE) [dst; op] su = ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  `~has_length_word (expr_type e)` by
    metis_tac[is_word_type_no_length_word] >>
  drule_all compile_get_target_ptr_toplevel >> strip_tac >>
  drule stmt_env_assign >> strip_tac >> gvs[] >>
  rename1 `FLOOKUP cenv.ce_module_vars _` >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  asm_simp_tac (srw_ss())
    [compile_stmt_def, compile_assign_value_def, comp_bind_def,
     comp_ignore_bind_def, comp_return_def, LET_THM] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv, sm)` >> simp[] >>
  asm_simp_tac (srw_ss())
    [Once compile_get_target_ptr_def, comp_bind_def, comp_return_def,
     LET_THM] >>
  qmatch_goalsub_abbrev_tac `emit_op ADD [Lit slot; Lit (n2w off)] sm` >>
  Cases_on `emit_op ADD [Lit slot; Lit (n2w off)] sm` >>
  rename1 `emit_op _ _ _ = (dst, sn)` >> simp[] >>
  Cases_on `unwrap_value cenv vv sn` >>
  rename1 `unwrap_value _ _ _ = (op, su)` >> simp[]
  >- (Cases_on `emit_void TSTORE [dst; op] su` >>
      rename1 `emit_void _ _ _ = (u, sc)` >> Cases_on `u` >>
      simp[comp_bind_def, comp_return_def]) >>
  Cases_on `emit_void SSTORE [dst; op] su` >>
  rename1 `emit_void _ _ _ = (u, sc)` >> Cases_on `u` >>
  simp[comp_bind_def, comp_return_def]
QED

(* An SSTORE or TSTORE at a variable holding a slot, run. *)
Theorem store_var_frag:
  !ctx func cenv cx es' s1 tr d a op w st st' R.
    emit_void (if tr then TSTORE else SSTORE) [Var d; op] st = ((), st') /\
    lookup_var d s1 = SOME a /\ eval_operand op s1 = SOME w /\
    stmt_state_rel ctx func cenv cx es'
      (if tr then tstore a w s1 else sstore a w s1) ==>
    frag_exec ctx st st' (\t. t = s1)
      (\t. stmt_state_rel ctx func cenv cx es' t /\
           (!x. lookup_var x t = lookup_var x s1) /\
           (!aid b. FLOOKUP s1.vs_allocas aid = SOME b ==>
                    FLOOKUP t.vs_allocas aid = SOME b)) R
Proof
  rpt strip_tac >>
  `eval_operand (Var d) s1 = SOME a` by simp[eval_operand_def] >>
  drule_all storage_emit_frame_frag >>
  disch_then (qspec_then `R` mp_tac) >>
  disch_then (mp_then Any irule frag_exec_weaken) >> simp[]
QED

Theorem assign_attr_storage_word_suffix[local]:
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  emit_op ADD [Lit (n2w slot); Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value cenv vv sn = (op,su) /\
  emit_void (if tr then TSTORE else SSTORE) [dst;op] su = ((),sf) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sn /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_var <= sn.cs_next_var /\
  stmt_state_rel ctx func cenv cx es s0 /\ is_word_type (expr_type e) /\
  fn_has_code sm sn func /\ fn_has_code sn su func /\
  fn_has_code su sf func /\ fn_inst_ids_distinct func /\
  vv_post ctx func cenv cx e es sa sm s0 ee raw vv s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ ee.gas_obs = [] /\
  (!v. read_result cx raw ee = (INL v,ee) ==>
    ?ftv res ee'.
      evaluate_type (get_tenv cx) (expr_type e) = SOME ftv /\
      encode_value ftv v = SOME [(0,typed_val_to_w256 ftv v)] /\
      write_storage_slot cx tr (n2w slot + n2w off) ftv v ee = (res,ee') /\
      (!tail. k raw (ee with gas_obs := tail) =
        (res,ee' with gas_obs := tail)) /\
      (!u st. storage_dead cx tr
        (update_storage (n2w slot + n2w off) u st) = storage_dead cx tr st)) ==>
  ?res ee' r.
    (!tail. k raw (ee with gas_obs := tail) = (res,ee' with gas_obs := tail)) /\
    gas_marked_path F ctx func s 0 r /\
    ?t'. r = OK t' /\ stmt_post ctx func cx lctx cenv cenv sa sf s0 res
      (ee' with gas_obs := []) t'
Proof
  strip_tac >>
  drule_all assign_attr_add_marked >> strip_tac >>
  drule_all assign_attr_word_marked_read >> strip_tac >>
  `read_result cx raw ee = (INL v,ee)` by
    (`ee with gas_obs := [] = ee` by
       simp[evaluation_state_component_equality] >>
     qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o cj 1 o REWRITE_RULE [gas_marked_exec_def]) >>
     disch_then (qspec_then `[]` mp_tac) >>
     simp[gas_explicit_def]) >>
  qpat_x_assum `!v. read_result cx raw ee = _ ==> _` drule >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) (expr_type e) = SOME ftv` >>
  `eval_operand dst u = SOME (n2w slot + n2w off)` by
    (gvs[eval_operand_def] >> metis_tac[]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `eval_operand op u = SOME (typed_val_to_w256 ftv v)` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  drule_all stmt_state_rel_write_storage_word >> strip_tac >> gvs[] >>
  `~u.vs_call_ctx.cc_static` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def] >>
  `gas_marked_path F ctx func u 0
    (OK ((if tr then tstore (n2w slot + n2w off) (typed_val_to_w256 ftv v) u
          else sstore (n2w slot + n2w off) (typed_val_to_w256 ftv v) u)
      with vs_inst_idx := SUC u.vs_inst_idx))` by
    (irule emit_inst_zero_marked_path >> simp[] >>
     qexistsl_tac [`[Var d;op]`, `if tr then TSTORE else SSTORE`, `[]`, `su`, `sf`] >>
     Cases_on `tr` >> gvs[emit_void_def,emit_inst_def,is_terminator_def] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     fs[mk_inst_def,exec_write2_def]) >>
  `~block_is_terminated sf` by
    (drule emit_void_terminated >> Cases_on `tr` >> simp[is_terminator_def]) >>
  `sf.cs_current_bb = su.cs_current_bb /\
   LENGTH sf.cs_current_insts = SUC (LENGTH su.cs_current_insts)` by
    (Cases_on `tr` >>
     gvs[emit_void_def,comp_bind_def,fresh_id_def,comp_ignore_bind_def,
         comp_return_def,emit_def]) >>
  `ee'.gas_obs = []` by
    (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
     simp[write_storage_slot_eq] >> Cases_on `tr` >>
     simp[set_storage_def] >> rw[] >> gvs[]) >>
  `ee' with gas_obs := [] = ee'` by
    simp[evaluation_state_component_equality] >>
  qexistsl_tac [`INL ()`, `ee'`,
    `OK ((if tr then tstore (n2w slot + n2w off) (typed_val_to_w256 ftv v) u
          else sstore (n2w slot + n2w off) (typed_val_to_w256 ftv v) u)
      with vs_inst_idx := SUC u.vs_inst_idx)`] >>
  simp[] >> conj_tac
  >- (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
      simp[gas_marked_exec_def] >> strip_tac >>
      metis_tac[gas_marked_path_then,ADD_CLAUSES]) >>
  simp[stmt_post_def,stmt_lands_def,cenv_top_ext_refl,
       stmt_state_rel_inst_idx] >>
  Cases_on `tr` >>
  gvs[sstore_def,tstore_def,lookup_var_def,LET_THM]
QED

(* self.x.f = e for a storage or transient struct x the lowering holds by
   slot (no hashmap) and a field f of a word type that e has, for every
   outcome: e's errors exit, and on a value its word is stored at the
   field's slot.  e may call internal functions: its simulation is a
   premise. *)
Theorem compile_assign_attr_storage_case:
  !ctx func cx lctx RetQ cenv ty env src id fld sid fty fsz e es ts
   tr id_str slot.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    is_word_type fty /\ expr_type e = fty /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    expr_body_pre cenv cx env e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id))
            fld)) e))
      (eval_stmt cx
         (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id))
            fld)) e))
      es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def,stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  `FLOOKUP cenv.ce_module_vars (src, id) =
     SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
    (irule toplevel_storage_ce_vars >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  `is_word_type (expr_type e)` by simp[] >>
  drule_all assign_attr_storage_code_parts >> strip_tac >>
  gvs[] >> rename1 `emit_void _ _ su = ((),sf)` >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn su /\ ci_mono su sf` by
    metis_tac[compile_expr_ci_mono,ci_mono_emit_op,ci_mono_unwrap_value,
              ci_mono_emit_void,pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\
   fn_has_code sn su func /\ fn_has_code su sf func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split,cs_extends_trans]) >>
  irule forced_vv_then_stmt_outcome >>
  qexistsl_tac [
    `\raw ee t. vv_post ctx func cenv cx e es sa sm s0 ee raw vv t /\
      t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts`, `e`,
    `\raw. do p <- eval_target_place cx
       (AttributeTarget (TopLevelNameTarget (src,id)) fld);
       v <- read_result cx raw; write_place cx p v od`] >>
  reverse conj_tac
  >- (conj_tac >- simp[eval_assign_attr_toplevel_action] >>
      qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_vv_sim_def]) >>
      disch_then (qspecl_then [`sa`,`sm`,`vv`,`s0`] mp_tac) >>
      impl_tac >- (simp[] >> metis_tac[expr_body_pre_vv_gas_admissible]) >>
      simp[]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  `local_ptrs_reserved cenv sn /\ sa.cs_next_var <= sm.cs_next_var /\
   sa.cs_next_var <= sn.cs_next_var` by
    (fs[ci_mono_def,cs_extends_def] >>
     metis_tac[local_ptrs_reserved_next_var]) >>
  `!v. read_result cx tv ee = (INL v,ee) ==>
    ?ftv res ee'.
      evaluate_type (get_tenv cx) (expr_type e) = SOME ftv /\
      encode_value ftv v = SOME [(0,typed_val_to_w256 ftv v)] /\
      write_storage_slot cx tr (n2w slot + n2w (struct_field_offset_slots
        (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))
        ftv v ee = (res,ee') /\
      (!tail. (do p <- eval_target_place cx
        (AttributeTarget (TopLevelNameTarget (src,id)) fld);
        v <- read_result cx tv; write_place cx p v od)
        (ee with gas_obs := tail) = (res,ee' with gas_obs := tail)) /\
      (!u st. storage_dead cx tr (update_storage
        (n2w slot + n2w (struct_field_offset_slots
          (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))
        u st) = storage_dead cx tr st)` by
    (rpt strip_tac >>
     drule_all (SRULE [] (Q.INST [`fty` |-> `expr_type e`]
       assign_attr_storage_source_counted)) >>
     strip_tac >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all (SRULE [] (Q.INST [`k` |-> `\raw. do
    p <- eval_target_place cx (AttributeTarget (TopLevelNameTarget (src,id)) fld);
    v <- read_result cx raw; write_place cx p v od`]
    assign_attr_storage_word_suffix)) >>
  disch_then (qspec_then `lctx` strip_assume_tac) >>
  qexistsl_tac [`res`,`ee'`,`r`] >> simp[]
QED

(* compile_assign_attr_storage_case for an e with no internal call. *)
Theorem compile_assign_attr_storage_stmt_frag:
  !ctx func cx lctx RetQ cenv ty env src id fld sid fty fsz e es ts
   tr id_str slot.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid), id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
      fld = SOME (fty, fsz) /\
    is_word_type fty /\ expr_type e = fty /\
    expr_vv_ok cenv e /\ expr_sim_pre cenv cx env e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id))
            fld)) e))
      (eval_stmt cx
         (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src, id))
            fld)) e))
      es
Proof
  rpt strip_tac >> irule compile_assign_attr_storage_case >>
  `expr_body_pre cenv cx env e es` by fs[expr_sim_pre_body] >>
  `expr_vv_sim ctx func cenv cx (expr_type e) e es` by
    metis_tac[expr_vv_ok_def] >>
  simp[] >> metis_tac[]
QED
