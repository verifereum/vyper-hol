(* The forced memory judgment from the value one: the memory twin of
   exprSimUnwrap's expr_sim_of_vv_sim, through unwrap_value's code. *)
Theory exprSimMemUnwrap
Ancestors
  exprSimMemDefs exprSimUnwrap exprSimDefs loweringPosts gasOutcome
  exprLowering compileEnv vyperInterpreter vyperState
  exprSimUnwrapProps exprSimProps exprSimMemorySource bodyFieldMemoryProps
  gasSummary gasSummaryCompose gasExemptCert fragGasMode fragGasPath
  fragGasPathMem fragGasSeqMem fragExecMem instMemFrontier allocaHistoryFragment
  emitHelperProps emitHelper exprLoweringProps loweringSlice context
  bodyImmutableUnwrapMemory memSafeRun exprSimAccounts
  fragExec exprOperandVar vyperEvalExprPreservesScopesDom
  exprSimAlloc exprSimStorageCopy exprSimCopy storageCopyGasPath
  immutableCopyExecution bodyImmutableCopyMemory bodyStorageCopyMemory
  bodyAllocMemory bodyDeclMemoryCounted valueEncodingProps abiBuiltinAllocation
  freshWrites allocaHistory immutableMemoryFrame venomMemDefs
  venomExecSemantics venomInst venomState list rich_list finite_map
  valueCopyBytes

(* A word's rounded footprint is its one word. *)
Theorem word_val_store_size[local]:
  is_word_type t /\ evaluate_type tenv t = SOME tv ==> val_store_size tv v = 32
Proof
  strip_tac >> drule_all word_tv_memory_size >> strip_tac >>
  Cases_on `t` >> gvs[is_word_type_def]
  >- (rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_word_type_def] >>
      TRY (rename1 `BytesT bd` >> Cases_on `bd` >> gvs[is_word_type_def]) >>
      gvs[vyperValueTheory.evaluate_type_def] >>
      Cases_on `v` >> simp[val_store_size_def]) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> simp[val_store_size_def]
QED

(* One emitted instruction that writes only its output, memory-checked. *)
Theorem emit_op_path_mem[local]:
  !ctx func cenv cx es opc args sa op sb s0 w.
    emit_op opc args sa = (op, sb) /\ local_ptrs_reserved cenv sa /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    opc <> INVOKE /\ opc <> GAS /\ opc <> ALLOCA /\ ~is_terminator opc /\
    stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
    ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!out. inst_mem_below_frontier (mk_inst sa.cs_next_id opc args [out]) s0 /\
           inst_dload_in_section (mk_inst sa.cs_next_id opc args [out]) s0) /\
    (!out. step_inst_base (mk_inst sa.cs_next_id opc args [out]) s0 =
           OK (update_var out w s0)) ==>
    ?s. gas_path_mem ctx func s0 0 (OK s) /\
        s.vs_current_bb = sb.cs_current_bb /\
        s.vs_inst_idx = LENGTH sb.cs_current_insts /\
        stmt_state_rel ctx func cenv cx es s /\ eval_operand op s = SOME w /\
        (!x w'. not_fresh_at sa x /\ lookup_var x s0 = SOME w' ==>
                lookup_var x s = SOME w') /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                 FLOOKUP s.vs_allocas aid = SOME b) /\
        s.vs_memory = s0.vs_memory /\
        s.vs_alloca_next = s0.vs_alloca_next /\ alloca_history func s
Proof
  rpt strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id opc args [out]` >>
  qexists_tac `update_var out w s0 with vs_inst_idx := SUC s0.vs_inst_idx` >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `not_local_ptr cenv es.scopes out` by
    (qunabbrev_tac `out` >> irule local_ptrs_reserved_fresh >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  `?bb rest. lookup_block s0.vs_current_bb func.fn_blocks = SOME bb /\
     DROP s0.vs_inst_idx bb.bb_instructions = [inst] ++ rest` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND, Abbr `inst`, Abbr `out`] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  `get_instruction bb s0.vs_inst_idx = SOME inst` by
    (simp[venomInstTheory.get_instruction_def] >>
     `s0.vs_inst_idx < LENGTH bb.bb_instructions` by
       (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
        simp[LENGTH_DROP]) >>
     qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `HD`) >>
     simp[HD_DROP]) >>
  `inst.inst_opcode = opc` by simp[Abbr `inst`, mk_inst_def] >>
  `step_inst_base inst s0 = OK (update_var out w s0)` by simp[Abbr `inst`] >>
  `alloca_inv s0` by fs[stmt_state_rel_def] >>
  rpt conj_tac
  >- (`gas_path_mem_edge ctx func s0 (if inst.inst_opcode = GAS then 1 else 0)
        (OK (update_var out w s0 with vs_inst_idx := SUC s0.vs_inst_idx))` by
        (irule straight_line_mem_edge >> simp[] >> metis_tac[]) >>
      gvs[] >>
      `0 = 0 + 0` by simp[] >> pop_assum SUBST1_TAC >>
      irule (cj 2 gas_path_mem_rules) >>
      qexists_tac `update_var out w s0 with vs_inst_idx := SUC s0.vs_inst_idx` >>
      gvs[] >> irule (cj 1 gas_path_mem_rules) >> simp[update_var_def])
  >- simp[update_var_def]
  >- simp[update_var_def]
  >- (simp[stmt_state_rel_inst_idx] >> irule stmt_state_rel_update_var >>
      simp[])
  >- simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
  >- (rpt strip_tac >> res_tac >>
      gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE])
  >- simp[update_var_def]
  >- simp[update_var_def]
  >- simp[update_var_def] >>
  qspecl_then [`func`, `bb`, `s0`, `[inst]`, `rest`,
               `update_var out w s0`] mp_tac alloca_history_run_inst_seq >>
  simp[run_inst_seq_def, arithmeticTheory.ADD1] >> disch_then irule >>
  simp[Abbr `inst`, mk_inst_def, is_terminator_def]
QED

Theorem unwrap_storage_word_path_mem:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    is_word_type t /\ local_ptrs_reserved cenv sm /\
    sa.cs_next_var <= sm.cs_next_var /\ fn_has_code sm sb func /\
    fn_inst_ids_distinct func /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path_mem ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >> (
  `t = post_value_type cenv e /\
   ?w. eval_operand p.ptr_operand s = SOME w /\
       storage_holds cx (p.ptr_location = LocTransient) (post_value_type cenv e)
         (Value v) w es' s /\
       stmt_state_rel ctx func cenv cx es' s` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  qabbrev_tac `ld = if p.ptr_location = LocTransient then tload w s
                    else sload w s` >>
  `!tvt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tvt ==>
         ld = typed_val_to_w256 tvt v` by
    (rpt strip_tac >> qunabbrev_tac `ld` >>
     drule_all storage_holds_load >> simp[]) >>
  `emit_op (if p.ptr_location = LocTransient then TLOAD else SLOAD)
     [p.ptr_operand] sm = (op, sb)` by
    gvs[unwrap_value_def, contextTheory.compile_ptr_load_def] >>
  drule emit_op_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es'`, `s`, `ld`]
    mp_tac) >>
  impl_tac
  >- (rw[is_terminator_def, Abbr `ld`] >>
      TRY (irule below_frontier_no_ranges >> simp[mk_inst_def] >> NO_TAC) >>
      TRY (simp[inst_dload_in_section_def, mk_inst_def] >> NO_TAC) >>
      gvs[step_inst_base_def, exec_read1_def, mk_inst_def]) >>
  strip_tac >> rename1 `gas_path_mem _ _ s 0 (OK u)` >>
  qexists_tac `u` >> simp[] >>
  irule expr_post_of_vv_post_load_physical >> simp[] >>
  qexistsl_tac [`p`, `s`, `sm`, `post_value_type cenv e`] >> simp[])
QED

Theorem unwrap_runtime_word_path_mem:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\
    sa.cs_next_var <= sm.cs_next_var /\ fn_has_code sm sb func /\
    fn_inst_ids_distinct func /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path_mem ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  `t = post_value_type cenv e /\
   ?w. eval_operand p.ptr_operand s = SOME w /\
       immutable_holds cenv cx (post_value_type cenv e) (Value v) w es' s /\
       stmt_state_rel ctx func cenv cx es' s` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  `?tv. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tv` by
    (gvs[immutable_holds_def] >> metis_tac[]) >>
  `w2n w + type_memory_size tv <= LENGTH s.vs_data_section` by
    (irule runtime_immutable_data_section >> metis_tac[]) >>
  drule_all immutable_holds_dload >> strip_tac >>
  `emit_op DLOAD [p.ptr_operand] sm = (op, sb)` by
    gvs[unwrap_value_def, contextTheory.compile_ptr_load_def,
        contextTheory.compile_imm_load_word_def] >>
  drule emit_op_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es'`, `s`,
    `typed_val_to_w256 tvt v`] mp_tac) >>
  impl_tac
  >- (simp[is_terminator_def] >> rpt strip_tac
      >- (irule below_frontier_no_ranges >> simp[mk_inst_def])
      >- (rw[inst_dload_in_section_def, mk_inst_def] >> gvs[])
      >- (qpat_x_assum `word_of_bytes _ _ _ = _` (SUBST1_TAC o SYM) >>
          irule step_DLOAD >> first_assum ACCEPT_TAC)) >>
  strip_tac >> rename1 `gas_path_mem _ _ s 0 (OK u)` >>
  qexists_tac `u` >> simp[] >>
  irule expr_post_of_vv_post_load_physical >> simp[] >>
  qexistsl_tac [`p`, `s`, `sm`, `post_value_type cenv e`] >> simp[]
QED

(* A constructor's immutable word lies below the allocation frontier. *)
Theorem ctor_immutable_word_frontier[local]:
  stmt_state_rel ctx func cenv cx es s /\ cenv.ce_is_ctor /\
  is_word_type t /\ immutable_holds cenv cx t tv w es s' ==>
  w2n w + 32 <= s.vs_alloca_next
Proof
  rw[immutable_holds_def, stmt_state_rel_def, immutable_alloca_sep_def] >>
  first_x_assum drule_all >> strip_tac >>
  drule_all word_tv_memory_size >> strip_tac >>
  gvs[sub_layout_def, wordsTheory.w2n_n2w]
QED

(* The constructor's immutable word load, memory-checked. *)
Theorem compile_imm_load_word_ctor_path_mem[local]:
  !ctx func cenv cx es pop sm op sb s0 w.
    compile_imm_load_word T cenv.ce_imm_alloca pop sm = (op, sb) /\
    local_ptrs_reserved cenv sm /\ fn_has_code sm sb func /\
    fn_inst_ids_distinct func /\
    stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
    ~s0.vs_halted /\
    s0.vs_current_bb = sm.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sm.cs_current_insts /\
    eval_operand pop s0 = SOME w /\ w2n w + 32 <= s0.vs_alloca_next ==>
    ?s. gas_path_mem ctx func s0 0 (OK s) /\
        s.vs_current_bb = sb.cs_current_bb /\
        s.vs_inst_idx = LENGTH sb.cs_current_insts /\
        stmt_state_rel ctx func cenv cx es s /\
        eval_operand op s = SOME (mload (w2n w) s0) /\
        (!x w'. not_fresh_at sm x /\ lookup_var x s0 = SOME w' ==>
                lookup_var x s = SOME w') /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                 FLOOKUP s.vs_allocas aid = SOME b) /\
        s.vs_memory = s0.vs_memory /\
        s.vs_alloca_next = s0.vs_alloca_next /\ alloca_history func s
Proof
  rpt strip_tac >> Cases_on `cenv.ce_imm_alloca` >>
  gvs[contextTheory.compile_imm_load_word_def]
  >- (drule emit_op_path_mem >>
      disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `s0`,
        `mload (w2n w) s0`] mp_tac) >>
      impl_tac
      >- (simp[is_terminator_def, below_frontier_ILOAD] >>
          simp[inst_dload_in_section_def, step_inst_base_def,
               exec_read1_def, mk_inst_def]) >>
      strip_tac >> goal_assum drule >> simp[]) >>
  rename1 `cenv.ce_imm_alloca = SOME ib` >>
  qpat_x_assum `comp_bind _ _ _ = _` mp_tac >>
  simp[comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_op ADD [pop; ib] sm = (addr, sm1)` >>
  `cs_extends sm sm1 /\ cs_extends sm1 sb` by
    metis_tac[exprSimAccountsTheory.emit_op_extends_next_var] >>
  `fn_has_code sm sm1 func /\ fn_has_code sm1 sb func` by
    metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm1` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sm` >>
     gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
         comp_ignore_bind_def, comp_return_def, emit_def]) >>
  `eval_operand ib s0 = SOME 0w` by
    gvs[exprLoweringPropsTheory.stmt_state_rel_def, immutable_base_zero_def] >>
  qpat_x_assum `emit_op ADD _ _ = _` assume_tac >>
  drule emit_op_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `s0`, `w`]
    mp_tac) >>
  impl_tac
  >- (simp[is_terminator_def] >> rpt strip_tac >>
      TRY (irule below_frontier_no_ranges >> simp[mk_inst_def] >> NO_TAC) >>
      simp[inst_dload_in_section_def, step_inst_base_def, exec_pure2_def,
           mk_inst_def, wordsTheory.WORD_ADD_0]) >>
  strip_tac >> rename1 `gas_path_mem _ _ s0 0 (OK s1)` >>
  `~s1.vs_halted` by metis_tac[gas_path_mem_exec, gas_path_normal] >>
  qpat_x_assum `emit_op ILOAD _ _ = _` assume_tac >>
  drule emit_op_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`, `s1`,
    `mload (w2n w) s1`] mp_tac) >>
  impl_tac
  >- (simp[is_terminator_def, below_frontier_ILOAD] >>
      simp[inst_dload_in_section_def, step_inst_base_def,
           exec_read1_def, mk_inst_def]) >>
  strip_tac >> rename1 `gas_path_mem _ _ s1 0 (OK s2)` >>
  qexists_tac `s2` >> gvs[mload_def] >>
  conj_tac
  >- (`0 = 0 + 0` by simp[] >> pop_assum SUBST1_TAC >>
      irule gas_path_mem_then >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum irule >> conj_tac
  >- (first_x_assum irule >> simp[]) >>
  gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
      comp_ignore_bind_def, comp_return_def, emit_def, not_fresh_at_def]
QED

Theorem unwrap_ctor_word_path_mem:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ cenv.ce_is_ctor /\ is_word_type t /\
    local_ptrs_reserved cenv sm /\
    sa.cs_next_var <= sm.cs_next_var /\ fn_has_code sm sb func /\
    fn_inst_ids_distinct func /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path_mem ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  `t = post_value_type cenv e /\
   ?w. eval_operand p.ptr_operand s = SOME w /\
       immutable_holds cenv cx (post_value_type cenv e) (Value v) w es' s /\
       stmt_state_rel ctx func cenv cx es' s` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  `w2n w + 32 <= s.vs_alloca_next` by
    metis_tac[ctor_immutable_word_frontier] >>
  drule_all immutable_holds_iload >> strip_tac >>
  `compile_imm_load_word T cenv.ce_imm_alloca p.ptr_operand sm = (op, sb)` by
    gvs[unwrap_value_def, contextTheory.compile_ptr_load_def] >>
  drule compile_imm_load_word_ctor_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `es'`, `s`, `w`] mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >> rename1 `gas_path_mem _ _ s 0 (OK u)` >>
  qexists_tac `u` >> simp[] >>
  irule expr_post_of_vv_post_load_physical >> simp[] >>
  qexistsl_tac [`p`, `s`, `sm`, `post_value_type cenv e`] >> simp[]
QED

(* ===== Copies into a fresh buffer ===== *)

Theorem copy_static_inst_idx[local,simp]:
  copy_static (s with vs_inst_idx := n) = copy_static s
Proof
  simp[exprSimStorageCopyTheory.copy_static_def]
QED

Theorem lookup_var_inst_idx[local,simp]:
  lookup_var x (s with vs_inst_idx := n) = lookup_var x s
Proof
  simp[lookup_var_def]
QED

Theorem straight_run_control[local]:
  run_inst_seq code s = OK t /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code ==>
  t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >>
  irule (SRULE [] (Q.ISPEC
    `\s:venom_state. (s.vs_halted,s.vs_current_bb)`
    run_inst_seq_preserves_field)) >>
  qexists_tac `code` >> simp[] >> rpt strip_tac >> fs[EVERY_MEM] >>
  metis_tac[venomInstProofsTheory.step_preserves_halted,
            venomInstProofsTheory.step_preserves_control_flow,
            step_inst_non_invoke]
QED

(* Straight-line code without GAS, memory-checked, keeping the history. *)
Theorem straight_path_mem[local]:
  fn_has_code sa sb func /\ same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_path_mem ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >>
  `gas_path_mem ctx func s 0
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    metis_tac[body_decl_zero_gas_path] >>
  `t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb` by
    (irule straight_run_control >> fs[EVERY_MEM] >> metis_tac[]) >>
  `~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb` by
    gvs[same_blocks_def] >>
  simp[] >>
  qabbrev_tac `em = emitted_insts sa sb` >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX sb.cs_current_insts bb.bb_instructions` by
    gvs[fn_has_code_def, same_blocks_def] >>
  `?rest. bb.bb_instructions = sb.cs_current_insts ++ rest` by
    metis_tac[IS_PREFIX_APPEND] >>
  `DROP s.vs_inst_idx bb.bb_instructions = em ++ rest` by
    (qpat_x_assum `bb.bb_instructions = _` SUBST1_TAC >>
     qpat_x_assum `sb.cs_current_insts = _` SUBST1_TAC >>
     qpat_x_assum `s.vs_inst_idx = _` SUBST1_TAC >>
     REWRITE_TAC[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) em` by fs[EVERY_MEM] >>
  qpat_x_assum `s.vs_inst_idx = _` (SUBST_ALL_TAC o SYM) >>
  irule alloca_history_run_inst_seq >> metis_tac[]
QED

(* The buffer's ALLOCA, memory-checked. *)
Theorem alloc_buffer_source_path_mem[local]:
  !ctx func cenv cx es sm mid buf sz s src a.
    compile_alloc_buffer sz sm = (buf,mid) /\ fn_has_code sm mid func /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sm /\ sz < dimword (:256) /\
    eval_operand src s = SOME a /\
    (!x. src = Var x ==> not_fresh_at sm x) /\ alloca_history func s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u w. gas_path_mem ctx func s 0 (OK u) /\
      ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
      u.vs_inst_idx = LENGTH mid.cs_current_insts /\
      eval_operand src u = SOME a /\
      stmt_state_rel ctx func cenv cx es u /\
      eval_operand buf.buf_operand u = SOME w /\
      FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,sz) /\
      w2n w + sz < dimword (:256) /\ w2n w + sz <= u.vs_alloca_next /\
      u.vs_memory = s.vs_memory /\ sm.cs_next_id < mid.cs_next_id /\
      (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP u.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < sm.cs_next_id /\
         FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
         regions_disjoint (w2n w) sz b len) /\
      (!name b len. local_region cenv es.scopes u name b len ==>
         regions_disjoint (w2n w) sz b len) /\
      (?p. buf.buf_operand = Var p /\ not_fresh_at mid p) /\
      s.vs_alloca_next <= u.vs_alloca_next /\ alloca_history func u /\
      contract_storage u = contract_storage s /\
      contract_transient u = contract_transient s /\
      u.vs_labels = s.vs_labels
Proof
  rpt gen_tac >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `t.vs_labels = s.vs_labels` by metis_tac[hash_alloc_buffer_labels] >>
  `contract_storage t = contract_storage s /\
   contract_transient t = contract_transient s` by
    metis_tac[alloc_buffer_storage] >>
  `eval_operand src t = SOME a` by
    (Cases_on `src` >> gvs[eval_operand_def]) >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (qpat_x_assum `run_inst_seq _ _ = OK t` mp_tac >>
     simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
          exec_alloca_def, eval_operand_def] >>
     Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >>
     simp[update_var_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
  `alloca_inv s /\ alloca_inv t` by fs[stmt_state_rel_def] >>
  `w2n w + sz <= t.vs_alloca_next` by
    (qpat_x_assum `alloca_inv t`
       (strip_assume_tac o REWRITE_RULE [alloca_inv_def, alloca_next_valid_def]) >>
     first_x_assum drule >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sm mid) s` by
    (qpat_x_assum `emitted_insts sm mid = _` SUBST1_TAC >>
     rewrite_tac[run_inst_seq_mem_ok_last] >> conj_tac
     >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
     simp[inst_dload_in_section_def, mk_inst_def]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) (emitted_insts sm mid)` by
    simp[mk_inst_def, is_terminator_def] >>
  qspecl_then [`sm`, `mid`, `func`, `s`, `t`, `ctx`] mp_tac
    (Q.GENL [`sa`, `sb`, `func`, `s`, `t`, `ctx`] straight_path_mem) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH mid.cs_current_insts`, `w`] >>
  simp[] >> Cases_on `src` >>
  gvs[stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def,
      local_region_def, venomStateTheory.contract_storage_def,
      venomStateTheory.contract_transient_def] >> metis_tac[]
QED

(* ----- storage and transient ----- *)

Theorem storage_unwrap_word_run:
  (loc = LocStorage \/ loc = LocTransient) /\
  do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
     emit_void MSTORE [dst; v] od sa = (u,sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  b+32 < 2**256 ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    copy_prefix loc a b 1 s 1 t /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_current_bb = s.vs_current_bb
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule storage_copy_word_layout >> strip_tac >>
  qabbrev_tac `v = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `w = copy_runtime_word loc s a` >>
  `step_inst_base (mk_inst sa.cs_next_id
    (if loc = LocStorage then SLOAD else TLOAD) [src] [v]) s =
    OK (update_var v w s)` by
    (gvs[step_inst_base_opcode_eqs, exec_read1_def, mk_inst_def,
         Abbr `w`, copy_runtime_word_def]) >>
  `eval_operand dst (update_var v w s) = SOME (n2w b)` by
    (Cases_on `dst` >> gvs[eval_operand_def, lookup_var_update_var] >> metis_tac[]) >>
  `w2n (n2w b : bytes32) = b` by
    (gvs[wordsTheory.w2n_n2w, wordsTheory.dimword_def] >> decide_tac) >>
  `step_inst_base (mk_inst (sa.cs_next_id+1) MSTORE [dst; Var v] [])
    (update_var v w s) = OK (mstore b w (update_var v w s))` by
    (qpat_assum `w2n (n2w b : bytes32) = b`
       (fn th => once_rewrite_tac[GSYM th]) >>
     irule step_MSTORE >> simp[eval_operand_update_var]) >>
  qexists_tac `mstore b w (update_var v w s)` >>
  simp[run_inst_seq_def, GSYM mk_inst_def] >>
  conj_tac
  >- (`copy_prefix loc a b 1 s (0+1)
        (mstore (b+32*0) (copy_runtime_word loc s (a+n2w 0))
          (update_var v w s))` by
        (irule copy_prefix_extend >> simp[copy_prefix_update_var, copy_prefix_zero]) >>
      gvs[Abbr `w`, Abbr `v`, wordsTheory.WORD_ADD_0]) >>
  simp[immutableMemoryFrameTheory.immutable_mstore_capacity, update_var_def] >>
  simp[mstore_def, write_memory_with_expansion_def, lookup_var_def] >>
  rpt strip_tac >> simp[FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem storage_unwrap_word_content_path_mem[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
     emit_void MSTORE [dst; v] od sa = (u,sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  b+32 < 2**256 /\ b + 32 <= s.vs_alloca_next /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z. gas_path_mem ctx func s 0 (OK z) /\ copy_prefix loc a b 1 s 1 z /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func z
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all storage_unwrap_word_run >> strip_tac >>
  drule storage_copy_word_layout >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (`?l. sb.cs_current_insts = sa.cs_current_insts ++ l` by
       metis_tac[IS_PREFIX_APPEND] >>
     pop_assum (fn th => REWRITE_TAC[emitted_insts_def, th,
                                     rich_listTheory.DROP_LENGTH_APPEND])) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (qpat_x_assum `emitted_insts sa sb = [_; _]` SUBST1_TAC >>
     irule body_storage_singleton_mem_ok >> rpt conj_tac
     >- metis_tac[]
     >- (qexists_tac `b` >> gvs[wordsTheory.dimword_def]) >>
     simp[]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (qpat_x_assum `emitted_insts sa sb = [_; _]` SUBST1_TAC >>
     rw[mk_inst_def, is_terminator_def]) >>
  qspecl_then [`sa`, `sb`, `func`, `s`, `t`, `ctx`] mp_tac
    (Q.GENL [`sa`, `sb`, `func`, `s`, `t`, `ctx`] straight_path_mem) >>
  impl_tac >- gvs[] >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[copy_prefix_idx]
QED

Theorem word_copy_loop_exit_empty[local]:
  compile_word_copy_loop src dst n l1 l2 c sa = (u,sb) ==>
  sb.cs_current_insts = []
Proof
  simp[compile_word_copy_loop_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[new_block_def]
QED

Theorem storage_unwrap_suffix_content_path_mem[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  (if n = 1 then
     do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [dst; v] od
   else do compile_word_copy_loop src dst n loc LocMemory F; return () od)
    sa = (u,sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  n < 2**256 /\ b+32*n < 2**256 /\ b + 32*n <= s.vs_alloca_next /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z. gas_path_mem ctx func s 0 (OK z) /\ copy_prefix loc a b n s n z /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func z
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  Cases_on `n = 1`
  >- (fs[] >> irule storage_unwrap_word_content_path_mem >> simp[] >>
      qexistsl_tac [`dst`, `src`] >> gvs[] >> metis_tac[]) >>
  fs[] >>
  `?u'. compile_word_copy_loop src dst n loc LocMemory F sa = (u',sb)` by
    (qpat_x_assum `_ sa = (u,sb)` mp_tac >>
     simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> simp[]) >>
  `?z. gas_path_mem ctx func s 0 (OK z) /\ copy_prefix loc a b n s n z /\
     LENGTH s.vs_memory <= LENGTH z.vs_memory /\
     (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
     z.vs_current_bb = sb.cs_current_bb /\
     z.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (mp_tac (storageCopyGasPathTheory.compile_storage_copy_content_capacity_path
       |> Q.SPEC `T`
       |> CONV_RULE (RAND_CONV (REWR_CONV (GSYM ETA_AX)))
       |> Q.SPEC `(ctx,func)`) >>
     simp[gas_marked_path_def] >>
     disch_then (qspecl_then [`loc`, `src`, `dst`, `n`, `sa`, `u'`, `sb`,
                              `s`, `a`, `b`] mp_tac) >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gvs[]) >>
     strip_tac >> metis_tac[]) >>
  qexists_tac `z` >> simp[] >>
  `sb.cs_current_insts = []` by metis_tac[word_copy_loop_exit_empty] >>
  `z.vs_allocas = s.vs_allocas` by
    (gvs[copy_prefix_def] >> drule copy_static_fields >> simp[]) >>
  `z.vs_inst_idx = 0` by gvs[] >>
  rpt conj_tac >> TRY (gvs[] >> NO_TAC) >>
  metis_tac[alloca_history_jump]
QED

Theorem storage_unwrap_typed_suffix_path_mem[local]:
  !loc tv src dst mid result sb ctx func cenv cx es u t v a w.
  (loc = LocStorage \/ loc = LocTransient) /\
  (if type_slot_size tv = 1 then
     do value <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [dst; value] od
   else do compile_word_copy_loop src dst (type_slot_size tv) loc LocMemory F;
           return () od) mid = (result,sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at mid x) /\
  stmt_state_rel ctx func cenv cx es u /\
  storage_holds cx (loc = LocTransient) t (Value v) a es u /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  eval_operand src u = SOME a /\ eval_operand dst u = SOME w /\
  type_slot_size tv < 2**256 /\ w2n w + 32*type_slot_size tv < 2**256 /\
  w2n w + 32*type_slot_size tv <= u.vs_alloca_next /\
  fn_has_code mid sb func /\ fn_inst_ids_distinct func /\
  alloca_history func u /\ ~u.vs_halted /\
  u.vs_current_bb = mid.cs_current_bb /\
  u.vs_inst_idx = LENGTH mid.cs_current_insts ==>
  ?z. gas_path_mem ctx func u 0 (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    copy_static z = copy_static u /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off+len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\ eval_operand dst z = SOME w /\
    alloca_history func z
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `alloca_inv u` by fs[stmt_state_rel_def] >>
  `eval_operand dst u = SOME (n2w (w2n w))` by simp[] >>
  drule_all storage_unwrap_suffix_content_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `copy_prefix (if loc = LocTransient then LocTransient else LocStorage)
     a (w2n w) (type_slot_size tv) u (type_slot_size tv) z` by
    (Cases_on `loc = LocTransient` >> gvs[]) >>
  drule_all copy_buffer_storage_contents >> strip_tac >>
  `copy_static z = copy_static u` by gvs[copy_prefix_def] >>
  `eval_operand dst z = SOME w` by
    (drule storage_copy_operand_preserved >>
     disch_then (qspecl_then [`mid`, `dst`] mp_tac) >> simp[]) >>
  qexists_tac `z` >>
  gvs[copy_prefix_def, valueEncodingPropsTheory.type_memory_size_slots] >>
  metis_tac[]
QED

Theorem storage_unwrap_layout_facts[local]:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  ~is_word_type t /\ fn_has_code sm sb func ==>
  ?buf mid.
    compile_alloc_buffer (type_memory_bytes cenv t) sm = (buf,mid) /\
    (if (type_memory_bytes cenv t + 31) DIV 32 = 1 then
       do value <- emit_op (if p.ptr_location = LocStorage then SLOAD else TLOAD)
                     [p.ptr_operand]; emit_void MSTORE [buf.buf_operand; value] od
     else do compile_word_copy_loop p.ptr_operand buf.buf_operand
               ((type_memory_bytes cenv t + 31) DIV 32) p.ptr_location LocMemory F;
             return () od) mid = ((),sb) /\
    op = buf.buf_operand /\ fn_has_code sm mid func /\ fn_has_code mid sb func /\
    sm.cs_next_var <= mid.cs_next_var /\ mid.cs_next_id <= sb.cs_next_id
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  `compile_ensure_in_memory p.ptr_operand p.ptr_location
     (type_memory_bytes cenv t) ((type_memory_bytes cenv t + 31) DIV 32)
     cenv.ce_is_ctor cenv.ce_imm_alloca sm = (op,sb)` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     Cases_on `p.ptr_location` >> gvs[unwrap_value_def]) >>
  qpat_x_assum `unwrap_value _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_ensure_in_memory _ _ _ _ _ _ _ = _` mp_tac >>
  drule ensure_storage_memory_layout >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gnvs[] >> rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  `cs_extends sm mid` by
    metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `cs_extends mid cs''` by
    (irule storage_copy_suffix_extends >>
     qexistsl_tac [`buf.buf_operand`, `p.ptr_location`,
       `(type_memory_bytes cenv t + 31) DIV 32`, `p.ptr_operand`, `()`] >>
     gvs[comp_ignore_bind_def]) >>
  `ci_mono sm mid` by
    (qspecl_then [`type_memory_bytes cenv t`, `sm`] mp_tac
       ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono mid cs''` by
    (irule storage_copy_suffix_ci_mono >>
     qexistsl_tac [`buf.buf_operand`, `p.ptr_location`,
       `(type_memory_bytes cenv t + 31) DIV 32`, `p.ptr_operand`, `()`] >>
     gvs[comp_ignore_bind_def]) >>
  gvs[comp_ignore_bind_def, ci_mono_def] >> metis_tac[fn_has_code_split]
QED

Theorem storage_unwrap_type_facts[local]:
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
    type_memory_bytes cenv t = type_memory_size tvt /\
    type_memory_size tvt < 2**64) ==>
  t = expr_type e /\ stmt_state_rel ctx func cenv cx es' s /\
  ?a tv. eval_operand p.ptr_operand s = SOME a /\
    storage_holds cx (p.ptr_location = LocTransient) t (Value v) a es' s /\
    evaluate_type (get_tenv cx) t = SOME tv /\
    type_memory_bytes cenv t = type_memory_size tv /\
    type_memory_size tv < 2**64 /\
    type_memory_bytes cenv t < dimword (:256) /\
    (type_memory_bytes cenv t + 31) DIV 32 = type_slot_size tv /\
    type_slot_size tv < 2**256
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `t = expr_type e /\ stmt_state_rel ctx func cenv cx es' s` by
    (Cases_on `p.ptr_location` >> gvs[vv_post_def, vv_holds_def]) >> simp[] >>
  `?a. eval_operand p.ptr_operand s = SOME a /\
       storage_holds cx (p.ptr_location = LocTransient) t (Value v) a es' s` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     Cases_on `p.ptr_location` >> gvs[vv_post_def, vv_holds_def]) >>
  `?tv. evaluate_type (get_tenv cx) t = SOME tv` by
    (gvs[storage_holds_def] >> metis_tac[]) >>
  `type_memory_bytes cenv t = type_memory_size tv /\
    type_memory_size tv < 2**64` by metis_tac[] >>
  qexistsl_tac [`a`, `tv`] >> simp[] >>
  gvs[valueEncodingPropsTheory.type_memory_size_slots, wordsTheory.dimword_def] >>
  decide_tac
QED

(* expr_post of a value copied into a fresh buffer. *)
Theorem buffer_post_transport[local]:
  !ctx func cenv cx e es sa sm mid sb s0 es' v t p s u z tv buf w.
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= mid.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < mid.cs_next_id /\
    mid.cs_next_id <= sb.cs_next_id /\
    stmt_state_rel ctx func cenv cx es' u /\ u.vs_memory = s.vs_memory /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sm.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n w) (type_memory_bytes cenv t) b len) /\
    (!name b len. local_region cenv es'.scopes u name b len ==>
       regions_disjoint (w2n w) (type_memory_bytes cenv t) b len) /\
    compile_alloc_buffer (type_memory_bytes cenv t) sm = (buf,mid) /\
    fn_has_code sm mid func /\
    FLOOKUP u.vs_allocas sm.cs_next_id =
      SOME (w2n w,type_memory_bytes cenv t) /\
    copy_static z = copy_static u /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off + len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
       mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    t = expr_type e /\ type_memory_bytes cenv t = type_memory_size tv /\
    ~is_word_type t /\ evaluate_type (get_tenv cx) t = SOME tv /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\
    eval_operand buf.buf_operand z = SOME w ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v buf.buf_operand z
Proof
  rpt gen_tac >> strip_tac >>
  `post_value_type cenv e = expr_type e` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_def, vv_holds_def] >> rpt strip_tac >>
     gvs[post_value_type_bytestring]) >>
  drule_all buffer_alloc_code >> strip_tac >>
  `~is_word_type (expr_type e)` by metis_tac[] >>
  irule copy_buffer_post_transport >> simp[] >>
  qexistsl_tac [`mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv t))]
                  [STRING #"%" (toString sm.cs_next_var)]`,
               `mid`, `s`, `sm`, `type_memory_bytes cenv t`, `tv`, `u`,
               `LocatedValue t p`] >>
  gvs[mk_inst_def, arithmeticTheory.ADD_COMM] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* The shared ending: compose the two paths and bound the buffer. *)
Theorem copy_finish[local]:
  !ctx func s u z cenv cx e es sa sb s0 es' v op w tv t.
  post_value_type cenv e = expr_type e /\
  gas_path_mem ctx func s 0 (OK u) /\ gas_path_mem ctx func u 0 (OK z) /\
  expr_post ctx func cenv cx e es sa sb s0 es' v op z /\
  eval_operand op z = SOME w /\
  w2n w + type_memory_size tv <= z.vs_alloca_next /\
  evaluate_type (get_tenv cx) t = SOME tv /\ t = expr_type e /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  z.vs_alloca_next = u.vs_alloca_next /\
  alloca_history func z /\ z.vs_current_bb = sb.cs_current_bb /\
  z.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?u. gas_path_mem ctx func s 0 (OK u) /\
      expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
      expr_store_bound cx t v op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >> qexists_tac `z` >> simp[] >> rpt conj_tac
  >- (`0 = 0 + 0` by simp[] >> pop_assum SUBST1_TAC >>
      irule gas_path_mem_then >> qexists_tac `u` >> simp[])
  >- (qpat_x_assum `t = _` SUBST_ALL_TAC >>
      drule expr_store_bound_capacity >> impl_tac
      >- (rpt strip_tac >> gvs[]) >>
      simp[]) >>
  decide_tac
QED

Theorem unwrap_storage_copy_path_mem[local]:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    ~is_word_type t /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
           type_memory_bytes cenv t = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path_mem ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        expr_store_bound cx t v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all storage_unwrap_layout_facts >> strip_tac >>
  drule_all storage_unwrap_type_facts >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  drule_all alloc_buffer_source_path_mem >> strip_tac >>
  `storage_holds cx (p.ptr_location = LocTransient) t (Value v) a es' u` by
    (qpat_x_assum `storage_holds _ _ _ _ _ _ s` mp_tac >>
     simp[storage_holds_def]) >>
  `!x. p.ptr_operand = Var x \/ buf.buf_operand = Var x ==>
       not_fresh_at mid x` by
    (gen_tac >> strip_tac
     >- (irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `sm` >> simp[]) >> fs[]) >>
  `w2n w + 32 * type_slot_size tv < 2**256 /\
   w2n w + 32 * type_slot_size tv <= u.vs_alloca_next` by
    fs[valueEncodingPropsTheory.type_memory_size_slots, wordsTheory.dimword_def] >>
  qpat_x_assum `(_ + 31) DIV 32 = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  qspecl_then [`p.ptr_location`, `tv`, `p.ptr_operand`, `buf.buf_operand`,
    `mid`, `()`, `sb`, `ctx`, `func`, `cenv`, `cx`, `es'`, `u`, `t`, `v`,
    `a`, `w`] mp_tac storage_unwrap_typed_suffix_path_mem >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gvs[]) >>
  strip_tac >>
  `expr_post ctx func cenv cx e es sa sb s0 es' v buf.buf_operand z` by
    (irule buffer_post_transport >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`mid`, `p`, `s`, `sm`, `t`, `tv`, `u`, `w`] >>
     asm_rewrite_tac [] >> simp[]) >>
  `z.vs_alloca_next = u.vs_alloca_next` by
    (drule copy_static_fields >> simp[]) >>
  qspecl_then [`ctx`, `func`, `s`, `u`, `z`, `cenv`, `cx`, `e`, `es`, `sa`,
    `sb`, `s0`, `es'`, `v`, `op`, `w`, `tv`, `t`] mp_tac copy_finish >>
  impl_tac >- gvs[] >> simp[]
QED

(* ----- code ----- *)

Theorem code_copy_path_mem[local]:
  !imm src dst n off sa sb func s a b ctx.
  compile_imm_copy_to_memory F imm src dst n off sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  w2n b + off + 32 * n <= s.vs_alloca_next /\
  w2n b + off + 32 * n < dimword (:256) /\
  w2n a + off + 32 * n <= LENGTH s.vs_data_section /\
  w2n a + off + 32 * n < dimword (:256) /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      t.vs_memory = (immutable_transfers F F a b n off s).vs_memory /\
      copy_static t = copy_static s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t
Proof
  rpt gen_tac >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[body_immutable_copy_mem_ok] >>
  drule code_copy_insts >> strip_tac >>
  drule_all copy_runtime_run >> strip_tac >>
  qpat_x_assum `copy_runtime_frame _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [copy_runtime_frame_def]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (`emitted_insts sa sb = is` by
       (qpat_x_assum `sb.cs_current_insts = _ ++ is` mp_tac >>
        qpat_x_assum `sb.cs_current_insts = _ ++ emitted_insts _ _`
          SUBST1_TAC >> simp[]) >>
     pop_assum SUBST1_TAC >> fs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[is_terminator_def]) >>
  qspecl_then [`sa`, `sb`, `func`, `s`, `s'`, `ctx`] mp_tac
    (Q.GENL [`sa`, `sb`, `func`, `s`, `t`, `ctx`] straight_path_mem) >>
  impl_tac >- simp[] >> strip_tac >>
  qexists_tac `s' with vs_inst_idx := LENGTH sb.cs_current_insts` >> simp[]
QED

Theorem body_ctor_load_mem_ok[local]:
  compile_imm_load_word T imm op sa = (r,sb) /\
  eval_operand op s = SOME a /\ w2n a + 32 <= s.vs_alloca_next /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  Cases_on `imm` >> simp[contextTheory.compile_imm_load_word_def] >> strip_tac
  >- (drule emitted_insts_emit_op >> strip_tac >>
      simp[run_inst_seq_mem_ok_last, below_frontier_ILOAD] >>
      simp[inst_dload_in_section_def, mk_inst_def]) >>
  gvs[comp_bind_def] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD _ sa = (addr, s1)` >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `emit_op ILOAD _ _ = _` assume_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa s1 ++ emitted_insts s1 sb` by
    (irule emitted_insts_append >> simp[]) >>
  gvs[run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last] >> rpt conj_tac >>
  TRY (irule below_frontier_no_ranges >> simp[mk_inst_def] >> NO_TAC) >>
  TRY (simp[inst_dload_in_section_def, mk_inst_def] >> NO_TAC) >>
  gvs[step_inst_base_def, exec_pure2_def, mk_inst_def] >>
  gvs[unitTransformDefsTheory.inst_mem_below_frontier_def,
      contextCodegenRelTheory.source_memory_read_ranges_def,
      codegenRelTheory.source_memory_write_ranges_def,
      inst_dload_in_section_def,
      eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
      wordsTheory.WORD_ADD_0]
QED

Theorem body_ctor_one_mem_ok[local]:
  immutable_copy_one T imm src dst off sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
     copy_old_operand sa region) /\
  w2n b + off + 32 <= s.vs_alloca_next /\
  w2n b + off + 32 < dimword (:256) /\
  w2n a + off + 32 <= s.vs_alloca_next /\
  w2n a + off + 32 < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[immutable_copy_one_def, immutable_comp_bind_cases] >> strip_tac >>
  drule_all copy_runtime_offset >> strip_tac >>
  rename1 `compile_lit_byte_offset src off sa = (sop,s1)` >>
  rename1 `copy_runtime_frame sa s s1 t1` >>
  `!region. imm = SOME region ==>
      eval_operand region t1 = SOME 0w /\ copy_old_operand s1 region` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!region. imm = SOME region ==>
                     eval_operand region s = _ /\ _`
       (qspec_then `region` mp_tac) >>
     simp[] >> strip_tac >>
     drule_all copy_runtime_frame_operand >> strip_tac >>
     conj_tac >- simp[] >>
     irule copy_old_operand_mono >> qexists_tac `sa` >>
     fs[copy_runtime_frame_def]) >>
  drule_all copy_ctor_load >> strip_tac >>
  rename1 `compile_imm_load_word T imm sop s1 = (value,s2)` >>
  rename1 `copy_runtime_frame s1 t1 s2 t2` >>
  `copy_runtime_frame sa s s2 t2` by metis_tac[copy_runtime_frame_trans] >>
  `copy_old_operand s2 dst` by
    metis_tac[copy_old_operand_mono, copy_runtime_frame_def] >>
  `eval_operand dst t2 = SOME b` by metis_tac[copy_runtime_frame_operand] >>
  `run_inst_seq_mem_ok (emitted_insts sa s1) s` by
    metis_tac[body_immutable_byte_offset_mem_ok] >>
  `t1.vs_alloca_next = s.vs_alloca_next` by
    metis_tac[body_copy_frame_frontier] >>
  `w2n (a + n2w off) + 32 <= t1.vs_alloca_next` by
    (irule body_immutable_copy_offset_range >> simp[] >> decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts s1 s2) t1` by
    (irule body_ctor_load_mem_ok >> metis_tac[]) >>
  qpat_x_assum `compile_lit_byte_offset src off sa = _` kall_tac >>
  drule_all copy_runtime_offset >> strip_tac >>
  rename1 `compile_lit_byte_offset dst off s2 = (dop,s3)` >>
  rename1 `copy_runtime_frame s2 t2 s3 t3` >>
  `copy_old_operand s3 value` by
    metis_tac[copy_old_operand_mono, copy_runtime_frame_def] >>
  `eval_operand value t3 = SOME (immutable_copy_read T (a + n2w off) t1)` by
    metis_tac[copy_runtime_frame_operand] >>
  drule_all copy_runtime_store >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts s3 sb) t3` by
    (drule body_immutable_store_mem_ok >> disch_then irule >>
     goal_assum (drule_at Any) >>
     `t3.vs_alloca_next = s.vs_alloca_next` by
       metis_tac[body_copy_frame_frontier, copy_runtime_frame_trans] >>
     irule body_immutable_copy_offset_range >> simp[] >> decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts s2 sb) t2` by
    (irule body_copy_frame_mem_append >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[body_immutable_byte_offset_mem_ok]) >>
  `run_inst_seq_mem_ok (emitted_insts s1 sb) t1` by
    (irule body_copy_frame_mem_append >>
     qexistsl [`s2`,`t2`] >> simp[] >>
     metis_tac[copy_runtime_frame_trans]) >>
  irule body_copy_frame_mem_append >> qexistsl [`s1`,`t1`] >> simp[] >>
  metis_tac[copy_runtime_frame_trans]
QED

Theorem body_ctor_copy_mem_ok:
  !n off sa sb s a b.
    compile_imm_copy_to_memory T imm src dst n off sa = ((),sb) /\
    copy_old_operand sa src /\ copy_old_operand sa dst /\
    eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
    (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
       copy_old_operand sa region) /\
    w2n b + off + 32 * n <= s.vs_alloca_next /\
    w2n b + off + 32 * n < dimword (:256) /\
    w2n a + off + 32 * n <= s.vs_alloca_next /\
    w2n a + off + 32 * n < dimword (:256) ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  Induct
  >- simp[compile_imm_copy_to_memory_def, comp_return_def, emitted_insts_def,
           run_inst_seq_mem_ok_def] >>
  simp[immutable_copy_suc, comp_ignore_bind_def, immutable_comp_bind_cases] >>
  rpt strip_tac >> drule_all copy_ctor_one >> strip_tac >>
  rename1 `immutable_copy_one T imm src dst off sa = ((),sm)` >>
  rename1 `copy_runtime_frame sa s sm t` >>
  `copy_old_operand sm src /\ copy_old_operand sm dst` by
    metis_tac[copy_old_operand_mono, copy_runtime_frame_def] >>
  `eval_operand src t = SOME a /\ eval_operand dst t = SOME b` by
    metis_tac[copy_runtime_frame_operand] >>
  `!region. imm = SOME region ==>
      eval_operand region t = SOME 0w /\ copy_old_operand sm region` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!region. imm = SOME region ==>
                     eval_operand region s = _ /\ _`
       (qspec_then `region` mp_tac) >>
     simp[] >> strip_tac >>
     drule_all copy_runtime_frame_operand >> strip_tac >>
     conj_tac >- simp[] >>
     irule copy_old_operand_mono >> qexists_tac `sa` >>
     fs[copy_runtime_frame_def]) >>
  `t.vs_alloca_next = s.vs_alloca_next` by metis_tac[body_copy_frame_frontier] >>
  `run_inst_seq_mem_ok (emitted_insts sa sm) s` by
    (irule body_ctor_one_mem_ok >> gvs[arithmeticTheory.MULT_SUC] >>
     qexistsl_tac [`a`, `b`, `dst`, `imm`, `off`, `src`] >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) t` by
    (first_x_assum (qspecl_then [`off + 32`, `sm`, `sb`, `t`, `a`, `b`] mp_tac) >>
     impl_tac >- gvs[arithmeticTheory.MULT_SUC] >> simp[]) >>
  drule_all copy_ctor_run >> strip_tac >>
  irule body_copy_frame_mem_append >> metis_tac[]
QED

Theorem ctor_code_copy_path_mem[local]:
  !imm src dst n off sa sb func s a b ctx.
  compile_imm_copy_to_memory T imm src dst n off sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
     copy_old_operand sa region) /\
  w2n b + off + 32 * n <= s.vs_alloca_next /\
  w2n b + off + 32 * n < dimword (:256) /\
  w2n a + off + 32 * n <= s.vs_alloca_next /\
  w2n a + off + 32 * n < dimword (:256) /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
      t.vs_memory = (immutable_transfers F T a b n off s).vs_memory /\
      copy_static t = copy_static s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t
Proof
  rpt gen_tac >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[body_ctor_copy_mem_ok] >>
  drule code_ctor_copy_insts >> strip_tac >>
  drule_all copy_ctor_run >> strip_tac >>
  qpat_x_assum `copy_runtime_frame _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [copy_runtime_frame_def]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (`emitted_insts sa sb = is` by
       (qpat_x_assum `sb.cs_current_insts = _ ++ is` mp_tac >>
        qpat_x_assum `sb.cs_current_insts = _ ++ emitted_insts _ _`
          SUBST1_TAC >> simp[]) >>
     pop_assum SUBST1_TAC >> fs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[is_terminator_def]) >>
  qspecl_then [`sa`, `sb`, `func`, `s`, `zz`, `ctx`] mp_tac
    (Q.GENL [`sa`, `sb`, `func`, `s`, `t`, `ctx`] straight_path_mem) >>
  impl_tac >- simp[] >> strip_tac >>
  qexists_tac `zz with vs_inst_idx := LENGTH sb.cs_current_insts` >> simp[]
QED

(* A constructor's immutable lies below the allocation frontier. *)
Theorem ctor_immutable_frontier:
  stmt_state_rel ctx func cenv cx es s /\ cenv.ce_is_ctor /\
  immutable_holds cenv cx t tv w es s' /\
  evaluate_type (get_tenv cx) t = SOME tvt ==>
  w2n w + type_memory_size tvt <= s.vs_alloca_next
Proof
  rw[immutable_holds_def, stmt_state_rel_def, immutable_alloca_sep_def] >>
  first_x_assum drule_all >> strip_tac >>
  gvs[sub_layout_def, wordsTheory.w2n_n2w]
QED

(* Runtime transfers leave memory outside the buffer alone. *)
Theorem runtime_copy_frame_facts[local]:
  w2n a + type_memory_size tv < dimword (:256) /\
  w2n w + type_memory_size tv < dimword (:256) /\
  zm = (immutable_transfers F F a w (type_slot_size tv) 0 u).vs_memory ==>
  LENGTH u.vs_memory <= LENGTH zm /\
  (!off len. off + len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
     mem_bytes_at off len zm = mem_bytes_at off len u.vs_memory)
Proof
  strip_tac >> Cases_on `type_slot_size tv = 0`
  >- gvs[immutable_transfers_def] >>
  `immutable_transfers F F a w (type_slot_size tv) 0 u =
    write_memory_with_expansion (w2n w)
      (mem_bytes_at (w2n a) (type_memory_size tv) u.vs_data_section) u` by
    (qspecl_then [`type_slot_size tv`, `w2n a`, `w2n w`, `0`, `u`] mp_tac
      immutable_runtime_transfers_snapshot >>
     simp[valueEncodingTheory.mem_bytes_at_def, valueEncodingPropsTheory.type_memory_size_slots] >>
     gvs[valueEncodingPropsTheory.type_memory_size_slots]) >>
  gvs[] >> conj_tac
  >- simp[immutableMemoryFrameTheory.immutable_write_memory_capacity] >>
  rpt strip_tac >>
  simp[valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint]
QED

Theorem unwrap_code_copy_path_mem[local]:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ ~is_word_type t /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
           type_memory_bytes cenv t = type_memory_size tvt) /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path_mem ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        expr_store_bound cx t v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, contextTheory.compile_ensure_in_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[] >> rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  rename1 `compile_imm_copy_to_memory _ _ _ _ _ _ mid = (_,sc)` >>
  `t = expr_type e` by gvs[vv_post_def, vv_holds_def] >>
  `?a. eval_operand p.ptr_operand s = SOME a /\
       immutable_holds cenv cx t (Value v) a es' s` by
    gvs[vv_post_def, vv_holds_def] >>
  `?tv. evaluate_type (get_tenv cx) t = SOME tv` by
    (gvs[immutable_holds_def] >> metis_tac[]) >>
  `val_wf tv v /\ w2n a + type_memory_size tv < dimword (:256)` by
    (drule_all immutable_holds_bounds >> simp[]) >>
  `type_memory_bytes cenv t = type_memory_size tv` by metis_tac[] >>
  `type_memory_bytes cenv t < dimword (:256)` by decide_tac >>
  `ci_mono sm mid` by
    (qspecl_then [`type_memory_bytes cenv t`, `sm`] mp_tac
       ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono mid sc` by
    (qpat_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND]) >>
  `cs_extends sm mid /\ cs_extends mid sc /\
   sm.cs_next_var <= mid.cs_next_var /\ mid.cs_next_id <= sc.cs_next_id` by
    gvs[ci_mono_def] >>
  `fn_has_code sm mid func /\ fn_has_code mid sc func` by
    metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx func cenv cx es' s` by fs[vv_post_def] >>
  drule_all alloc_buffer_source_path_mem >> strip_tac >>
  `copy_old_operand mid p.ptr_operand /\ copy_old_operand mid buf.buf_operand` by
    (rw[copy_old_operand_def] >> gvs[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `(type_memory_bytes cenv t + 31) DIV 32 = type_slot_size tv` by
    (simp[valueEncodingPropsTheory.type_memory_size_slots] >> decide_tac) >>
  qpat_x_assum `(_ + 31) DIV 32 = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  `alloca_inv u` by fs[stmt_state_rel_def] >>
  `w2n w + type_memory_size tv <= u.vs_alloca_next /\
   w2n w + type_memory_size tv < dimword (:256)` by gvs[] >>
  `w2n w + 0 + 32 * type_slot_size tv <= u.vs_alloca_next /\
   w2n w + 0 + 32 * type_slot_size tv < dimword (:256) /\
   w2n a + 0 + 32 * type_slot_size tv < dimword (:256)` by
    gvs[valueEncodingPropsTheory.type_memory_size_slots] >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv t))]
       [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  `?z. gas_path_mem ctx func u 0 (OK z) /\
       copy_static z = copy_static u /\
       (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
       z.vs_current_bb = sc.cs_current_bb /\
       z.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func z /\
       LENGTH u.vs_memory <= LENGTH z.vs_memory /\
       (!off len. off + len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
          mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
       val_in_memory tv v (w2n w) z.vs_memory /\
       val_footprint tv v <= type_memory_size tv` by
    (Cases_on `cenv.ce_is_ctor` >> fs[]
     >- (`immutable_base_zero cenv s` by fs[stmt_state_rel_def] >>
         `!region. cenv.ce_imm_alloca = SOME region ==>
             eval_operand region u = SOME 0w /\ copy_old_operand mid region` by
           (rpt strip_tac >>
            `eval_operand region s = SOME 0w` by fs[immutable_base_zero_def] >>
            `!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x` by
              metis_tac[local_ptrs_reserved_imm_base] >>
            `copy_old_operand sa region` by
              (simp[copy_old_operand_def] >> rpt strip_tac >> gvs[]) >>
            `copy_old_operand sm region` by
              (irule copy_old_operand_mono >> qexists_tac `sa` >> fs[]) >>
            `copy_old_operand mid region` by
              (irule copy_old_operand_mono >> qexists_tac `sm` >> fs[]) >>
            `eval_operand region u = eval_operand region s` by
              (Cases_on `region` >>
               fs[eval_operand_def, copy_old_operand_def]) >>
            fs[]) >>
         `w2n a + type_memory_size tv <= s.vs_alloca_next` by
           metis_tac[ctor_immutable_frontier] >>
         `w2n a + 0 + 32 * type_slot_size tv <= u.vs_alloca_next` by
           gvs[valueEncodingPropsTheory.type_memory_size_slots] >>
         qspecl_then [`cenv.ce_imm_alloca`, `p.ptr_operand`, `buf.buf_operand`,
           `type_slot_size tv`, `0`, `mid`, `sc`, `func`, `u`, `a`, `w`, `ctx`]
           mp_tac ctor_code_copy_path_mem >>
         impl_tac >- simp[] >> strip_tac >>
         qexists_tac `t'` >> simp[] >>
         `immutable_holds cenv cx t (Value v) a es' u` by
           (qpat_x_assum `immutable_holds _ _ _ _ _ _ s` mp_tac >>
            simp[immutable_holds_def]) >>
         `regions_disjoint (w2n a) (type_memory_size tv)
             (w2n w) (type_memory_size tv)` by
           (irule immutable_holds_alloca_disjoint >>
            qexistsl_tac [`cenv`, `ctx`, `cx`, `es'`, `func`] >>
            goal_assum (drule_at Any) >> simp[mk_inst_def] >>
            qexists_tac `mk_inst sm.cs_next_id ALLOCA
              [Lit (n2w (type_memory_size tv))]
              [STRING #"%" (toString sm.cs_next_var)]` >>
            gvs[mk_inst_def]) >>
         mp_tac (copy_ctor_contents
                 |> Q.INST [`uu` |-> `u`, `zz` |-> `t'`, `es` |-> `es'`]) >>
         impl_tac
         >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[]) >>
         strip_tac >> gvs[] >> first_assum ACCEPT_TAC) >>
     `w2n a + type_memory_size tv <= LENGTH u.vs_data_section` by
       (irule runtime_immutable_data_section >> metis_tac[]) >>
     `w2n a + 0 + 32 * type_slot_size tv <= LENGTH u.vs_data_section` by
       gvs[valueEncodingPropsTheory.type_memory_size_slots] >>
     qspecl_then [`cenv.ce_imm_alloca`, `p.ptr_operand`, `buf.buf_operand`,
       `type_slot_size tv`, `0`, `mid`, `sc`, `func`, `u`, `a`, `w`, `ctx`]
       mp_tac code_copy_path_mem >>
     impl_tac >- simp[] >> strip_tac >>
     qexists_tac `t'` >> simp[] >>
     mp_tac (runtime_copy_frame_facts |> Q.INST [`zm` |-> `t'.vs_memory`]) >>
     impl_tac >- fs[] >> strip_tac >>
     mp_tac (copy_runtime_contents
             |> Q.SPECL [`ctx`, `func`, `cenv`, `cx`, `es'`, `u`, `t`, `v`,
                         `a`, `tv`, `w`, `t'`, `s`]) >>
     impl_tac
     >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[]) >>
     strip_tac >> gvs[] >> first_assum ACCEPT_TAC) >>
  `eval_operand buf.buf_operand z = SOME w` by
    (qsuff_tac `eval_operand buf.buf_operand z = eval_operand buf.buf_operand u`
     >- gvs[] >>
     irule exprSimStorageCopyTheory.storage_copy_operand_preserved >> simp[] >>
     qexists_tac `mid` >> simp[]) >>
  `expr_post ctx func cenv cx e es sa sc s0 es' v buf.buf_operand z` by
    (irule buffer_post_transport >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`mid`, `p`, `s`, `sm`, `t`, `tv`, `u`, `w`] >>
     asm_rewrite_tac [] >> simp[]) >>
  `z.vs_alloca_next = u.vs_alloca_next` by
    (drule copy_static_fields >> simp[]) >>
  qspecl_then [`ctx`, `func`, `s`, `u`, `z`, `cenv`, `cx`, `e`, `es`, `sa`,
    `sc`, `s0`, `es'`, `v`, `buf.buf_operand`, `w`, `tv`, `t`] mp_tac
    copy_finish >>
  impl_tac >- gvs[] >> simp[]
QED

(* The copies into a fresh buffer: storage/transient and both kinds of
   code. *)
Theorem unwrap_copy_path_mem:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv (LocatedValue t p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
     p.ptr_location = LocCode) /\ ~is_word_type t /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt ==>
           type_memory_bytes cenv t = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue t p) s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path_mem ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        expr_store_bound cx t v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac
  >- (irule unwrap_storage_copy_path_mem >> rpt conj_tac >>
       TRY (first_assum ACCEPT_TAC) >> qexistsl_tac [`p`, `sm`] >> fs[])
  >- (irule unwrap_storage_copy_path_mem >> rpt conj_tac >>
       TRY (first_assum ACCEPT_TAC) >> qexistsl_tac [`p`, `sm`] >> fs[]) >>
  irule unwrap_code_copy_path_mem >> simp[] >> metis_tac[]
QED

(* unwrap_value_path's memory-checked form: every value_vv's code, one
   path, keeping the allocation history and bounding the result. *)
Theorem unwrap_value_path_mem:
  !ctx func cenv cx e es sa sm sb s0 es' v vv op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv vv sm = (op, sb) /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!t op'. vv = StackValue t op' ==> is_word_type (expr_type e)) /\
    (is_word_type (expr_type e) ==>
     ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
           ~is_word_type (expr_type e) ==>
           type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) es' (Value v) vv s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u. gas_path_mem ctx func s 0 (OK u) /\
        expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
        expr_store_bound cx (expr_type e) v op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  Cases_on `vv`
  >- (gvs[unwrap_value_def, comp_return_def] >> qexists_tac `s` >>
      simp[cj 1 gas_path_mem_rules, expr_store_bound_word] >>
      metis_tac[expr_post_of_vv_post_stack]) >>
  rename1 `LocatedValue t p` >>
  RULE_ASSUM_TAC (REWRITE_RULE [contextTheory.vv_operand_def]) >>
  Cases_on `p.ptr_location = LocCalldata`
  >- gvs[vv_post_calldata] >>
  Cases_on `p.ptr_location = LocMemory`
  >- (`is_word_type t ==> t = expr_type e` by
        (gvs[vv_post_def, vv_holds_def] >> metis_tac[is_bytestring_word_type]) >>
      reverse (Cases_on `is_word_type t`)
      >- (gvs[unwrap_value_def, comp_return_def] >> qexists_tac `s` >>
          simp[cj 1 gas_path_mem_rules] >>
          conj_tac >- metis_tac[expr_post_of_vv_post_memory] >>
          qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
          simp[vv_store_bound_def, expr_store_bound_def, read_result_def,
               return_def] >>
          metis_tac[]) >>
      gvs[] >>
      `read_result cx (Value v) es' = (INL v, es')` by
        simp[read_result_def, return_def] >>
      `is_word_type (expr_type e) ==> ?w. eval_operand p.ptr_operand s = SOME w /\
                              w2n w + 32 <= s.vs_alloca_next` by
        (strip_tac >> gvs[] >>
         `?w. eval_operand p.ptr_operand s = SOME w` by
           gvs[vv_post_def, vv_holds_def] >>
         qexists_tac `w` >> simp[] >>
         qpat_x_assum `vv_store_bound _ _ _ _ _ _ _`
           (mp_tac o CONJUNCT1 o REWRITE_RULE [vv_store_bound_def]) >>
         disch_then (qspecl_then [`expr_type e`, `p.ptr_operand`, `v`, `tvt`, `w`] mp_tac) >>
         simp[] >>
         `val_store_size tvt v = 32` by metis_tac[word_val_store_size] >>
         simp[]) >>
      drule_at (Pat `unwrap_value _ _ _ = _`) body_unwrap_memory_counted_read >>
      disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      simp[] >>
      disch_then (qspec_then `lowered_value_type cenv e` strip_assume_tac) >>
      qexists_tac `u` >> gvs[]) >>
  `t = expr_type e` by
    (Cases_on `p.ptr_location` >> gvs[vv_post_def, vv_holds_def]) >>
  Cases_on `is_word_type t`
  >- (Cases_on `p.ptr_location = LocCode`
      >- (Cases_on `cenv.ce_is_ctor`
          >- (drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_ctor_word_path_mem >>
              disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
              simp[] >> strip_tac >> qexists_tac `u` >>
              gvs[expr_store_bound_word]) >>
          drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_runtime_word_path_mem >>
          disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
          simp[] >> strip_tac >> qexists_tac `u` >>
          gvs[expr_store_bound_word]) >>
      `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` by
        (Cases_on `p.ptr_location` >> gvs[]) >>
      drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_storage_word_path_mem >>
      disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      simp[] >> strip_tac >> qexists_tac `u` >>
      gvs[expr_store_bound_word]) >>
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient \/
   p.ptr_location = LocCode` by (Cases_on `p.ptr_location` >> gvs[]) >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_copy_path_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> strip_tac >> gvs[] >> goal_assum drule >> simp[]
QED

(* The counted read suffix, memory-checked. *)
Theorem unwrap_value_marked_read_mem:
  !ctx func cenv cx e es sa sm sb s0 ee tv vv op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv vv sm = (op, sb) /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!t op'. vv = StackValue t op' ==> is_word_type (expr_type e)) /\
    (is_word_type (expr_type e) ==>
     ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
           ~is_word_type (expr_type e) ==>
           type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) /\
    vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?v u. gas_marked_exec T (ctx,func) (read_result cx tv) (ee,s)
            [] (INL v) ee (OK u) /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
      expr_store_bound cx (expr_type e) v op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `read_result cx tv ee` >> rename1 `_ = (res, ee')` >>
  `ee' = ee` by metis_tac[read_result_state] >> gvs[] >>
  reverse (Cases_on `res`)
  >- metis_tac[vv_post_failed_read] >>
  rename1 `read_result cx tv ee = (INL v, ee)` >>
  `vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee (Value v) vv s` by
    (qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
     rw[vv_store_bound_def] >> gvs[read_result_def, return_def] >>
     first_x_assum irule >> metis_tac[]) >>
  drule vv_post_read_result >> strip_tac >> gvs[] >> pop_assum kall_tac >>
  drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_path_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [`v`, `u`] >> simp[] >>
  simp[gas_marked_exec_def, gas_marked_path_def] >>
  metis_tac[read_result_gas_obs, APPEND]
QED

Theorem expr_sim_mem_of_vv_sim_mem:
  !ctx func cenv cx ty e es.
    post_value_type cenv e = expr_type e /\
    expr_vv_sim_mem ctx func cenv cx ty e es /\
    (!sa t op sb. compile_expr cenv ty e sa = (StackValue t op, sb) ==>
                  is_word_type (expr_type e)) /\
    (is_word_type (expr_type e) ==>
     ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
           ~is_word_type (expr_type e) ==>
           type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) ==>
    expr_sim_mem ctx func cenv cx ty e es
Proof
  rw[expr_sim_mem_def] >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty e sa` >> rename1 `_ = (vv, sm)` >>
  simp[] >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    (drule (cj 1 exprOperandVarTheory.compiler_compile_var) >> simp[]) >>
  `!t op'. vv = StackValue t op' ==> is_word_type (expr_type e)` by
    (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_sim_mem_def] >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `s0`] mp_tac) >>
  simp[] >>
  rewrite_tac[gas_outcome_def] >> strip_tac >>
  qexists_tac `marks`
  >- (disj1_tac >> gvs[gas_summary_at_def]
      >- (rename1 `vv_post _ _ _ _ _ _ _ _ _ _ tv vv u` >>
          `~u.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          `MAP FDOM es.scopes = MAP FDOM (es_end with gas_obs := []).scopes` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
               (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
             strip_tac >> first_x_assum (qspec_then `[]` assume_tac) >>
             drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >>
             simp[]) >>
          drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_marked_read_mem >>
          disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
          impl_tac >- simp[] >> strip_tac >>
          rename1 `gas_marked_exec T _ (read_result _ _) _ [] _ _ (OK u2)` >>
          qexistsl_tac [`INL v`, `es_end with gas_obs := []`, `OK u2`] >>
          simp[] >>
          `marks = marks ++ []` by simp[] >>
          pop_assum SUBST1_TAC >> irule gas_marked_exec_bind_normal >>
          goal_assum drule >> simp[]) >>
      Cases_on `res`
      >- (Cases_on `r` >> gvs[expr_exit_def]) >>
      rename1 `expr_exit (INR exc) r` >>
      `expr_res_ok (INR exc : value + exception)` by
        (Cases_on `exc` >> Cases_on `r` >>
         gvs[expr_exit_def, expr_res_ok_def, AllCaseEqs()] >>
         Cases_on `e'` >> gvs[expr_exit_def, expr_res_ok_def]) >>
      qexistsl_tac [`INR exc`, `es_end`, `r`] >>
      simp[GSYM expr_exit_exception_transport] >>
      irule gas_marked_exec_bind_exception >> goal_assum drule) >>
  disj2_tac >> metis_tac[force_exempt_cert]
QED
