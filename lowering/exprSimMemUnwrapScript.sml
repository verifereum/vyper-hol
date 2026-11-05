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
  venomExecSemantics venomInst venomState list rich_list finite_map

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
  `t = expr_type e /\
   ?w. eval_operand p.ptr_operand s = SOME w /\
       storage_holds cx (p.ptr_location = LocTransient) (expr_type e)
         (Value v) w es' s /\
       stmt_state_rel ctx func cenv cx es' s` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  qabbrev_tac `ld = if p.ptr_location = LocTransient then tload w s
                    else sload w s` >>
  `!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
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
  irule expr_post_of_vv_post_load >> simp[] >>
  qexistsl_tac [`p`, `s`, `sm`, `expr_type e`] >> simp[])
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
  `t = expr_type e /\
   ?w. eval_operand p.ptr_operand s = SOME w /\
       immutable_holds cenv cx (expr_type e) (Value v) w es' s /\
       stmt_state_rel ctx func cenv cx es' s` by
    gvs[vv_post_def, vv_holds_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv` by
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
  irule expr_post_of_vv_post_load >> simp[] >>
  qexistsl_tac [`p`, `s`, `sm`, `expr_type e`] >> simp[]
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
  `t = expr_type e /\
   ?w. eval_operand p.ptr_operand s = SOME w /\
       immutable_holds cenv cx (expr_type e) (Value v) w es' s /\
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
  irule expr_post_of_vv_post_load >> simp[] >>
  qexistsl_tac [`p`, `s`, `sm`, `expr_type e`] >> simp[]
QED

(* The copies into a fresh buffer: storage/transient and both kinds of
   code. *)
Theorem unwrap_copy_path_mem:
  !ctx func cenv cx e es sa sm sb s0 es' v t p op s.
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
  cheat
QED

(* unwrap_value_path's memory-checked form: every value_vv's code, one
   path, keeping the allocation history and bounding the result. *)
Theorem unwrap_value_path_mem:
  !ctx func cenv cx e es sa sm sb s0 es' v vv op s.
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
    vv_store_bound cx (expr_type e) es' (Value v) vv s /\
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
  `t = expr_type e` by gvs[vv_post_def, vv_holds_def] >>
  Cases_on `p.ptr_location = LocCalldata`
  >- gvs[vv_post_calldata] >>
  Cases_on `p.ptr_location = LocMemory`
  >- (`read_result cx (Value v) es' = (INL v, es')` by
        simp[read_result_def, return_def] >>
      `is_word_type t ==> ?w. eval_operand p.ptr_operand s = SOME w /\
                              w2n w + 32 <= s.vs_alloca_next` by
        (strip_tac >> gvs[] >>
         `?w. eval_operand p.ptr_operand s = SOME w` by
           gvs[vv_post_def, vv_holds_def] >>
         qexists_tac `w` >> simp[] >>
         qpat_x_assum `vv_store_bound _ _ _ _ _ _`
           (mp_tac o REWRITE_RULE [vv_store_bound_def]) >>
         disch_then (qspecl_then [`expr_type e`, `p`, `v`, `tvt`, `w`] mp_tac) >>
         simp[] >> metis_tac[word_val_store_size]) >>
      drule_at (Pat `unwrap_value _ _ _ = _`) body_unwrap_memory_counted_read >>
      disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      simp[] >> strip_tac >> qexists_tac `u` >> gvs[]) >>
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
    vv_store_bound cx (expr_type e) ee tv vv s /\
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
  `vv_store_bound cx (expr_type e) ee (Value v) vv s` by
    (qpat_x_assum `vv_store_bound _ _ _ _ _ _` mp_tac >>
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
