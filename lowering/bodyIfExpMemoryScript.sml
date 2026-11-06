Theory bodyIfExpMemory
Ancestors
  loweringPosts
  exprBopSimProps
  exprSimIfExp fragExec fragExecMem instMemFrontier allocaHistoryFragment
  emitHelper emitHelperProps compileEnv venomState venomInst
  list rich_list loweringSlice venomExecSemantics venomExecProofs exprLoweringProps
  bodyMemoryDefs exprSimMemDefs exprSimDefs vyperAST vyperInterpreter memSafeRun allocaHistory

Theorem frag_exec_assign_mem:
  !ctx st st' src out P Q R.
    emit_inst ASSIGN [src] [out] st = ((), st') /\
    (!s. P s ==> ?w. eval_operand src s = SOME w /\
                     Q ((update_var out w s) with
                          vs_inst_idx := LENGTH st'.cs_current_insts)) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  rpt strip_tac >> imp_res_tac emit_inst_extends >>
  irule frag_exec_mem_run_inst_seq >>
  `emitted_insts st st' = [mk_inst st.cs_next_id ASSIGN [src] [out]]` by
    simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[venomInstTheory.mk_inst_def, is_terminator_def] >> gen_tac >> disch_tac >>
  first_x_assum drule >> strip_tac >>
  conj_tac
  >- (simp[GSYM mk_inst_def, run_inst_seq_mem_ok_last] >>
      irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  disj1_tac >>
  simp[run_inst_seq_def, step_inst_base_def, exec_pure1_def, comp_bind_def,
       comp_return_def] >> gvs[]
QED

Theorem assign_history[local]:
  emit_inst ASSIGN [src] [out] st = ((),st') /\ fn_has_code st st' func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand src s = SOME w ==>
  alloca_history func ((update_var out w s) with
                       vs_inst_idx := LENGTH st'.cs_current_insts)
Proof
  rpt strip_tac >> imp_res_tac emit_inst_extends >>
  `emitted_insts st st' = [mk_inst st.cs_next_id ASSIGN [src] [out]]` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `run_inst_seq (emitted_insts st st') s = OK (update_var out w s)` by
    simp[run_inst_seq_def, mk_inst_def, step_inst_base_def, exec_pure1_def,
         comp_bind_def, comp_return_def] >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts st st' ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts st st') = LENGTH st'.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st st')` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def, is_terminator_def]) >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

Theorem frag_exec_assign_mem_at:
  emit_inst ASSIGN [src] [out] st = ((),st') /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func entry /\ alloca_inv entry /\
  eval_operand src entry = SOME w ==>
  frag_exec_mem ctx st st' (\s. s = entry)
    (\s. s = ((update_var out w entry) with
                vs_inst_idx := LENGTH st'.cs_current_insts) /\
         alloca_history func s /\
         s.vs_alloca_next = entry.vs_alloca_next) R
Proof
  rpt strip_tac >>
  qabbrev_tac `P = \s. s = entry /\ ~s.vs_halted /\
     s.vs_current_bb = st.cs_current_bb /\
     s.vs_inst_idx = LENGTH st.cs_current_insts` >>
  `frag_exec_mem ctx st st' P
    (\s. s = ((update_var out w entry) with
                vs_inst_idx := LENGTH st'.cs_current_insts) /\
         alloca_history func s /\
         s.vs_alloca_next = entry.vs_alloca_next) R` suffices_by
    (simp[frag_exec_mem_def, Abbr `P`] >> metis_tac[]) >>
  irule frag_exec_assign_mem >> qexistsl_tac [`out`, `src`] >> simp[] >>
  gen_tac >> strip_tac >> gvs[Abbr `P`] >>
  drule_all assign_history >> simp[update_var_def]
QED

Theorem ifexp_arm_frag_mem:
  !ctx func cenv cx ty e es1 res es' bs bm bn eop rv tt lbl.
    expr_sim_mem ctx func cenv cx ty e es1 /\
    lower_value compile_expr cenv ty e bs = (eop, bm) /\
    emit_inst ASSIGN [eop] [rv] bm = ((), bn) /\
    (do result <- eval_expr cx e; read_result cx result od) es1 = (res, es') /\
    expr_res_ok res /\ fn_has_code bs bn func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv bs /\ stmt_state_rel ctx func cenv cx es1 tt /\
    cs_extends bs bm /\ alloca_history func (jump_to lbl tt) /\
    res <> INR (Error (RuntimeError "convert empty bytes to signed")) ==>
    frag_exec_mem ctx bs bn (\s. s = jump_to lbl tt)
      (\s. (?v u w. res = INL v /\
             expr_post ctx func cenv cx e es1 bs bm (jump_to lbl tt) es' v eop u /\
             eval_operand eop u = SOME w /\
             s = (update_var rv w u) with
                   vs_inst_idx := LENGTH bn.cs_current_insts) /\
           alloca_history func s /\
           (jump_to lbl tt).vs_alloca_next <= s.vs_alloca_next)
      (expr_exit res)
Proof
  rpt strip_tac >>
  `cs_extends bm bn` by metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code bs bm func /\ fn_has_code bm bn func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`bs`, `bm`, `eop`, `res`, `es'`, `jump_to lbl tt`]
                mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_pre_exit_c) >>
  disch_then (qspecl_then [`\s. s = jump_to lbl tt`, `expr_exit res`] mp_tac) >>
  (impl_tac >- simp[stmt_state_rel_jump_to]) >>
  disch_then (fn th => irule (MATCH_MP frag_exec_mem_then th)) >>
  simp[] >> rpt strip_tac >>
  `?w. eval_operand eop t = SOME w` by
    (gvs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  `alloca_inv t` by gvs[expr_post_def, stmt_state_rel_def] >>
  drule_all frag_exec_assign_mem_at >>
  disch_then (qspecl_then [`ctx`, `expr_exit res`] mp_tac) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_weaken) >>
  disch_then irule >> simp[] >>
  strip_tac >> qexistsl_tac [`t`, `w`] >> simp[]
QED

Theorem ifexp_jump_result_mem[local]:
  !fuel ctx fn s bb inst lbl r.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst_base inst s = OK (jump_to lbl s) /\ ~s.vs_halted /\
    inst_mem_below_frontier inst s /\
    run_from fuel ctx fn (jump_to lbl s) = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn (jump_to lbl s) ==>
       mem_safe_run fuel' ctx fn s)
Proof
  rpt strip_tac >> qexists_tac `SUC fuel` >> conj_tac
  >- (irule run_from_jump_result >> metis_tac[]) >>
  strip_tac >>
  Cases_on `lookup_block lbl fn.fn_blocks`
  >- gvs[run_from_def, jump_to_def] >>
  rename1 `lookup_block lbl _ = SOME bb'` >>
  Cases_on `phi_prefix_length bb'.bb_instructions = 0`
  >- (`eval_phis (jump_to lbl s) bb'.bb_instructions = OK (jump_to lbl s)` by
        (Cases_on `bb'.bb_instructions` >> gvs[phi_prefix_length_def] >>
         rename1 `h.inst_opcode` >> Cases_on `h.inst_opcode = PHI` >>
         gvs[phi_prefix_length_def, eval_phis_def]) >>
      simp[mem_safe_run_def, Once mem_safe_block_def,
           mem_safe_step_non_invoke, step_inst_non_invoke,
           Once exec_block_def, jump_to_def] >>
      mp_tac mem_safe_blocks_run >>
      disch_then (qspecl_then [`fuel`, `ctx`, `fn`, `jump_to lbl s`,
                             `bb'`, `jump_to lbl s`] mp_tac) >>
      simp[jump_to_def] >> gvs[jump_to_def]) >>
  `?phi rest. bb'.bb_instructions = phi :: rest /\ phi.inst_opcode = PHI` by
    (Cases_on `bb'.bb_instructions` >> gvs[phi_prefix_length_def] >>
     rename1 `h.inst_opcode` >> Cases_on `h.inst_opcode = PHI` >> gvs[]) >>
  qpat_x_assum `run_from _ _ _ _ = _` mp_tac >>
  simp[run_from_def, jump_to_def, Once exec_block_def, get_instruction_def,
       step_inst_non_invoke, step_inst_base_def]
QED

Theorem ifexp_branch_to_exit_mem:
  !ctx fn s0 sc jbb jnz sa sb sx sd lbl lbl' x P Q R.
    lookup_block sc.vs_current_bb fn.fn_blocks = SOME jbb /\
    get_instruction jbb sc.vs_inst_idx = SOME jnz /\
    is_terminator jnz.inst_opcode /\ jnz.inst_opcode <> INVOKE /\
    step_inst_base jnz sc = OK (jump_to sa.cs_current_bb sc) /\
    ~sc.vs_halted /\ inst_mem_below_frontier jnz sc /\
    (!fuel r. run_from fuel ctx fn sc = r /\ (!e. r <> Error e) ==>
              ?fuel'. run_from fuel' ctx fn s0 = r /\
                (mem_safe_run fuel ctx fn sc ==> mem_safe_run fuel' ctx fn s0)) /\
    sa.cs_current_insts = [] /\ P (jump_to sa.cs_current_bb sc) /\
    frag_exec_mem ctx sa sb P Q R /\ cs_extends sa sb /\
    emit_inst JMP [Label lbl] [] sb = ((), sx) /\
    new_block lbl' sx = (x, sd) /\ fn_has_code sa sd fn ==>
    (?s'. Q s' /\ ~s'.vs_halted /\
          !fuel r. run_from fuel ctx fn (jump_to lbl s') = r /\
                   (!e. r <> Error e) ==>
                   ?fuel'. run_from fuel' ctx fn s0 = r /\
                     (mem_safe_run fuel ctx fn (jump_to lbl s') ==>
                      mem_safe_run fuel' ctx fn s0)) \/
    (?fuel r. run_from fuel ctx fn s0 = r /\ exit_result r /\ R r /\
              mem_safe_run fuel ctx fn s0)
Proof
  rpt strip_tac >>
  `cs_extends sb sx /\ cs_extends sx sd` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def, cs_extends_new_block] >>
  `fn_has_code sa sb fn /\ fn_has_code sx sd fn` by
    metis_tac[fn_has_code_mid, cs_extends_refl, cs_extends_trans] >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [frag_exec_mem_def]) >>
  disch_then (qspecl_then [`fn`, `jump_to sa.cs_current_bb sc`] mp_tac) >>
  (impl_tac >- simp[jump_to_def]) >>
  strip_tac
  >- (disj1_tac >> qexists_tac `s'` >> simp[] >> rpt strip_tac >>
      imp_res_tac emit_inst_extends >>
      qabbrev_tac `j = mk_inst sb.cs_next_id JMP [Label lbl] []` >>
      qabbrev_tac `jb = <| bb_label := sx.cs_current_bb;
                           bb_instructions := sx.cs_current_insts |>` >>
      `lookup_block s'.vs_current_bb fn.fn_blocks = SOME jb` by
        metis_tac[fn_has_code_new_block] >>
      `get_instruction jb s'.vs_inst_idx = SOME j` by
        simp[Abbr `jb`, get_instruction_def, EL_LENGTH_APPEND] >>
      `j.inst_opcode = JMP /\ step_inst_base j s' = OK (jump_to lbl s')` by
        simp[Abbr `j`, mk_inst_def, step_jmp_behavior] >>
      `is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
       inst_mem_below_frontier j s'` by
        (simp[is_terminator_def] >> irule below_frontier_no_ranges >>
         simp[Abbr `j`, mk_inst_def]) >>
      `?fuel'. run_from fuel' ctx fn s' = run_from fuel ctx fn (jump_to lbl s') /\
         (mem_safe_run fuel ctx fn (jump_to lbl s') ==>
          mem_safe_run fuel' ctx fn s')` by
        (irule ifexp_jump_result_mem >> metis_tac[]) >>
      qpat_x_assum `!fuel r. run_from fuel ctx fn s' = r /\ _ ==> _`
        drule_all >> strip_tac >>
      drule_all ifexp_jump_result_mem >> strip_tac >>
      metis_tac[]) >>
  disj2_tac >>
  `!e. r <> Error e` by metis_tac[exit_result_not_error] >>
  drule_all ifexp_jump_result_mem >> strip_tac >>
  metis_tac[]
QED

Theorem ifexp_history_jump[local]:
  alloca_history func s ==> alloca_history func (jump_to lbl s)
Proof
  strip_tac >> irule alloca_history_jump >> simp[jump_to_def] >>
  qexists_tac `s` >> simp[]
QED

Theorem ifexp_point_branch_to_exit_mem[local]:
  !ctx fn sc jbb jnz sa sb sx sd lbl lbl' x Q R.
    lookup_block sc.vs_current_bb fn.fn_blocks = SOME jbb /\
    get_instruction jbb sc.vs_inst_idx = SOME jnz /\
    is_terminator jnz.inst_opcode /\ jnz.inst_opcode <> INVOKE /\
    step_inst_base jnz sc = OK (jump_to sa.cs_current_bb sc) /\
    ~sc.vs_halted /\ inst_mem_below_frontier jnz sc /\
    sa.cs_current_insts = [] /\
    frag_exec_mem ctx sa sb (\s. s = jump_to sa.cs_current_bb sc) Q R /\
    cs_extends sa sb /\ emit_inst JMP [Label lbl] [] sb = ((),sx) /\
    new_block lbl' sx = (x,sd) /\ fn_has_code sa sd fn ==>
    (?s'. Q s' /\ ~s'.vs_halted /\
          !fuel r. run_from fuel ctx fn (jump_to lbl s') = r /\
                   (!e. r <> Error e) ==>
                   ?fuel'. run_from fuel' ctx fn sc = r /\
                     (mem_safe_run fuel ctx fn (jump_to lbl s') ==>
                      mem_safe_run fuel' ctx fn sc)) \/
    (?fuel r. run_from fuel ctx fn sc = r /\ exit_result r /\ R r /\
              mem_safe_run fuel ctx fn sc)
Proof
  rpt strip_tac >> irule ifexp_branch_to_exit_mem >>
  qexists_tac `\s. s = jump_to sa.cs_current_bb sc` >>
  simp[] >> metis_tac[]
QED

Theorem ifexp_jnz_arm_mem:
  !ctx func cenv cx t c a b e bv es es1 es' res sa sb s0 s1 s5 s6 x6 s7
   bs bm bn bo bx bp tl el xl bl lbl rv cond_op eop tt.
    frag_exec_mem ctx bs bn (\s. s = jump_to bl tt)
      (\s. (?v u w. res = INL v /\
             expr_post ctx func cenv cx e es1 bs bm (jump_to bl tt) es' v eop u /\
             eval_operand eop u = SOME w /\
             s = (update_var rv w u) with
                   vs_inst_idx := LENGTH bn.cs_current_insts) /\
           alloca_history func s /\ tt.vs_alloca_next <= s.vs_alloca_next)
      (expr_exit res) /\
    expr_post ctx func cenv cx c es sa s1 s0 es1 (BoolV bv) cond_op tt /\
    eval_operand cond_op tt = SOME (val_to_w256 (BoolV bv)) /\
    emit_inst JNZ [cond_op; Label tl; Label el] [] s5 = ((), s6) /\
    new_block tl s6 = (x6, s7) /\
    emit_inst JMP [Label xl] [] bn = ((), bo) /\
    new_block lbl bo = (bx, bp) /\
    (if bv then tl else el) = bl /\ bs.cs_current_bb = bl /\
    bs.cs_current_insts = [] /\
    s5.cs_current_bb = s1.cs_current_bb /\
    s5.cs_current_insts = s1.cs_current_insts /\
    sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
    cs_extends s1 s6 /\ cs_extends s6 s7 /\ cs_extends s7 sb /\
    cs_extends s1 bs /\ cs_extends bs bn /\ cs_extends bs bp /\
    cs_extends bp sb /\
    sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= bs.cs_next_var /\
    sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= bs.cs_next_id /\
    bm.cs_next_id <= sb.cs_next_id /\
    expr_type e = t /\ post_value_type cenv e = expr_type e /\
    (!x. not_fresh_at sa x ==> x <> rv) /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    s0.vs_alloca_next <= tt.vs_alloca_next ==>
    frag_exec_mem ctx s1 sb (\s. s = tt)
      (\s. (?v. res = INL v /\
                vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 es' (Value v)
                  (if is_word_type t then StackValue t (Var rv)
                   else LocatedValue t (mk_ptr (Var rv) LocMemory)) s) /\
            s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
      (expr_exit res)
Proof
  rpt strip_tac >> imp_res_tac emit_inst_extends >>
  PURE_REWRITE_TAC[frag_exec_mem_def] >> BETA_TAC >> rpt strip_tac >>
  qpat_x_assum `_ = tt` SUBST_ALL_TAC >>
  `step_inst_base (mk_inst s5.cs_next_id JNZ [cond_op; Label tl; Label el] [])
     tt = OK (jump_to bl tt)` by
    (qpat_x_assum `(if _ then _ else _) = bl` (SUBST_ALL_TAC o SYM) >>
     simp[mk_inst_def] >> drule step_jnz_behavior >>
     disch_then (fn th => simp[th]) >> Cases_on `bv` >> simp[valueEncodingTheory.val_to_w256_def]) >>
  qabbrev_tac `jnz = mk_inst s5.cs_next_id JNZ [cond_op; Label tl; Label el] []` >>
  qabbrev_tac `jbb = <| bb_label := s6.cs_current_bb;
                        bb_instructions := s6.cs_current_insts |>` >>
  `fn_has_code s6 s7 fn /\ fn_has_code bs bp fn` by
    metis_tac[fn_has_code_mid, cs_extends_trans, cs_extends_refl] >>
  `lookup_block tt.vs_current_bb fn.fn_blocks = SOME jbb` by
    (`tt.vs_current_bb = s6.cs_current_bb` by fs[] >>
     simp[Abbr `jbb`] >> metis_tac[fn_has_code_new_block]) >>
  `get_instruction jbb tt.vs_inst_idx = SOME jnz` by
    fs[Abbr `jbb`, get_instruction_def, EL_LENGTH_APPEND] >>
  `is_terminator jnz.inst_opcode /\ jnz.inst_opcode <> INVOKE /\
   inst_mem_below_frontier jnz tt` by
    (simp[Abbr `jnz`, mk_inst_def, is_terminator_def] >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `step_inst_base jnz tt = OK (jump_to bs.cs_current_bb tt)` by simp[] >>
  qpat_x_assum `bs.cs_current_bb = bl` (SUBST_ALL_TAC o SYM) >>
  drule_all ifexp_point_branch_to_exit_mem >>
  BETA_TAC >> strip_tac
  >- (disj1_tac >> qexists_tac `jump_to xl s'` >> rpt conj_tac
      >- (qexists_tac `v` >> simp[] >>
          qspecl_then [`func`, `cenv`, `cx`, `IfExp t c a b`] mp_tac
            vv_post_of_expr_post >>
          simp[expr_type_def] >> disch_then irule >>
          irule expr_post_ifexp >>
          first_assum (irule_at Any) >> first_assum (irule_at Any) >>
          qexistsl_tac [`BoolV bv`, `s1`, `cond_op`] >> simp[] >> metis_tac[])
      >- (gvs[jump_to_def, update_var_def] >> decide_tac)
      >- (irule ifexp_history_jump >> simp[])
      >- (gvs[jump_to_def, update_var_def])
      >- simp[jump_to_def]
      >- simp[jump_to_def] >>
      simp[]) >>
  disj2_tac >> metis_tac[]
QED

Theorem ifexp_branch_sim_mem:
  !ctx func cenv cx ty t c a b e bv es es1 es' res sa sb s0 s1 s5 s6 x6 s7
   bs bm bn bo bx bp tl el xl bl lbl rv cond_op eop.
    expr_type c = BaseT BoolT /\ expr_sim_mem ctx func cenv cx (BaseT BoolT) c es /\
    expr_sim_mem ctx func cenv cx ty e es1 /\
    (do result <- eval_expr cx c; read_result cx result od) es = (INL (BoolV bv), es1) /\
    (do result <- eval_expr cx e; read_result cx result od) es1 = (res, es') /\
    expr_res_ok res /\ expr_type e = t /\ post_value_type cenv e = expr_type e /\
    res <> INR (Error (RuntimeError "convert empty bytes to signed")) /\
    lower_value compile_expr cenv (BaseT BoolT) c sa = (cond_op, s1) /\
    emit_inst JNZ [cond_op; Label tl; Label el] [] s5 = ((), s6) /\
    new_block tl s6 = (x6, s7) /\
    lower_value compile_expr cenv ty e bs = (eop, bm) /\
    emit_inst ASSIGN [eop] [rv] bm = ((), bn) /\
    emit_inst JMP [Label xl] [] bn = ((), bo) /\
    new_block lbl bo = (bx, bp) /\
    (if bv then tl else el) = bl /\ bs.cs_current_bb = bl /\
    bs.cs_current_insts = [] /\
    s5.cs_current_bb = s1.cs_current_bb /\
    s5.cs_current_insts = s1.cs_current_insts /\
    sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
    cs_extends sa s1 /\ cs_extends s1 s5 /\ cs_extends s7 bs /\
    cs_extends bs bm /\ cs_extends bp sb /\
    sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= bs.cs_next_var /\
    sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= bs.cs_next_id /\
    bm.cs_next_id <= sb.cs_next_id /\
    (!x. not_fresh_at sa x ==> x <> rv) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
    alloca_history func s0 ==>
    frag_exec_mem ctx sa sb
      (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s)
      (\s. (?v. res = INL v /\
                vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 es' (Value v)
                  (if is_word_type t then StackValue t (Var rv)
                   else LocatedValue t (mk_ptr (Var rv) LocMemory)) s) /\
            s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
      (expr_exit res)
Proof
  rpt strip_tac >>
  `cs_extends s5 s6 /\ cs_extends bm bn /\ cs_extends bn bo` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends s6 s7 /\ cs_extends bo bp` by metis_tac[cs_extends_new_block] >>
  `cs_extends bs bn /\ cs_extends bs bp /\ cs_extends bs sb /\
   cs_extends bm sb /\ cs_extends s1 s6 /\ cs_extends s1 s7 /\
   cs_extends s7 sb /\ cs_extends s1 bs /\ cs_extends s1 sb /\
   cs_extends sa bs` by metis_tac[cs_extends_trans] >>
  `cs_extends bn sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func` by metis_tac[fn_has_code_split] >>
  `fn_has_code bs bn func` by
    (irule fn_has_code_mid >> simp[] >> qexistsl_tac [`sb`, `sa`] >> simp[]) >>
  `local_ptrs_reserved cenv bs` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
    (qpat_x_assum `(do result <- eval_expr cx c; read_result cx result od) es = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[vyperStateTheory.bind_def, AllCaseEqs()] >> strip_tac >>
     imp_res_tac vyperStateTheory.read_result_state >> gvs[] >>
     metis_tac[vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ (BaseT BoolT) c _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `cond_op`, `INL (BoolV bv)`, `es1`, `s0`] mp_tac) >>
  (impl_tac >- simp[expr_res_ok_def]) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_pre_exit_c) >>
  disch_then (qspecl_then
    [`\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s`,
     `expr_exit res`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => irule (MATCH_MP frag_exec_mem_then th)) >>
  simp[] >> rpt strip_tac >> fs[] >>
  rename1 `expr_post ctx func cenv cx c es sa s1 s0 es1 (BoolV bv) cond_op tt` >>
  `stmt_state_rel ctx func cenv cx es1 tt /\
   eval_operand cond_op tt = SOME (val_to_w256 (BoolV bv))` by
    (fs[expr_post_def] >>
     qspecl_then [`cx`, `BaseT BoolT`, `BoolV bv`, `cond_op`, `tt`] mp_tac
       exprBopSimPropsTheory.expr_val_rel_word >>
     simp[word_value_def, is_word_type_def, vyperValueTheory.evaluate_type_def] >>
     disch_then irule >> gvs[]) >>
  `alloca_history func (jump_to bs.cs_current_bb tt)` by
    (irule ifexp_history_jump >> simp[]) >>
  `!l s. (jump_to l s).vs_alloca_next = s.vs_alloca_next` by
    simp[jump_to_def] >>
  drule_all ifexp_arm_frag_mem >> simp[] >> strip_tac >>
  irule ifexp_jnz_arm_mem >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _` (irule_at Any) >>
  simp[] >>
  qpat_assum `expr_post _ _ _ _ c _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `emit_inst JNZ _ _ _ = _` (irule_at Any) >>
  qpat_assum `new_block tl _ = _` (irule_at Any) >>
  qpat_assum `new_block lbl _ = _` (irule_at Any) >> simp[]
QED

Theorem compile_ifexp_forced_frag_mem:
  !ctx func cenv cx ty t c a b es.
    expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
    (!e. (e = a \/ e = b) ==> post_value_type cenv e = expr_type e) /\
    (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    (!e sa sb op. (e = a \/ e = b) /\
       lower_value compile_expr cenv ty e sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    expr_sim_mem ctx func cenv cx (BaseT BoolT) c es /\
    (!tv es1. (do result <- eval_expr cx c; read_result cx result od) es = (INL tv, es1) ==>
       expr_sim_mem ctx func cenv cx ty a es1 /\
       expr_sim_mem ctx func cenv cx ty b es1) ==>
    !sa sb vv res es' s0.
      compile_expr cenv ty (IfExp t c a b) sa = (vv, sb) /\
      (do result <- eval_expr cx (IfExp t c a b); read_result cx result od) es = (res, es') /\
      expr_res_ok res /\
      res <> INR (Error (RuntimeError "convert empty bytes to signed")) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec_mem ctx sa sb
        (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s)
        (\s. (?v. res = INL v /\
                  vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 es' (Value v) vv s) /\
              s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
        (expr_exit res)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0`)
  >- (simp[frag_exec_mem_def] >> metis_tac[]) >>
  gvs[] >> drule_all compile_expr_ifexp_states >> strip_tac >>
  drule eval_expr_ifexp_cases >> strip_tac
  >- (`fn_has_code sa s1 func` by metis_tac[fn_has_code_split] >>
      qpat_x_assum `expr_sim_mem _ _ _ _ (BaseT BoolT) c _`
        (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
      disch_then (qspecl_then [`sa`, `s1`, `cond_op`, `INR exc`, `es'`, `s0`] mp_tac) >>
      (impl_tac >- gvs[]) >>
      disch_then (mp_tac o MATCH_MP frag_exec_mem_weaken) >>
      disch_then (qspecl_then
        [`\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s`,
         `\s. F`, `expr_exit res`] mp_tac) >>
      (impl_tac >- gvs[]) >> strip_tac >>
      irule frag_exec_mem_exit_prefix >> qexists_tac `s1` >> simp[])
  >- (qpat_x_assum `!tv es1. (do result <- eval_expr cx c; read_result cx result od) es = _ ==> _` drule >>
      strip_tac >> Cases_on `bv` >> fs[]
      >- (irule ifexp_branch_sim_mem >> simp[cs_extends_refl] >>
          qpat_assum `lower_value _ _ _ a s7 = _` (irule_at Any) >>
          qpat_assum `emit_inst ASSIGN [aop] _ _ = _` (irule_at Any) >>
          qpat_assum `emit_inst JMP _ _ s9 = _` (irule_at Any) >>
          qpat_assum `new_block el s10 = _` (irule_at Any) >>
          simp[] >> qpat_assum `emit_inst JNZ _ _ _ = _` (irule_at Any) >>
          qpat_assum `new_block tl s6 = _` (irule_at Any) >> simp[cs_extends_refl]) >>
      irule ifexp_branch_sim_mem >> simp[cs_extends_refl] >>
      qpat_assum `lower_value _ _ _ b s11 = _` (irule_at Any) >>
      qpat_assum `emit_inst ASSIGN [bop] _ _ = _` (irule_at Any) >>
      qpat_assum `emit_inst JMP _ _ s13 = _` (irule_at Any) >>
      qpat_assum `new_block xl s14 = _` (irule_at Any) >>
      simp[] >> qpat_assum `emit_inst JNZ _ _ _ = _` (irule_at Any) >>
      qpat_assum `new_block tl s6 = _` (irule_at Any) >> simp[cs_extends_refl]) >>
  gvs[expr_res_ok_def]
QED

Theorem readable_eval_frag_transport_mem:
  eval_expr cx e es = (raw,es') /\ expr_read_res_ok cx es' raw /\
  raw <> INR (Error (RuntimeError "convert empty bytes to signed")) /\
  (!res. (do result <- eval_expr cx e; read_result cx result od) es = (res,es') /\
         expr_res_ok res /\
         res <> INR (Error (RuntimeError "convert empty bytes to signed")) ==>
         frag_exec_mem ctx sa sb P
           (\s. (?v. res = INL v /\
                vv_post ctx func cenv cx e es sa sb s0 es' (Value v) vv s) /\
                 s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
           (expr_exit res)) ==>
  frag_exec_mem ctx sa sb P
    (\s. (?tv. raw = INL tv /\
         vv_post ctx func cenv cx e es sa sb s0 es' tv vv s) /\
          s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
    (expr_exit raw)
Proof
  strip_tac >> fs[expr_read_res_ok_def] >> gvs[]
  >- (qpat_x_assum `!res. _` (qspec_then `INL v` mp_tac) >>
      simp[vyperStateTheory.bind_def, expr_res_ok_def] >>
      drule exprSimUnwrapTheory.vv_post_read_result >> strip_tac >>
      `expr_exit (INL v) = (\r. F)` by simp[FUN_EQ_THM] >>
      `expr_exit (INL r) = (\r. F)` by simp[FUN_EQ_THM] >> simp[]) >>
  `expr_exit (INR exc : value + exception) =
   expr_exit (INR exc : eval_result + exception)` by
    (fs[expr_res_ok_def] >> rewrite_tac[FUN_EQ_THM] >> Cases >> simp[expr_exit_def]) >>
  qpat_x_assum `!res. _` (qspec_then `INR exc` mp_tac) >> simp[vyperStateTheory.bind_def]
QED

Theorem compile_ifexp_vv_sim_mem:
  !ctx func cenv cx ty t c a b es.
    expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
    (!e. (e = a \/ e = b) ==> post_value_type cenv e = expr_type e) /\
    (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    (!e sa sb op. (e = a \/ e = b) /\
       lower_value compile_expr cenv ty e sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    expr_sim_mem ctx func cenv cx (BaseT BoolT) c es /\
    (!tv es1. (do result <- eval_expr cx c; read_result cx result od) es = (INL tv, es1) ==>
       expr_sim_mem ctx func cenv cx ty a es1 /\
       expr_sim_mem ctx func cenv cx ty b es1) ==>
    !sa sb vv res es' s0.
      compile_expr cenv ty (IfExp t c a b) sa = (vv, sb) /\
      eval_expr cx (IfExp t c a b) es = (res, es') /\ expr_read_res_ok cx es' res /\
      res <> INR (Error (RuntimeError "convert empty bytes to signed")) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec_mem ctx sa sb
        (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s)
        (\s. (?tv. res = INL tv /\
                  vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 es' tv vv s) /\
              s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
        (expr_exit res)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  irule readable_eval_frag_transport_mem >>
  simp[] >> rpt strip_tac >>
  irule compile_ifexp_forced_frag_mem >> simp[] >> qexists_tac `ty` >> simp[] >>
  first_assum ACCEPT_TAC
QED

Theorem compile_ifexp_word_sim_mem:
  !ctx func cenv cx ty t c a b es.
    is_word_type t /\
    expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
    (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    (!e sa sb op. (e = a \/ e = b) /\
       lower_value compile_expr cenv ty e sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    expr_sim_mem ctx func cenv cx (BaseT BoolT) c es /\
    (!tv es1. (do result <- eval_expr cx c; read_result cx result od) es = (INL tv, es1) ==>
       expr_sim_mem ctx func cenv cx ty a es1 /\
       expr_sim_mem ctx func cenv cx ty b es1) ==>
    expr_sim_mem ctx func cenv cx ty (IfExp t c a b) es
Proof
  rpt gen_tac >> strip_tac >> pure_rewrite_tac[expr_sim_mem_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `compile_expr cenv ty (IfExp t c a b) sa` >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[exprLoweringTheory.lower_value_def, comp_bind_def] >> strip_tac >>
  drule_all compile_expr_ifexp_states >> strip_tac >>
  gvs[exprLoweringTheory.unwrap_value_def, comp_return_def] >>
  irule frag_exec_mem_weaken >>
  qexists_tac `\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s` >>
  qexists_tac `\s. (?v. res = INL v /\
    vv_post ctx func cenv cx (IfExp (expr_type a) c a b) es sa r s0 es'
      (Value v) (StackValue (expr_type a) (Var rv)) s) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s` >>
  qexists_tac `expr_exit res` >>
  simp[] >> reverse conj_tac
  >- (irule compile_ifexp_forced_frag_mem >> simp[post_value_type_word] >>
      qexists_tac `ty` >>
      simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[] >> rpt strip_tac >>
  drule exprSimUnwrapTheory.expr_post_of_vv_post_stack >> metis_tac[]
QED

