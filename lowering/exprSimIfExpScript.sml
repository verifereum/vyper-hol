(*
 * Expression simulation for the conditional expression (#636, part 3)
 *
 * x if c else y lowers to c's fragment, a JNZ on its operand, one block per
 * branch that lowers its expression and assigns its operand to a fresh
 * variable, and a JMP from each branch to a common exit block
 * (compile_expr_ifexp).  The source evaluates c and then the branch its
 * boolean picks (eval_expr_ifexp_cases).
 *
 * TOP-LEVEL:
 *   compile_ifexp_vv_sim   — expr_vv_sim of an IfExp, on results that are
 *                            values, from expr_sim of its three operands and
 *                            the compile-state shape of their lowering
 *   ifexp_branch_sim       — one arm of it, from the condition's fragment
 *                            through the arm's jump to the exit block
 *
 * Helpers: compile_expr_ifexp, compile_expr_ifexp_states,
 * eval_expr_ifexp_cases, frag_exec_assign, ifexp_arm_frag, ifexp_jnz_arm,
 * expr_post_ifexp, vv_post_of_expr_post.
 *)

Theory exprSimIfExp
Ancestors
  list rich_list finite_map marker
  fragExec exprSim exprSimOps freshWrites exprBopLowering loweringSlice
  vyperEvalExprPreservesScopesDom exprLowering emitHelperProps
  exprLoweringProps compileEnv context vyperAST vyperInterpreter vyperState
  vyperValue valueEncoding venomExecSemantics venomExecProofs venomInst
  venomState
Libs
  pairLib

(* What compile_expr emits for an IfExp. *)
Theorem compile_expr_ifexp:
  !cenv ty t c a b st vv st'.
    compile_expr cenv ty (IfExp t c a b) st = (vv, st') ==>
    ?cond_op s1 rv s2 tl s3 el s4 xl s5 s6 x6 s7 aop s8 s9 s10 x10 s11 bop
     s12 s13 s14 x14.
      lower_value compile_expr cenv (BaseT BoolT) c st = (cond_op, s1) /\
      fresh_var s1 = (rv, s2) /\
      fresh_label "then" s2 = (tl, s3) /\ fresh_label "else" s3 = (el, s4) /\
      fresh_label "exit" s4 = (xl, s5) /\
      emit_inst JNZ [cond_op; Label tl; Label el] [] s5 = ((), s6) /\
      new_block tl s6 = (x6, s7) /\
      lower_value compile_expr cenv ty a s7 = (aop, s8) /\
      emit_inst ASSIGN [aop] [rv] s8 = ((), s9) /\
      emit_inst JMP [Label xl] [] s9 = ((), s10) /\
      new_block el s10 = (x10, s11) /\
      lower_value compile_expr cenv ty b s11 = (bop, s12) /\
      emit_inst ASSIGN [bop] [rv] s12 = ((), s13) /\
      emit_inst JMP [Label xl] [] s13 = ((), s14) /\
      new_block xl s14 = (x14, st') /\
      vv = if is_word_type t then StackValue t (Var rv)
           else LocatedValue t (mk_ptr (Var rv) LocMemory)
Proof
  rpt gen_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def] >>
  rpt (pairarg_tac >> gvs[]) >> rw[] >> gvs[vyperASTTheory.expr_type_def]
QED

Theorem eval_expr_ifexp_cases:
  !cx t c a b es res es'.
    eval_expr cx (IfExp t c a b) es = (res, es') ==>
    (?exc. eval_expr cx c es = (INR exc, es') /\ res = INR exc) \/
    (?es1. eval_expr cx c es = (INL (Value (BoolV T)), es1) /\
           eval_expr cx a es1 = (res, es')) \/
    (?es1. eval_expr cx c es = (INL (Value (BoolV F)), es1) /\
           eval_expr cx b es1 = (res, es')) \/
    (?tv. (?es1. eval_expr cx c es = (INL tv, es1)) /\
          tv <> Value (BoolV T) /\ tv <> Value (BoolV F) /\
          ?m. res = INR (Error (TypeError m)))
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def, switch_BoolV_def, raise_def] >>
  Cases_on `eval_expr cx c es` >> rename1 `_ = (r1, es1)` >>
  Cases_on `r1` >> simp[] >>
  rw[vyperStateTheory.raise_def] >> gvs[vyperStateTheory.raise_def]
QED

Theorem expr_post_ifexp:
  !func cenv cx t c a b e es es1 es' sa s1 sc sd sb s0 tt u cop aop
             rv v1 v lbl w k xl.
    expr_post func cenv cx c es sa s1 s0 es1 v1 cop tt /\
    expr_post func cenv cx e es1 sc sd (jump_to lbl tt) es' v aop u /\
    expr_type e = t /\ eval_operand aop u = SOME w /\
    (!x. not_fresh_at sa x ==> x <> rv) /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel func cenv cx es s0 /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
    sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
    sd.cs_next_id <= sb.cs_next_id ==>
    expr_post func cenv cx (IfExp t c a b) es sa sb s0 es' v (Var rv)
      (jump_to xl (update_var rv w u with vs_inst_idx := k))
Proof
  rpt gen_tac >> simp[expr_post_def] >> strip_tac >>
  qabbrev_tac `ss = jump_to xl (update_var rv w u with vs_inst_idx := k)` >>
  `ss.vs_memory = u.vs_memory /\ ss.vs_allocas = u.vs_allocas /\
   lookup_var rv ss = SOME w /\
   (!x. x <> rv ==> lookup_var x ss = lookup_var x u)` by
    simp[Abbr `ss`, jump_to_def, update_var_def, lookup_var_def,
         FLOOKUP_UPDATE] >>
  `!x. (jump_to lbl tt).vs_allocas = tt.vs_allocas /\
       lookup_var x (jump_to lbl tt) = lookup_var x tt /\
       (jump_to lbl tt).vs_memory = tt.vs_memory` by
    simp[jump_to_def, lookup_var_def] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel func cenv cx es' ss` by
    (simp[Abbr `ss`, stmt_state_rel_jump_to, stmt_state_rel_inst_idx,
          update_var_def] >>
     irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
     `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> res_tac) >>
     `p <> rv` by metis_tac[] >>
     simp[lookup_var_def, FLOOKUP_UPDATE]) >>
  asm_rewrite_tac[] >> simp[vyperASTTheory.expr_type_def] >>
  conj_tac
  >- (qpat_x_assum `expr_val_rel cx (expr_type e) v aop u` mp_tac >>
      simp[expr_val_rel_def, eval_operand_def] >> strip_tac >> gvs[]) >>
  conj_tac
  >- (qpat_x_assum `expr_val_at cenv cx (expr_type e) sc sd es' v aop u` mp_tac >>
      simp[expr_val_at_def, eval_operand_def] >> rpt strip_tac >>
      first_x_assum drule_all >> strip_tac
      >- (disj1_tac >> qexists_tac `aid` >> first_assum (irule_at Any) >>
          simp[] >> fs[] >> decide_tac) >>
      disj2_tac >> qexists_tac `n` >>
  `local_region cenv es'.scopes ss n b sz` by
    (qpat_x_assum `local_region _ _ u _ _ _` mp_tac >>
     simp[local_region_def] >> strip_tac >>
     `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> res_tac) >>
     `p <> rv` by metis_tac[] >> metis_tac[]) >>
  first_assum (irule_at Any) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> rename1 `lookup_var z s0 = SOME w'` >>
      `z <> rv` by metis_tac[] >>
      `lookup_var z tt = SOME w'` by metis_tac[] >>
      metis_tac[]) >>
  rpt strip_tac >>
  qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
    (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (fn th => rewrite_tac [GSYM th]) >>
  qpat_x_assum `!aid off sz. FLOOKUP (jump_to lbl tt).vs_allocas aid = _ /\ _ ==> _`
    (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
  asm_rewrite_tac[] >> disch_then irule >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!n b sz'. local_region _ es.scopes s0 _ _ _ ==> _` irule >>
      qexists_tac `n` >>
      irule local_region_frame >>
      conj_tac >- (qexistsl_tac [`cx`, `func`] >> first_assum ACCEPT_TAC) >>
      qexistsl_tac [`sa`, `es1.scopes`, `tt`] >> asm_rewrite_tac[] >>
      fs[local_region_def] >> metis_tac[])
  >- decide_tac >>
  qpat_x_assum `!aid b. FLOOKUP s0.vs_allocas aid = _ ==> _` irule >>
  first_assum ACCEPT_TAC
QED

(* An ASSIGN as a fragment. *)
Theorem frag_exec_assign:
  !ctx st st' src out P Q R.
    emit_inst ASSIGN [src] [out] st = ((), st') /\
    (!s. P s ==> ?w. eval_operand src s = SOME w /\
                     Q ((update_var out w s) with
                          vs_inst_idx := LENGTH st'.cs_current_insts)) ==>
    frag_exec ctx st st' P Q R
Proof
  rpt strip_tac >> imp_res_tac emit_inst_extends >>
  irule frag_exec_run_inst_seq >>
  `emitted_insts st st' = [mk_inst st.cs_next_id ASSIGN [src] [out]]` by
    simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[venomInstTheory.mk_inst_def, is_terminator_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> disj1_tac >>
  simp[run_inst_seq_def, step_inst_base_def, exec_pure1_def, comp_bind_def,
       comp_return_def] >> gvs[]
QED

(* expr_post of an operand held by a variable, as vv_post of the value_vv
   compile_expr makes of the variable. *)
Theorem vv_post_of_expr_post:
  !func cenv cx e es sa sb s0 es' v rv s.
    expr_post func cenv cx e es sa sb s0 es' v (Var rv) s ==>
    vv_post func cenv cx e es sa sb s0 es' (Value v)
      (if is_word_type (expr_type e) then StackValue (expr_type e) (Var rv)
       else LocatedValue (expr_type e) (mk_ptr (Var rv) LocMemory)) s
Proof
  rw[expr_post_def, vv_post_def] >>
  gvs[vv_holds_def, vv_at_def, contextTheory.mk_ptr_def, materialise_def,
      return_def] >>
  fs[expr_val_rel_def, expr_val_at_def] >> metis_tac[]
QED

(* One arm of an IfExp, lowered to eop between bs and bm, then assigned to
   rv: from the jump into the arm's block, the arm's fragment and the
   ASSIGN run to bn with eop's word in rv. *)
Theorem ifexp_arm_frag:
  !ctx func cenv cx ty e es1 res es' bs bm bn eop rv tt lbl.
    expr_sim ctx func cenv cx ty e es1 /\
    lower_value compile_expr cenv ty e bs = (eop, bm) /\
    emit_inst ASSIGN [eop] [rv] bm = ((), bn) /\
    eval_expr cx e es1 = (res, es') /\ expr_res_ok res /\
    fn_has_code bs bm func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv bs /\ stmt_state_rel func cenv cx es1 tt /\
    cs_extends bs bm ==>
    frag_exec ctx bs bn (\s. s = jump_to lbl tt)
      (\s. ?v u w. res = INL (Value v) /\
             expr_post func cenv cx e es1 bs bm (jump_to lbl tt) es' v eop u /\
             eval_operand eop u = SOME w /\
             s = (update_var rv w u) with
                   vs_inst_idx := LENGTH bn.cs_current_insts)
      (expr_exit res)
Proof
  rpt strip_tac >>
  `cs_extends bm bn` by metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  qpat_x_assum `expr_sim _ _ _ _ ty e es1`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`bs`, `bm`, `eop`, `res`, `es'`, `jump_to lbl tt`]
                mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (mp_tac o MATCH_MP frag_exec_pre_exit_c) >>
  disch_then (qspecl_then [`\s. s = jump_to lbl tt`, `expr_exit res`] mp_tac) >>
  (impl_tac >- simp[stmt_state_rel_jump_to]) >>
  disch_then (fn th => irule (MATCH_MP frag_exec_then th)) >>
  asm_rewrite_tac[] >> rpt strip_tac >> fs[] >>
  irule frag_exec_assign >> first_assum (irule_at Any) >>
  rpt strip_tac >> gvs[] >>
  rename1 `expr_post func cenv cx e es1 bs bm _ es' v eop uu` >>
  `?w. eval_operand eop uu = SOME w` by
    (qpat_x_assum `expr_post func cenv cx e _ _ _ _ _ _ _ uu` mp_tac >>
     simp[expr_post_def, expr_val_rel_def] >> strip_tac >>
     qexists_tac `w` >> simp[]) >>
  qexists_tac `w` >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`uu`, `w`] >> asm_rewrite_tac[]
QED

(* The JNZ that ends c's code, from the state tt c's fragment ends in: it
   jumps to bl, the block bs starts, where the arm runs as ifexp_arm_frag
   says, and the arm's JMP reaches the exit block xl, which sb starts. *)
Theorem ifexp_jnz_arm:
  !ctx func cenv cx t c a b e bv es es1 es' res sa sb s0 s1 s5 s6 x6 s7
   bs bm bn bo bx bp tl el xl bl lbl rv cond_op eop tt.
    frag_exec ctx bs bn (\s. s = jump_to bl tt)
      (\s. ?v u w. res = INL (Value v) /\
             expr_post func cenv cx e es1 bs bm (jump_to bl tt) es' v eop u /\
             eval_operand eop u = SOME w /\
             s = (update_var rv w u) with
                   vs_inst_idx := LENGTH bn.cs_current_insts)
      (expr_exit res) /\
    expr_post func cenv cx c es sa s1 s0 es1 (BoolV bv) cond_op tt /\
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
    expr_type e = t /\ (!x. not_fresh_at sa x ==> x <> rv) /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel func cenv cx es s0 /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes ==>
    frag_exec ctx s1 sb (\s. s = tt)
      (\s. ?tv. res = INL tv /\
                vv_post func cenv cx (IfExp t c a b) es sa sb s0 es' tv
                  (if is_word_type t then StackValue t (Var rv)
                   else LocatedValue t (mk_ptr (Var rv) LocMemory)) s)
      (expr_exit res)
Proof
  rpt strip_tac >> imp_res_tac emit_inst_extends >>
  PURE_REWRITE_TAC[frag_exec_def] >> BETA_TAC >> rpt strip_tac >>
  qpat_x_assum `_ = tt` SUBST_ALL_TAC >>
  `step_inst_base (mk_inst s5.cs_next_id JNZ [cond_op; Label tl; Label el] [])
     tt = OK (jump_to bl tt)` by
    (qpat_x_assum `(if _ then _ else _) = bl` (SUBST_ALL_TAC o SYM) >>
     simp[venomInstTheory.mk_inst_def] >>
     drule venomExecProofsTheory.step_jnz_behavior >>
     disch_then (fn th => simp[th]) >> Cases_on `bv` >> simp[val_to_w256_def]) >>
  qabbrev_tac `jnz = mk_inst s5.cs_next_id JNZ [cond_op; Label tl; Label el] []` >>
  qabbrev_tac `jbb = <| bb_label := s6.cs_current_bb;
                        bb_instructions := s6.cs_current_insts |>` >>
  `fn_has_code s6 s7 fn` by
    (irule fn_has_code_mid >> asm_rewrite_tac[] >>
     qexistsl_tac [`sb`, `s1`] >> asm_rewrite_tac[]) >>
  `fn_has_code bs bp fn` by
    (irule fn_has_code_mid >> asm_rewrite_tac[] >>
     qexistsl_tac [`sb`, `s1`] >> asm_rewrite_tac[] >> rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC) >> metis_tac[cs_extends_trans]) >>
  `lookup_block tt.vs_current_bb fn.fn_blocks = SOME jbb` by
    (`tt.vs_current_bb = s6.cs_current_bb` by fs[] >>
     simp[Abbr `jbb`] >> metis_tac[fn_has_code_new_block]) >>
  `get_instruction jbb tt.vs_inst_idx = SOME jnz` by
    fs[Abbr `jbb`, get_instruction_def, EL_LENGTH_APPEND] >>
  `is_terminator jnz.inst_opcode /\ jnz.inst_opcode <> INVOKE` by
    simp[Abbr `jnz`, venomInstTheory.mk_inst_def, is_terminator_def] >>
  qspecl_then [`ctx`, `fn`, `tt`, `tt`, `jbb`, `jnz`, `bs`, `bn`, `bo`,
     `bp`, `xl`, `lbl`, `bx`, `\s. s = jump_to bl tt`,
     `\s. ?v u w. res = INL (Value v) /\
            expr_post func cenv cx e es1 bs bm (jump_to bl tt) es' v eop u /\
            eval_operand eop u = SOME w /\
            s = (update_var rv w u) with
                  vs_inst_idx := LENGTH bn.cs_current_insts`,
     `expr_exit res`] mp_tac if_branch_to_exit >>
  (impl_tac >- (asm_rewrite_tac[] >> BETA_TAC >> rpt strip_tac >> metis_tac[])) >>
  BETA_TAC >> strip_tac
  >- (disj1_tac >>
      qpat_x_assum `!fuel r. run_from _ _ _ (jump_to xl _) = _ /\ _ ==> _`
        mp_tac >>
      qmatch_goalsub_rename_tac `jump_to xl ss` >> strip_tac >>
      qexists_tac `jump_to xl ss` >> rpt conj_tac
      >- (qexists_tac `Value v` >> simp[] >>
          qspecl_then [`func`, `cenv`, `cx`, `IfExp t c a b`, `es`, `sa`, `sb`,
                       `s0`, `es'`, `v`, `rv`, `jump_to xl ss`] mp_tac
            vv_post_of_expr_post >>
          simp[vyperASTTheory.expr_type_def] >> disch_then irule >>
          qpat_x_assum `ss = _` SUBST_ALL_TAC >> irule expr_post_ifexp >>
          conj_tac >- (rpt strip_tac >> gvs[]) >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- first_assum ACCEPT_TAC >>
          qexistsl_tac [`eop`, `cond_op`, `e`, `es1`, `bl`, `s1`, `bs`, `bm`,
                        `tt`, `BoolV bv`] >>
          asm_rewrite_tac[] >> fs[])
      >- (qpat_x_assum `~ss.vs_halted` mp_tac >>
          qpat_x_assum `ss = _` (fn th => rewrite_tac[th]) >>
          simp[jump_to_def])
      >- (simp[jump_to_def] >> asm_rewrite_tac[])
      >- (simp[jump_to_def] >> asm_rewrite_tac[listTheory.LENGTH]) >>
      first_assum ACCEPT_TAC) >>
  disj2_tac >> metis_tac[]
QED

(* An IfExp whose condition c evaluates to bv, lowered to cond_op between sa
   and s1: the JNZ on cond_op (emitted between s5 and s6) jumps to bl, the
   block bs starts, where the arm e that bv picks runs as ifexp_arm_frag
   says, and a JMP to the exit block xl, which sb starts, ends the arm
   (ifexp_jnz_arm).  Both arms of compile_ifexp_vv_sim are this lemma. *)
Theorem ifexp_branch_sim:
  !ctx func cenv cx ty t c a b e bv es es1 es' res sa sb s0 s1 s5 s6 x6 s7
   bs bm bn bo bx bp tl el xl bl lbl rv cond_op eop.
    expr_type c = BaseT BoolT /\ expr_sim ctx func cenv cx (BaseT BoolT) c es /\
    expr_sim ctx func cenv cx ty e es1 /\
    eval_expr cx c es = (INL (Value (BoolV bv)), es1) /\
    eval_expr cx e es1 = (res, es') /\ expr_res_ok res /\ expr_type e = t /\
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
    local_ptrs_reserved cenv sa /\ stmt_state_rel func cenv cx es s0 ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
      (\s. ?tv. res = INL tv /\
                vv_post func cenv cx (IfExp t c a b) es sa sb s0 es' tv
                  (if is_word_type t then StackValue t (Var rv)
                   else LocatedValue t (mk_ptr (Var rv) LocMemory)) s)
      (expr_exit res)
Proof
  rpt strip_tac >> imp_res_tac emit_inst_extends >>
  `cs_extends s5 s6 /\ cs_extends bm bn /\ cs_extends bn bo` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends s6 s7 /\ cs_extends bo bp` by metis_tac[cs_extends_new_block] >>
  `cs_extends bs bn` by metis_tac[cs_extends_trans] >>
  `cs_extends bs bp` by metis_tac[cs_extends_trans] >>
  `cs_extends bs sb` by metis_tac[cs_extends_trans] >>
  `cs_extends bm sb` by metis_tac[cs_extends_trans] >>
  `cs_extends s1 s6` by metis_tac[cs_extends_trans] >>
  `cs_extends s1 s7` by metis_tac[cs_extends_trans] >>
  `cs_extends s7 sb` by metis_tac[cs_extends_trans] >>
  `cs_extends s1 bs` by metis_tac[cs_extends_trans] >>
  `cs_extends s1 sb` by metis_tac[cs_extends_trans] >>
  `cs_extends sa bs` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func` by metis_tac[fn_has_code_split] >>
  `fn_has_code bs bm func` by metis_tac[fn_has_code_mid] >>
  `local_ptrs_reserved cenv bs` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
    metis_tac[eval_expr_preserves_scopes_dom] >>
  (* the condition's fragment *)
  qpat_x_assum `expr_sim _ _ _ _ (BaseT BoolT) c _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `cond_op`, `INL (Value (BoolV bv))`,
                           `es1`, `s0`] mp_tac) >>
  (impl_tac >- simp[expr_res_ok_def]) >>
  disch_then (mp_tac o MATCH_MP frag_exec_pre_exit_c) >>
  disch_then (qspecl_then [`\s. s = s0 /\ stmt_state_rel func cenv cx es s`,
                           `expr_exit res`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => irule (MATCH_MP frag_exec_then th)) >>
  asm_rewrite_tac[] >> rpt strip_tac >> fs[] >>
  rename1 `expr_post func cenv cx c es sa s1 s0 es1 (BoolV bv) cond_op tt` >>
  `stmt_state_rel func cenv cx es1 tt /\
   eval_operand cond_op tt = SOME (val_to_w256 (BoolV bv))` by
    (fs[expr_post_def] >>
     qspecl_then [`cx`, `BaseT BoolT`, `BoolV bv`, `cond_op`, `tt`] mp_tac
       expr_val_rel_word >>
     simp[word_value_def, is_word_type_def, evaluate_type_def] >>
     disch_then irule >> gvs[]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ty`, `e`, `es1`, `res`, `es'`,
               `bs`, `bm`, `bn`, `eop`, `rv`, `tt`, `bs.cs_current_bb`] mp_tac
    ifexp_arm_frag >>
  (impl_tac >- simp[]) >> strip_tac >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `t`, `c`, `a`, `b`, `e`, `bv`, `es`,
               `es1`, `es'`, `res`, `sa`, `sb`, `s0`, `s1`, `s5`, `s6`, `x6`,
               `s7`, `bs`, `bm`, `bn`, `bo`, `bx`, `bp`, `tl`, `el`,
               `sb.cs_current_bb`, `bs.cs_current_bb`, `lbl`, `rv`, `cond_op`,
               `eop`, `tt`] mp_tac ifexp_jnz_arm >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[])) >>
  simp[]
QED

(* compile_expr_ifexp with what the two arms of compile_ifexp_vv_sim need
   of its states, from the compile-state shape of the operands' lowering. *)
Theorem compile_expr_ifexp_states:
  !cenv ty t c a b st vv st'.
    compile_expr cenv ty (IfExp t c a b) st = (vv, st') /\
    (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    (!e sa sb op. (e = a \/ e = b) /\
       lower_value compile_expr cenv ty e sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) ==>
    ?cond_op s1 rv tl el xl s5 s6 x6 s7 aop s8 s9 s10 x10 s11 bop s12 s13
     s14 x14.
      lower_value compile_expr cenv (BaseT BoolT) c st = (cond_op, s1) /\
      emit_inst JNZ [cond_op; Label tl; Label el] [] s5 = ((), s6) /\
      new_block tl s6 = (x6, s7) /\
      lower_value compile_expr cenv ty a s7 = (aop, s8) /\
      emit_inst ASSIGN [aop] [rv] s8 = ((), s9) /\
      emit_inst JMP [Label xl] [] s9 = ((), s10) /\
      new_block el s10 = (x10, s11) /\
      lower_value compile_expr cenv ty b s11 = (bop, s12) /\
      emit_inst ASSIGN [bop] [rv] s12 = ((), s13) /\
      emit_inst JMP [Label xl] [] s13 = ((), s14) /\
      new_block xl s14 = (x14, st') /\
      vv = (if is_word_type t then StackValue t (Var rv)
            else LocatedValue t (mk_ptr (Var rv) LocMemory)) /\
      s5.cs_current_bb = s1.cs_current_bb /\
      s5.cs_current_insts = s1.cs_current_insts /\
      s7.cs_current_bb = tl /\ s11.cs_current_bb = el /\
      st'.cs_current_bb = xl /\ s7.cs_current_insts = [] /\
      s11.cs_current_insts = [] /\ st'.cs_current_insts = [] /\
      cs_extends st s1 /\ cs_extends s1 s5 /\ cs_extends s7 s8 /\
      cs_extends s7 s11 /\ cs_extends s11 s12 /\ cs_extends s11 st' /\
      cs_extends s1 st' /\
      st.cs_next_var <= s1.cs_next_var /\ st.cs_next_id <= s1.cs_next_id /\
      s1.cs_next_var <= s7.cs_next_var /\ s1.cs_next_id <= s7.cs_next_id /\
      s1.cs_next_var <= s11.cs_next_var /\ s1.cs_next_id <= s11.cs_next_id /\
      s8.cs_next_id <= st'.cs_next_id /\ s12.cs_next_id <= st'.cs_next_id /\
      !x. not_fresh_at st x ==> x <> rv
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_expr_ifexp >> strip_tac >>
  qpat_x_assum `!st sb op. lower_value _ _ (BaseT BoolT) c _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  `cs_extends s7 s8 /\ s7.cs_next_var <= s8.cs_next_var /\
   s7.cs_next_id <= s8.cs_next_id` by
    (qpat_x_assum `!e st sb op. _` (qspecl_then [`a`, `s7`, `s8`, `aop`] mp_tac) >>
     simp[]) >>
  `cs_extends s11 s12 /\ s11.cs_next_var <= s12.cs_next_var /\
   s11.cs_next_id <= s12.cs_next_id` by
    (qpat_x_assum `!e st sb op. _` (qspecl_then [`b`, `s11`, `s12`, `bop`] mp_tac) >>
     simp[]) >>
  imp_res_tac fresh_label_props >> imp_res_tac emit_inst_extends >>
  `cs_extends s1 s2` by metis_tac[cs_extends_fresh_var] >>
  `cs_extends s2 s3 /\ cs_extends s3 s4 /\ cs_extends s4 s5` by
     metis_tac[cs_extends_fresh_label] >>
  `cs_extends s5 s6 /\ cs_extends s8 s9 /\ cs_extends s9 s10 /\
   cs_extends s12 s13 /\ cs_extends s13 s14` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends s6 s7 /\ cs_extends s10 s11 /\ cs_extends s14 st'` by
    metis_tac[cs_extends_new_block] >>
  `Abbrev (rv = STRING #"%" (toString s1.cs_next_var)) /\
   s2.cs_next_var = s1.cs_next_var + 1 /\ s2.cs_next_id = s1.cs_next_id /\
   s2.cs_current_bb = s1.cs_current_bb /\
   s2.cs_current_insts = s1.cs_current_insts /\ s2.cs_blocks = s1.cs_blocks` by
    (qpat_x_assum `fresh_var s1 = _` mp_tac >>
     simp[fresh_var_def, markerTheory.Abbrev_def] >> strip_tac >> gvs[]) >>
  `!x. not_fresh_at st x ==> x <> rv` by
    (fs[markerTheory.Abbrev_def] >> rw[not_fresh_at_def] >>
     first_x_assum (qspec_then `s1.cs_next_var` mp_tac) >> simp[]) >>
  `s7.cs_next_var = s2.cs_next_var /\ s7.cs_next_id = s1.cs_next_id + 1 /\
   s11.cs_next_var = s10.cs_next_var /\ s11.cs_next_id = s10.cs_next_id /\
   st'.cs_next_var = s14.cs_next_var /\ st'.cs_next_id = s14.cs_next_id /\
   s7.cs_current_insts = [] /\ s11.cs_current_insts = [] /\
   st'.cs_current_insts = [] /\ s7.cs_current_bb = tl /\
   s11.cs_current_bb = el /\ st'.cs_current_bb = xl` by
    (imp_res_tac new_block_props >>
     rpt conj_tac >> asm_rewrite_tac []) >>
  `cs_extends s1 s5 /\ cs_extends s7 s11 /\ cs_extends s11 st'` by
    metis_tac[cs_extends_trans] >>
  `cs_extends s1 st'` by metis_tac[cs_extends_trans] >>
  qexistsl_tac [`cond_op`, `s1`, `rv`, `tl`, `el`, `xl`, `s5`, `s6`, `x6`,
                `s7`, `aop`, `s8`, `s9`, `s10`, `x10`, `s11`, `bop`, `s12`,
                `s13`, `s14`, `x14`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]
QED

Theorem compile_ifexp_vv_sim:
  !ctx func cenv cx ty t c a b es.
    expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
    (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    (!e sa sb op. (e = a \/ e = b) /\
       lower_value compile_expr cenv ty e sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    expr_sim ctx func cenv cx (BaseT BoolT) c es /\
    (!tv es1. eval_expr cx c es = (INL tv, es1) ==>
       expr_sim ctx func cenv cx ty a es1 /\
       expr_sim ctx func cenv cx ty b es1) ==>
    !sa sb vv res es' s0.
      compile_expr cenv ty (IfExp t c a b) sa = (vv, sb) /\
      eval_expr cx (IfExp t c a b) es = (res, es') /\ expr_res_ok res /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
        (\s. ?tv. res = INL tv /\
                  vv_post func cenv cx (IfExp t c a b) es sa sb s0 es' tv vv s)
        (expr_exit res)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `stmt_state_rel func cenv cx es s0`)
  >- (`frag_exec ctx sa sb (\s. F) (\s. F) (\r. F)` by
        simp[frag_exec_false_pre] >>
      pop_assum (fn th => irule (MATCH_MP frag_exec_weaken th)) >>
      simp[]) >>
  drule_all compile_expr_ifexp_states >> strip_tac >>
  drule eval_expr_ifexp_cases >> strip_tac
  >- ((* the condition raises *)
      `fn_has_code sa s1 func` by metis_tac[fn_has_code_split] >>
      qpat_x_assum `expr_sim _ _ _ _ (BaseT BoolT) c _`
        (mp_tac o REWRITE_RULE [expr_sim_def]) >>
      disch_then (qspecl_then [`sa`, `s1`, `cond_op`, `INR exc`, `es'`, `s0`]
                    mp_tac) >>
      (impl_tac >- gvs[]) >>
      disch_then (mp_tac o MATCH_MP frag_exec_weaken) >>
      disch_then (qspecl_then [`\s. s = s0 /\ stmt_state_rel func cenv cx es s`,
                               `\s. F`, `expr_exit res`] mp_tac) >>
      (impl_tac >- gvs[]) >> strip_tac >>
      irule frag_exec_exit_prefix >> qexists_tac `s1` >> simp[])
  >- ((* the condition is true: the then arm *)
      qpat_x_assum `!tv es1. eval_expr cx c es = _ ==> _` drule >> strip_tac >>
      qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ty`, `t`, `c`, `a`, `b`, `a`,
                   `T`, `es`, `es1`, `es'`, `res`, `sa`, `sb`, `s0`, `s1`, `s5`,
                   `s6`, `x6`, `s7`, `s7`, `s8`, `s9`, `s10`, `x10`, `s11`,
                   `tl`, `el`, `xl`, `tl`, `el`, `rv`, `cond_op`, `aop`]
        mp_tac ifexp_branch_sim >>
      (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
                    simp[cs_extends_refl])) >> simp[])
  >- ((* the condition is false: the else arm *)
      qpat_x_assum `!tv es1. eval_expr cx c es = _ ==> _` drule >> strip_tac >>
      qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ty`, `t`, `c`, `a`, `b`, `b`,
                   `F`, `es`, `es1`, `es'`, `res`, `sa`, `sb`, `s0`, `s1`, `s5`,
                   `s6`, `x6`, `s7`, `s11`, `s12`, `s13`, `s14`, `x14`, `sb`,
                   `tl`, `el`, `xl`, `el`, `xl`, `rv`, `cond_op`, `bop`]
        mp_tac ifexp_branch_sim >>
      (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
                    simp[cs_extends_refl])) >> simp[]) >>
  (* the condition is no bool: a type error, which expr_res_ok excludes *)
  gvs[expr_res_ok_def]
QED
