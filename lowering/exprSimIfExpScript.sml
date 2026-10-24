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
 *
 * Helpers: compile_expr_ifexp, eval_expr_ifexp_cases, frag_exec_assign,
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
  drule compile_expr_ifexp >> strip_tac >>
  qpat_x_assum `!sa sb op. lower_value _ _ (BaseT BoolT) c _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  `cs_extends s7 s8 /\ s7.cs_next_var <= s8.cs_next_var /\
   s7.cs_next_id <= s8.cs_next_id` by
    (qpat_x_assum `!e sa sb op. _` (qspecl_then [`a`, `s7`, `s8`, `aop`] mp_tac) >>
     simp[]) >>
  `cs_extends s11 s12 /\ s11.cs_next_var <= s12.cs_next_var /\
   s11.cs_next_id <= s12.cs_next_id` by
    (qpat_x_assum `!e sa sb op. _` (qspecl_then [`b`, `s11`, `s12`, `bop`] mp_tac) >>
     simp[]) >>
  imp_res_tac fresh_label_props >> imp_res_tac emit_inst_extends >>
  `cs_extends s1 s2` by metis_tac[cs_extends_fresh_var] >>
  `cs_extends s2 s3 /\ cs_extends s3 s4 /\ cs_extends s4 s5` by
     metis_tac[cs_extends_fresh_label] >>
  `cs_extends s5 s6 /\ cs_extends s8 s9 /\ cs_extends s9 s10 /\
   cs_extends s12 s13 /\ cs_extends s13 s14` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends s6 s7 /\ cs_extends s10 s11 /\ cs_extends s14 sb` by
    metis_tac[cs_extends_new_block] >>
  `Abbrev (rv = STRING #"%" (toString s1.cs_next_var)) /\
   s2.cs_next_var = s1.cs_next_var + 1 /\ s2.cs_next_id = s1.cs_next_id /\
   s2.cs_current_bb = s1.cs_current_bb /\
   s2.cs_current_insts = s1.cs_current_insts /\ s2.cs_blocks = s1.cs_blocks` by
    (qpat_x_assum `fresh_var s1 = _` mp_tac >>
     simp[fresh_var_def, markerTheory.Abbrev_def] >> strip_tac >> gvs[]) >>
  `!x. not_fresh_at sa x ==> x <> rv` by
    (fs[markerTheory.Abbrev_def] >> rw[not_fresh_at_def] >>
     first_x_assum (qspec_then `s1.cs_next_var` mp_tac) >> simp[]) >>
  `s7.cs_next_var = s2.cs_next_var /\ s7.cs_next_id = s1.cs_next_id + 1 /\
   s11.cs_next_var = s10.cs_next_var /\ s11.cs_next_id = s10.cs_next_id /\
   sb.cs_next_var = s14.cs_next_var /\ sb.cs_next_id = s14.cs_next_id /\
   s7.cs_current_insts = [] /\ s11.cs_current_insts = [] /\
   sb.cs_current_insts = [] /\ s7.cs_current_bb = tl /\
   s11.cs_current_bb = el /\ sb.cs_current_bb = xl` by
    (rpt (qpat_x_assum `new_block _ _ = _` mp_tac) >> simp[new_block_def] >>
     rpt strip_tac >> gvs[]) >>
  `cs_extends s1 s5 /\ cs_extends s5 s7 /\ cs_extends s7 s9 /\
   cs_extends s9 s11 /\ cs_extends s11 s13 /\ cs_extends s13 sb` by
    metis_tac[cs_extends_trans] >>
  `cs_extends s1 sb /\ cs_extends sa sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    metis_tac[fn_has_code_split] >>
  `cs_extends sa s7 /\ cs_extends s8 sb /\ cs_extends s12 sb` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code s7 s8 func /\ fn_has_code s11 s12 func` by
    metis_tac[fn_has_code_mid, cs_extends_trans] >>
  `local_ptrs_reserved cenv s7 /\ local_ptrs_reserved cenv s11` by
    (conj_tac >> irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     simp[]) >>
  `cs_extends s1 s6` by (irule cs_extends_trans >> qexists_tac `s5` >> simp[]) >>
  `cs_extends s7 s11` by (irule cs_extends_trans >> qexists_tac `s9` >> simp[]) >>
  `cs_extends s11 sb` by (irule cs_extends_trans >> qexists_tac `s13` >> simp[]) >>
  `cs_extends s7 sb` by (irule cs_extends_trans >> qexists_tac `s11` >> simp[]) >>
  `cs_extends s6 sb` by (irule cs_extends_trans >> qexists_tac `s7` >> simp[]) >>
  drule eval_expr_ifexp_cases >> strip_tac
  >- ((* the condition raises *)
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
  >- (* the condition is true: the then branch *)
     (qpat_x_assum `!tv es1. eval_expr cx c es = _ ==> _` drule >> strip_tac >>
      `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
        metis_tac[eval_expr_preserves_scopes_dom] >>
      qpat_x_assum `expr_sim _ _ _ _ (BaseT BoolT) c _`
        (mp_tac o REWRITE_RULE [expr_sim_def]) >>
      disch_then (qspecl_then [`sa`, `s1`, `cond_op`, `INL (Value (BoolV T))`,
                               `es1`, `s0`] mp_tac) >>
      (impl_tac >- simp[expr_res_ok_def]) >>
      disch_then (mp_tac o MATCH_MP frag_exec_pre_exit_c) >>
      disch_then (qspecl_then [`\s. s = s0 /\ stmt_state_rel func cenv cx es s`,
                               `expr_exit res`] mp_tac) >>
      (impl_tac >- simp[]) >>
      disch_then (fn th => irule (MATCH_MP frag_exec_then th)) >>
      asm_rewrite_tac[] >> rpt strip_tac >> fs[] >>
      rename1 `expr_post func cenv cx c es sa s1 s0 es1 (BoolV T) cond_op tt` >>
      `stmt_state_rel func cenv cx es1 tt /\ eval_operand cond_op tt = SOME 1w` by
        (fs[expr_post_def] >>
         qspecl_then [`cx`, `BaseT BoolT`, `BoolV T`, `cond_op`, `tt`] mp_tac
           expr_val_rel_word >>
         simp[word_value_def, val_to_w256_def, is_word_type_def,
              evaluate_type_def] >> disch_then irule >> gvs[]) >>
      (* the branch, then the ASSIGN to the result *)
      `frag_exec ctx s7 s9 (\s. s = jump_to tl tt)
         (\s. ?v u w. res = INL (Value v) /\
                expr_post func cenv cx a es1 s7 s8 (jump_to tl tt) es' v aop u /\
                eval_operand aop u = SOME w /\
                s = (update_var rv w u) with
                      vs_inst_idx := LENGTH s9.cs_current_insts)
         (expr_exit res)` by
        (qpat_x_assum `expr_sim _ _ _ _ ty a es1`
           (mp_tac o REWRITE_RULE [expr_sim_def]) >>
         disch_then (qspecl_then [`s7`, `s8`, `aop`, `res`, `es'`,
                                  `jump_to tl tt`] mp_tac) >>
         (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
         disch_then (mp_tac o MATCH_MP frag_exec_pre_exit_c) >>
         disch_then (qspecl_then [`\s. s = jump_to tl tt`, `expr_exit res`]
                       mp_tac) >>
         (impl_tac >- simp[stmt_state_rel_jump_to]) >>
         disch_then (fn th => irule (MATCH_MP frag_exec_then th)) >>
         asm_rewrite_tac[] >> rpt strip_tac >> fs[] >>
         irule frag_exec_assign >> first_assum (irule_at Any) >>
         rpt strip_tac >> gvs[] >>
         rename1 `expr_post func cenv cx a es1 s7 s8 _ es' v aop uu` >>
         `?w. eval_operand aop uu = SOME w` by
           (qpat_x_assum `expr_post func cenv cx a _ _ _ _ _ _ _ uu` mp_tac >>
            simp[expr_post_def, expr_val_rel_def] >> strip_tac >>
            qexists_tac `w` >> simp[]) >>
         qexists_tac `w` >> conj_tac >- first_assum ACCEPT_TAC >>
         qexistsl_tac [`uu`, `w`] >> asm_rewrite_tac[]) >>
      (* the JNZ into the branch *)
      PURE_REWRITE_TAC[frag_exec_def] >> BETA_TAC >> rpt strip_tac >>
      qpat_x_assum `_ = tt` SUBST_ALL_TAC >>
      qabbrev_tac `jnz = mk_inst s5.cs_next_id JNZ [cond_op; Label tl; Label el] []` >>
      qabbrev_tac `jbb = <| bb_label := s6.cs_current_bb;
                            bb_instructions := s6.cs_current_insts |>` >>
      `fn_has_code s6 s7 fn` by
        (irule fn_has_code_mid >> asm_rewrite_tac[] >>
         qexistsl_tac [`sb`, `s1`] >> asm_rewrite_tac[]) >>
      `fn_has_code s7 s11 fn` by
        (irule fn_has_code_mid >> asm_rewrite_tac[] >>
         qexistsl_tac [`sb`, `s1`] >> asm_rewrite_tac[] >> rpt conj_tac >>
         TRY (first_assum ACCEPT_TAC) >>
         metis_tac[cs_extends_trans, cs_extends_refl]) >>
      `lookup_block tt.vs_current_bb fn.fn_blocks = SOME jbb` by
        (`tt.vs_current_bb = s6.cs_current_bb` by fs[] >>
         simp[Abbr `jbb`] >> metis_tac[fn_has_code_new_block]) >>
      `get_instruction jbb tt.vs_inst_idx = SOME jnz` by
        fs[Abbr `jbb`, get_instruction_def, EL_LENGTH_APPEND] >>
      `step_inst_base jnz tt = OK (jump_to tl tt)` by
        (qunabbrev_tac `jnz` >> simp[venomInstTheory.mk_inst_def] >>
         drule venomExecProofsTheory.step_jnz_behavior >>
         disch_then (fn th => simp[th])) >>
      `is_terminator jnz.inst_opcode /\ jnz.inst_opcode <> INVOKE` by
        simp[Abbr `jnz`, venomInstTheory.mk_inst_def, is_terminator_def] >>
      qspecl_then [`ctx`, `fn`, `tt`, `tt`, `jbb`, `jnz`, `s7`, `s9`, `s10`,
         `s11`, `xl`, `el`, `x10`, `\s. s = jump_to tl tt`,
         `\s. ?v u w. res = INL (Value v) /\
                expr_post func cenv cx a es1 s7 s8 (jump_to tl tt) es' v aop u /\
                eval_operand aop u = SOME w /\
                s = (update_var rv w u) with
                      vs_inst_idx := LENGTH s9.cs_current_insts`,
         `expr_exit res`] mp_tac if_branch_to_exit >>
      (impl_tac
       >- (qpat_x_assum `s7.cs_current_bb = tl` (fn th => rewrite_tac[th]) >>
           asm_rewrite_tac[] >> BETA_TAC >> rpt strip_tac >> metis_tac[])) >>
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
              qexistsl_tac [`aop`, `cond_op`, `a`, `es1`, `tl`, `s1`, `s7`,
                            `s8`, `tt`, `BoolV T`] >>
              asm_rewrite_tac[] >> fs[])
          >- (qpat_x_assum `~ss.vs_halted` mp_tac >>
              qpat_x_assum `ss = _` (fn th => rewrite_tac[th]) >>
              simp[jump_to_def])
          >- (simp[jump_to_def] >> asm_rewrite_tac[])
          >- (simp[jump_to_def] >> asm_rewrite_tac[listTheory.LENGTH]) >>
          first_assum ACCEPT_TAC) >>
      disj2_tac >> metis_tac[])
  >- (* the condition is false: the else branch *)
     (qpat_x_assum `!tv es1. eval_expr cx c es = _ ==> _` drule >> strip_tac >>
      `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
        metis_tac[eval_expr_preserves_scopes_dom] >>
      qpat_x_assum `expr_sim _ _ _ _ (BaseT BoolT) c _`
        (mp_tac o REWRITE_RULE [expr_sim_def]) >>
      disch_then (qspecl_then [`sa`, `s1`, `cond_op`, `INL (Value (BoolV F))`,
                               `es1`, `s0`] mp_tac) >>
      (impl_tac >- simp[expr_res_ok_def]) >>
      disch_then (mp_tac o MATCH_MP frag_exec_pre_exit_c) >>
      disch_then (qspecl_then [`\s. s = s0 /\ stmt_state_rel func cenv cx es s`,
                               `expr_exit res`] mp_tac) >>
      (impl_tac >- simp[]) >>
      disch_then (fn th => irule (MATCH_MP frag_exec_then th)) >>
      asm_rewrite_tac[] >> rpt strip_tac >> fs[] >>
      rename1 `expr_post func cenv cx c es sa s1 s0 es1 (BoolV F) cond_op tt` >>
      `stmt_state_rel func cenv cx es1 tt /\ eval_operand cond_op tt = SOME 0w` by
        (fs[expr_post_def] >>
         qspecl_then [`cx`, `BaseT BoolT`, `BoolV F`, `cond_op`, `tt`] mp_tac
           expr_val_rel_word >>
         simp[word_value_def, val_to_w256_def, is_word_type_def,
              evaluate_type_def] >> disch_then irule >> gvs[]) >>
      (* the branch, then the ASSIGN to the result *)
      `frag_exec ctx s11 s13 (\s. s = jump_to el tt)
         (\s. ?v u w. res = INL (Value v) /\
                expr_post func cenv cx b es1 s11 s12 (jump_to el tt) es' v bop u /\
                eval_operand bop u = SOME w /\
                s = (update_var rv w u) with
                      vs_inst_idx := LENGTH s13.cs_current_insts)
         (expr_exit res)` by
        (qpat_x_assum `expr_sim _ _ _ _ ty b es1`
           (mp_tac o REWRITE_RULE [expr_sim_def]) >>
         disch_then (qspecl_then [`s11`, `s12`, `bop`, `res`, `es'`,
                                  `jump_to el tt`] mp_tac) >>
         (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
         disch_then (mp_tac o MATCH_MP frag_exec_pre_exit_c) >>
         disch_then (qspecl_then [`\s. s = jump_to el tt`, `expr_exit res`]
                       mp_tac) >>
         (impl_tac >- simp[stmt_state_rel_jump_to]) >>
         disch_then (fn th => irule (MATCH_MP frag_exec_then th)) >>
         asm_rewrite_tac[] >> rpt strip_tac >> fs[] >>
         irule frag_exec_assign >> first_assum (irule_at Any) >>
         rpt strip_tac >> gvs[] >>
         rename1 `expr_post func cenv cx b es1 s11 s12 _ es' v bop uu` >>
         `?w. eval_operand bop uu = SOME w` by
           (qpat_x_assum `expr_post func cenv cx b _ _ _ _ _ _ _ uu` mp_tac >>
            simp[expr_post_def, expr_val_rel_def] >> strip_tac >>
            qexists_tac `w` >> simp[]) >>
         qexists_tac `w` >> conj_tac >- first_assum ACCEPT_TAC >>
         qexistsl_tac [`uu`, `w`] >> asm_rewrite_tac[]) >>
      (* the JNZ into the branch *)
      PURE_REWRITE_TAC[frag_exec_def] >> BETA_TAC >> rpt strip_tac >>
      qpat_x_assum `_ = tt` SUBST_ALL_TAC >>
      qabbrev_tac `jnz = mk_inst s5.cs_next_id JNZ [cond_op; Label tl; Label el] []` >>
      qabbrev_tac `jbb = <| bb_label := s6.cs_current_bb;
                            bb_instructions := s6.cs_current_insts |>` >>
      `fn_has_code s6 s7 fn` by
        (irule fn_has_code_mid >> asm_rewrite_tac[] >>
         qexistsl_tac [`sb`, `s1`] >> asm_rewrite_tac[]) >>
      `fn_has_code s11 sb fn` by
        (irule fn_has_code_mid >> asm_rewrite_tac[] >>
         qexistsl_tac [`sb`, `s1`] >> asm_rewrite_tac[] >> rpt conj_tac >>
         TRY (first_assum ACCEPT_TAC) >>
         metis_tac[cs_extends_trans, cs_extends_refl]) >>
      `lookup_block tt.vs_current_bb fn.fn_blocks = SOME jbb` by
        (`tt.vs_current_bb = s6.cs_current_bb` by fs[] >>
         simp[Abbr `jbb`] >> metis_tac[fn_has_code_new_block]) >>
      `get_instruction jbb tt.vs_inst_idx = SOME jnz` by
        fs[Abbr `jbb`, get_instruction_def, EL_LENGTH_APPEND] >>
      `step_inst_base jnz tt = OK (jump_to el tt)` by
        (qunabbrev_tac `jnz` >> simp[venomInstTheory.mk_inst_def] >>
         drule venomExecProofsTheory.step_jnz_behavior >>
         disch_then (fn th => simp[th])) >>
      `is_terminator jnz.inst_opcode /\ jnz.inst_opcode <> INVOKE` by
        simp[Abbr `jnz`, venomInstTheory.mk_inst_def, is_terminator_def] >>
      qspecl_then [`ctx`, `fn`, `tt`, `tt`, `jbb`, `jnz`, `s11`, `s13`, `s14`,
         `sb`, `xl`, `xl`, `x14`, `\s. s = jump_to el tt`,
         `\s. ?v u w. res = INL (Value v) /\
                expr_post func cenv cx b es1 s11 s12 (jump_to el tt) es' v bop u /\
                eval_operand bop u = SOME w /\
                s = (update_var rv w u) with
                      vs_inst_idx := LENGTH s13.cs_current_insts`,
         `expr_exit res`] mp_tac if_branch_to_exit >>
      (impl_tac
       >- (qpat_x_assum `s11.cs_current_bb = el` (fn th => rewrite_tac[th]) >>
           asm_rewrite_tac[] >> BETA_TAC >> rpt strip_tac >> metis_tac[])) >>
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
              qexistsl_tac [`bop`, `cond_op`, `b`, `es1`, `el`, `s1`, `s11`,
                            `s12`, `tt`, `BoolV F`] >>
              asm_rewrite_tac[] >> fs[])
          >- (qpat_x_assum `~ss.vs_halted` mp_tac >>
              qpat_x_assum `ss = _` (fn th => rewrite_tac[th]) >>
              simp[jump_to_def])
          >- (simp[jump_to_def] >> asm_rewrite_tac[])
          >- (simp[jump_to_def] >> asm_rewrite_tac[listTheory.LENGTH]) >>
          first_assum ACCEPT_TAC) >>
      disj2_tac >> metis_tac[]) >>
  (* the condition is no bool: a type error, which expr_res_ok excludes *)
  gvs[expr_res_ok_def]
QED
