(*
 * Fuel bound for an iteration loop (For over an Array), the loop part of
 * the statement-level fuel bound.
 *
 * Why it terminates: the index is a fresh variable, set to 0 in the entry
 * block and incremented by one (mod 2^256) in the incr block, and the loop
 * exits when it EQuals len_op: a literal (static array) or the fresh
 * result of compile_ptr_load (dynamic array), computed once before the
 * loop.  The body writes only the pointer variables of its environment's
 * locals (all allocated before the index and len_op: cenv_ptrs_below) and
 * the variables it allocates itself, so neither the index nor len_op
 * changes in the body, and the loop runs at most 2^256 rounds, each
 * within the body's bound plus a constant.  The array pointer arr_op only
 * feeds address arithmetic, so its value doesn't matter.  A jump out of
 * the body goes to exit_lbl (break: the end of the loop), incr_lbl
 * (continue) or the constructor's exit label (in E).
 *
 * TOP-LEVEL:
 *   fuel_okS_compile_for_iter
 *)

Theory fragFuelLoopForIter
Ancestors
  fragFuel fragFuelContextBase fragFuelContext fragFuelStmtBase
  stmtLowering exprLowering compileEnv emitHelper context venomInst
Libs
  fragFuelLib monadsyntax

(* Restrict writes to pre-loop variables and, when present, the newly
   allocated local pointer.  Later compiler temporaries remain protected. *)
Theorem iter_body_kept_outer[local]:
  vars_kept M ({x | x IN Wv /\ var_below N0 x} UNION P) s t /\
  N <= M /\ N <= N0 /\ (!x. x IN P ==> ~var_below N x) ==>
  vars_kept N Wv s t
Proof
  rw[vars_kept_def, var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem iter_body_fresh_protected[local]:
  N0 <= n /\ n < M /\
  (!x. x IN P ==> x <> STRING #"%" (toString n)) ==>
  var_below M (STRING #"%" (toString n)) /\
  STRING #"%" (toString n) NOTIN
    ({x | x IN Wv /\ var_below N0 x} UNION P)
Proof
  simp[var_below_def, ASCIInumbersTheory.toString_inj] >>
  rpt strip_tac >> gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem iter_body_kept_protected[local]:
  vars_kept M ({x | x IN Wv /\ var_below N0 x} UNION P) s t /\
  var_below M x /\ ~var_below N0 x /\ x NOTIN P ==>
  lookup_var x t = lookup_var x s
Proof
  simp[vars_kept_def] >> metis_tac[]
QED

Theorem iter_declare_ctor_exit[local]:
  declare_local ce id ty st = (bc,st') ==>
  bc.ce_ctor_exit_label = ce.ce_ctor_exit_label
Proof
  simp[declare_local_def] >>
  Cases_on `ce.ce_alloca_locals` >>
  simp[comp_bind_def, comp_return_def, fresh_var_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem iter_declare_ptrs[local]:
  declare_local ce id ty st = (bc,st') /\
  cenv_ptrs_in Wv ce /\ cenv_ptrs_below N0 ce /\
  N0 <= st.cs_next_var /\ st'.cs_next_var <= M ==>
  cenv_ptrs_in
    ({x | x IN Wv /\ var_below N0 x} UNION
     (if ce.ce_alloca_locals then {STRING #"%" (toString st.cs_next_var)} else {})) bc /\
  cenv_ptrs_below M bc
Proof
  Cases_on `ce.ce_alloca_locals` >>
  simp[declare_local_def, comp_bind_def, comp_return_def, fresh_var_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[cenv_ptrs_in_def, cenv_ptrs_below_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> gvs[] >>
  rpt (first_x_assum (drule_then assume_tac)) >>
  fs[var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem iter_ptr_load_fresh[local]:
  !ctor imm loc op st v st'.
  compile_ptr_load ctor imm loc op st = (v,st') ==>
  ?n. v = Var (STRING #"%" (toString n)) /\
      st.cs_next_var <= n /\ n < st'.cs_next_var
Proof
  rpt gen_tac >> Cases_on `ctor` >> Cases_on `imm` >>
  Cases_on `loc` >> simp[compile_ptr_load_def] >>
  simp[compile_imm_load_word_def, emit_op_def, fresh_id_def,
       fresh_var_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt strip_tac >> gvs[] >> simp[]
QED

Theorem iter_declare_exits[local]:
  declare_local ce id ty st = (bc,st') /\ stmt_exits_in E ce lc ==>
  stmt_exits_in (E UNION {exit_lbl; incr_lbl}) bc (InLoop exit_lbl incr_lbl)
Proof
  rpt strip_tac >> drule iter_declare_ctor_exit >>
  gvs[stmt_exits_in_def] >> metis_tac[]
QED

(* Modular distance decreases even when the index increment wraps. *)
Theorem iter_distance_decreases[local]:
  !(i:256 word) len.
    i <> len ==> w2n (len - (i + 1w)) < w2n (len - i)
Proof
  rpt strip_tac >>
  `len - (i + 1w) = (len - i) - 1w` by wordsLib.WORD_DECIDE_TAC >>
  pure_asm_rewrite_tac [] >> irule wordsTheory.WORD_PRED_THM >>
  simp[wordsTheory.WORD_EQ_SUB_ZERO]
QED

(* One non-exiting round preserves length and advances the equality counter.
   Fixed outcomes and external exits are carried by fuel_outcome and Q. *)
Theorem iter_equality_cycle[local]:
  !G ctx fn H Q idx len Kround.
    (!s. H s ==>
      ?j. j <= Kround /\
          fuel_outcome G ctx fn s j
            (\t. Q t \/
                 (H t /\ idx s <> len s /\
                  (idx t :256 word) = idx s + 1w /\ len t = len s))) ==>
    !s. H s ==>
      ?j. j <= (2 ** 256) * Kround /\ fuel_outcome G ctx fn s j Q
Proof
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac fuel_outcome_iterate >>
  qexists_tac `\s. w2n (len s - idx s :256 word)` >>
  conj_tac
  >- (rpt strip_tac >>
      qspec_then `len s - idx s :256 word` mp_tac wordsTheory.w2n_lt >>
      simp[wordsTheory.dimword_def]) >>
  rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >>
  qexists_tac `j` >> conj_tac >- asm_rewrite_tac[] >>
  irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
  gen_tac >> BETA_TAC >> strip_tac
  >- simp[] >>
  disj2_tac >> asm_rewrite_tac[] >>
  metis_tac[iter_distance_decreases]
QED

Theorem iter_cond_outcome[local]:
  (do d <- emit_op EQ [Var idx; lenop];
      emit_inst JNZ [d; Label ex; Label bl] [] od) a = ((),b) /\
  fn_has_code a b fn /\ no_phi_fn fn /\ callees_stable G ctx fn /\
  at_point a s /\ lookup_var idx s = SOME i /\
  eval_operand lenop s = SOME l /\ N <= a.cs_next_var ==>
  ?j. j <= 1 /\ fuel_outcome G ctx fn s j
    (\t. vars_kept N {} s t /\
         t.vs_current_bb = (if i = l then ex else bl) /\
         t.vs_inst_idx = 0)
Proof
  simp[emit_op_def, emit_inst_def, comp_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def, comp_ignore_bind_def] >>
  rpt strip_tac >> gvs[] >>
  drule fragExecTheory.fn_has_code_same_block >> simp[GSYM listTheory.APPEND_ASSOC] >>
  strip_tac >>
  `get_instruction bb (LENGTH a.cs_current_insts) =
     SOME (mk_inst a.cs_next_id EQ [Var idx; lenop]
        [STRING #"%" (toString a.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `get_instruction bb (LENGTH a.cs_current_insts + 1) =
     SOME (mk_inst (a.cs_next_id + 1) JNZ
        [Var (STRING #"%" (toString a.cs_next_var)); Label ex; Label bl] [])` by
    (first_x_assum (qspec_then `1` mp_tac) >> simp[]) >>
  gvs[at_point_def] >>
  qspecl_then [`G`, `ctx`, `fn`, `s`, `bb`,
    `mk_inst a.cs_next_id EQ [Var idx; lenop]
       [STRING #"%" (toString a.cs_next_var)]`] mp_tac
    run_from_nonterm_stable >>
  simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
  reverse strip_tac
  >- (qexists_tac `0` >> simp[fuel_outcome_def]) >>
  gvs[venomExecSemanticsTheory.step_inst_non_invoke,
      venomExecSemanticsTheory.step_inst_base_opcode_eqs,
      venomExecSemanticsTheory.exec_pure2_def,
      venomStateTheory.eval_operand_def] >>
  qmatch_asmsub_abbrev_tac `update_var v w s with vs_inst_idx := k` >>
  qabbrev_tac `u = update_var v w s with vs_inst_idx := k` >>
  `fuel_outcome G ctx fn u 1
    (\t. vars_kept N {} s t /\
         t.vs_current_bb = (if i = l then ex else bl) /\
         t.vs_inst_idx = 0)` suffices_by
    (strip_tac >> qexists_tac `1` >> gvs[fuel_outcome_def] >>
     metis_tac[]) >>
  irule fuel_outcome_jump >>
  conj_tac >- simp[] >>
  qexistsl_tac [`bb`,
    `mk_inst (a.cs_next_id + 1) JNZ [Var v; Label ex; Label bl] []`,
    `if i = l then ex else bl`] >>
  simp[Abbr `u`, venomInstTheory.mk_inst_def,
       venomInstTheory.is_terminator_def,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomStateTheory.eval_operand_def, venomStateTheory.update_var_def,
       venomStateTheory.lookup_var_def, venomStateTheory.jump_to_def] >>
  simp[Abbr `k`, Abbr `w`, finite_mapTheory.FLOOKUP_UPDATE,
       arithmeticPropsTheory.bool_to_word_neq_0w, GSYM venomInstTheory.mk_inst_def] >>
  Cases_on `i = l` >> simp[vars_kept_def, venomStateTheory.lookup_var_def,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  (conj_tac >- metis_tac[arithmeticTheory.ADD1]) >>
  rw[] >> `x <> v` by (gvs[Abbr `v`, var_below_def] >> metis_tac[]) >>
  simp[EQ_SYM_EQ]
QED

Theorem iter_cond_missing[local]:
  (do d <- emit_op EQ [Var idx; lenop];
      emit_inst JNZ [d; Label ex; Label bl] [] od) a = ((),b) /\
  fn_has_code a b fn /\ at_point a s /\
  (lookup_var idx s = NONE \/ eval_operand lenop s = NONE) ==>
  ?j. j <= 1 /\ fuel_outcome G ctx fn s j (\t. F)
Proof
  simp[emit_op_def, emit_inst_def, comp_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def, comp_ignore_bind_def] >>
  rpt strip_tac >> gvs[] >>
  drule fragExecTheory.fn_has_code_same_block >>
  simp[GSYM listTheory.APPEND_ASSOC] >> strip_tac >>
  `get_instruction bb (LENGTH a.cs_current_insts) =
     SOME (mk_inst a.cs_next_id EQ [Var idx; lenop]
        [STRING #"%" (toString a.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  gvs[at_point_def] >>
  qexists_tac `0` >> simp[fuel_outcome_def] >> rpt strip_tac >>
  simp[fragExecTheory.run_from_def,
       Once venomExecSemanticsTheory.exec_block_def,
       venomExecSemanticsTheory.step_inst_non_invoke,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomExecSemanticsTheory.exec_pure2_def,
       venomStateTheory.eval_operand_def, venomInstTheory.mk_inst_def,
       at_point_def] >>
  simp[Once venomExecSemanticsTheory.exec_block_def,
       venomExecSemanticsTheory.step_inst_non_invoke,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomExecSemanticsTheory.exec_pure2_def,
       venomStateTheory.eval_operand_def, venomInstTheory.mk_inst_def,
       AllCaseEqs()] >>
  once_rewrite_tac[venomExecSemanticsTheory.exec_block_def] >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomExecSemanticsTheory.exec_pure2_def,
       venomStateTheory.eval_operand_def, venomInstTheory.mk_inst_def,
       AllCaseEqs()] >>
  Cases_on `lookup_var idx s` >> simp[]
QED

Theorem iter_incr_outcome[local]:
  (do d <- emit_op ADD [Var idx; Lit 1w];
      emit_inst ASSIGN [d] [idx];
      emit_inst JMP [Label cond] [] od) a = ((),b) /\
  fn_has_code a b fn /\ no_phi_fn fn /\ callees_stable G ctx fn /\
  at_point a s /\ lookup_var idx s = SOME i /\
  var_below a.cs_next_var idx /\ N <= a.cs_next_var ==>
  ?j. j <= 1 /\ fuel_outcome G ctx fn s j
    (\t. vars_kept N {idx} s t /\ lookup_var idx t = SOME (i + 1w) /\
         t.vs_current_bb = cond /\ t.vs_inst_idx = 0)
Proof
  simp[emit_op_def, emit_inst_def, comp_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def, comp_ignore_bind_def] >>
  rpt strip_tac >> gvs[] >>
  drule fragExecTheory.fn_has_code_same_block >>
  simp[GSYM listTheory.APPEND_ASSOC] >> strip_tac >>
  `get_instruction bb (LENGTH a.cs_current_insts) =
     SOME (mk_inst a.cs_next_id ADD [Var idx; Lit 1w]
        [STRING #"%" (toString a.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `get_instruction bb (LENGTH a.cs_current_insts + 1) =
     SOME (mk_inst (a.cs_next_id + 1) ASSIGN
       [Var (STRING #"%" (toString a.cs_next_var))] [idx])` by
    (first_x_assum (qspec_then `1` mp_tac) >> simp[]) >>
  `get_instruction bb (LENGTH a.cs_current_insts + 2) =
     SOME (mk_inst (a.cs_next_id + 2) JMP [Label cond] [])` by
    (first_x_assum (qspec_then `2` mp_tac) >> simp[]) >>
  gvs[at_point_def] >>
  qspecl_then [`G`, `ctx`, `fn`, `s`, `bb`,
    `mk_inst a.cs_next_id ADD [Var idx; Lit 1w]
       [STRING #"%" (toString a.cs_next_var)]`] mp_tac
    run_from_nonterm_stable >>
  simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
  reverse strip_tac
  >- (qexists_tac `0` >> simp[fuel_outcome_def]) >>
  gvs[venomExecSemanticsTheory.step_inst_non_invoke,
      venomExecSemanticsTheory.step_inst_base_opcode_eqs,
      venomExecSemanticsTheory.exec_pure2_def,
      venomStateTheory.eval_operand_def] >>
  qmatch_asmsub_abbrev_tac `update_var v w s with vs_inst_idx := k` >>
  qabbrev_tac `u = update_var v w s with vs_inst_idx := k` >>
  `fuel_outcome G ctx fn u 1
    (\t. vars_kept N {idx} s t /\ lookup_var idx t = SOME (i + 1w) /\
         t.vs_current_bb = cond /\ t.vs_inst_idx = 0)` suffices_by
    (strip_tac >> qexists_tac `1` >> gvs[fuel_outcome_def] >> metis_tac[]) >>
  qspecl_then [`G`, `ctx`, `fn`, `u`, `bb`,
    `mk_inst (a.cs_next_id + 1) ASSIGN [Var v] [idx]`] mp_tac
    run_from_nonterm_stable >>
  simp[Abbr `u`, Abbr `k`, venomStateTheory.update_var_def,
       venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def,
       arithmeticTheory.ADD1] >>
  reverse strip_tac
  >- simp[fuel_outcome_def] >>
  gvs[venomExecSemanticsTheory.step_inst_non_invoke,
      venomExecSemanticsTheory.step_inst_base_opcode_eqs,
      venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE] >>
  qmatch_goalsub_abbrev_tac `fuel_outcome G ctx fn z 1` >>
  `fuel_outcome G ctx fn
     (update_var idx w z with vs_inst_idx := LENGTH a.cs_current_insts + 2) 1
     (\t. vars_kept N {idx} s t /\
          finite_map$FLOOKUP t.vs_vars idx = SOME w /\
          t.vs_current_bb = cond /\ t.vs_inst_idx = 0)` suffices_by
    (strip_tac >> gvs[fuel_outcome_def] >> metis_tac[]) >>
  irule fuel_outcome_jump >> conj_tac >- simp[] >>
  qexistsl_tac [`bb`, `mk_inst (a.cs_next_id + 2) JMP [Label cond] []`, `cond`] >>
  simp[Abbr `z`, venomStateTheory.update_var_def,
       venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomStateTheory.jump_to_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[vars_kept_def, venomStateTheory.lookup_var_def,
     finite_mapTheory.FLOOKUP_UPDATE] >>
  `x <> v` by (gvs[Abbr `v`, var_below_def] >> metis_tac[]) >>
  simp[EQ_SYM_EQ]
QED

Theorem iter_prefix_fuel[local]:
  (!c t e W E. fuel_ok W {} E (compile_expr c t e)) /\
  cenv_ptrs_in Wv ce /\ stmt_exits_in E ce lc ==>
  fuel_okS (\s. cenv_ptrs_below s.cs_next_var ce) Wv {} E
    (let arr_ty = expr_type arr_e in
     let is_dynamic = (case arr_ty of ArrayT _ (Dynamic _) => T | _ => F) in
     let count = (case arr_ty of ArrayT _ (Dynamic n) => n
                               | ArrayT _ (Fixed n) => n | _ => 0) in
     do arr_vv <- compile_expr ce arr_ty arr_e;
        arr_op <- return (vv_operand arr_vv);
        loc <- return (case vv_location arr_vv of SOME l => l | NONE => LocMemory);
        len_op <- (if is_dynamic then
          compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc arr_op
          else return (Lit (n2w count)));
        body_cenv <- declare_local ce id fty;
        emit_local_alloca body_cenv id;
        entry_lbl <- fresh_label "iter_entry";
        cond_lbl <- fresh_label "iter_cond";
        body_lbl <- fresh_label "iter_body";
        incr_lbl <- fresh_label "iter_incr";
        exit_lbl <- fresh_label "iter_exit";
        emit_inst JMP [Label entry_lbl] [];
        new_block entry_lbl;
        idx_var <- fresh_var;
        emit_inst ASSIGN [Lit 0w] [idx_var];
        (if is_dynamic then
          do invalid <- emit_op GT [len_op; Lit (n2w count)];
             valid <- emit_op ISZERO [invalid];
             emit_void ASSERT [valid] od
         else return ());
        return (body_cenv,arr_op,loc,len_op,idx_var,
                cond_lbl,body_lbl,incr_lbl,exit_lbl)
     od)
Proof
  rpt strip_tac >> irule fuel_okS_of_ok >>
  simp_tac std_ss [LET_THM, declare_local_def, comp_bind_assoc,
                   comp_bind_return] >>
  Cases_on `ce.ce_alloca_locals` >> simp[comp_bind_assoc, comp_bind_return] >>
  fuel_auto [fuel_ok_compile_ptr_load, fuel_ok_emit_local_alloca,
             fuel_ok_emit_op, fuel_ok_emit_void, fuel_ok_emit_inst_jmp,
             fuel_ok_emit_inst] >>
  simp[venomInstTheory.is_terminator_def, cenv_ptrs_in_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> gvs[cenv_ptrs_in_def] >> metis_tac[]
QED

Theorem iter_prefix_protected[local]:
  (!c t e W E. fuel_ok W {} E (compile_expr c t e)) /\
  cenv_ptrs_in Wv ce /\ stmt_exits_in E ce lc /\
  cenv_ptrs_below s.cs_next_var ce /\
  (let arr_ty = expr_type arr_e in
   let is_dynamic = (case arr_ty of ArrayT _ (Dynamic _) => T | _ => F) in
   let count = (case arr_ty of ArrayT _ (Dynamic n) => n
                             | ArrayT _ (Fixed n) => n | _ => 0) in
   do arr_vv <- compile_expr ce arr_ty arr_e;
      arr_op <- return (vv_operand arr_vv);
      loc <- return (case vv_location arr_vv of SOME l => l | NONE => LocMemory);
      len_op <- (if is_dynamic then
        compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc arr_op
        else return (Lit (n2w count)));
      body_cenv <- declare_local ce id fty;
      emit_local_alloca body_cenv id;
      entry_lbl <- fresh_label "iter_entry";
      cond_lbl <- fresh_label "iter_cond";
      body_lbl <- fresh_label "iter_body";
      incr_lbl <- fresh_label "iter_incr";
      exit_lbl <- fresh_label "iter_exit";
      emit_inst JMP [Label entry_lbl] [];
      new_block entry_lbl;
      idx_var <- fresh_var;
      emit_inst ASSIGN [Lit 0w] [idx_var];
      (if is_dynamic then
        do invalid <- emit_op GT [len_op; Lit (n2w count)];
           valid <- emit_op ISZERO [invalid];
           emit_void ASSERT [valid] od
       else return ());
      return (body_cenv,arr_op,loc,len_op,idx_var,
              cond_lbl,body_lbl,incr_lbl,exit_lbl)
   od) s = ((bc,arr,loc,lenop,idx,cl,bl,il,xl),p) ==>
  ?Wb. cenv_ptrs_in Wb bc /\ cenv_ptrs_below p.cs_next_var bc /\
       stmt_exits_in (E UNION {xl;il}) bc (InLoop xl il) /\
       var_below p.cs_next_var idx /\ idx NOTIN Wb /\
       (case lenop of Lit w => T
        | Var v => var_below p.cs_next_var v /\ v NOTIN Wb /\ v <> idx
        | _ => F) /\
       (!x. var_below s.cs_next_var x /\ x IN Wb ==> x IN Wv) /\
       ALL_DISTINCT [cl;bl;il;xl]
Proof
  simp_tac std_ss [LET_THM, comp_bind_def, comp_ignore_bind_def,
                   comp_return_def] >>
  rpt strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_expr ce (expr_type arr_e) arr_e s = (av,s1)` >>
  rename1 `declare_local ce id fty s2 = (bc,s3)` >>
  rename1 `emit_local_alloca bc id s3 = ((),s4)` >>
  `s.cs_next_var <= s1.cs_next_var` by
    (qpat_x_assum `!c t e W E. _` (qspecl_then [`ce`, `expr_type arr_e`, `arr_e`, `{}`, `{}`] mp_tac) >>
     simp[fuel_ok_def] >> metis_tac[]) >>
  gvs[fresh_label_def, fresh_var_def, emit_inst_def, fresh_id_def,
      emit_def, new_block_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def] >>
  `s3.cs_next_var <= s4.cs_next_var` by
    (qspecl_then [`bc`, `id`, `UNIV`, `{}`] mp_tac fuel_ok_emit_local_alloca >>
     simp[cenv_ptrs_in_def, fuel_ok_def] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `if dyn then compile_ptr_load _ _ _ _ else _` >>
  Cases_on `dyn` >>
  gs[emit_op_def, emit_void_def, emit_inst_def, fresh_id_def,
      fresh_var_def, emit_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def] >>
  TRY (drule iter_ptr_load_fresh >> strip_tac >> gvs[]) >>
  `s2.cs_next_var <= s3.cs_next_var` by
    (Cases_on `ce.ce_alloca_locals` >>
     gvs[declare_local_def, comp_bind_def, comp_return_def, fresh_var_def]) >>
  gvs[] >> rename1 `declare_local ce id fty s2 = (bc,s3)` >>
  qexists_tac `({x | x IN Wv /\ var_below s.cs_next_var x} UNION
    (if ce.ce_alloca_locals then {STRING #"%" (toString s2.cs_next_var)} else {}))` >>
  (conj_tac
   >- (irule (cj 1 iter_declare_ptrs) >> goal_assum (drule_at Any) >>
       simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS])) >>
  (conj_tac
   >- (qmatch_goalsub_abbrev_tac `cenv_ptrs_below M bc` >>
       drule iter_declare_ptrs >>
       disch_then (qspecl_then [`Wv`, `s.cs_next_var`, `M`] mp_tac) >>
       simp[Abbr `M`])) >>
  (conj_tac >- metis_tac[iter_declare_exits]) >>
  simp[var_below_def, ASCIInumbersTheory.toString_inj] >>
  Cases_on `ce.ce_alloca_locals` >>
  gvs[declare_local_def, comp_bind_def, comp_return_def, fresh_var_def,
      fresh_label_output_def, ASCIInumbersTheory.toString_inj] >>
  `s.cs_next_var <= s2.cs_next_var` by decide_tac >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!n. s.cs_next_var <= n ==> _` (qspec_then `s2.cs_next_var` mp_tac) >>
  simp[]

QED

Theorem fuel_okS_compile_for_iter:
  !cenv lctx ty id fty arr_e bound body Wv E.
    (!c t e Wv' E'. fuel_ok Wv' {} E' (compile_expr c t e)) /\
    (!cenv' lc Wv' E'.
       cenv_ptrs_in Wv' cenv' /\ stmt_exits_in E' cenv' lc ==>
       fuel_okS (\st. cenv_ptrs_below st.cs_next_var cenv') Wv' {} E'
         (compile_stmts cenv' lc ty body)) /\
    cenv_ptrs_in Wv cenv /\ stmt_exits_in E cenv lctx ==>
    fuel_okS (\st. cenv_ptrs_below st.cs_next_var cenv) Wv {} E
      (compile_stmt cenv lctx ty (For id fty (Array arr_e) bound body))
Proof
  cheat
QED
