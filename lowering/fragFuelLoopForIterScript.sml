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
       ~var_below s.cs_next_var idx /\
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

Theorem iter_body_slice_fuel[local]:
  !bc Wb E xl il ty body ce id fty arr_elem_ty loc arr idx is_dynamic.
  fuel_okS (\s. cenv_ptrs_below s.cs_next_var bc) Wb {} (E UNION {xl;il})
    (compile_stmts bc (InLoop xl il) ty body) ==>
  fuel_okS (\s. cenv_ptrs_below s.cs_next_var bc) Wb {} (E UNION {xl;il})
    (do offset_base <- return (if is_dynamic then word_scale loc else 0);
        idx_offset <- emit_op MUL [Var idx;
          Lit (n2w (elem_size_in_location ce loc arr_elem_ty))];
        total_offset <- (if offset_base > 0 then
          emit_op ADD [Lit (n2w offset_base); idx_offset] else return idx_offset);
        elem_ptr <- emit_op ADD [arr; total_offset];
        (case FLOOKUP bc.ce_vars id of
           SOME (MemLoc off _) =>
             compile_iter_elem_copy ce elem_ptr (Lit (n2w off))
               (elem_size_in_location ce loc arr_elem_ty)
               loc (is_slot_addressed loc) fty arr_elem_ty
         | SOME (PtrVar ptr_op _) =>
             compile_iter_elem_copy ce elem_ptr ptr_op
               (elem_size_in_location ce loc arr_elem_ty)
               loc (is_slot_addressed loc) fty arr_elem_ty
         | _ => emit_void INVALID []);
        compile_stmts bc (InLoop xl il) ty body;
        emit_jmp_if_not_terminated il
     od)
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac std_ss [comp_bind_return] >>
  rpt (FIRST [first_assum MATCH_ACCEPT_TAC,
       conj_tac,
       match_mp_tac fuel_okS_bind_keep >> conj_tac >- simp[next_stable_cenv_ptrs_below],
       match_mp_tac fuel_okS_ignore_bind_keep >> conj_tac >- simp[next_stable_cenv_ptrs_below],
       irule fuel_okS_if >> conj_tac >> strip_tac,
       gen_tac >> BETA_TAC]) >>
  irule fuel_okS_of_ok >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_compile_iter_elem_copy,
             fuel_ok_emit_void, fuel_ok_emit_jmp_if_not_terminated] >>
  simp[venomInstTheory.is_terminator_def] >>
  Cases_on `FLOOKUP bc.ce_vars id`
  >- (simp[] >> irule fuel_ok_emit_void_halt >> simp[]) >>
  simp[] >>
  rename1 `SOME binding` >> Cases_on `binding` >>
  simp[fuel_ok_compile_iter_elem_copy] >>
  irule fuel_ok_emit_void_halt >> simp[]
QED

Theorem iter_compile_layout[local]:
  !ce lc ty id fty arr_e bound body s r t.
  compile_stmt ce lc ty (For id fty (Array arr_e) bound body) s = (r,t) ==>
  r = () /\
  ?bc arr loc lenop idx cl bl il xl p c0 c1 b0 b1 i0 i1.
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
             valid <- emit_op ISZERO [invalid]; emit_void ASSERT [valid] od
         else return ());
        return (body_cenv,arr_op,loc,len_op,idx_var,
                cond_lbl,body_lbl,incr_lbl,exit_lbl)
     od) s = ((bc,arr,loc,lenop,idx,cl,bl,il,xl),p) /\
    (do emit_inst JMP [Label cl] []; new_block cl; return () od) p = ((),c0) /\
    (do d <- emit_op EQ [Var idx;lenop];
        emit_inst JNZ [d;Label xl;Label bl] [] od) c0 = ((),c1) /\
    (do new_block bl; return () od) c1 = ((),b0) /\
    (let arr_ty = expr_type arr_e in
     let is_dynamic = (case arr_ty of ArrayT _ (Dynamic _) => T | _ => F) in
     let arr_elem_ty = (case arr_ty of ArrayT et _ => et | _ => fty) in
     do offset_base <- return (if is_dynamic then word_scale loc else 0);
        idx_offset <- emit_op MUL [Var idx;
          Lit (n2w (elem_size_in_location ce loc arr_elem_ty))];
        total_offset <- (if offset_base > 0 then
          emit_op ADD [Lit (n2w offset_base);idx_offset] else return idx_offset);
        elem_ptr <- emit_op ADD [arr;total_offset];
        (case FLOOKUP bc.ce_vars id of
           SOME (MemLoc off _) =>
             compile_iter_elem_copy ce elem_ptr (Lit (n2w off))
               (elem_size_in_location ce loc arr_elem_ty)
               loc (is_slot_addressed loc) fty arr_elem_ty
         | SOME (PtrVar ptr_op _) =>
             compile_iter_elem_copy ce elem_ptr ptr_op
               (elem_size_in_location ce loc arr_elem_ty)
               loc (is_slot_addressed loc) fty arr_elem_ty
         | _ => emit_void INVALID []);
        compile_stmts bc (InLoop xl il) ty body;
        emit_jmp_if_not_terminated il od) b0 = ((),b1) /\
    (do new_block il; return () od) b1 = ((),i0) /\
    (do d <- emit_op ADD [Var idx;Lit 1w];
        emit_inst ASSIGN [d] [idx];
        emit_inst JMP [Label cl] [] od) i0 = ((),i1) /\
    (do new_block xl; return () od) i1 = ((),t)
Proof
  rpt gen_tac >>
  simp_tac std_ss [Once compile_stmt_def, LET_THM,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem iter_control_contract[local]:
  (do emit_inst JMP [Label cl] []; new_block cl; return () od) p = ((),c0) /\
  (do d <- emit_op EQ [Var idx;lenop];
      emit_inst JNZ [d;Label xl;Label bl] [] od) c0 = ((),c1) /\
  (do new_block bl; return () od) c1 = ((),b0) /\
  (do new_block il; return () od) b1 = ((),i0) /\
  (do d <- emit_op ADD [Var idx;Lit 1w];
      emit_inst ASSIGN [d] [idx];
      emit_inst JMP [Label cl] [] od) i0 = ((),i1) /\
  (do new_block xl; return () od) i1 = ((),t) ==>
  cs_extends p c0 /\ cs_extends c0 c1 /\ cs_extends c1 b0 /\
  cs_extends b1 i0 /\ cs_extends i0 i1 /\ cs_extends i1 t /\
  p.cs_next_var <= c0.cs_next_var /\ c0.cs_next_var <= c1.cs_next_var /\
  c1.cs_next_var <= b0.cs_next_var /\ b1.cs_next_var <= i0.cs_next_var /\
  i0.cs_next_var <= i1.cs_next_var /\ i1.cs_next_var <= t.cs_next_var /\
  (cs_no_phi p ==> cs_no_phi b0) /\
  (cs_no_phi b1 ==> cs_no_phi t)
Proof
  strip_tac >>
  `fuel_ok {} {} {cl}
    (do emit_inst JMP [Label cl] []; new_block cl; return () od)` by
    (fuel_auto [fuel_ok_emit_inst_jmp] >> simp[]) >>
  `fuel_ok {} {} {xl;bl}
    (do d <- emit_op EQ [Var idx;lenop];
        emit_inst JNZ [d;Label xl;Label bl] [] od)` by
    (fuel_auto [fuel_ok_emit_op, fuel_ok_emit_inst_jnz] >>
     simp[venomInstTheory.is_terminator_def]) >>
  `fuel_ok {idx} {} {cl}
    (do d <- emit_op ADD [Var idx;Lit 1w];
        emit_inst ASSIGN [d] [idx]; emit_inst JMP [Label cl] [] od)` by
    (fuel_auto [fuel_ok_emit_op, fuel_ok_emit_inst_jmp, fuel_ok_emit_inst] >>
     simp[venomInstTheory.is_terminator_def]) >>
  `!lbl. fuel_ok {} {} {} (do new_block lbl; return () od)` by
    (gen_tac >> fuel_auto []) >>
  first_assum (qspec_then `bl` assume_tac) >>
  first_assum (qspec_then `il` assume_tac) >>
  first_assum (qspec_then `xl` assume_tac) >>
  qpat_x_assum `!lbl. fuel_ok _ _ _ _` kall_tac >>
  rpt (qpat_x_assum `fuel_ok _ _ _ _`
         (mp_tac o PURE_REWRITE_RULE [fuel_ok_def]) >>
       disch_then (drule_then strip_assume_tac)) >>
  metis_tac[]
QED

Theorem iter_slice_contract[local]:
  !body.
  (!c t e W E. fuel_ok W {} E (compile_expr c t e)) /\
  (!bc lc W E. cenv_ptrs_in W bc /\ stmt_exits_in E bc lc ==>
     fuel_okS (\s. cenv_ptrs_below s.cs_next_var bc) W {} E
       (compile_stmts bc lc ty body)) /\
  cenv_ptrs_in Wv ce /\ stmt_exits_in E ce lc /\
  cenv_ptrs_below s.cs_next_var ce /\ p.cs_next_var <= b0.cs_next_var /\
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
           valid <- emit_op ISZERO [invalid]; emit_void ASSERT [valid] od
       else return ());
      return (body_cenv,arr_op,loc,len_op,idx_var,
              cond_lbl,body_lbl,incr_lbl,exit_lbl)
   od) s = ((bc,arr,loc,lenop,idx,cl,bl,il,xl),p) /\
  (let arr_ty = expr_type arr_e in
   let is_dynamic = (case arr_ty of ArrayT _ (Dynamic _) => T | _ => F) in
   let arr_elem_ty = (case arr_ty of ArrayT et _ => et | _ => fty) in
   do offset_base <- return (if is_dynamic then word_scale loc else 0);
      idx_offset <- emit_op MUL [Var idx;
        Lit (n2w (elem_size_in_location ce loc arr_elem_ty))];
      total_offset <- (if offset_base > 0 then
        emit_op ADD [Lit (n2w offset_base);idx_offset] else return idx_offset);
      elem_ptr <- emit_op ADD [arr;total_offset];
      (case FLOOKUP bc.ce_vars id of
         SOME (MemLoc off _) =>
           compile_iter_elem_copy ce elem_ptr (Lit (n2w off))
             (elem_size_in_location ce loc arr_elem_ty)
             loc (is_slot_addressed loc) fty arr_elem_ty
       | SOME (PtrVar ptr_op _) =>
           compile_iter_elem_copy ce elem_ptr ptr_op
             (elem_size_in_location ce loc arr_elem_ty)
             loc (is_slot_addressed loc) fty arr_elem_ty
       | _ => emit_void INVALID []);
      compile_stmts bc (InLoop xl il) ty body;
      emit_jmp_if_not_terminated il od) b0 = ((),b1) ==>
  cs_extends s p /\ s.cs_next_var <= p.cs_next_var /\
  (cs_no_phi s ==> cs_no_phi p) /\
  cs_extends b0 b1 /\ b0.cs_next_var <= b1.cs_next_var /\
  (cs_no_phi b0 ==> cs_no_phi b1) /\
  ?Wb Kpre Kbody.
    cenv_ptrs_in Wb bc /\ cenv_ptrs_below p.cs_next_var bc /\
    stmt_exits_in (E UNION {xl;il}) bc (InLoop xl il) /\
    var_below p.cs_next_var idx /\ idx NOTIN Wb /\
       ~var_below s.cs_next_var idx /\
    (case lenop of Lit w => T
     | Var v => var_below p.cs_next_var v /\ v NOTIN Wb /\ v <> idx
     | _ => F) /\
    (!x. var_below s.cs_next_var x /\ x IN Wb ==> x IN Wv) /\
    ALL_DISTINCT [cl;bl;il;xl] /\
    frag_fuel Wv {} E s p Kpre /\
    frag_fuel Wb {} (E UNION {xl;il}) b0 b1 Kbody
Proof
  gen_tac >> strip_tac >>
  drule_all iter_prefix_fuel >>
  simp_tac bool_ss [fuel_okS_def] >>
  disch_then (drule_all_then strip_assume_tac) >>
  drule_all iter_prefix_protected >> strip_tac >>
  `cenv_ptrs_below b0.cs_next_var bc` by
    (qpat_x_assum `cenv_ptrs_below p.cs_next_var bc` mp_tac >>
     qpat_x_assum `p.cs_next_var <= b0.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >>
     rw[cenv_ptrs_below_def, var_below_def] >>
     first_x_assum drule >> strip_tac >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qpat_x_assum `!bc lc W E. _` drule_all >>
  disch_then (mp_tac o GEN_ALL o MATCH_MP iter_body_slice_fuel) >>
  qpat_x_assum `_ b0 = ((),b1)`
    (assume_tac o SIMP_RULE std_ss [LET_THM]) >>
  simp_tac bool_ss [fuel_okS_def] >>
  disch_then (drule_all_then strip_assume_tac) >>
  metis_tac[]
QED

Theorem iter_layout_structure[local]:
  (do emit_inst JMP [Label cl] []; new_block cl; return () od) p = ((),c0) /\
  (do d <- emit_op EQ [Var idx;lenop];
      emit_inst JNZ [d;Label xl;Label bl] [] od) c0 = ((),c1) /\
  (do new_block bl; return () od) c1 = ((),b0) /\
  (do new_block il; return () od) b1 = ((),i0) /\
  (do d <- emit_op ADD [Var idx;Lit 1w];
      emit_inst ASSIGN [d] [idx]; emit_inst JMP [Label cl] [] od) i0 = ((),i1) /\
  (do new_block xl; return () od) i1 = ((),t) /\
  cs_extends s p /\ s.cs_next_var <= p.cs_next_var /\
  (cs_no_phi s ==> cs_no_phi p) /\
  cs_extends b0 b1 /\ b0.cs_next_var <= b1.cs_next_var /\
  (cs_no_phi b0 ==> cs_no_phi b1) ==>
  cs_extends s t /\ s.cs_next_var <= t.cs_next_var /\
  (cs_no_phi s ==> cs_no_phi t) /\
  (!fn. fn_has_code s t fn ==>
     fn_has_code s p fn /\ fn_has_code p c0 fn /\
     fn_has_code c0 c1 fn /\ fn_has_code b0 b1 fn /\
     fn_has_code i0 i1 fn)
Proof
  strip_tac >> drule_all iter_control_contract >> strip_tac >>
  `cs_extends s c0` by metis_tac[cs_extends_trans] >>
  `cs_extends s c1` by metis_tac[cs_extends_trans] >>
  `cs_extends s b0` by metis_tac[cs_extends_trans] >>
  `cs_extends s b1` by metis_tac[cs_extends_trans] >>
  `cs_extends s i0` by metis_tac[cs_extends_trans] >>
  `cs_extends s i1` by metis_tac[cs_extends_trans] >>
  `cs_extends i0 t` by metis_tac[cs_extends_trans] >>
  `cs_extends b1 t` by metis_tac[cs_extends_trans] >>
  `cs_extends b0 t` by metis_tac[cs_extends_trans] >>
  `cs_extends c1 t` by metis_tac[cs_extends_trans] >>
  `cs_extends c0 t` by metis_tac[cs_extends_trans] >>
  `cs_extends p t` by metis_tac[cs_extends_trans] >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  conj_tac >- decide_tac >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  metis_tac[fragExecTheory.fn_has_code_mid, cs_extends_refl]
QED
Theorem iter_body_route[local]:
  frag_fuel Wb {} (E UNION {xl;il}) b0 b1 Kbody /\
  cs_extends b0 b1 /\ b0.cs_next_var <= b1.cs_next_var /\
  (do new_block il; return () od) b1 = ((),i0) ==>
  ?Kroute. frag_fuel Wb {il} (E UNION {xl}) b0 i0 Kroute
Proof
  strip_tac >>
  qspecl_then [`il`, `Wb`, `E UNION {xl}`] mp_tac fuel_ok_new_block >>
  simp_tac bool_ss [fuel_ok_def] >>
  qpat_x_assum `(do new_block il; return () od) b1 = ((),i0)` mp_tac >>
  simp_tac std_ss [comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  Cases_on `new_block il b1` >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  qexists_tac `Kbody + Kb` >>
  irule (Q.SPECL [`Wb`, `{}`, `{il}`] frag_fuel_seq |> SIMP_RULE (srw_ss()) []) >>
  qexistsl_tac [`E UNION {xl;il}`, `E UNION {xl}`, `b1`] >>
  simp[pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Theorem iter_body_route_outcome[local]:
  frag_fuel Wb {il} (E UNION {xl}) b0 i0 Kroute /\
  N <= M /\ M <= b0.cs_next_var /\
  (!x. var_below N x /\ x IN Wb ==> x IN Wv) /\
  var_below M idx /\ idx NOTIN Wb /\
  (case lenop of Lit w => T
   | Var v => var_below M v /\ v NOTIN Wb | _ => F) /\
  fn_has_code b0 i0 fn /\ no_phi_fn fn /\ callees_stable G ctx fn /\
  at_point b0 u ==>
  ?j. j <= Kroute /\ fuel_outcome G ctx fn u j
    (\v. vars_kept N Wv u v /\ lookup_var idx v = lookup_var idx u /\
         eval_operand lenop v = eval_operand lenop u /\
         (at_point i0 v \/ (v.vs_current_bb IN (E UNION {xl}) /\ v.vs_inst_idx = 0)))
Proof
  strip_tac >>
  qpat_x_assum `frag_fuel _ _ _ _ _ _` (mp_tac o PURE_REWRITE_RULE [frag_fuel_def]) >>
  disch_then (qspecl_then [`G`, `M`, `ctx`, `fn`, `u`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `j` >> simp[] >>
  irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
  qx_gen_tac `v` >> simp[] >> strip_tac >>
  `vars_kept N Wv u v` by
    (gvs[vars_kept_def, var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `lookup_var idx v = lookup_var idx u` by metis_tac[vars_kept_def] >>
  simp[] >> Cases_on `lenop` >> gvs[venomStateTheory.eval_operand_def] >>
  metis_tac[vars_kept_def]
QED

Theorem iter_incr_frame_outcome[local]:
  (do d <- emit_op ADD [Var idx; Lit 1w];
      emit_inst ASSIGN [d] [idx]; emit_inst JMP [Label cl] [] od) i0 = ((),i1) /\
  fn_has_code i0 i1 fn /\ no_phi_fn fn /\ callees_stable G ctx fn /\
  at_point i0 u /\ lookup_var idx u = SOME i /\
  var_below M idx /\ M <= i0.cs_next_var /\ N <= M /\
  ~var_below N idx /\
  (case lenop of Lit w => T
   | Var v => var_below M v /\ v <> idx | _ => F) ==>
  ?j. j <= 1 /\ fuel_outcome G ctx fn u j
    (\v. vars_kept N Wv u v /\ lookup_var idx v = SOME (i + 1w) /\
         eval_operand lenop v = eval_operand lenop u /\
         v.vs_current_bb = cl /\ v.vs_inst_idx = 0)
Proof
  strip_tac >>
  `var_below i0.cs_next_var idx` by
    (gvs[var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  drule_all iter_incr_outcome >>
  strip_tac >>
  qexists_tac `j` >> simp[] >>
  irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
  qx_gen_tac `v` >> simp[] >> strip_tac >>
  `vars_kept N Wv u v` by
    (gvs[vars_kept_def, var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  simp[] >> Cases_on `lenop` >> gvs[venomStateTheory.eval_operand_def] >>
  metis_tac[vars_kept_def, pred_setTheory.IN_SING]
QED

Theorem iter_body_incr_outcome[local]:
  frag_fuel Wb {il} (E UNION {xl}) b0 i0 Kroute /\
  (do d <- emit_op ADD [Var idx; Lit 1w];
      emit_inst ASSIGN [d] [idx]; emit_inst JMP [Label cl] [] od) i0 = ((),i1) /\
  fn_has_code b0 i0 fn /\ fn_has_code i0 i1 fn /\
  no_phi_fn fn /\ callees_stable G ctx fn /\
  N <= M /\ M <= b0.cs_next_var /\ M <= i0.cs_next_var /\
  (!x. var_below N x /\ x IN Wb ==> x IN Wv) /\
  var_below M idx /\ idx NOTIN Wb /\ ~var_below N idx /\
  (case lenop of Lit w => T
   | Var v => var_below M v /\ v NOTIN Wb /\ v <> idx | _ => F) /\
  at_point b0 u /\ lookup_var idx u = SOME i /\ eval_operand lenop u = SOME l ==>
  ?j. j <= Kroute + 1 /\ fuel_outcome G ctx fn u j
    (\v. vars_kept N Wv u v /\
      ((v.vs_current_bb IN (E UNION {xl}) /\ v.vs_inst_idx = 0) \/
       (v.vs_current_bb = cl /\ v.vs_inst_idx = 0 /\
        lookup_var idx v = SOME (i + 1w) /\ eval_operand lenop v = SOME l)))
Proof
  strip_tac >>
  `case lenop of Lit w => T | Var v => var_below M v /\ v NOTIN Wb | _ => F` by
    (Cases_on `lenop` >> gvs[]) >>
  drule_all iter_body_route_outcome >> strip_tac >>
  drule fuel_outcome_compose >>
  disch_then (qspecl_then
    [`\v. vars_kept N Wv u v /\
      ((v.vs_current_bb IN (E UNION {xl}) /\ v.vs_inst_idx = 0) \/
       (v.vs_current_bb = cl /\ v.vs_inst_idx = 0 /\
        lookup_var idx v = SOME (i + 1w) /\ eval_operand lenop v = SOME l))`, `1`] mp_tac) >>
  (impl_tac >- (
    qx_gen_tac `v` >> BETA_TAC >> disch_tac >>
    Cases_on `v.vs_current_bb IN (E UNION {xl}) /\ v.vs_inst_idx = 0`
    >- (qexists_tac `0` >> simp[] >> irule fuel_outcome_refl >> gvs[]) >>
    rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
    `at_point i0 v` by metis_tac[] >>
    `lookup_var idx v = SOME i` by metis_tac[] >>
    `case lenop of Lit w => T | Var x => var_below M x /\ x <> idx | _ => F` by
      (Cases_on `lenop` >> gvs[]) >>
    drule_all iter_incr_frame_outcome >>
    disch_then (qspec_then `Wv` strip_assume_tac) >>
    qexists_tac `j'` >> simp[] >>
    irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
    simp[] >> metis_tac[vars_kept_trans])) >>
  strip_tac >> qexists_tac `j'` >> simp[] >> decide_tac
QED


Theorem iter_round_outcome[local]:
  (do d <- emit_op EQ [Var idx; lenop];
      emit_inst JNZ [d; Label xl; Label bl] [] od) c0 = ((),c1) /\
  (do d <- emit_op ADD [Var idx; Lit 1w];
      emit_inst ASSIGN [d] [idx]; emit_inst JMP [Label cl] [] od) i0 = ((),i1) /\
  frag_fuel Wb {il} (E UNION {xl}) b0 i0 Kroute /\
  fn_has_code c0 c1 fn /\ fn_has_code b0 i0 fn /\ fn_has_code i0 i1 fn /\
  no_phi_fn fn /\ callees_stable G ctx fn /\
  c0.cs_current_bb = cl /\ c0.cs_current_insts = [] /\
  b0.cs_current_bb = bl /\ b0.cs_current_insts = [] /\
  N <= M /\ M <= c0.cs_next_var /\ M <= b0.cs_next_var /\ M <= i0.cs_next_var /\
  (!x. var_below N x /\ x IN Wb ==> x IN Wv) /\
  var_below M idx /\ idx NOTIN Wb /\ ~var_below N idx /\
  (case lenop of Lit w => T
   | Var v => var_below M v /\ v NOTIN Wb /\ v <> idx | _ => F) /\
  at_point c0 u /\ lookup_var idx u = SOME i /\ eval_operand lenop u = SOME l ==>
  ?j. j <= Kroute + 2 /\ fuel_outcome G ctx fn u j
    (\v. vars_kept N Wv u v /\
      ((v.vs_current_bb IN (E UNION {xl}) /\ v.vs_inst_idx = 0) \/
       (at_point c0 v /\ i <> l /\
        lookup_var idx v = SOME (i + 1w) /\ eval_operand lenop v = SOME l)))
Proof
  strip_tac >>
  drule_all iter_cond_outcome >> strip_tac >>
  drule fuel_outcome_compose >>
  disch_then (qspecl_then
    [`\v. vars_kept N Wv u v /\
      ((v.vs_current_bb IN (E UNION {xl}) /\ v.vs_inst_idx = 0) \/
       (at_point c0 v /\ i <> l /\
        lookup_var idx v = SOME (i + 1w) /\ eval_operand lenop v = SOME l))`,
     `Kroute + 1`] mp_tac) >>
  (impl_tac >- (
    qx_gen_tac `v` >> BETA_TAC >> strip_tac >>
    `vars_kept N Wv u v` by
      (gvs[vars_kept_def, var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
    Cases_on `i = l`
    >- (qexists_tac `0` >> simp[] >> irule fuel_outcome_refl >> gvs[]) >>
    `at_point b0 v` by gvs[at_point_def] >>
    `lookup_var idx v = SOME i` by metis_tac[vars_kept_def, pred_setTheory.NOT_IN_EMPTY] >>
    `eval_operand lenop v = SOME l` by
      (Cases_on `lenop` >> gvs[venomStateTheory.eval_operand_def] >>
       metis_tac[vars_kept_def, pred_setTheory.NOT_IN_EMPTY]) >>
    drule_all iter_body_incr_outcome >> strip_tac >>
    qexists_tac `j'` >> simp[] >>
    irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
    simp[at_point_def] >> metis_tac[vars_kept_trans])) >>
  strip_tac >> qexists_tac `j'` >> simp[] >> decide_tac
QED

Theorem iter_round_cycle[local]:
  !K. (!u i l. at_point c0 u /\ lookup_var idx u = SOME i /\
      eval_operand lenop u = SOME l ==>
    ?j. j <= K /\ fuel_outcome G ctx fn u j
      (\v. vars_kept N Wv u v /\
        ((v.vs_current_bb IN X /\ v.vs_inst_idx = 0) \/
         (at_point c0 v /\ i <> l /\ lookup_var idx v = SOME (i + 1w) /\
          eval_operand lenop v = SOME l)))) ==>
  !u i l. at_point c0 u /\ lookup_var idx u = SOME i /\
      eval_operand lenop u = SOME l ==>
    ?j. j <= (2 ** 256) * K /\ fuel_outcome G ctx fn u j
      (\v. vars_kept N Wv u v /\ v.vs_current_bb IN X /\ v.vs_inst_idx = 0)
Proof
  qx_gen_tac `Kround` >> disch_tac >> rpt gen_tac >> strip_tac >>
  qspecl_then [`G`, `ctx`, `fn`,
    `\v. at_point c0 v /\ IS_SOME (lookup_var idx v) /\
         IS_SOME (eval_operand lenop v) /\ vars_kept N Wv u v`,
    `\v. vars_kept N Wv u v /\ v.vs_current_bb IN X /\ v.vs_inst_idx = 0`,
    `\v. THE (lookup_var idx v)`, `\v. THE (eval_operand lenop v)`, `Kround`]
    mp_tac iter_equality_cycle >> BETA_TAC >>
  (impl_tac >- (
    qx_gen_tac `v` >> strip_tac >>
    Cases_on `lookup_var idx v` >> gvs[] >>
    Cases_on `eval_operand lenop v` >> gvs[] >>
    first_x_assum (drule_all_then strip_assume_tac) >>
    qexists_tac `j` >> simp[] >>
    irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
    gen_tac >> strip_tac >>
    `vars_kept N Wv u t` by metis_tac[vars_kept_trans] >>
    gvs[])) >>
  disch_then (qspec_then `u` mp_tac) >>
  simp[vars_kept_refl]
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
  rpt gen_tac >> strip_tac >>
  simp_tac bool_ss [fuel_okS_def] >>
  rpt gen_tac >> strip_tac >>
  drule iter_compile_layout >> strip_tac >>
  drule_all iter_control_contract >> strip_tac >>
  `p.cs_next_var <= b0.cs_next_var` by decide_tac >>
  drule_all iter_slice_contract >> strip_tac >>
  drule_all iter_layout_structure >> strip_tac >>
  simp[] >>
  rename1 `frag_fuel Wv {} E st p Kpre` >>
  rename1 `frag_fuel Wb {} (E UNION {xl;il}) b0 b1 Kbody` >>
  drule_all iter_body_route >> strip_tac >>
  `fuel_ok Wv {} E
     (do emit_inst JMP [Label cl] []; new_block cl; return () od)` by
    (fuel_auto [fuel_ok_emit_inst_jmp] >> simp[]) >>
  qpat_x_assum `fuel_ok Wv {} E _`
    (mp_tac o PURE_REWRITE_RULE [fuel_ok_def]) >>
  disch_then (drule_then strip_assume_tac) >>
  rename1 `frag_fuel Wv {} E p c0 Kentry` >>
  `frag_fuel Wv {} E st c0 (Kpre + Kentry)` by
    (irule (Q.SPECL [`Wv`, `{}`, `{}`] frag_fuel_seq |> SIMP_RULE (srw_ss()) []) >>
     qexistsl_tac [`E`, `E`, `p`] >> simp[]) >>
  qexists_tac `Kpre + Kentry + (2 ** 256) * (Kroute + 2) + 1` >>
  simp_tac bool_ss [frag_fuel_def] >> rpt gen_tac >> strip_tac >>
  gvs[pred_setTheory.NOT_IN_EMPTY] >>
  `fn_has_code c0 c1 fn /\ fn_has_code i0 i1 fn /\ fn_has_code b0 b1 fn` by metis_tac[] >>
  `cs_extends st c0` by metis_tac[cs_extends_trans] >>
  `cs_extends st c1` by metis_tac[cs_extends_trans] >>
  `cs_extends st b0` by metis_tac[cs_extends_trans] >>
  `cs_extends b0 i0` by metis_tac[cs_extends_trans] >>
  `cs_extends i0 st'` by metis_tac[cs_extends_trans] >>
  `cs_extends b0 st'` by metis_tac[cs_extends_trans] >>
  `cs_extends c1 st'` by metis_tac[cs_extends_trans] >>
  `cs_extends c0 st'` by metis_tac[cs_extends_trans] >>
  `fn_has_code st c0 fn /\ fn_has_code b0 i0 fn` by
    metis_tac[fragExecTheory.fn_has_code_mid, cs_extends_refl] >>
  `c0.cs_current_bb = cl /\ c0.cs_current_insts = [] /\
   b0.cs_current_bb = bl /\ b0.cs_current_insts = [] /\
   st'.cs_current_bb = xl /\ st'.cs_current_insts = []` by
    (qpat_x_assum `_ p = ((),c0)` mp_tac >>
     qpat_x_assum `_ c1 = ((),b0)` mp_tac >>
     qpat_x_assum `_ i1 = ((),st')` mp_tac >>
     simp[comp_ignore_bind_def, comp_bind_def, comp_return_def,
          new_block_def, emit_inst_def, emit_def, fresh_id_def] >>
     rpt strip_tac >> gvs[]) >>
  `N <= p.cs_next_var /\ p.cs_next_var <= i0.cs_next_var` by decide_tac >>
  `~var_below N idx` by
    (gvs[var_below_def] >> decide_tac) >>
  `!x. var_below N x /\ x IN Wb ==> x IN Wv` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     gvs[var_below_def] >> decide_tac) >>
  `!u i l. at_point c0 u /\ lookup_var idx u = SOME i /\
      eval_operand lenop u = SOME l ==>
    ?j. j <= Kroute + 2 /\ fuel_outcome G ctx fn u j
      (\v. vars_kept N Wv u v /\
        ((v.vs_current_bb IN (E UNION {xl}) /\ v.vs_inst_idx = 0) \/
         (at_point c0 v /\ i <> l /\ lookup_var idx v = SOME (i + 1w) /\
          eval_operand lenop v = SOME l)))` by
    (rpt gen_tac >> strip_tac >> irule iter_round_outcome >> simp[] >>
     qexistsl_tac [`p.cs_next_var`, `Wb`, `b0`, `c1`, `i0`, `i1`, `il`] >> simp[]) >>
  drule iter_round_cycle >> strip_tac >>
  qpat_x_assum `frag_fuel Wv {} E st c0 _`
    (mp_tac o PURE_REWRITE_RULE [frag_fuel_def]) >>
  disch_then (qspecl_then [`G`, `N`, `ctx`, `fn`, `s`] mp_tac) >>
  simp[] >> strip_tac >>
  drule fuel_outcome_compose >>
  disch_then (qspecl_then
    [`\t. vars_kept N Wv s t /\
       (at_point st' t \/ (t.vs_current_bb IN E /\ t.vs_inst_idx = 0))`,
     `(2 ** 256) * (Kroute + 2) + 1`] mp_tac) >>
  (impl_tac >- (
    qx_gen_tac `v` >> BETA_TAC >> disch_tac >>
    Cases_on `v.vs_current_bb IN E /\ v.vs_inst_idx = 0`
    >- (qexists_tac `0` >> simp[] >> irule fuel_outcome_refl >> gvs[]) >>
    `at_point c0 v` by metis_tac[] >>
    Cases_on `lookup_var idx v = NONE \/ eval_operand lenop v = NONE`
    >- (drule_all iter_cond_missing >>
        disch_then (qspecl_then [`ctx`, `G`] strip_assume_tac) >>
        qexists_tac `j'` >> conj_tac >- decide_tac >>
        irule fuel_outcome_weaken >> goal_assum (drule_at Any) >> simp[]) >>
    Cases_on `lookup_var idx v` >> Cases_on `eval_operand lenop v` >> gvs[] >>
    first_x_assum (drule_all_then strip_assume_tac) >>
    qexists_tac `j'` >> conj_tac >- decide_tac >>
    irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
    qx_gen_tac `t` >> BETA_TAC >> strip_tac >>
    `vars_kept N Wv s t` by metis_tac[vars_kept_trans] >>
    simp[at_point_def] >> gvs[])) >>
  strip_tac >> qexists_tac `j'` >> gvs[] >> decide_tac
QED
