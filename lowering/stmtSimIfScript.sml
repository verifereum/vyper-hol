(*
 * Statement simulation: If, Raise and Assert (#637)
 *
 * Cases of stmt_frag (stmtSim).  A condition's fragment and its JNZ
 * (cond_jump_frag), then either branch as a statement list in a scope of
 * its own; Raise and Assert with no reason, whose aborts are exits.
 *
 * TOP-LEVEL:
 *   cond_jump_frag        — a condition and the jump on it
 *   compile_if_stmt_frag  — If, either branch, every outcome
 *   compile_raise_frag, compile_assert_frag
 *)

Theory stmtSimIf
Ancestors
  stmtSimProps stmtSimIfProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set
  fragExec localPtrsProps  loweringSlice
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding
  vyperInterpreter vyperState vyperValue vyperEvalPreservesScopes
  vyperExprNoControl vyperValueOperation vyperStatePreservation
  venomExecSemantics venomExecProofs venomInst venomState integer_word
Libs
  monadsyntax intLib

(* Source-level forcing boundary for conditions with arbitrary branches. *)



(* ===== A condition and its JNZ ===== *)

(* A boolean condition lowered from sa to s1 and a JNZ on it right after,
   in a block that fn holds as finished: on a value, b, the run goes on
   from the JNZ's target for b in a state related at the source state
   after the condition, the variables handed out before sa and the
   allocations kept; on an error it exits as expr_exit allows. *)
Theorem cond_jump_frag:
  !ctx func cx cenv e es r1 es1 sa op s1 s3 s4 lt lf s0.
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    expr_type e = BaseT BoolT /\
    lower_value compile_expr cenv (BaseT BoolT) e sa = (op, s1) /\
    (do result <- eval_expr cx e; read_result cx result od) es = (r1, es1) /\ expr_res_ok r1 /\
    (!v. r1 = INL v ==> ?b. v = BoolV b) /\
    s3.cs_current_bb = s1.cs_current_bb /\
    s3.cs_current_insts = s1.cs_current_insts /\
    emit_inst JNZ [op; Label lt; Label lf] [] s3 = ((), s4) /\
    lookup_block s4.cs_current_bb func.fn_blocks =
      SOME <| bb_label := s4.cs_current_bb;
              bb_instructions := s4.cs_current_insts |> /\
    fn_has_code sa s1 func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    (?b s. r1 = INL (BoolV b) /\
           stmt_state_rel ctx func cenv cx es1 s /\ ~s.vs_halted /\
           (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                  lookup_var x s = SOME w) /\
           (!aid bnd. FLOOKUP s0.vs_allocas aid = SOME bnd ==>
                      FLOOKUP s.vs_allocas aid = SOME bnd) /\
           !fuel r. run_from fuel ctx func (jump_to (if b then lt else lf) s) = r /\
                    (!e. r <> Error e) ==>
                    ?fuel'. run_from fuel' ctx func s0 = r) \/
    (?fuel r. run_from fuel ctx func s0 = r /\ exit_result r /\
              expr_exit r1 r)
Proof
  rpt strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `op`, `r1`, `es1`, `s0`] mp_tac) >>
  impl_tac >- fs[] >>
  simp[frag_exec_def] >>
  disch_then (qspec_then `func` mp_tac) >> impl_tac >- fs[] >> strip_tac
  >- (
    disj1_tac >> gvs[expr_post_def] >>
    rename1 `stmt_state_rel ctx func cenv cx es1 sv` >> qexists_tac `sv` >>
    simp[] >> rpt strip_tac >>
    drule emit_inst_extends >> strip_tac >>
    qabbrev_tac `jnz = mk_inst s3.cs_next_id JNZ [op; Label lt; Label lf] []` >>
    `get_instruction <| bb_label := s4.cs_current_bb;
                        bb_instructions := s4.cs_current_insts |>
       sv.vs_inst_idx = SOME jnz` by
      gvs[get_instruction_def, EL_LENGTH_APPEND] >>
    `eval_operand op sv = SOME (if b then 1w else 0w)` by
      gvs[expr_val_rel_def, evaluate_type_def, is_word_type_def,
          typed_val_to_w256_def, val_to_w256_def] >>
    `step_inst_base jnz sv = OK (jump_to (if b then lt else lf) sv)` by
      (qunabbrev_tac `jnz` >> simp[venomInstTheory.mk_inst_def] >>
       drule step_jnz_behavior >> disch_then (fn th => simp[th]) >>
       Cases_on `b` >> simp[]) >>
    `is_terminator jnz.inst_opcode /\ jnz.inst_opcode <> INVOKE` by
      simp[Abbr `jnz`, venomInstTheory.mk_inst_def, is_terminator_def] >>
    `run_from (SUC fuel) ctx func sv =
     run_from fuel ctx func (jump_to (if b then lt else lf) sv)` by
      (qspecl_then [`fuel`, `ctx`, `func`, `sv`,
         `<| bb_label := s4.cs_current_bb;
             bb_instructions := s4.cs_current_insts |>`,
         `jnz`, `if b then lt else lf`,
         `run_from fuel ctx func (jump_to (if b then lt else lf) sv)`]
         mp_tac run_from_jump_result >>
       impl_tac >- gvs[] >> simp[]) >>
    qpat_x_assum `!fuel. (!e. run_from fuel ctx func sv <> Error e) ==> _`
      (qspec_then `SUC fuel` mp_tac) >>
    impl_tac >- metis_tac[] >> metis_tac[]) >>
  disj2_tac >> qexists_tac `fuel` >> fs[]
QED

(* ===== if/else ===== *)

(* An if/else in the source, for every outcome: the condition's error,
   a condition that is not a bool (a type error), or the branch the
   condition selects run in a fresh scope, which is popped after it
   whatever its outcome; its declarations are new to the scopes below. *)

(* compile_if_parts (loweringSlice), with where the code ends when both
   branches end their blocks: no exit block follows. *)

(* The branch an if/else takes, from the start of its block, run in the
   branch's fresh scope: on normal completion it jumps to the exit block
   (when its code does not end its block, a JMP there follows it), and
   leaving the branch pops its scope, which goes back to cenv. *)
Theorem if_branch_frag[local]:
  !ctx func cx lctx RetQ cenv ty ss esA res es2 sc rest sa sb sj sx lbl' x
   exit_lbl st' s0.
    stmt_frag ctx func cx lctx RetQ cenv (stmts_env cenv lctx ty ss)
      esA res es2 /\
    compile_stmts cenv lctx ty ss sa = ((), sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
    sa.cs_current_insts = [] /\ stmt_res_ok lctx res /\
    stmt_state_rel ctx func cenv cx esA s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = 0 /\
    es2.scopes = sc :: rest /\
    (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) /\
    (~block_is_terminated sb ==>
     emit_inst JMP [Label exit_lbl] [] sb = ((), sj) /\
     new_block lbl' sj = (x, sx) /\ fn_has_code sb sx func /\
     st'.cs_current_bb = exit_lbl /\ st'.cs_current_insts = []) ==>
    (?s. stmt_lands lctx st' res s /\ ~s.vs_halted /\
         (res = INL () ==> ~block_is_terminated sb) /\
         stmt_state_rel ctx func cenv cx (es2 with scopes := rest) s /\
         (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                lookup_var x s = SOME w) /\
         (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                  FLOOKUP s.vs_allocas aid = SOME b) /\
         !fuel r. run_from fuel ctx func s = r /\ (!e. r <> Error e) ==>
                  ?fuel'. run_from fuel' ctx func s0 = r) \/
    (?fuel r. run_from fuel ctx func s0 = r /\ exit_result r /\
              stmt_exit RetQ (es2 with scopes := rest) res r)
Proof
  rpt strip_tac >>
  qpat_x_assum `stmt_frag _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[stmt_frag_def] >>
  disch_then (qspecl_then [`sa`, `sb`, `s0`,
                           `FST (stmts_env cenv lctx ty ss sa)`] mp_tac) >>
  impl_tac
  >- (fs[compile_stmts_env, block_is_terminated_def] >>
      Cases_on `stmts_env cenv lctx ty ss sa` >> gvs[]) >>
  strip_tac
  >- (
    rename1 `stmt_state_rel ctx func cenv2 cx es2 s1` >>
    `stmt_state_rel ctx func cenv cx (es2 with scopes := rest) s1` by
      (qspecl_then [`func`, `cenv`, `cenv2`, `cx`, `es2`, `s1`, `sc`, `rest`, `ctx`]
         mp_tac stmt_state_rel_pop_top_ext >> simp[]) >>
    qpat_x_assum `stmt_lands _ _ _ _`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [stmt_lands_def])
    >- (
      (* the branch completes: the JMP to the exit block *)
      fs[] >>
      drule emit_inst_extends >> strip_tac >>
      `cs_extends sb sj /\ cs_extends sj sx` by
        metis_tac[cs_appends_emit_helpers, cs_appends_def,
                  cs_extends_new_block] >>
      `fn_has_code sb sj func` by metis_tac[fn_has_code_split] >>
      qspecl_then [`ctx`, `func`, `sb`, `sj`, `s1`,
                   `mk_inst sb.cs_next_id JMP [Label exit_lbl] []`, `exit_lbl`]
        mp_tac run_from_jump_end >>
      impl_tac
      >- simp[venomInstTheory.mk_inst_def, step_jmp_behavior,
              is_terminator_def] >>
      strip_tac >>
      disj1_tac >> qexists_tac `jump_to exit_lbl s1` >>
      simp[stmt_lands_def, stmt_state_rel_jump_to] >>
      rpt conj_tac >> TRY (simp[jump_to_def] >> NO_TAC) >>
      TRY (fs[jump_to_def, lookup_var_def] >> NO_TAC) >>
      TRY (fs[] >> NO_TAC) >>
      rpt strip_tac >>
      qpat_x_assum
        `!fuel r. run_from fuel ctx func (jump_to _ _) = r /\ _ ==> _`
        (qspecl_then [`fuel`, `run_from fuel ctx func (jump_to exit_lbl s1)`]
           mp_tac) >>
      simp[] >> strip_tac >>
      qpat_x_assum `!fuel. (!e. run_from fuel ctx func s1 <> Error e) ==> _`
        (qspec_then `fuel'` mp_tac) >>
      impl_tac >- metis_tac[] >> metis_tac[]) >>
    (* a break or continue: at the loop's block *)
    disj1_tac >> qexists_tac `s1` >> fs[stmt_lands_def]) >>
  disj2_tac >> qexists_tac `fuel` >> fs[stmt_exit_def]
QED

(* if/else, for every outcome: the condition's error exits, and the
   branch the condition selects runs in a fresh scope, from the block the
   JNZ enters, with its own judgment at cenv. *)

(* ===== Raise and Assert ===== *)

(* An emitted instruction that aborts where the run reaches it exits as
   the source outcome allows. *)



(* raise and raise UNREACHABLE: a REVERT with no data, and INVALID. *)

(* assert and assert UNREACHABLE: the condition, a JNZ to the ok block,
   which is where the code ends, and a fail block that aborts with REVERT
   (no data) or INVALID. *)

(* Integrity gate for forced condition consumers and their semantic boundary. *)
val () = List.app (fn th =>
  let val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "IF_FORCE_AUDIT OK\n"
     else raise Fail "forced condition inherited admission"
  end) [eval_expr_switch_forced, eval_assert_forced_parts,
        eval_assert_forced_ok, cond_jump_frag, eval_stmt_if_all,
        compile_if_stmt_frag, compile_raise_frag, compile_assert_frag];
