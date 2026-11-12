(*
 * Fuel bound for the decimal-digit loop of uint2str.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_uint2str
 *)

Theory fragFuelLoopUint2str
Ancestors
  fragFuel fragFuelContextBase compileEnv emitHelper context venomInst
  builtinStrings exprSimUint2Str
Libs
  fragFuelLib

(* Structural boundary for the post-allocation tail.  Its layout and
   templates are shared with the existing uint2str simulation proof. *)
Theorem uint2str_tail_structure[local]:
  cs_extends a (u2s_end a op buf n) /\
  a.cs_next_var <= (u2s_end a op buf n).cs_next_var /\
  (cs_no_phi a ==> cs_no_phi (u2s_end a op buf n))
Proof
  conj_tac
  >- (simp[cs_extends_def, u2s_end_def] >>
      simp[u2s_blocks_def]) >>
  simp[u2s_end_def, cs_no_phi_def, u2s_blocks_def,
       u2s_setup_def, u2s_check_def, u2s_cond_def, u2s_body_def,
       u2s_zero_def, u2s_final_def, u2s_inst_def, mk_inst_def,
       listTheory.EVERY_APPEND]
QED

Theorem uint2str_structure[local]:
  compile_uint2str op n sz st = (x,st') ==>
  cs_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
  (cs_no_phi st ==> cs_no_phi st')
Proof
  strip_tac >> drule compile_uint2str_layout >> strip_tac >>
  gvs[u2s_layout_def] >>
  mp_tac (Q.SPECL [`n + sz`, `{}:string set`, `{}:string set`]
    fuel_ok_compile_alloc_buffer) >>
  rewrite_tac[fuel_ok_def] >> disch_then drule >> strip_tac >>
  mp_tac (Q.INST [`buf` |-> `ba.buf_operand`] uint2str_tail_structure) >>
  strip_tac >> conj_tac
  >- metis_tac[cs_extends_trans] >>
  simp[u2s_end_def]
QED

(* Every destination in the shared templates is fresh at the allocation
   endpoint, hence outside all protected variables at the original entry. *)
Theorem uint2str_var_not_below[local]:
  N <= a.cs_next_var ==> ~var_below N (u2s_var a k)
Proof
  strip_tac >> simp[u2s_var_def, fresh_var_def] >>
  irule var_below_fresh >> simp[]
QED

(* A failed call-free prefix fixes the result before any block transition. *)
Theorem uint2str_prefix_failure[local]:
  !is s ctx fn bb.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX is (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is /\
    (!t. run_inst_seq is s <> OK t) ==>
    !f. run_from f ctx fn s = run_from 0 ctx fn s
Proof
  Induct >> simp[exprLoweringPropsTheory.run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >> fs[] >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = h :: rest /\
          isPREFIX is rest` by
    (Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> gvs[]) >>
  drule fragExecTheory.DROP_EQ_CONS >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    simp[get_instruction_def] >>
  `!f. run_from f ctx fn s =
    case step_inst_base h s of
      OK s1 => run_from f ctx fn (s1 with vs_inst_idx := SUC s.vs_inst_idx)
    | IntRet v s1 => IntRet v s1
    | Halt s1 => Halt s1
    | Abort a s1 => Abort a s1
    | Error e => Error e` by
    (gen_tac >> drule_all run_from_nonterm >>
     simp[venomExecSemanticsTheory.step_inst_non_invoke]) >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK s1` >>
  `s1.vs_current_bb = s.vs_current_bb /\ s1.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow, venomExecSemanticsTheory.step_inst_non_invoke] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) is` by fs[listTheory.EVERY_MEM] >>
  first_x_assum irule >> simp[] >>
  simp[fragExecTheory.run_inst_seq_inst_idx] >>
  Cases_on `run_inst_seq is s1` >> gvs[instIdxIndepTheory.exec_result_map_def]
QED

Theorem uint2str_prefix_outcome[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX is (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is ==>
  ((?t. run_inst_seq is s = OK t /\
        t.vs_current_bb = s.vs_current_bb /\
        t.vs_inst_idx = s.vs_inst_idx /\
        (!x. EVERY (\i. ~MEM x i.inst_outputs) is ==>
             lookup_var x t = lookup_var x s) /\
        (!f. run_from f ctx fn s =
             run_from f ctx fn (t with vs_inst_idx := s.vs_inst_idx + LENGTH is))) \/
   (!f. run_from f ctx fn s = run_from 0 ctx fn s))
Proof
  strip_tac >> Cases_on `?t. run_inst_seq is s = OK t`
  >- (pop_assum strip_assume_tac >> disj1_tac >> qexists_tac `t` >> simp[] >>
      rpt conj_tac
      >- (drule_all fragExecTheory.exec_block_run_inst_seq >> metis_tac[]) 
      >- (irule exprLoweringPropsTheory.run_inst_seq_preserves_field >>
          qexists_tac `is` >> simp[] >> rpt strip_tac >>
          fs[listTheory.EVERY_MEM] >>
          metis_tac[venomInstPropsTheory.step_preserves_control_flow,
                    venomExecSemanticsTheory.step_inst_non_invoke])
      >- (rpt strip_tac >>
          irule exprLoweringPropsTheory.run_inst_seq_preserves_field >>
          qexists_tac `is` >> simp[] >> rpt strip_tac >>
          fs[listTheory.EVERY_MEM] >>
          metis_tac[venomInstPropsTheory.step_preserves_non_output_vars,
                    venomExecSemanticsTheory.step_inst_non_invoke]) >>
      gen_tac >> drule_all u2s_run_from_prefix >> simp[arithmeticTheory.ADD_COMM]) >>
  disj2_tac >> irule uint2str_prefix_failure >> metis_tac[]
QED

Theorem uint2str_body_quotient[local]:
  eval_operand (Var (u2s_var a 0)) s = SOME xw /\
  run_inst_seq (TAKE 9 (u2s_body a buf n)) s = OK t ==>
  eval_operand (Var (u2s_var a 0)) t = SOME (safe_div xw 10w)
Proof
  strip_tac >>
  `TAKE 9 (u2s_body a buf n) = TAKE 5 (u2s_body a buf n) ++
     (TAKE 2 (DROP 5 (u2s_body a buf n)) ++
      TAKE 2 (DROP 7 (u2s_body a buf n)))` by simp[u2s_body_def] >>
  `?s1. run_inst_seq (TAKE 5 (u2s_body a buf n)) s = OK s1` by
    (Cases_on `run_inst_seq (TAKE 5 (u2s_body a buf n)) s` >>
     gvs[] >>
     gvs[exprLoweringPropsTheory.run_inst_seq_append_err]) >>
  `eval_operand (Var (u2s_var a 0)) s1 = SOME xw` by
    (`lookup_var (u2s_var a 0) s1 = lookup_var (u2s_var a 0) s` by
       (irule exprLoweringPropsTheory.run_inst_seq_preserves_field >>
        qexists_tac `TAKE 5 (u2s_body a buf n)` >> simp[] >>
        rpt strip_tac >>
        `~MEM (u2s_var a 0) i.inst_outputs /\
         i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
          (gvs[u2s_body_def, u2s_inst_def, mk_inst_def, is_terminator_def] >> simp[]) >>
        metis_tac[venomInstPropsTheory.step_preserves_non_output_vars,
                  venomExecSemanticsTheory.step_inst_non_invoke]) >>
     gvs[venomStateTheory.eval_operand_def]) >>
  drule u2s_body_div_run >> strip_tac >>
  `run_inst_seq (TAKE 2 (DROP 7 (u2s_body a buf n)))
     (update_var (u2s_var a 0) (safe_div xw 10w)
       (update_var (u2s_var a 9) (safe_div xw 10w) s1)) = OK t` by
    (qpat_x_assum `run_inst_seq (TAKE 9 _) _ = _` mp_tac >>
     asm_rewrite_tac[] >>
     drule_all exprLoweringPropsTheory.run_inst_seq_append >>
     disch_then (qspec_then `TAKE 2 (DROP 5 (u2s_body a buf n)) ++ TAKE 2 (DROP 7 (u2s_body a buf n))` SUBST1_TAC) >>
     first_x_assum (qspecl_then [`n`, `buf`] assume_tac) >>
     drule_all exprLoweringPropsTheory.run_inst_seq_append >>
     simp[]) >>
  `lookup_var (u2s_var a 0) t =
     lookup_var (u2s_var a 0)
       (update_var (u2s_var a 0) (safe_div xw 10w)
         (update_var (u2s_var a 9) (safe_div xw 10w) s1))` by
    (irule exprLoweringPropsTheory.run_inst_seq_preserves_field >>
     qexists_tac `TAKE 2 (DROP 7 (u2s_body a buf n))` >> simp[] >>
     rpt strip_tac >>
     `~MEM (u2s_var a 0) i.inst_outputs /\
      i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
       (gvs[u2s_body_def, u2s_inst_def, mk_inst_def, is_terminator_def] >> simp[]) >>
     metis_tac[venomInstPropsTheory.step_preserves_non_output_vars,
               venomExecSemanticsTheory.step_inst_non_invoke]) >>
  gvs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
      venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem uint2str_block_outcome[local]:
  no_phi_fn fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions = is ++ [inst] /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  (!x. var_below N x /\ x NOTIN Wv ==>
       EVERY (\i. ~MEM x i.inst_outputs) is) /\
  (!t. run_inst_seq is s = OK t ==> ?lbl.
     step_inst_base inst (t with vs_inst_idx := s.vs_inst_idx + LENGTH is) =
       OK (jump_to lbl (t with vs_inst_idx := s.vs_inst_idx + LENGTH is)) /\
     P (jump_to lbl (t with vs_inst_idx := s.vs_inst_idx + LENGTH is))) ==>
  fuel_outcome G ctx fn s 1 (\u. P u /\ vars_kept N Wv s u)
Proof
  strip_tac >>
  `isPREFIX is (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all uint2str_prefix_outcome >> disch_then (qspec_then `ctx` strip_assume_tac)
  >- (first_x_assum drule >> strip_tac >>
      `get_instruction bb (s.vs_inst_idx + LENGTH is) = SOME inst` by
        (`DROP (LENGTH is) (DROP s.vs_inst_idx bb.bb_instructions) = [inst]` by simp[exprLoweringPropsTheory.DROP_PREFIX] >>
         fs[rich_listTheory.DROP_DROP_T] >>
         drule fragExecTheory.DROP_EQ_CONS >>
         simp[get_instruction_def, arithmeticTheory.ADD_COMM]) >>
      `vars_kept N Wv s (jump_to lbl (t with vs_inst_idx := s.vs_inst_idx + LENGTH is))` by
        (simp[vars_kept_def, venomStateTheory.lookup_var_def] >>
         metis_tac[venomStateTheory.lookup_var_def]) >>
      `fuel_outcome G ctx fn
         (t with vs_inst_idx := s.vs_inst_idx + LENGTH is) 1
         (\u. P u /\ vars_kept N Wv s u)` by
        (irule fuel_outcome_jump >> simp[] >>
         qexistsl [`inst`, `lbl`] >> gvs[arithmeticTheory.ADD_COMM]) >>
      gvs[fuel_outcome_def] >> metis_tac[]) >>
  simp[fuel_outcome_def] >> disj2_tac >> metis_tac[]
QED

Theorem uint2str_body_outcome[local]:
  no_phi_fn fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = u2s_body a buf n /\ s.vs_inst_idx = 0 /\
  eval_operand (Var (u2s_var a 0)) s = SOME xw /\
  (!x. var_below N x /\ x NOTIN Wv ==>
       EVERY (\i. ~MEM x i.inst_outputs) (TAKE 9 (u2s_body a buf n))) ==>
  fuel_outcome G ctx fn s 1
    (\t. (t.vs_current_bb = u2s_label a 1 /\ t.vs_inst_idx = 0 /\
         eval_operand (Var (u2s_var a 0)) t = SOME (safe_div xw 10w)) /\
         vars_kept N Wv s t)
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST [`is` |-> `TAKE 9 (u2s_body a buf n)`,
                          `inst` |-> `LAST (u2s_body a buf n)`]
                         uint2str_block_outcome) >>
  simp[u2s_body_def, u2s_inst_def, mk_inst_def, is_terminator_def] >>
  rpt strip_tac >>
  drule_all (SRULE [u2s_body_def, u2s_inst_def, mk_inst_def]
                  uint2str_body_quotient) >>
  strip_tac >> qexists_tac `u2s_label a 1` >>
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomStateTheory.jump_to_def]
QED

Theorem uint2str_cond_outcome[local]:
  no_phi_fn fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = u2s_cond a /\ s.vs_inst_idx = 0 /\
  lookup_var (u2s_var a 0) s = SOME (n2w x) /\ x < dimword (:256) /\
  (!v. var_below N v /\ v NOTIN Wv ==> v <> u2s_var a 4) ==>
  fuel_outcome G ctx fn s 1
    (\t. (t.vs_current_bb = u2s_label a (if x = 0 then 4 else 2) /\
          t.vs_inst_idx = 0 /\ lookup_var (u2s_var a 0) t = SOME (n2w x)) /\
         vars_kept N Wv s t)
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST [`is` |-> `TAKE 1 (u2s_cond a)`,
                          `inst` |-> `LAST (u2s_cond a)`]
                         uint2str_block_outcome) >>
  simp[u2s_cond_def, u2s_inst_def, mk_inst_def, is_terminator_def] >>
  rpt strip_tac >>
  drule_all (SRULE [] (Q.INST [`t` |-> `update_var (u2s_var a 4) (bool_to_word (x = 0)) s`]
                   u2s_cond_run)) >>
  simp[u2s_cond_def, u2s_inst_def, mk_inst_def] >> strip_tac >>
  gvs[] >> qexists_tac `u2s_label a (if x = 0 then 4 else 2)` >>
  Cases_on `x = 0` >>
  gvs[venomStateTheory.lookup_var_def] >>
  simp[Q.INST [`cond` |-> `1w`]
              (SPEC_ALL venomExecPropsTheory.step_jnz_behavior),
       Q.INST [`cond` |-> `0w`]
              (SPEC_ALL venomExecPropsTheory.step_jnz_behavior),
       venomStateTheory.jump_to_def, venomStateTheory.update_var_def,
       venomStateTheory.lookup_var_def, venomStateTheory.eval_operand_def,
       finite_mapTheory.FLOOKUP_UPDATE, u2s_var_injective,
       arithmeticPropsTheory.bool_to_word_T, arithmeticPropsTheory.bool_to_word_F]
QED

Theorem uint2str_round[local]:
  no_phi_fn fn /\
  lookup_block (u2s_label a 1) fn.fn_blocks = SOME cb /\
  cb.bb_instructions = u2s_cond a /\
  lookup_block (u2s_label a 2) fn.fn_blocks = SOME bb /\
  bb.bb_instructions = u2s_body a buf n /\
  (!v. var_below N v /\ v NOTIN Wv ==>
       v <> u2s_var a 4 /\
       EVERY (\i. ~MEM v i.inst_outputs) (TAKE 9 (u2s_body a buf n))) /\
  H = (\s. s.vs_current_bb = u2s_label a 1 /\ s.vs_inst_idx = 0 /\
           (?w. lookup_var (u2s_var a 0) s = SOME w) /\ vars_kept N Wv s0 s) /\
  Q = (\s. s.vs_current_bb = u2s_label a 4 /\ s.vs_inst_idx = 0 /\
           vars_kept N Wv s0 s) /\
  mu = (\s. w2n (THE (lookup_var (u2s_var a 0) s))) ==>
  !s. H s ==> ?j. j <= 2 /\
    fuel_outcome G ctx fn s j (\t. Q t \/ (H t /\ mu t < mu s))
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `?w. lookup_var (u2s_var a 0) s = SOME w` by gvs[] >>
  `w2n w < dimword (:256)` by simp[wordsTheory.w2n_lt] >>
  `lookup_var (u2s_var a 0) s = SOME (n2w (w2n w))` by simp[] >>
  `fuel_outcome G ctx fn s 1
     (\t. (t.vs_current_bb = u2s_label a (if w2n w = 0 then 4 else 2) /\
           t.vs_inst_idx = 0 /\ lookup_var (u2s_var a 0) t = SOME (n2w (w2n w))) /\
          vars_kept N Wv s t)` by
    (irule uint2str_cond_outcome >> gvs[] >> metis_tac[]) >>
  `2 = 1 + 1` by simp[] >> pop_assum SUBST1_TAC >>
  irule fuel_outcome_compose >> goal_assum (drule_at Any) >>
  rpt strip_tac >>
  Cases_on `w2n w = 0`
  >- (qexists_tac `0` >> simp[] >> irule fuel_outcome_refl >>
      gvs[] >> metis_tac[vars_kept_trans]) >>
  `eval_operand (Var (u2s_var a 0)) t = SOME w` by
    gvs[venomStateTheory.eval_operand_def] >>
  `fuel_outcome G ctx fn t 1
     (\u. (u.vs_current_bb = u2s_label a 1 /\ u.vs_inst_idx = 0 /\
           eval_operand (Var (u2s_var a 0)) u = SOME (safe_div w 10w)) /\
          vars_kept N Wv t u)` by
    (irule uint2str_body_outcome >> gvs[] >> metis_tac[]) >>
  qexists_tac `1` >> simp[] >>
  irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
  rpt strip_tac >>
  `w2n (safe_div w 10w) < w2n w` by
    (`w2n w DIV 10 < dimword (:256)` by
       (irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
        qexists_tac `w2n w` >> simp[arithmeticTheory.DIV_LESS_EQ]) >>
     simp[venomExecSemanticsTheory.safe_div_def, wordsTheory.word_div_def,
          wordsTheory.w2n_n2w, wordsTheory.dimword_def,
          venomLayoutTheory.dimindex_256] >>
     irule arithmeticTheory.DIV_LESS >> simp[]) >>
  gvs[venomStateTheory.eval_operand_def] >>
  metis_tac[vars_kept_trans]
QED

Theorem uint2str_loop_outcome[local]:
  no_phi_fn fn /\
  lookup_block (u2s_label a 1) fn.fn_blocks = SOME cb /\
  cb.bb_instructions = u2s_cond a /\
  lookup_block (u2s_label a 2) fn.fn_blocks = SOME bb /\
  bb.bb_instructions = u2s_body a buf n /\
  (!v. var_below N v /\ v NOTIN Wv ==>
       v <> u2s_var a 4 /\
       EVERY (\i. ~MEM v i.inst_outputs) (TAKE 9 (u2s_body a buf n))) /\
  H = (\s. s.vs_current_bb = u2s_label a 1 /\ s.vs_inst_idx = 0 /\
           (?w. lookup_var (u2s_var a 0) s = SOME w) /\ vars_kept N Wv s0 s) /\
  Q = (\s. s.vs_current_bb = u2s_label a 4 /\ s.vs_inst_idx = 0 /\
           vars_kept N Wv s0 s) ==>
  !s. H s ==> ?j. j <= (2 ** 256) * 2 /\ fuel_outcome G ctx fn s j Q
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST [`M` |-> `2 ** 256`, `Kb` |-> `2`,
      `mu` |-> `\s. w2n (THE (lookup_var (u2s_var a 0) s))`]
      (SPEC_ALL fuel_outcome_iterate)) >>
  conj_tac
  >- (rpt strip_tac >>
      qspec_then `THE (lookup_var (u2s_var a 0) s)` mp_tac wordsTheory.w2n_lt >>
      simp[wordsTheory.dimword_def, venomLayoutTheory.dimindex_256]) >>
  mp_tac (Q.INST [`mu` |-> `\s. w2n (THE (lookup_var (u2s_var a 0) s))`]
          (SPEC_ALL uint2str_round)) >> simp[]
QED

Theorem uint2str_setup_word[local]:
  run_inst_seq (TAKE 3 (u2s_setup a op buf)) s = OK t ==>
  ?w. lookup_var (u2s_var a 0) t = SOME w
Proof
  simp[u2s_setup_def, u2s_inst_def, mk_inst_def] >>
  pure_rewrite_tac[exprLoweringPropsTheory.run_inst_seq_def] >>
  simp[venomExecSemanticsTheory.step_inst_base_def] >>
  Cases_on `eval_operand op s` >> simp[] >>
  rename1 `eval_operand op s = SOME w` >>
  simp[venomStateTheory.eval_operand_def] >>
  Cases_on `eval_operand buf (update_var (u2s_var a 1) 0w
      (update_var (u2s_var a 0) w s))` >> simp[] >>
  strip_tac >> gvs[] >>
  simp[venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, u2s_var_injective]
QED

Theorem uint2str_setup_outcome[local]:
  no_phi_fn fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions = u2s_setup a op buf /\
  (!v. var_below N v /\ v NOTIN Wv ==>
       EVERY (\i. ~MEM v i.inst_outputs) (TAKE 3 (u2s_setup a op buf))) ==>
  fuel_outcome G ctx fn s 1
    (\t. (t.vs_current_bb = u2s_label a 0 /\ t.vs_inst_idx = 0 /\
          (?w. lookup_var (u2s_var a 0) t = SOME w)) /\
         vars_kept N Wv s t)
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST [`is` |-> `TAKE 3 (u2s_setup a op buf)`,
                          `inst` |-> `LAST (u2s_setup a op buf)`]
                         uint2str_block_outcome) >>
  simp[u2s_setup_def, u2s_inst_def, mk_inst_def, is_terminator_def] >>
  rpt strip_tac >>
  drule (SRULE [u2s_setup_def, u2s_inst_def, mk_inst_def]
               uint2str_setup_word) >> strip_tac >>
  qexists_tac `u2s_label a 0` >>
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomStateTheory.jump_to_def, venomStateTheory.lookup_var_def] >>
  metis_tac[venomStateTheory.lookup_var_def]
QED

Theorem uint2str_check_outcome[local]:
  no_phi_fn fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = u2s_check a /\ s.vs_inst_idx = 0 /\
  (?w. lookup_var (u2s_var a 0) s = SOME w) /\
  (!v. var_below N v /\ v NOTIN Wv ==> v <> u2s_var a 3) ==>
  fuel_outcome G ctx fn s 1
    (\t. ((t.vs_current_bb = u2s_label a 3 \/
           t.vs_current_bb = u2s_label a 1) /\ t.vs_inst_idx = 0 /\
          (?w. lookup_var (u2s_var a 0) t = SOME w)) /\
         vars_kept N Wv s t)
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST [`is` |-> `TAKE 1 (u2s_check a)`,
                          `inst` |-> `LAST (u2s_check a)`]
                         uint2str_block_outcome) >>
  simp[u2s_check_def, u2s_inst_def, mk_inst_def, is_terminator_def] >>
  rpt strip_tac >>
  `w2n w < dimword (:256)` by simp[wordsTheory.w2n_lt] >>
  `lookup_var (u2s_var a 0) s = SOME (n2w (w2n w))` by simp[] >>
  drule_all (SRULE [] (Q.INST [`x` |-> `w2n w`,
                  `t` |-> `update_var (u2s_var a 3)
                  (bool_to_word (w2n w = 0)) s`]
                  u2s_check_run)) >>
  simp[u2s_check_def, u2s_inst_def, mk_inst_def] >> strip_tac >>
  gvs[] >>
  qexists_tac `u2s_label a (if w2n w = 0 then 3 else 1)` >>
  Cases_on `w2n w = 0` >>
  gvs[venomStateTheory.lookup_var_def] >>
  simp[Q.INST [`cond` |-> `1w`]
              (SPEC_ALL venomExecPropsTheory.step_jnz_behavior),
       Q.INST [`cond` |-> `0w`]
              (SPEC_ALL venomExecPropsTheory.step_jnz_behavior),
       venomStateTheory.jump_to_def, venomStateTheory.update_var_def,
       venomStateTheory.lookup_var_def, venomStateTheory.eval_operand_def,
       finite_mapTheory.FLOOKUP_UPDATE, u2s_var_injective,
       arithmeticPropsTheory.bool_to_word_T, arithmeticPropsTheory.bool_to_word_F]
QED

Theorem uint2str_zero_outcome[local]:
  no_phi_fn fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = u2s_zero a buf n /\ s.vs_inst_idx = 0 /\
  (!v. var_below N v /\ v NOTIN Wv ==>
       EVERY (\i. ~MEM v i.inst_outputs) (TAKE 6 (u2s_zero a buf n))) ==>
  fuel_outcome G ctx fn s 1
    (\t. (t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0) /\
         vars_kept N Wv s t)
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST [`is` |-> `TAKE 6 (u2s_zero a buf n)`,
                          `inst` |-> `LAST (u2s_zero a buf n)`]
                         uint2str_block_outcome) >>
  simp[u2s_zero_def, u2s_inst_def, mk_inst_def, is_terminator_def] >>
  rpt strip_tac >> qexists_tac `u2s_label a 5` >>
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomStateTheory.jump_to_def]
QED

Theorem uint2str_final_outcome[local]:
  no_phi_fn fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = u2s_final a buf n /\ s.vs_inst_idx = 0 /\
  (!v. var_below N v /\ v NOTIN Wv ==>
       EVERY (\i. ~MEM v i.inst_outputs) (TAKE 4 (u2s_final a buf n))) ==>
  fuel_outcome G ctx fn s 1
    (\t. (t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0) /\
         vars_kept N Wv s t)
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST [`is` |-> `TAKE 4 (u2s_final a buf n)`,
                          `inst` |-> `LAST (u2s_final a buf n)`]
                         uint2str_block_outcome) >>
  simp[u2s_final_def, u2s_inst_def, mk_inst_def, is_terminator_def] >>
  rpt strip_tac >> qexists_tac `u2s_label a 5` >>
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomStateTheory.jump_to_def]
QED

(* From the condition head through the final tail. *)
Theorem uint2str_finish_outcome[local]:
  no_phi_fn fn /\
  (!bb. MEM bb (u2s_blocks a op buf n) ==>
        lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
  N <= a.cs_next_var /\
  s.vs_current_bb = u2s_label a 1 /\ s.vs_inst_idx = 0 /\
  (?w. lookup_var (u2s_var a 0) s = SOME w) ==>
  ?j. j <= (2 ** 256) * 2 + 1 /\
    fuel_outcome G ctx fn s j
      (\t. (t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0) /\
           vars_kept N Wv s t)
Proof
  strip_tac >>
  `lookup_block (u2s_label a 1) fn.fn_blocks =
     SOME <|bb_label := u2s_label a 1; bb_instructions := u2s_cond a|> /\
   lookup_block (u2s_label a 2) fn.fn_blocks =
     SOME <|bb_label := u2s_label a 2; bb_instructions := u2s_body a buf n|> /\
   lookup_block (u2s_label a 4) fn.fn_blocks =
     SOME <|bb_label := u2s_label a 4; bb_instructions := u2s_final a buf n|>` by
    (fs[u2s_blocks_def, boolTheory.DISJ_IMP_THM, boolTheory.FORALL_AND_THM]) >>
  `!v k. var_below N v ==> v <> u2s_var a k` by
    metis_tac[uint2str_var_not_below] >>
  mp_tac (Q.INST [`s0` |-> `s`,
    `cb` |-> `<|bb_label := u2s_label a 1; bb_instructions := u2s_cond a|>`,
    `bb` |-> `<|bb_label := u2s_label a 2; bb_instructions := u2s_body a buf n|>`,
    `H` |-> `\t. t.vs_current_bb = u2s_label a 1 /\ t.vs_inst_idx = 0 /\
                 (?w. lookup_var (u2s_var a 0) t = SOME w) /\ vars_kept N Wv s t`,
    `Q` |-> `\t. t.vs_current_bb = u2s_label a 4 /\ t.vs_inst_idx = 0 /\
                 vars_kept N Wv s t`] (SPEC_ALL uint2str_loop_outcome)) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
      simp[u2s_body_def, u2s_inst_def, mk_inst_def])) >>
  disch_then (qspec_then `s` mp_tac) >> simp[] >> strip_tac >>
  drule fuel_outcome_compose >>
  disch_then (qspecl_then
    [`\t. (t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0) /\
           vars_kept N Wv s t`, `1`] mp_tac) >>
  (impl_tac >- (rpt strip_tac >> fs[] >> qexists_tac `1` >> simp[] >>
    `fuel_outcome G ctx fn t 1
       (\u. (u.vs_current_bb = u2s_label a 5 /\ u.vs_inst_idx = 0) /\
            vars_kept N Wv t u)` by
      (irule (Q.INST [`buf` |-> `buf`, `n` |-> `n`] (SPEC_ALL uint2str_final_outcome)) >>
       simp[] >> rpt strip_tac >>
       simp[u2s_final_def, u2s_inst_def, mk_inst_def] >> metis_tac[]) >>
    irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
    simp[] >> metis_tac[vars_kept_trans])) >>
  strip_tac >> qexists_tac `j'` >> simp[]
QED

Theorem uint2str_checked_outcome[local]:
  no_phi_fn fn /\
  (!bb. MEM bb (u2s_blocks a op buf n) ==>
        lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
  N <= a.cs_next_var /\
  s.vs_current_bb = u2s_label a 0 /\ s.vs_inst_idx = 0 /\
  (?w. lookup_var (u2s_var a 0) s = SOME w) ==>
  ?j. j <= 1 + ((2 ** 256) * 2 + 1) /\
    fuel_outcome G ctx fn s j
      (\t. (t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0) /\
           vars_kept N Wv s t)
Proof
  strip_tac >>
  `lookup_block (u2s_label a 0) fn.fn_blocks =
     SOME <|bb_label := u2s_label a 0; bb_instructions := u2s_check a|> /\
   lookup_block (u2s_label a 3) fn.fn_blocks =
     SOME <|bb_label := u2s_label a 3; bb_instructions := u2s_zero a buf n|>` by
    fs[u2s_blocks_def, boolTheory.DISJ_IMP_THM, boolTheory.FORALL_AND_THM] >>
  `!v k. var_below N v ==> v <> u2s_var a k` by
    metis_tac[uint2str_var_not_below] >>
  `fuel_outcome G ctx fn s 1
    (\t. ((t.vs_current_bb = u2s_label a 3 \/ t.vs_current_bb = u2s_label a 1) /\
          t.vs_inst_idx = 0 /\ (?w. lookup_var (u2s_var a 0) t = SOME w)) /\
         vars_kept N Wv s t)` by
    (irule uint2str_check_outcome >> simp[] >> metis_tac[]) >>
  drule fuel_outcome_compose >>
  disch_then (qspecl_then
    [`\t. (t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0) /\
           vars_kept N Wv s t`, `(2 ** 256) * 2 + 1`] mp_tac) >>
  (impl_tac >- (rpt gen_tac >> simp[] >> strip_tac >>
    `?j. j <= (2 ** 256) * 2 + 1 /\
      fuel_outcome G ctx fn t j
        (\u. (u.vs_current_bb = u2s_label a 5 /\ u.vs_inst_idx = 0) /\
             vars_kept N Wv t u)` by suspend "branch" >>
    qexists_tac `j` >> fs[] >>
    irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
    simp[] >> metis_tac[vars_kept_trans])) >> simp[]
QED

Resume uint2str_checked_outcome[branch]:
  markerLib.RESUME_TAC >> (rpt strip_tac >>
  Cases_on `t.vs_current_bb = u2s_label a 3` >> fs[]
  >- (qexists_tac `1` >> simp[] >>
      irule (Q.INST [`buf` |-> `buf`, `n` |-> `n`] (SPEC_ALL uint2str_zero_outcome)) >>
      simp[] >> rpt strip_tac >>
      simp[u2s_zero_def, u2s_inst_def, mk_inst_def] >> metis_tac[]) >>
  irule (Q.INST [`op` |-> `op`, `buf` |-> `buf`, `n` |-> `n`]
               (SPEC_ALL (SRULE [] uint2str_finish_outcome))) >> simp[] >>
  qexistsl_tac [`buf`, `n`, `op`] >> simp[])
QED

Finalise uint2str_checked_outcome

Theorem uint2str_tail_outcome[local]:
  no_phi_fn fn /\
  (!bb. MEM bb (u2s_blocks a op buf n) ==>
        lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
  N <= a.cs_next_var /\ at_point a s ==>
  ?j. j <= 2 + ((2 ** 256) * 2 + 1) /\
    fuel_outcome G ctx fn s j
      (\t. (t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0) /\
           vars_kept N Wv s t)
Proof
  strip_tac >>
  `lookup_block a.cs_current_bb fn.fn_blocks =
    SOME <|bb_label := a.cs_current_bb;
      bb_instructions := a.cs_current_insts ++ u2s_setup a op buf|>` by
    fs[u2s_blocks_def, boolTheory.DISJ_IMP_THM, boolTheory.FORALL_AND_THM] >>
  `!v k. var_below N v ==> v <> u2s_var a k` by
    metis_tac[uint2str_var_not_below] >>
  `fuel_outcome G ctx fn s 1
    (\t. (t.vs_current_bb = u2s_label a 0 /\ t.vs_inst_idx = 0 /\
          (?w. lookup_var (u2s_var a 0) t = SOME w)) /\ vars_kept N Wv s t)` by
    (irule (Q.INST [`op` |-> `op`, `buf` |-> `buf`, `a` |-> `a`]
      (SPEC_ALL uint2str_setup_outcome)) >>
     fs[at_point_def] >>
     qexistsl_tac [`buf`, `op`] >>
     simp[rich_listTheory.DROP_LENGTH_APPEND] >> rpt strip_tac >>
     simp[u2s_setup_def, u2s_inst_def, mk_inst_def] >> metis_tac[]) >>
  drule fuel_outcome_compose >>
  disch_then (qspecl_then
    [`\t. (t.vs_current_bb = u2s_label a 5 /\ t.vs_inst_idx = 0) /\
           vars_kept N Wv s t`, `1 + ((2 ** 256) * 2 + 1)`] mp_tac) >>
  (impl_tac >- (rpt strip_tac >>
    `?j. j <= 1 + ((2 ** 256) * 2 + 1) /\
      fuel_outcome G ctx fn t j
        (\u. (u.vs_current_bb = u2s_label a 5 /\ u.vs_inst_idx = 0) /\
             vars_kept N Wv t u)` by
      (irule uint2str_checked_outcome >> simp[] >>
       metis_tac[]) >>
    qexists_tac `j` >> fs[] >>
    irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
    simp[] >> metis_tac[vars_kept_trans])) >> simp[]
QED

Theorem fuel_ok_compile_uint2str:
  !val_op n_digits buf_size Wv E.
    fuel_ok Wv {} E (compile_uint2str val_op n_digits buf_size)
Proof
  rpt gen_tac >> rewrite_tac[fuel_ok_def] >> rpt gen_tac >> strip_tac >>
  drule uint2str_structure >> strip_tac >> simp[] >>
  drule compile_uint2str_layout >> strip_tac >>
  mp_tac (Q.SPECL [`buf_size + n_digits`, `Wv`, `{}:string set`]
    fuel_ok_compile_alloc_buffer) >>
  rewrite_tac[fuel_ok_def] >> disch_then drule >> strip_tac >>
  qexists_tac `Kb + (2 + ((2 ** 256) * 2 + 1))` >>
  rewrite_tac[frag_fuel_def] >> rpt gen_tac >> strip_tac >>
  drule_all u2s_alloc_layout_code >> strip_tac >>
  `N <= a.cs_next_var` by decide_tac >>
  qpat_x_assum `frag_fuel _ _ _ _ _ _` mp_tac >>
  rewrite_tac[frag_fuel_def] >>
  disch_then (qspecl_then [`G`, `N`, `ctx`, `fn`, `s`] mp_tac) >>
  simp[] >> strip_tac >>
  drule fuel_outcome_compose >>
  disch_then (qspecl_then
    [`\u. vars_kept N Wv s u /\
       (at_point st' u \/ (u.vs_current_bb IN E /\ u.vs_inst_idx = 0))`,
     `2 + ((2 ** 256) * 2 + 1)`] mp_tac) >>
  (impl_tac >- (rpt strip_tac >> fs[] >>
    `?j. j <= 2 + ((2 ** 256) * 2 + 1) /\
       fuel_outcome G ctx fn t j
        (\u. (u.vs_current_bb = u2s_label a 5 /\ u.vs_inst_idx = 0) /\
             vars_kept N Wv t u)` by
       (irule uint2str_tail_outcome >> simp[] >> metis_tac[]) >>
    qexists_tac `j'` >> fs[] >>
    irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
    fs[u2s_layout_def] >>
    simp[u2s_end_def, at_point_def] >>
    rpt strip_tac >> irule vars_kept_trans >>
    goal_assum (drule_at Any) >> simp[])) >>
  strip_tac >> qexists_tac `j'` >> simp[] >> gvs[]
QED
