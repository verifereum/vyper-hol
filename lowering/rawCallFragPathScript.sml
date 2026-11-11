(* Counted fragments for the raw_call of msg.data simulation: frag_exec's
   judgment with an actual target GAS path in place of run_from.  The path's
   GAS count is left open, since the raw_call tail's only GAS read is a
   target-only one, which the counted judgments mark F. *)
Theory rawCallFragPath
Ancestors
  fragExec fragGasPath fragGasSeq fragGasSeqAbort exprLoweringProps
  compileEnv emitHelperProps venomExecSemantics venomState venomInst instIdxIndep
  list rich_list arithmetic

Definition frag_path_def:
  frag_path ctx (st : compile_state) (st' : compile_state) P Q R <=>
    !fn s.
      fn_has_code st st' fn /\ P s /\ ~s.vs_halted /\
      s.vs_current_bb = st.cs_current_bb /\
      s.vs_inst_idx = LENGTH st.cs_current_insts ==>
      ?n r. gas_path ctx fn s n r /\
            ((?s'. r = OK s' /\ Q s' /\
                   s'.vs_current_bb = st'.cs_current_bb /\
                   s'.vs_inst_idx = LENGTH st'.cs_current_insts) \/
             (exit_result r /\ R r))
End

Theorem frag_path_conseq:
  !ctx st st' P Q R P' Q' R'.
    frag_path ctx st st' P Q R /\
    (!s. P' s ==> P s) /\ (!s. Q s ==> Q' s) /\ (!r. R r ==> R' r) ==>
    frag_path ctx st st' P' Q' R'
Proof
  rw[frag_path_def] >>
  first_x_assum (qspecl_then [`fn`, `s`] mp_tac) >> simp[] >>
  strip_tac >> metis_tac[]
QED

Theorem frag_path_pointwise:
  !ctx st st' P Q R.
    (!s0. P s0 ==> frag_path ctx st st' (\s. s = s0) Q R) ==>
    frag_path ctx st st' P Q R
Proof
  rw[frag_path_def] >> first_x_assum drule >> simp[frag_path_def]
QED

Theorem frag_path_seq:
  !ctx st1 st2 st3 P Q Q2 R.
    frag_path ctx st1 st2 P Q R /\ frag_path ctx st2 st3 Q Q2 R /\
    cs_extends st1 st2 /\ cs_extends st2 st3 ==>
    frag_path ctx st1 st3 P Q2 R
Proof
  rpt gen_tac >> strip_tac >> simp[frag_path_def] >> rpt strip_tac >>
  `fn_has_code st1 st2 fn /\ fn_has_code st2 st3 fn` by
    metis_tac[fn_has_code_split] >>
  qpat_x_assum `frag_path ctx st1 st2 P Q R`
    (mp_tac o SIMP_RULE std_ss [frag_path_def]) >>
  disch_then (qspecl_then [`fn`, `s`] mp_tac) >> simp[] >> strip_tac
  >- (rename1 `Q s2` >> gvs[] >>
      `~s2.vs_halted` by metis_tac[gas_path_normal] >>
      qpat_x_assum `frag_path ctx st2 st3 Q Q2 R`
        (mp_tac o SIMP_RULE std_ss [frag_path_def]) >>
      disch_then (qspecl_then [`fn`, `s2`] mp_tac) >> simp[] >> strip_tac >>
      metis_tac[gas_path_then]) >>
  metis_tac[]
QED

Theorem frag_path_false_pre:
  !ctx st st' Q R. frag_path ctx st st' (\s. F) Q R
Proof
  rw[frag_path_def]
QED

Theorem frag_path_exit_prefix:
  !ctx st1 st2 st3 P Q R.
    frag_path ctx st1 st2 P (\s. F) R /\ cs_extends st1 st2 /\
    cs_extends st2 st3 ==>
    frag_path ctx st1 st3 P Q R
Proof
  rpt strip_tac >> irule frag_path_seq >> qexistsl_tac [`\s. F`, `st2`] >>
  simp[frag_path_false_pre]
QED

Theorem frag_path_then:
  !ctx st1 st2 P Q1 R.
    frag_path ctx st1 st2 P Q1 R ==>
    !st3 Q.
      (!t. Q1 t ==> frag_path ctx st2 st3 (\s. s = t) Q R) /\
      cs_extends st1 st2 /\ cs_extends st2 st3 ==>
      frag_path ctx st1 st3 P Q R
Proof
  rpt strip_tac >> irule frag_path_seq >> qexistsl_tac [`Q1`, `st2`] >>
  simp[] >> irule frag_path_pointwise >> simp[]
QED

Theorem frag_path_run_inst_seq:
  !ctx st st' P Q R.
    st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
    isPREFIX st.cs_current_insts st'.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st st') /\
    (!s. P s ==>
       (?s'. run_inst_seq (emitted_insts st st') s = OK s' /\
             Q (s' with vs_inst_idx := LENGTH st'.cs_current_insts)) \/
       (?a s'. run_inst_seq (emitted_insts st st') s = Abort a s' /\
               !n. R (Abort a (s' with vs_inst_idx := n)))) ==>
    frag_path ctx st st' P Q R
Proof
  rw[frag_path_def] >>
  `?bb. lookup_block st.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX st'.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  `?t. st'.cs_current_insts = st.cs_current_insts ++ t /\
       emitted_insts st st' = t` by
    (qpat_x_assum `isPREFIX st.cs_current_insts st'.cs_current_insts` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND]) >>
  `isPREFIX t (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX st'.cs_current_insts _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     simp[IS_PREFIX_APPEND] >>
     rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     metis_tac[]) >>
  qpat_x_assum `emitted_insts st st' = t` (fn th => fs[th]) >>
  first_x_assum drule >> strip_tac
  >- (qspecl_then [`t`, `s`, `s'`, `ctx`, `fn`, `bb`] mp_tac
        tuple_run_inst_seq_gas_path >>
      (impl_tac >- gvs[]) >> strip_tac >>
      `s'.vs_current_bb = s.vs_current_bb` by
        (qspecl_then [`t`, `s`, `0`, `ctx`, `bb`] mp_tac
           exec_block_run_inst_seq >> simp[]) >>
      goal_assum drule >> disj1_tac >> gvs[]) >>
  qspecl_then [`F`, `t`, `s`, `s'`, `a`, `ctx`, `fn`, `bb`] mp_tac
    run_inst_seq_abort_gas_path >>
  (impl_tac >- gvs[]) >> simp[fragGasModeTheory.gas_marked_path_def] >>
  strip_tac >> goal_assum drule >> simp[exit_result_def]
QED

(* A JMP/JNZ-like step into the block that starts a counted fragment. *)
Theorem frag_path_enter:
  !ctx fn s bb inst sa sb P Q R.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst_base inst s = OK (jump_to sa.cs_current_bb s) /\
    ~s.vs_halted /\
    frag_path ctx sa sb P Q R /\ fn_has_code sa sb fn /\
    sa.cs_current_insts = [] /\ P (jump_to sa.cs_current_bb s) ==>
    ?n r. gas_path ctx fn s n r /\
          ((?s'. r = OK s' /\ Q s' /\
                 s'.vs_current_bb = sb.cs_current_bb /\
                 s'.vs_inst_idx = LENGTH sb.cs_current_insts) \/
           (exit_result r /\ R r))
Proof
  rpt strip_tac >>
  `gas_path_edge ctx fn s (gas_count_step 0 ctx inst s)
     (OK (jump_to sa.cs_current_bb s))` by
    (simp[gas_path_edge_def] >> qexists_tac `0` >>
     simp[step_inst_non_invoke] >> disj2_tac >> disj1_tac >>
     qexists_tac `sa.cs_current_bb` >> simp[]) >>
  qpat_x_assum `frag_path _ _ _ _ _ _` mp_tac >> simp[frag_path_def] >>
  disch_then (qspecl_then [`fn`, `jump_to sa.cs_current_bb s`] mp_tac) >>
  impl_tac >- simp[jump_to_def] >>
  strip_tac >> metis_tac[gas_path_rules]
QED

Theorem frag_path_fresh_label:
  frag_path ctx sa sb P Q R /\ fresh_label prefix sb = (lbl,sc) ==>
  frag_path ctx sa sc P Q R
Proof
  strip_tac >> drule fresh_label_props >> strip_tac >>
  fs[frag_path_def, fn_has_code_def, emitted_blocks_def]
QED

(* ===== Straight-line code that ends in an aborting instruction ===== *)

Theorem run_idx_norm0[local]:
  !pre last s n.
    EVERY (\i. ~is_terminator i.inst_opcode) pre ==>
    exec_result_map (\t. t with vs_inst_idx := 0)
      (run_inst_seq (pre ++ [last]) (s with vs_inst_idx := n)) =
    exec_result_map (\t. t with vs_inst_idx := 0)
      (run_inst_seq (pre ++ [last]) s)
Proof
  Induct >> rpt gen_tac >> simp[run_inst_seq_def]
  >- (Cases_on `is_terminator last.inst_opcode`
      >- (drule terminator_step_inst_base_idx_norm0 >>
          disch_then (qspecl_then [`s`,`n`] mp_tac) >>
          Cases_on `step_inst_base last (s with vs_inst_idx := n)` >>
          Cases_on `step_inst_base last s` >>
          simp[exec_result_map_def, run_inst_seq_def]) >>
      simp[step_inst_inst_idx_indep] >>
      Cases_on `step_inst_base last s` >>
      simp[exec_result_map_def, run_inst_seq_def]) >>
  strip_tac >> simp[step_inst_inst_idx_indep] >>
  Cases_on `step_inst_base h s` >>
  simp[exec_result_map_def, run_inst_seq_def]
QED

Theorem abort_suffix_gas_path:
  !pre last s a t ctx fn bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (pre ++ [last]) (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre /\
    last.inst_opcode <> INVOKE /\
    run_inst_seq (pre ++ [last]) s = Abort a t ==>
    ?n j. gas_path ctx fn s n (Abort a (t with vs_inst_idx := j))
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (qpat_x_assum `isPREFIX _ _` (mp_tac o REWRITE_RULE [APPEND]) >>
      strip_tac >> drule instruction_prefix_cursor >> strip_tac >>
      gvs[run_inst_seq_def, AllCaseEqs()] >>
      qexistsl_tac [`gas_count_step 0 ctx last s`, `t.vs_inst_idx`] >>
      `t with vs_inst_idx := t.vs_inst_idx = t` by
        simp[venom_state_component_equality] >>
      pop_assum SUBST1_TAC >>
      irule (cj 3 gas_path_rules) >> simp[exit_result_def] >>
      simp[gas_path_edge_def] >> qexists_tac `0` >>
      simp[step_inst_non_invoke, exit_result_def]) >>
  qpat_x_assum `isPREFIX _ _` (mp_tac o REWRITE_RULE [APPEND]) >>
  strip_tac >> drule instruction_prefix_cursor >> strip_tac >> fs[] >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[Once run_inst_seq_def] >>
  Cases_on `step_inst_base h s` >> simp[] >> strip_tac
  >- (rename1 `step_inst_base h s = OK u` >>
      `gas_path_edge ctx fn s (if h.inst_opcode = GAS then 1 else 0)
         (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
        (irule tuple_straight_line_edge >> metis_tac[]) >>
      `~(u with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by
        metis_tac[gas_path_edge_normal] >>
      `EVERY (\i. ~is_terminator i.inst_opcode) pre` by fs[EVERY_MEM] >>
      drule run_idx_norm0 >>
      disch_then (qspecl_then [`last`,`u`,`SUC s.vs_inst_idx`] mp_tac) >>
      Cases_on `run_inst_seq (pre ++ [last])
                  (u with vs_inst_idx := SUC s.vs_inst_idx)` >>
      simp[exec_result_map_def] >> strip_tac >> gvs[] >>
      rename1 `run_inst_seq _ (u with vs_inst_idx := _) = Abort _ u2` >>
      `u.vs_current_bb = s.vs_current_bb` by
        (qspecl_then [`0`, `ctx`, `h`, `s`, `u`] mp_tac
           venomInstProofsTheory.step_preserves_control_flow >>
         simp[step_inst_non_invoke]) >>
      first_x_assum (qspecl_then [`last`,
        `u with vs_inst_idx := SUC s.vs_inst_idx`, `a`, `u2`, `ctx`, `fn`, `bb`]
        mp_tac) >>
      simp[] >> strip_tac >>
      `u2 with vs_inst_idx := j = t with vs_inst_idx := j` by
        (qpat_x_assum `u2 with vs_inst_idx := 0 = _` mp_tac >>
         simp[venom_state_component_equality]) >>
      qexistsl_tac [`(if h.inst_opcode = GAS then 1 else 0) + n`, `j`] >>
      irule (cj 2 gas_path_rules) >> gvs[] >> metis_tac[]) >>
  rename1 `step_inst_base h s = Abort a' t'` >> gvs[] >>
  `~is_terminator h.inst_opcode /\ h.inst_opcode <> INVOKE` by fs[] >>
  qexistsl_tac [`gas_count_step 0 ctx h s`, `t.vs_inst_idx`] >>
  `t with vs_inst_idx := t.vs_inst_idx = t` by
    simp[venom_state_component_equality] >>
  pop_assum SUBST1_TAC >>
  irule (cj 3 gas_path_rules) >> simp[exit_result_def] >>
  simp[gas_path_edge_def] >> qexists_tac `0` >>
  simp[step_inst_non_invoke, exit_result_def]
QED

Theorem frag_path_abort_suffix:
  !ctx sa sb pre last P R.
    sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
    isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    emitted_insts sa sb = pre ++ [last] /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre /\
    last.inst_opcode <> INVOKE /\
    (!s. P s ==> ?a t. run_inst_seq (pre ++ [last]) s = Abort a t /\
                         !n. R (Abort a (t with vs_inst_idx := n))) ==>
    frag_path ctx sa sb P (\s. F) R
Proof
  rw[frag_path_def] >>
  `?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
        isPREFIX sb.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  `sb.cs_current_insts = sa.cs_current_insts ++ (pre ++ [last])` by
    (gvs[rich_listTheory.IS_PREFIX_APPEND, emitted_insts_def] >>
     gvs[rich_listTheory.DROP_LENGTH_APPEND]) >>
  `isPREFIX (pre ++ [last]) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX sb.cs_current_insts _` mp_tac >>
     simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
     simp[rich_listTheory.IS_PREFIX_APPEND] >>
     rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     metis_tac[]) >>
  first_x_assum drule >> strip_tac >>
  qspecl_then [`pre`, `last`, `s`, `a`, `t`, `ctx`, `fn`, `bb`] mp_tac
    abort_suffix_gas_path >>
  (impl_tac >- gvs[]) >> strip_tac >>
  goal_assum drule >> simp[exit_result_def]
QED
