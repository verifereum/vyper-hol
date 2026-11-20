(* Bounds for the optimizer's two double-ISZERO rules with own-code reads. *)
Theory asmOptWithinIszero
Ancestors
  asmSpliceWithinOwn asmSpliceWithin asmSpliceOwn asmRefinesWithin
  asmOptOwnMergeIszero asmOptMergeIszero asmFinalizerPrefixIszero
  asmSplice asmSymOwnCode asmSymPc asmSymPcOwn asmSymSem asmSymSemWithin
  asmOptimizer asmWf asmSem symbolResolve arithmetic list

Theorem bounded_source_step[local]:
  ss.sym_base.as_pc < LENGTH p /\ EL ss.sym_base.as_pc p = (x:asm_inst) /\
  ~Q x /\ stepf x ss = result /\ sym_run_within_for stepf P Q p (SUC n) ss ==>
  P x ss.sym_stack /\
  (case result of SymOK next => sym_run_within_for stepf P Q p n next
   | SymError _ => F | SymBad _ => F | _ => T)
Proof
  strip_tac >>
  qpat_x_assum `sym_run_within_for _ _ _ _ (SUC n) ss` mp_tac >>
  Cases_on `result` >> simp[sym_run_within_for_def]
QED

Theorem iszero_pair_within_own[local]:
  asm_returns_zero_or_one x ==>
  own_window_within pre [x; AsmOp "ISZERO"; AsmOp "ISZERO"] [x] post
Proof
  disch_tac >> BETA_TAC >> rpt gen_tac >> strip_tac >>
  `x <> AsmOp "JUMP" /\ x <> AsmOp "JUMPI" /\
   x <> AsmOp "CODESIZE" /\ x <> AsmOp "CODECOPY"` by
    fs[asm_returns_zero_or_one_def] >>
  qabbrev_tac `p = pre ++ [x; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ post` >>
  qabbrev_tac `q = pre ++ [x] ++ post` >>
  `LENGTH pre < LENGTH p /\ EL (LENGTH pre) p = x /\
   LENGTH pre + 1 < LENGTH p /\ EL (LENGTH pre + 1) p = AsmOp "ISZERO" /\
   LENGTH pre + 2 < LENGTH p /\ EL (LENGTH pre + 2) p = AsmOp "ISZERO" /\
   LENGTH pre < LENGTH q /\ EL (LENGTH pre) q = x` by
    simp[Abbr `p`, Abbr `q`, EL_APPEND_EQN] >>
  `sym_step p env x ss = sym_step q env x ss` by
    (irule sym_step_prog_cong >> simp[Abbr `p`, Abbr `q`]) >>
  Cases_on `k` >- fs[sym_run_within_for_def] >>
  `2 * SUC n = SUC (2 * n + 1)` by decide_tac >> pop_assum SUBST1_TAC >>
  Cases_on `Q x`
  >- (disj1_tac >> simp[sym_run_within_for_def]) >>
  `P x ss.sym_stack /\
   (case sym_step q env x ss of
      SymOK next => sym_run_within_for (sym_step_own p env own) P Q p n next
    | SymError _ => F | SymBad _ => F | _ => T)` by
    (mp_tac (Q.INST [`stepf` |-> `sym_step_own p env own`,
       `result` |-> `sym_step q env x ss`] bounded_source_step) >>
     (impl_tac >- simp[sym_step_own_eq]) >>
     disch_then ACCEPT_TAC) >>
  Cases_on `sym_step q env x ss` >> fs[sym_step_own_eq] >>
  TRY (disj1_tac >> simp[sym_run_within_for_def, sym_step_own_eq] >> NO_TAC) >>
  rename1 `sym_step _ env x ss = SymOK s1` >>
  `s1.sym_base.as_pc = LENGTH pre + 1` by
    (drule_at (Pos last) sym_step_pc_next >> simp[]) >>
  drule_all sym_step_zero_or_one >>
  disch_then (qx_choosel_then [`w`, `stk`] (CONJUNCTS_THEN assume_tac)) >>
  drule_then (qspecl_then [`p`, `env`] assume_tac) sym_step_iszero_val >>
  qmatch_asmsub_abbrev_tac `sym_step p env (AsmOp "ISZERO") s1 = SymOK s2` >>
  `s2.sym_stack = Val (b2w (w = 0w)) :: stk /\
   s2.sym_base.as_pc = LENGTH pre + 2` by simp[Abbr `s2`, asm_next_def] >>
  drule_then (qspecl_then [`p`, `env`] assume_tac) sym_step_iszero_val >>
  qmatch_asmsub_abbrev_tac `sym_step p env (AsmOp "ISZERO") s2 = SymOK s3` >>
  `sym_steps_own p env own 3 ss = SymOK s3` by
    simp[sym_steps_own_pos, sym_steps_own_def, sym_step_own_eq] >>
  `~Q (AsmOp "ISZERO")` by fs[sym_within_ok_def, asm_plain_inst_def, is_data_inst_def] >>
  `sym_prefix_all (sym_steps_own p env own) (λi stk. T) Q p 3 ss` by
    (BETA_TAC >> rpt gen_tac >> strip_tac >>
     `m = 0 \/ m = 1 \/ m = 2` by decide_tac >>
     gvs[sym_steps_own_pos, sym_steps_own_def, sym_step_own_eq]) >>
  `sym_run_within_for (sym_step_own p env own) P Q p (SUC n) ss` by
    simp[sym_run_within_for_def, sym_step_own_eq] >>
  mp_tac (Q.INST [`stepf` |-> `sym_step_own p env own`,
    `runf` |-> `sym_steps_own p env own`, `P` |-> `P`, `Q` |-> `Q`, `p` |-> `p`]
    (INST_TYPE [alpha |-> ``:asm_inst``] sym_prefix_all_split_within)) >>
  (impl_tac >- simp[sym_steps_own_def]) >>
  disch_then (qspecl_then [`3`, `ss`, `s3`, `SUC n`] mp_tac) >>
  (impl_tac >- (fs[] >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  mp_tac (Q.INST [`pfx` |-> `pre`, `rest` |-> `post`]
    (BETA_RULE iszero_pair_window_results)) >>
  (impl_tac >- simp[]) >>
  strip_tac >>
  disj2_tac >> qexistsl_tac [`3`, `1`, `s3`] >>
  fs[Abbr `p`, Abbr `q`, sym_steps_own_def, EL_APPEND_EQN]
QED

Theorem iszero_jumpi_within_own[local]:
  own_window_within pre [AsmOp "ISZERO"; AsmOp "ISZERO"] []
    (AsmPushLabel l :: AsmOp "JUMPI" :: post)
Proof
  mp_tac (Q.INST [
    `pat` |-> `[AsmOp "ISZERO"; AsmOp "ISZERO"]`, `repl` |-> `[]`,
    `post` |-> `AsmPushLabel l :: AsmOp "JUMPI" :: post`] own_window_plain_within) >>
  (impl_tac >- suspend "certificate") >> disch_then ACCEPT_TAC
QED

Resume iszero_jumpi_within_own[certificate]:
  rpt gen_tac >> strip_tac >>
  `own_window_results pre [AsmOp "ISZERO"; AsmOp "ISZERO"] []
      (AsmPushLabel l :: AsmOp "JUMPI" :: post) env own ss 4 2` by
    (mp_tac (Q.INST [`pfx` |-> `pre`, `rest` |-> `post`]
       iszero_jumpi_window_results) >>
     (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
  `sym_prefix_all
      (sym_steps_own (pre ++ [AsmOp "ISZERO"; AsmOp "ISZERO"] ++
          AsmPushLabel l :: AsmOp "JUMPI" :: post) env own)
      (λi stk. asm_plain_inst i) (λi. F)
      (pre ++ [AsmOp "ISZERO"; AsmOp "ISZERO"] ++ AsmPushLabel l :: AsmOp "JUMPI" :: post) 4 ss` by
    (mp_tac (Q.INST
       [`chunk` |-> `[AsmOp "ISZERO"; AsmOp "ISZERO"; AsmPushLabel l; AsmOp "JUMPI"]`]
       plain_chunk_prefix_last_jump) >>
     (impl_tac >- simp[asm_plain_inst_def, is_data_inst_def]) >>
     simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  `sym_prefix_all (sym_steps_own (pre ++ AsmPushLabel l :: AsmOp "JUMPI" :: post) env own)
      (λi stk. asm_plain_inst i) (λi. F)
      (pre ++ AsmPushLabel l :: AsmOp "JUMPI" :: post) 2 ss` by
    (mp_tac (Q.INST [`chunk` |-> `[AsmPushLabel l; AsmOp "JUMPI"]`]
       plain_chunk_prefix_last_jump) >>
     (impl_tac >- simp[asm_plain_inst_def, is_data_inst_def]) >>
     simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  qexistsl_tac [`4`, `2`] >> fs[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise iszero_jumpi_within_own

Theorem merge_iszero_within_own:
  asm_within_own p (FST (merge_iszero p))
Proof
  BETA_TAC >> strip_tac >>
  mp_tac (Q.SPEC `asm_within_own` merge_iszero_prefix_transport_for) >>
  (impl_tac >-
    (rpt conj_tac
     >- metis_tac[asm_within_own_refl]
     >- metis_tac[asm_within_own_trans]
     >- (rpt gen_tac >> strip_tac >>
         `∃name. x = AsmOp name` by fs[asm_returns_zero_or_one_def] >>
         gvs[] >>
         mp_tac (Q.INST [`pat` |-> `[AsmOp name; AsmOp "ISZERO"; AsmOp "ISZERO"]`,
           `repl` |-> `[AsmOp name]`, `post` |-> `rest`]
           asm_splice_window_within_own) >>
         (impl_tac >- simp[asm_splice_ok_def, asm_label_refs_def, is_data_inst_def,
              asm_inst_size_def, iszero_pair_within_own]) >>
         BETA_TAC >> simp[])
     >- (rpt gen_tac >> strip_tac >>
         mp_tac (Q.INST [`pat` |-> `[AsmOp "ISZERO"; AsmOp "ISZERO"]`,
           `repl` |-> `[]`, `post` |-> `AsmPushLabel l :: AsmOp "JUMPI" :: rest`]
           asm_splice_window_within_own) >>
         (impl_tac >- simp[asm_splice_ok_def, asm_label_refs_def, is_data_inst_def,
              asm_inst_size_def, iszero_jumpi_within_own]) >>
         BETA_TAC >> simp[]))) >>
  disch_then (qspec_then `p` mp_tac) >> BETA_TAC >> simp[]
QED
