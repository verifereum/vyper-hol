(* The optimizer leaves a final data header in place and emits only
   encodable instructions. Actual byte length then bounds label offsets. *)
Theory asmOptEncodingLayout
Ancestors
  asmOptNonemptyCompose asmOptNonemptyWitness asmOptMergeJumpdests asmOptimizer
  asmToBytecodeProofs codegenEncodingWf asmWf asmIR symbolResolve
  list rich_list finite_map arithmetic

Overload encodable[local] = ``\inst. case inst of
  AsmOp name => IS_SOME (evm_opcode_byte name)
| AsmPush bytes => LENGTH bytes <= 32
| AsmPushOfst _ _ => F
| _ => T``

Overload ends_at[local] = ``\label p. p <> [] /\ LAST p = AsmDataHeader label``

Overload layout_ready[local] = ``\label p. ends_at label p /\ EVERY encodable p``

Theorem layout_ready_cons[local]:
  layout_ready label (h::t) <=>
  (if t = [] then h = AsmDataHeader label else ends_at label t) /\
  encodable h /\ EVERY encodable t
Proof
  Cases_on `t` >> simp[]
QED

Theorem prune_unreachable_layout[local]:
  !p dropping. layout_ready label p ==>
    layout_ready label (FST (prune_unreachable_walk dropping p))
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `p = []`
  >- gvs[asm_reachable_marker_def, prune_unreachable_walk_def] >>
  fs[LAST_CONS_cond] >>
  ONCE_REWRITE_TAC [prune_unreachable_walk_def] >>
  simp_tac bool_ss [LET_THM, pairTheory.ELIM_UNCURRY, pairTheory.FST] >>
  IF_CASES_TAC >> simp[] >>
  first_x_assum (qspec_then `asm_terminal_op h` strip_assume_tac) >>
  gvs[LAST_CONS_cond]
QED

Theorem merge_iszero_pairs_layout[local]:
  !p. layout_ready label p ==> layout_ready label (FST (merge_iszero_pairs p))
Proof
  ho_match_mp_tac merge_iszero_pairs_ind >>
  rpt gen_tac >> strip_tac >>
  ONCE_REWRITE_TAC [merge_iszero_pairs_def] >>
  simp_tac bool_ss [LET_THM, pairTheory.ELIM_UNCURRY, pairTheory.FST] >>
  rw[] >> fs[LAST_CONS_cond] >> res_tac >> gvs[LAST_CONS_cond] >>
  Cases_on `rest` >> gvs[] >> res_tac >> gvs[]
QED

Theorem merge_iszero_jumpi_layout[local]:
  !p. layout_ready label p ==> layout_ready label (FST (merge_iszero_jumpi p))
Proof
  ho_match_mp_tac merge_iszero_jumpi_ind >>
  rpt gen_tac >> strip_tac >>
  ONCE_REWRITE_TAC [merge_iszero_jumpi_def] >>
  simp_tac bool_ss [LET_THM, pairTheory.ELIM_UNCURRY, pairTheory.FST] >>
  rw[] >> fs[LAST_CONS_cond] >> res_tac >> gvs[LAST_CONS_cond]
QED

Theorem rename_push_label_encodable[local]:
  !i. encodable (rename_push_label x y i) <=> encodable i
Proof
  Cases >> rw[rename_push_label_def]
QED

Theorem merge_jumpdests_layout[local]:
  !done rest changed.
    layout_ready label (REVERSE done ++ rest) ==>
    layout_ready label (FST (merge_jumpdests_walk done rest changed))
Proof
  recInduct merge_jumpdests_walk_ind >> rpt gen_tac >> strip_tac >>
  Cases_on `rest` >- simp[merge_jumpdests_walk_def] >>
  rename1 `h::tail` >> Cases_on `tail`
  >- simp[merge_jumpdests_walk_def] >>
  rename1 `h::next::tail` >> Cases_on `tail`
  >- simp[merge_jumpdests_walk_def] >>
  rename1 `h::next::third::more` >>
  Cases_on `h` >> gvs[] >>
  ONCE_REWRITE_TAC [merge_jumpdests_walk_def] >> gvs[] >>
  qmatch_asmsub_abbrev_tac `target = NONE` >>
  Cases_on `target` >> gvs[] >>
  disch_tac >> first_x_assum irule >>
  gvs[LAST_CONS_cond, rename_push_label_facts, EVERY_MAP,
      combinTheory.o_DEF, rename_push_label_encodable] >>
  Cases_on `more = []` >> gvs[rename_push_label_facts]
QED

Theorem prune_inefficient_layout[local]:
  !p. layout_ready label p ==>
    layout_ready label (FST (prune_inefficient_jumps p))
Proof
  ho_match_mp_tac prune_inefficient_jumps_ind >>
  rpt gen_tac >> strip_tac >>
  ONCE_REWRITE_TAC [prune_inefficient_jumps_def] >>
  simp_tac bool_ss [LET_THM, pairTheory.ELIM_UNCURRY, pairTheory.FST] >>
  rw[] >> fs[LAST_CONS_cond] >> res_tac >> gvs[LAST_CONS_cond]
QED

Theorem optimize_inefficient_layout[local]:
  !p. layout_ready label p ==>
    layout_ready label (FST (optimize_inefficient_jumps p))
Proof
  ho_match_mp_tac optimize_inefficient_jumps_ind >>
  rpt gen_tac >> strip_tac >>
  ONCE_REWRITE_TAC [optimize_inefficient_jumps_def] >>
  simp_tac bool_ss [LET_THM, pairTheory.ELIM_UNCURRY, pairTheory.FST] >>
  rw[] >> fs[LAST_CONS_cond] >> res_tac >> gvs[LAST_CONS_cond] >>
  fs[asm_jumpi_over_jump_def, EVAL ``evm_opcode_byte "ISZERO"``] >>
  res_tac >> gvs[]
QED

Theorem layout_ready_snoc[local]:
  layout_ready label p <=> ?pre. p = pre ++ [AsmDataHeader label] /\ EVERY encodable pre
Proof
  eq_tac >> strip_tac >-
    (qexists_tac `FRONT p` >>
     `p = FRONT p ++ [AsmDataHeader label]` by metis_tac[APPEND_FRONT_LAST] >>
     qpat_assum `p = FRONT p ++ _` (fn th =>
       qpat_x_assum `EVERY _ p` (mp_tac o ONCE_REWRITE_RULE [th])) >> simp[]) >>
  simp[]
QED

Theorem prune_unused_layout[local]:
  !p. layout_ready label p ==> layout_ready label (FST (prune_unused_jumpdests p))
Proof
  gen_tac >> simp[layout_ready_snoc] >> strip_tac >>
  simp[prune_unused_jumpdests_def, FILTER_APPEND, asm_unused_label_def] >>
  irule EVERY_FILTER_IMP >> simp[]
QED

Theorem peep_swap_pair_layout[local]:
  layout_ready label (a::b::c::rest) /\ peep_swap_pair a b c rest = (p,ch) ==>
  layout_ready label p
Proof
  rw[peep_swap_pair_def] >> gvs[]
QED

Theorem peep_swap_comm_layout[local]:
  layout_ready label p /\ peep_swap_comm p = SOME (q,ch) ==>
  layout_ready label q
Proof
  rw[peep_swap_comm_def, AllCaseEqs()] >> gvs[]
QED

Theorem peep_dup_swap_layout[local]:
  layout_ready label p /\ peep_dup_swap p = SOME (q,ch) ==>
  layout_ready label q
Proof
  rw[peep_dup_swap_def, AllCaseEqs()] >>
  gvs[LAST_CONS_cond] >> BasicProvers.every_case_tac >> gvs[]
QED

Theorem stack_peephole_layout[local]:
  !p q ch. layout_ready label p /\ stack_peephole_opts p = SOME (q,ch) ==>
    layout_ready label q
Proof
  measureInduct_on `LENGTH p` >> rpt gen_tac >> strip_tac >>
  Cases_on `p` >- gvs[] >>
  rename1 `a::tail` >> Cases_on `tail`
  >- (qpat_x_assum `stack_peephole_opts _ = _` mp_tac >>
      ONCE_REWRITE_TAC [stack_peephole_opts_def] >>
      simp_tac bool_ss [list_case_def, optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
      disch_then (SUBST1_TAC o SYM o CONJUNCT1) >> asm_rewrite_tac[]) >>
  rename1 `a::b::tail` >> Cases_on `tail`
  >- (qpat_x_assum `stack_peephole_opts _ = _` mp_tac >>
      ONCE_REWRITE_TAC [stack_peephole_opts_def] >>
      simp_tac bool_ss [list_case_def, optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
      disch_then (SUBST1_TAC o SYM o CONJUNCT1) >> asm_rewrite_tac[]) >>
  rename1 `a::b::c::rest` >>
  qpat_x_assum `stack_peephole_opts _ = _` mp_tac >>
  ONCE_REWRITE_TAC [stack_peephole_opts_def] >>
  simp_tac bool_ss [list_case_def, MAP] >>
  simp_tac bool_ss [AllCaseEqs(), listTheory.CONS_11] >>
  strip_tac >> gvs[]
  >- (PairCases_on `z` >> gvs[] >> first_x_assum irule >>
      qexistsl_tac [`z1`, `AsmOp "SWAP1"::AsmOp "DUP2"::rest`] >>
      Cases_on `rest` >> gvs[EVAL ``evm_opcode_byte "DUP2"``])
  >- (PairCases_on `z` >> gvs[] >> first_x_assum irule >>
      qexistsl_tac [`z1`, `rest`] >> Cases_on `rest` >> gvs[])
  >- (PairCases_on `z` >> gvs[] >> first_x_assum irule >>
      qexistsl_tac [`z1`, `AsmOp "POP"::AsmOp "POP"::rest`] >> simp[]) >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  `layout_ready label (a::b::c::rest)` by simp[] >>
  drule_all peep_swap_pair_layout >> disch_tac >>
  qpat_assum `layout_ready label l1` (fn ready =>
    qpat_assum `peep_swap_comm l1 = _`
      (assume_tac o MATCH_MP peep_swap_comm_layout o CONJ ready)) >>
  qpat_assum `layout_ready label l2` (fn ready =>
    qpat_assum `peep_dup_swap l2 = _`
      (assume_tac o MATCH_MP peep_dup_swap_layout o CONJ ready)) >>
  `LENGTH l3 <= LENGTH rest + 3` by
    (drule peep_swap_pair_length >> drule peep_swap_comm_length >>
     drule peep_dup_swap_length >> rpt strip_tac >> decide_tac) >>
  Cases_on `l3` >> gvs[] >> PairCases_on `z` >> gvs[] >>
  Cases_on `t = []` >> gvs[layout_ready_cons]
  >- (qpat_x_assum `_ = stack_peephole_opts []` mp_tac >>
      ONCE_REWRITE_TAC [stack_peephole_opts_def] >> simp[]) >>
  `layout_ready label z0` by
    (first_x_assum irule >> qexistsl_tac [`z1`, `t`] >>
     gvs[LAST_CONS_cond] >> decide_tac) >>
  gvs[LAST_CONS_cond]
QED

Theorem asm_opt_finalizer_layout_ready[local]:
  !rpolicy p q. layout_ready label p /\ asm_opt_finalizer rpolicy p = SOME q ==>
    layout_ready label q
Proof
  ho_match_mp_tac asm_opt_finalizer_preserves_predicate >>
  ho_match_mp_tac optimize_round_preserves_predicate >>
  simp[prune_unreachable_code_def, merge_iszero_def, merge_jumpdests_def,
       prune_unreachable_layout, prune_inefficient_layout, optimize_inefficient_layout,
       prune_unused_layout, stack_peephole_layout] >>
  conj_tac
  >- (gen_tac >> strip_tac >> rpt (pairarg_tac >> gvs[]) >>
      metis_tac[merge_iszero_pairs_layout, merge_iszero_jumpi_layout, pairTheory.FST]) >>
  conj_tac
  >- (qx_gen_tac `p` >>
      mp_tac (Q.SPECL [`[]`, `p`, `F`] merge_jumpdests_layout) >> simp[]) >>
  MATCH_ACCEPT_TAC stack_peephole_layout
QED

Theorem encodable_min_size[local]:
  encodable inst ==> asm_inst_size inst <= LENGTH (encode_inst offsets inst)
Proof
  Cases_on `inst` >> simp[asm_inst_size_def, encode_inst_def] >>
  all_tac
  >~ [`encode_inst offsets (AsmPush l)`] >-
    (Cases_on `l` >> simp[encode_inst_def]) >>
  BasicProvers.every_case_tac >> gvs[] >> rw[pad_bytes_def] >> decide_tac
QED

Theorem encodable_size_bound[local]:
  !p offsets. EVERY encodable p ==>
  SUM (MAP asm_inst_size p) <= LENGTH (FLAT (MAP (encode_inst offsets) p))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `asm_inst_size h <= LENGTH (encode_inst offsets h)` by simp[encodable_min_size] >>
  res_tac >> first_x_assum (qspec_then `offsets` assume_tac) >> decide_tac
QED

Theorem asm_opt_finalizer_end_offset:
  p = prefix ++ [AsmDataHeader label] /\ asm_encoding_wf p /\
  (!lbl d. ~MEM (AsmPushOfst lbl d) p) /\
  asm_opt_finalizer rpolicy p = SOME q /\ LENGTH (assemble q) < 65536 ==>
  (?head. q = head ++ [AsmDataHeader label]) /\ asm_encoding_wf q
Proof
  strip_tac >>
  `ends_at label p` by simp[] >>
  `EVERY encodable p` by
    (qpat_x_assum `p = _` kall_tac >>
     Cases_on `compute_label_offsets p` >> fs[asm_encoding_wf_def] >>
     simp[EVERY_EL] >> qx_gen_tac `n` >> strip_tac >>
     Cases_on `EL n p` >> gvs[] >> metis_tac[EL_MEM]) >>
  `layout_ready label p` by simp[] >>
  drule_all asm_opt_finalizer_layout_ready >> strip_tac >>
  `SUM (MAP asm_inst_size q) <= LENGTH (assemble q)` by
    (simp[assemble_def, pairTheory.ELIM_UNCURRY] >>
     irule encodable_size_bound >> simp[]) >>
  `SUM (MAP asm_inst_size q) < 65536` by decide_tac >>
  conj_tac
  >- metis_tac[layout_ready_snoc] >>
  qspec_then `q` strip_assume_tac compute_label_offsets_bound >>
  Cases_on `compute_label_offsets q` >> simp[asm_encoding_wf_def] >>
  fs[EVERY_EL] >> rpt strip_tac >>
  (irule encode_num_bytes_length_le_symbol_size >> res_tac >> decide_tac
   ORELSE
   (qpat_x_assum `!n. n < LENGTH q ==> _` (qspec_then `i` mp_tac) >> simp[]))
QED
