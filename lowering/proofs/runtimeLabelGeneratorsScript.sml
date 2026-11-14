(* Runtime orchestration consumes body certificates at the proof interface. *)
Theory runtimeLabelGenerators
Ancestors
  runtimeLabelInvariant runtimeLabelValues runtimeLabelBuiltins runtimeLabelABI
  moduleLowering stmtLowering compileEnv context emitHelper venomInst list
  loweringShapeDefs combinatorics alist

Theorem rb_compile_selector_checks:
  !sels. rb_operand_ok mid /\
    EVERY (\(sel,lbl). rb_operand_ok (Label lbl)) sels ==>
    rb_step (K T) (compile_selector_checks mid sels)
Proof
  Induct >> simp[compile_selector_checks_def, rb_step_return] >>
  gen_tac >> PairCases_on `h` >>
  simp[compile_selector_checks_def] >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  ntac 2 (irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac) >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  irule rb_ignore >> conj_tac >- gvs[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  first_x_assum irule >> gvs[]
QED

Theorem rb_compile_selector_dispatch_linear:
  EVERY (\(sel,lbl). rb_operand_ok (Label lbl)) sels /\
  rb_operand_ok (Label fallback) ==>
  rb_step (K T) (compile_selector_dispatch_linear sels fallback)
Proof
  strip_tac >> rewrite_tac[compile_selector_dispatch_linear_def] >>
  ntac 3 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  ntac 2 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule rb_ignore >> simp[rb_compile_selector_checks, rb_emit_inst]
QED

Theorem rb_compile_sparse_bucket_search:
  !sels. rb_operand_ok mid /\ rb_operand_ok (Label fallback) /\
    EVERY (\(sel,lbl,tz). rb_operand_ok (Label lbl)) sels ==>
    rb_step (K T) (compile_sparse_bucket_search mid sels fallback)
Proof
  Induct >> simp[compile_sparse_bucket_search_def, rb_emit_inst] >>
  gen_tac >> PairCases_on `h` >>
  simp[compile_sparse_bucket_search_def] >> strip_tac >>
  ntac 2 (irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[rb_step_return] >>
      ntac 3 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      simp[rb_emit_op]) >>
  gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  first_x_assum irule >> gvs[]
QED

Theorem rb_alloc_bucket_labels:
  !n. rb_step (EVERY (\l. rb_operand_ok (Label l))) (alloc_bucket_labels n)
Proof
  completeInduct_on `n` >> Cases_on `n` >>
  simp[Once alloc_bucket_labels_def, rb_step_return] >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `EVERY (\l. rb_operand_ok (Label l))` >>
  BETA_TAC >> reverse conj_tac >- (first_x_assum irule >> simp[]) >>
  gen_tac >> strip_tac >> irule rb_step_return >> gvs[]
QED

Theorem rb_group_into_buckets:
  !sels n. EVERY (\(sel,lbl,tz). rb_operand_ok (Label lbl)) sels ==>
  EVERY (\b. EVERY (\(sel,lbl,tz). rb_operand_ok (Label lbl)) (SND b))
    (group_into_buckets sels n)
Proof
  Induct >- simp[group_into_buckets_def] >>
  PairCases >> rpt gen_tac >> strip_tac >>
  simp_tac std_ss [group_into_buckets_def, LET_THM] >> gvs[] >>
  first_x_assum (qspec_then `n` mp_tac) >>
  rw[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD] >>
  gvs[MEM_MAP, pairTheory.EXISTS_PROD, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem rb_create_bucket_blocks:
  !mid lbls buckets fallback.
    rb_operand_ok mid /\ rb_operand_ok (Label fallback) /\
    EVERY (\b. EVERY (\(sel,lbl,tz). rb_operand_ok (Label lbl)) (SND b)) buckets ==>
    rb_step (K T) (create_bucket_blocks mid lbls buckets fallback)
Proof
  ho_match_mp_tac create_bucket_blocks_ind >> rpt strip_tac >>
  simp[Once create_bucket_blocks_def, rb_step_return] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  irule rb_ignore >> conj_tac >- gvs[rb_compile_sparse_bucket_search] >>
  first_x_assum irule >> gvs[]
QED

Theorem rb_emit_data_section:
  rb_step (K T) (emit_data_section label)
Proof
  simp[rb_step_def, rb_state_ok_def, emit_data_section_def,
       state_insts_def, all_blocks_def]
QED

Theorem rb_emit_data_item:
  rb_step (K T) (emit_data_item item)
Proof
  rw[rb_step_def, rb_state_ok_def, emit_data_item_def,
       state_insts_def, all_blocks_def] >>
  Cases_on `st.cs_data_sections` >> gvs[]
QED

Theorem rb_data_label_fold:
  !labels. rb_step (K T)
    (FOLDL (\m lbl. comp_ignore_bind m (emit_data_item (DataLabel lbl)))
      (comp_return ()) labels)
Proof
  Induct using SNOC_INDUCT >> simp[FOLDL_SNOC, rb_step_return] >>
  gen_tac >> irule rb_ignore >> simp[rb_emit_data_item]
QED

Theorem rb_sparse_target_list:
  EVERY (\l. rb_operand_ok (Label l)) labels /\
  rb_operand_ok (Label fallback) ==>
  EVERY (\l. rb_operand_ok (Label l))
    (GENLIST (\i. case ALOOKUP (MAP2 (\(bid,items) lbl. (bid,lbl)) buckets labels) i of
       SOME lbl => lbl | NONE => fallback) n)
Proof
  strip_tac >> simp[EVERY_GENLIST] >> gen_tac >> strip_tac >>
  CASE_TAC >> gvs[] >>
  drule alistTheory.ALOOKUP_MEM >>
  disch_then (mp_tac o MATCH_MP combinatoricsTheory.MEM_MAP2) >>
  simp[pairTheory.EXISTS_PROD] >> rpt strip_tac >> gvs[] >>
  gvs[EVERY_MEM]
QED

Theorem rb_compile_selector_dispatch_sparse:
  EVERY (\(sel,lbl,tz). rb_operand_ok (Label lbl)) sels /\
  rb_operand_ok (Label fallback) ==>
  rb_step (K T) (compile_selector_dispatch_sparse sels bucket_count fallback)
Proof
  strip_tac >> rewrite_tac[compile_selector_dispatch_sparse_def] >>
  ntac 3 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_inst] >>
  irule rb_ignore >> conj_tac >- simp[rb_new_block] >>
  ntac 2 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  IF_CASES_TAC
  >- (irule rb_ignore >> conj_tac
      >- (irule rb_compile_selector_checks >>
          gvs[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD]) >>
      simp[rb_emit_inst]) >>
  irule rb_step_bind >> qexists_tac `EVERY (\l. rb_operand_ok (Label l))` >>
  BETA_TAC >> reverse conj_tac >- simp[rb_alloc_bucket_labels] >>
  gen_tac >> strip_tac >>
  ntac 2 (irule rb_bind_return >> BETA_TAC) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_return >> BETA_TAC >>
  ntac 3 (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_ignore >> conj_tac
  >- (irule rb_emit_inst >> simp[EVERY_MAP] >>
      irule (SRULE [] rb_sparse_target_list) >> gvs[]) >>
  irule rb_ignore >> conj_tac >- simp[rb_emit_data_section] >>
  irule rb_ignore >> conj_tac >- simp[rb_data_label_fold] >>
  irule rb_create_bucket_blocks >> simp[rb_group_into_buckets]
QED
