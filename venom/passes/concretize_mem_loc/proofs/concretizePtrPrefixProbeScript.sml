Theory concretizePtrPrefixProbe
Ancestors
  concretizePtrPrefixRelation concretizePtrStoreSteps concretizePtrChronologicalHistory contextCodegenRel
  venomExecSemantics venomInst venomState ptrDiscipline list finite_map words

Definition ptr_probe_fn_def:
  ptr_probe_fn code = mk_raw_function "probe"
    [<| bb_label := "entry"; bb_instructions := code |>]
End

Definition ptr_probe_ctx_def:
  ptr_probe_ctx code = mk_venom_context [ptr_probe_fn code] (SOME "probe")
End

Definition ptr_probe_entry_state_def:
  ptr_probe_entry_state s = s with <| vs_prev_bb := NONE;
    vs_current_bb := "entry"; vs_inst_idx := 0 |>
End

Theorem ptr_probe_entry_history:
  inst.inst_opcode <> PHI ==>
  ptr_chrono_history s (ptr_probe_ctx (inst::rest))
    [ptr_observe [] [] FEMPTY entry_taint (ptr_probe_fn (inst::rest)) inst
      (ptr_probe_entry_state s)]
    (ptr_observe [] [] FEMPTY entry_taint (ptr_probe_fn (inst::rest)) inst
      (ptr_probe_entry_state s))
Proof
  strip_tac >> irule (cj 1 ptr_chrono_history_rules) >>
  simp[ptr_probe_ctx_def, ptr_probe_fn_def, ptr_probe_entry_state_def,
    mk_venom_context_def, mk_raw_function_def, lookup_function_def,
    fn_entry_label_def, enters_block_def, active_inst_def,
    lookup_block_def, eval_phis_def, phi_prefix_length_def,
    FIND_def, INDEX_FIND_def, entry_block_def]
QED

Theorem ptr_probe_alloca_step:
  FLOOKUP s.vs_allocas aid = NONE ==>
  step_inst fuel C (mk_inst aid ALLOCA [Lit szword] [p]) s =
    OK (update_var p (n2w s.vs_alloca_next)
      (s with <| vs_allocas := s.vs_allocas |+
        (aid,(s.vs_alloca_next,w2n szword));
        vs_alloca_next := s.vs_alloca_next + w2n szword |>))
Proof
  simp[step_inst_non_invoke, mk_inst_def, step_inst_base_def,
    exec_alloca_def, eval_operand_def]
QED

Definition ptr_probe_allocated_state_def:
  ptr_probe_allocated_state aid p szword s =
    update_var p (n2w s.vs_alloca_next)
      (s with <| vs_allocas := s.vs_allocas |+
        (aid,(s.vs_alloca_next,w2n szword));
        vs_alloca_next := s.vs_alloca_next + w2n szword |>)
End

Theorem ptr_probe_alloca_history:
  FLOOKUP s.vs_allocas aid = NONE ==>
  ?h. ptr_chrono_history s
    (ptr_probe_ctx (mk_inst aid ALLOCA [Lit szword] [p] :: inst :: rest)) h
    (ptr_observe [] []
      (step_prov [] FEMPTY (mk_inst aid ALLOCA [Lit szword] [p])
        (ptr_probe_allocated_state aid p szword (ptr_probe_entry_state s)))
      (step_taint (mk_inst aid ALLOCA [Lit szword] [p]) (ptr_probe_entry_state s)
        (ptr_probe_allocated_state aid p szword (ptr_probe_entry_state s)) entry_taint)
      (ptr_probe_fn (mk_inst aid ALLOCA [Lit szword] [p] :: inst :: rest)) inst
      ((ptr_probe_allocated_state aid p szword (ptr_probe_entry_state s))
        with vs_inst_idx := 1))
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `ptr_observe [] [] G tn fn inst endpoint` >>
  qabbrev_tac `ai = mk_inst aid ALLOCA [Lit szword] [p]` >>
  `ptr_chrono_history s (ptr_probe_ctx (ai::inst::rest))
    [ptr_observe [] [] FEMPTY entry_taint fn ai (ptr_probe_entry_state s)]
    (ptr_observe [] [] FEMPTY entry_taint fn ai (ptr_probe_entry_state s))` by
    (simp[Abbr `ai`, Abbr `fn`] >> irule ptr_probe_entry_history >> simp[mk_inst_def]) >>
  `ptr_chrono_step (ptr_probe_ctx (ai::inst::rest))
    (ptr_observe [] [] FEMPTY entry_taint fn ai (ptr_probe_entry_state s))
    (ptr_observe [] [] G tn fn inst endpoint)` by
    (simp[Once ptr_chrono_step_cases, ptr_observe_def,
       Abbr `ai`, Abbr `G`, Abbr `tn`, Abbr `endpoint`, Abbr `fn`,
       ptr_probe_fn_def, mk_raw_function_def, active_inst_def,
       mk_inst_def, is_terminator_def, ptr_probe_entry_state_def] >>
     qexistsl_tac [`ptr_probe_allocated_state aid p szword (ptr_probe_entry_state s)`, `0`] >>
     simp[ptr_probe_allocated_state_def, ptr_probe_entry_state_def,
       step_inst_non_invoke, step_inst_base_def, exec_alloca_def, eval_operand_def,
       mk_inst_def, update_var_def]) >>
  metis_tac[ptr_chrono_history_rules]
QED

Theorem ptr_probe_alloca_values:
  reloc (s.vs_alloca_next,w2n szword) = SOME pos ==>
  ptr_prefix_vars reloc (FEMPTY |+ (p,(s.vs_alloca_next,w2n szword))) FEMPTY
    (ptr_probe_allocated_state aid p szword (ptr_probe_entry_state s)
      with vs_inst_idx := 1)
    (update_var p pos (ptr_probe_entry_state s) with vs_inst_idx := 1)
Proof
  strip_tac >> simp[ptr_prefix_vars_def] >> gen_tac >>
  Cases_on `v = p` >>
  simp[ptr_prefix_value_def, ptr_probe_allocated_state_def,
    ptr_probe_entry_state_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE, WORD_SUB_REFL] >>
  Cases_on `FLOOKUP s.vs_vars v` >> simp[word_agree_except_def]
QED
