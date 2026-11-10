(* One-edit source locations; PHI repair is visible in fetched fields. *)
Theory functionInlinerLocation
Ancestors
  functionInlinerRoutedProvenance functionInlinerPhiTransport
  functionInlinerSiteLayout functionInlinerActivation functionInlinerDefs
  venomInst list rich_list

Theorem inline_keep_before_location:
  loc.il_phase = InlineAtInstruction j /\
  (loc.il_block <> e.ise_block \/ j < e.ise_index) ==>
  inline_choice_location (InlineKeep e) loc = SOME loc
Proof
  Cases_on `loc` >> simp[inline_choice_location_def] >> rpt strip_tac >>
  Cases_on `s = e.ise_block` >> gvs[inline_location_fn_updates]
QED

Theorem inline_keep_after_location:
  loc.il_phase = InlineAtInstruction j /\ loc.il_block = e.ise_block /\
  e.ise_index < j ==>
  inline_choice_location (InlineKeep e) loc =
    SOME (loc with <|il_block := e.ise_return;
                    il_phase := InlineAtInstruction (j - (e.ise_index + 1))|>)
Proof
  simp[inline_choice_location_def] >> rpt strip_tac >> simp[]
QED

Theorem inline_keep_selected_location:
  inline_choice_location (InlineKeep e)
    <|il_block := e.ise_block; il_phase := InlineAtInstruction e.ise_index;
      il_counter := k|> = NONE
Proof simp[inline_choice_location_def]
QED

Theorem inline_enter_instruction_location:
  lookup_block loc.il_block e.ise_callee.fn_blocks = SOME cb /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  loc.il_phase = InlineAtInstruction j /\
  j <= LENGTH cb.bb_instructions /\ e.ise_index < LENGTH bb.bb_instructions ==>
  inline_choice_location (InlineEnter e) loc =
    let pre = rewrite_inline_insts
      (rotate_invoke_ops (EL e.ise_index bb.bb_instructions).inst_operands)
      (EL e.ise_index bb.bb_instructions).inst_outputs e.ise_return
      (MAP (clone_instruction e.ise_prefix (fn_labels e.ise_callee))
        (TAKE j cb.bb_instructions)) 0
    in SOME <|il_block := STRCAT e.ise_prefix loc.il_block;
              il_phase := InlineAtInstruction (LENGTH (FST pre));
              il_counter := SND pre|>
Proof
  simp[inline_choice_location_def]
QED

Definition inline_edit_repair_def:
  inline_edit_repair e source_bb label inst =
    if MEM label
         (bb_succs <|bb_label := e.ise_return;
           bb_instructions := DROP (e.ise_index+1) source_bb.bb_instructions|>) /\
       inst.inst_opcode = PHI
    then subst_label_inst e.ise_block e.ise_return inst else inst
End

(* General final fetch projection. Unlike a raw layout equality, it also
   accounts for a PHI located in a successor of the split return block. *)
Theorem inline_edit_final_fetch:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  lookup_block l
    (inline_call_site e.ise_prefix e.ise_return e.ise_caller e.ise_callee
      e.ise_block e.ise_index).fn_blocks = SOME bb /\
  get_instruction bb j = SOME inst ==>
  inline_fetched_fields e.ise_final l j
    (inline_inst_fields (inline_edit_repair e source_bb bb.bb_label inst))
Proof
  rpt strip_tac >>
  gvs[inline_edit_repair_def, inline_site_edit_valid_def] >>
  drule inline_one_site_lookup_fields >> simp[] >>
  disch_then (drule_at (Pat `lookup_block _ (inline_call_site _ _ _ _ _ _).fn_blocks = _`)) >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `MAP inline_inst_fields (if affected then _ else _)` >>
  Cases_on `affected` >> gvs[] >>
  `LENGTH tb.bb_instructions = LENGTH bb.bb_instructions` by
    metis_tac[LENGTH_MAP] >>
  gvs[get_instruction_def] >>
  simp[inline_fetched_fields_def] >>
  qexists `EL j tb.bb_instructions` >>
  simp[get_instruction_def] >>
  gvs[LIST_EQ_REWRITE, EL_MAP] >>
  first_x_assum (qspec_then `j` mp_tac) >> simp[] >>
  Cases_on `(EL j bb.bb_instructions).inst_opcode = PHI` >> gvs[]
QED

Theorem inline_edit_prefix_fetch:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  e.ise_index <= LENGTH bb.bb_instructions /\ j < e.ise_index ==>
  inline_fetched_fields e.ise_final e.ise_block j
    (inline_inst_fields (inline_edit_repair e bb bb.bb_label
      (EL j bb.bb_instructions)))
Proof
  strip_tac >>
  drule inline_call_site_lookup_call >>
  disch_then (qspecl_then [`e.ise_return`, `e.ise_prefix`, `e.ise_index`,
                          `e.ise_callee`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `SOME raw` >>
  `get_instruction raw j = SOME (EL j bb.bb_instructions)` by
    simp[Abbr `raw`, get_instruction_def, EL_APPEND1, EL_TAKE] >>
  drule_all inline_edit_final_fetch >> simp[Abbr `raw`]
QED

Theorem inline_edit_suffix_fetch:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  e.ise_index < j /\ j < LENGTH bb.bb_instructions ==>
  inline_fetched_fields e.ise_final e.ise_return (j - (e.ise_index+1))
    (inline_inst_fields (inline_edit_repair e bb e.ise_return
      (EL j bb.bb_instructions)))
Proof
  strip_tac >>
  drule_all inline_call_site_lookup_return >>
  disch_then (qspecl_then [`e.ise_prefix`, `e.ise_index`, `e.ise_callee`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `SOME raw` >>
  `get_instruction raw (j - (e.ise_index+1)) = SOME (EL j bb.bb_instructions)` by
    simp[Abbr `raw`, get_instruction_def, EL_DROP] >>
  drule_all inline_edit_final_fetch >> simp[Abbr `raw`]
QED

Theorem inline_edit_selected_jump:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  e.ise_index <= LENGTH bb.bb_instructions ==>
  inline_fetched_fields e.ise_final e.ise_block e.ise_index
    (JMP, [Label (case (clone_function e.ise_prefix e.ise_callee).fn_blocks of
                   [] => "" | eb::_ => eb.bb_label)], [])
Proof
  strip_tac >> drule inline_call_site_lookup_call >>
  disch_then (qspecl_then [`e.ise_return`, `e.ise_prefix`, `e.ise_index`,
                          `e.ise_callee`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `SOME raw` >>
  qmatch_goalsub_abbrev_tac `(JMP, ops, [])` >>
  `get_instruction raw e.ise_index =
    SOME <|inst_id := 0; inst_opcode := JMP; inst_operands := ops; inst_outputs := []|>` by
    simp[Abbr `raw`, Abbr `ops`, get_instruction_def, EL_APPEND2] >>
  drule_all inline_edit_final_fetch >>
  simp[inline_edit_repair_def, inline_inst_fields_def]
QED

Theorem inline_edit_enter_focus_fetch:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  lookup_block cl e.ise_callee.fn_blocks = SOME cb /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  ~MEM (STRCAT e.ise_prefix cl) (fn_labels e.ise_caller) /\
  STRCAT e.ise_prefix cl <> e.ise_return /\ j < LENGTH cb.bb_instructions ==>
  let args = rotate_invoke_ops (EL e.ise_index bb.bb_instructions).inst_operands;
      outs = (EL e.ise_index bb.bb_instructions).inst_outputs;
      clone = clone_instruction e.ise_prefix (fn_labels e.ise_callee);
      pre = rewrite_inline_insts args outs e.ise_return
              (MAP clone (TAKE j cb.bb_instructions)) 0;
      focus = rewrite_inline_inst args outs e.ise_return
                (clone (EL j cb.bb_instructions)) (SND pre)
  in !k. k < LENGTH (FST focus) ==>
    inline_fetched_fields e.ise_final (STRCAT e.ise_prefix cl)
      (LENGTH (FST pre) + k)
      (inline_inst_fields (inline_edit_repair e bb (STRCAT e.ise_prefix cl)
        (EL k (FST focus))))
Proof
  strip_tac >> simp[LET_THM] >>
  `cb.bb_instructions = TAKE j cb.bb_instructions ++
     EL j cb.bb_instructions :: DROP (SUC j) cb.bb_instructions` by
    metis_tac[TAKE_DROP, DROP_CONS_EL] >>
  drule_all inline_call_site_lookup_clone_focus >>
  disch_then (qspec_then `e.ise_index` mp_tac) >> simp[] >>
  qmatch_goalsub_abbrev_tac `SOME raw` >> strip_tac >>
  gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `EL k (FST focus)` >>
  qmatch_goalsub_abbrev_tac `inline_fetched_fields _ _ offset _` >>
  `get_instruction raw offset = SOME (EL k (FST focus))` by
    simp[Abbr `raw`, Abbr `offset`, Abbr `focus`, get_instruction_def,
         EL_APPEND2, EL_APPEND1] >>
  drule_all inline_edit_final_fetch >>
  simp[Abbr `raw`, clone_basic_block_def] >>
  metis_tac[venomExecPropsTheory.lookup_block_label]
QED

Theorem inline_edit_other_fetch:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  lookup_block l e.ise_caller.fn_blocks = SOME bb /\ l <> e.ise_block /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  get_instruction bb j = SOME inst ==>
  inline_fetched_fields e.ise_final l j
    (inline_inst_fields (inline_edit_repair e source_bb bb.bb_label inst))
Proof
  strip_tac >> drule_all inline_call_site_lookup_other >>
  disch_then (qspecl_then [`e.ise_return`, `e.ise_prefix`, `e.ise_index`,
                          `e.ise_callee`] assume_tac) >>
  drule_all inline_edit_final_fetch >> simp[]
QED
