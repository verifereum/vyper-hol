(* Static parameter adapters paired with the selecting call incidence. *)
Theory functionInlinerSelectedParameters
Ancestors
  functionInlinerEntryParameters functionInlinerParameterLineage
  functionInlinerReachableCuts functionInlinerOccurrences callLayoutDefs
  functionInlinerDefs functionInlinerSiteLayout functionInlinerLocation venomInst list rich_list

Theorem inline_parameter_prefix_count:
  !params k j. param_insts_from k params /\ j <= LENGTH params ==>
    LENGTH (FILTER (\i. is_param_opcode i.inst_opcode) (TAKE j params)) = j
Proof
  Induct >> simp[param_insts_from_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `j` >> gvs[param_inst_at_def] >>
  first_x_assum drule >> simp[]
QED

Theorem inline_current_entry_parameter_counter:
  cb.bb_instructions = params ++ tail /\ param_insts_from 0 params /\
  j < LENGTH params /\
  j < LENGTH (rotate_invoke_ops (EL e.ise_index bb.bb_instructions).inst_operands) ==>
  SND (inline_cell_prefix e bb cb j) = j
Proof
  strip_tac >>
  `j <= LENGTH cb.bb_instructions` by simp[] >>
  `j <= LENGTH params /\ j - LENGTH params = 0` by decide_tac >>
  `LENGTH (FILTER (\i. is_param_opcode i.inst_opcode) (TAKE j params)) = j` by
    metis_tac[inline_parameter_prefix_count] >>
  drule inline_cell_prefix_counter >>
  disch_then (qspecl_then [`e`, `bb`] mp_tac) >>
  simp[TAKE_APPEND, inline_parameter_prefix_count, arithmeticTheory.MIN_DEF]
QED

Theorem inline_entry_parameter_emits:
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_caller a /\
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_callee b /\
  inline_site_edit_valid e /\
  (inline_entry_function b).fn_blocks = entry::rest /\
  entry.bb_instructions = params ++ tail /\ param_insts_from 0 params /\
  k < LENGTH params /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  k < LENGTH (rotate_invoke_ops (EL e.ise_index bb.bb_instructions).inst_operands) ==>
  ?cb ps post c mid.
    lookup_block entry.bb_label e.ise_callee.fn_blocks = SOME cb /\
    cb.bb_instructions = ps ++ post /\
    MAP inline_inst_fields ps = MAP inline_inst_fields params /\
    param_insts_from 0 ps /\
    c = inline_make_cell e.ise_callee entry.bb_label k
      (inline_inst_fields (EL k params)) /\
    inline_cell_frame (EnterCell e 0) c mid /\
    SND (inline_cell_prefix e bb cb k) = k /\
    mid.ic_fields =
      (ASSIGN, [EL k (rotate_invoke_ops
        (EL e.ise_index bb.bb_instructions).inst_operands)],
       MAP (STRCAT e.ise_prefix) (EL k params).inst_outputs)
Proof
  strip_tac >> drule_all inline_annotated_entry_parameter_prefix >> strip_tac >>
  rename1 `lookup_block entry.bb_label e.ise_callee.fn_blocks = SOME cb` >>
  `k < LENGTH ps` by metis_tac[LENGTH_MAP] >>
  `SND (inline_cell_prefix e bb cb k) = k` by
    metis_tac[inline_current_entry_parameter_counter] >>
  `inline_inst_fields (EL k cb.bb_instructions) = inline_inst_fields (EL k params)` by
    (simp[EL_APPEND_EQN] >> metis_tac[EL_MAP]) >>
  `is_param_opcode (EL k cb.bb_instructions).inst_opcode` by
    (drule_all param_insts_from_el >> simp[param_inst_at_def, EL_APPEND_EQN]) >>
  drule_all inline_annotated_edit_fetch_facts >> strip_tac >>
  `MEM entry.bb_label (fn_labels e.ise_callee)` by
    (simp[fn_labels_def, MEM_MAP] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM, venomExecPropsTheory.lookup_block_label]) >>
  qabbrev_tac `c = inline_make_cell e.ise_callee entry.bb_label k
    (inline_inst_fields (EL k params))` >>
  `inline_cell_at c` by
    (simp[Abbr `c`, inline_cell_at_def, inline_make_cell_def, inline_fetched_fields_def] >>
     qexists_tac `EL k cb.bb_instructions` >>
     simp[get_instruction_def]) >>
  `inline_cell_focus e bb cb k =
    ([(clone_instruction e.ise_prefix (fn_labels e.ise_callee)
       (EL k cb.bb_instructions)) with
       <|inst_opcode := ASSIGN; inst_operands := [EL k (rotate_invoke_ops
         (EL e.ise_index bb.bb_instructions).inst_operands)]|>],k+1)` by
    gvs[inline_cell_focus_def, rewrite_inline_inst_def, clone_instruction_def] >>
  `?mid. inline_cell_frame (EnterCell e 0) c mid` by
    (irule inline_enter_cell_produce >>
     simp[Abbr `c`, inline_make_cell_def] >> gvs[] >> metis_tac[]) >>
  qexistsl_tac [`cb`, `ps`, `post`, `c`, `mid`] >> simp[] >>
  qpat_x_assum `inline_cell_frame _ _ _` mp_tac >>
  simp[inline_cell_frame_def, Abbr `c`, inline_make_cell_def] >>
  rpt strip_tac >>
  gvs[inline_make_cell_def, inline_edit_repair_def, inline_inst_fields_def,
    clone_instruction_def] >> metis_tac[]
QED
