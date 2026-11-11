(* Contiguous ASSIGN*;JMP adapters survive surrounding compiler edits.
   Fields, rather than instruction records, abstract over renumbering. *)
Theory functionInlinerReturnAdapterLayout
Ancestors
  functionInlinerParameterLocations functionInlinerParameterPropagation
  functionInlinerReachableCuts functionInlinerLocation functionInlinerSiteLayout
  functionInlinerOccurrences functionInlinerActivation functionInlinerRoutedProvenance
  functionInlinerDefs functionInlinerFrame venomInst list rich_list

Definition inline_adapter_interval_def:
  inline_adapter_interval fn l start assigns target <=>
    EVERY (\fields. FST fields = ASSIGN) assigns /\
    ?bb. lookup_block l fn.fn_blocks = SOME bb /\
      start + LENGTH assigns + 1 <= LENGTH bb.bb_instructions /\
      MAP inline_inst_fields
        (TAKE (LENGTH assigns + 1) (DROP start bb.bb_instructions)) =
        assigns ++ [(JMP,[Label target],[])]
End

Theorem inline_adapter_focus_length:
  (EL j cb.bb_instructions).inst_opcode = ASSIGN \/
  (EL j cb.bb_instructions).inst_opcode = JMP ==>
  LENGTH (FST (inline_cell_focus e bb cb j)) = 1
Proof
  strip_tac >>
  gvs[inline_cell_focus_def, clone_instruction_def, rewrite_inline_inst_def,
      is_param_opcode_def]
QED

Theorem inline_adapter_prefix_length_suc:
  j < LENGTH cb.bb_instructions /\
  ((EL j cb.bb_instructions).inst_opcode = ASSIGN \/
   (EL j cb.bb_instructions).inst_opcode = JMP) ==>
  LENGTH (FST (inline_cell_prefix e bb cb (SUC j))) =
    SUC (LENGTH (FST (inline_cell_prefix e bb cb j)))
Proof
  strip_tac >> drule inline_cell_prefix_suc >>
  disch_then (qspecl_then [`e`, `bb`] assume_tac) >>
  simp[inline_adapter_focus_length]
QED

Theorem inline_adapter_prefix_length_interval:
  !count start.
  start + count <= LENGTH cb.bb_instructions /\
  (!k. k < count ==>
    (EL (start+k) cb.bb_instructions).inst_opcode = ASSIGN \/
    (EL (start+k) cb.bb_instructions).inst_opcode = JMP) ==>
  LENGTH (FST (inline_cell_prefix e bb cb (start+count))) =
    LENGTH (FST (inline_cell_prefix e bb cb start)) + count
Proof
  Induct >> simp[] >> qx_gen_tac `start` >> strip_tac >>
  rename1 `start + SUC n <= LENGTH cb.bb_instructions` >>
  `start + n < LENGTH cb.bb_instructions` by decide_tac >>
  `LENGTH (FST (inline_cell_prefix e bb cb (SUC (start+n)))) =
     SUC (LENGTH (FST (inline_cell_prefix e bb cb (start+n))))` by
    (irule inline_adapter_prefix_length_suc >> simp[arithmeticTheory.ADD_COMM]) >>
  qpat_x_assum `!start. _ /\ _ ==> LENGTH _ = _`
    (qspec_then `start` mp_tac) >>
  impl_tac >- (conj_tac >- decide_tac >> rpt strip_tac >> simp[]) >>
  strip_tac >> gvs[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD_COMM]
QED

Theorem inline_fields_slice_eq:
  start + LENGTH fields <= LENGTH bb.bb_instructions ==>
  (MAP inline_inst_fields
      (TAKE (LENGTH fields) (DROP start bb.bb_instructions)) = fields <=>
   (!k. k < LENGTH fields ==>
     inline_inst_fields (EL (start+k) bb.bb_instructions) = EL k fields))
Proof
  strip_tac >>
  simp[LIST_EQ_REWRITE, LENGTH_TAKE, LENGTH_DROP, EL_MAP,
       EL_TAKE, EL_DROP] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem inline_adapter_interval_points:
  inline_adapter_interval fn l start assigns target <=>
  EVERY (\fields. FST fields = ASSIGN) assigns /\
  ?bb. lookup_block l fn.fn_blocks = SOME bb /\
    start + LENGTH assigns + 1 <= LENGTH bb.bb_instructions /\
    (!k. k < LENGTH assigns + 1 ==>
      inline_fetched_fields fn l (start+k)
        (EL k (assigns ++ [(JMP,[Label target],[])])))
Proof
  simp[inline_adapter_interval_def, inline_fetched_fields_def,
       get_instruction_def] >>
  eq_tac >> strip_tac >> simp[] >>
  mp_tac (Q.INST [`fields` |-> `assigns ++ [(JMP,[Label target],[])]`]
    inline_fields_slice_eq) >> simp[] >>
  gvs[arithmeticTheory.ADD_COMM]
QED

Theorem inline_adapter_interval_class:
  inline_adapter_interval fn l start assigns target /\
  k < LENGTH assigns + 1 /\
  inline_fetched_fields fn l (start+k) fields ==>
  FST fields = ASSIGN \/ FST fields = JMP
Proof
  simp[inline_adapter_interval_points] >> strip_tac >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[] >>
  gvs[inline_fetched_fields_def, get_instruction_def] >> strip_tac >>
  Cases_on `k < LENGTH assigns` >> gvs[EL_APPEND_EQN] >-
    (gvs[EVERY_EL] >> metis_tac[]) >>
  `k = LENGTH assigns` by decide_tac >> gvs[]
QED

Theorem inline_adapter_interval_fetched:
  inline_adapter_interval fn l start assigns target /\ k < LENGTH assigns + 1 ==>
  inline_fetched_fields fn l (start+k)
    (EL k (assigns ++ [(JMP,[Label target],[])]))
Proof
  simp[inline_adapter_interval_points] >> metis_tac[]
QED

Theorem inline_adapter_excludes_split:
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  (EL e.ise_index source_bb.bb_instructions).inst_opcode = INVOKE /\
  inline_adapter_interval e.ise_caller l start assigns target ==>
  l = e.ise_block ==> !i. i < LENGTH assigns + 1 ==>
    start+i <> e.ise_index
Proof
  rpt strip_tac >>
  `?fields. inline_fetched_fields e.ise_caller l (start+i) fields /\
    (FST fields = ASSIGN \/ FST fields = JMP)` by
    (qexists `EL i (assigns ++ [(JMP,[Label target],[])])` >>
     conj_asm1_tac >- (irule inline_adapter_interval_fetched >> simp[]) >>
     irule inline_adapter_interval_class >> metis_tac[]) >>
  gvs[inline_fetched_fields_def, get_instruction_def, inline_inst_fields_def]
QED

Theorem inline_adapter_keep_points:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  e.ise_index < LENGTH source_bb.bb_instructions /\
  (EL e.ise_index source_bb.bb_instructions).inst_opcode = INVOKE /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  inline_adapter_interval e.ise_caller l start assigns target ==>
  !k fields. k < LENGTH assigns + 1 /\
    inline_fetched_fields e.ise_caller l (start+k) fields ==>
    inline_fetched_fields e.ise_final
      (FST (inline_keep_boundary e l start))
      (SND (inline_keep_boundary e l start)+k) fields
Proof
  strip_tac >>
  `l = e.ise_block ==> !i. i < LENGTH assigns + 1 ==>
     start+i <> e.ise_index` by
    (metis_tac[inline_adapter_excludes_split]) >>
  rpt strip_tac >>
  `inline_cell_at (inline_make_cell e.ise_caller l (start+k) fields)` by
    gvs[inline_cell_at_def, inline_make_cell_def] >>
  `?d. inline_cell_frame (KeepCell e)
    (inline_make_cell e.ise_caller l (start+k) fields) d` by
    (irule inline_keep_cell_produce >> simp[inline_make_cell_def] >> gvs[]) >>
  `d.ic_block = FST (inline_keep_boundary e l start) /\
   d.ic_index = SND (inline_keep_boundary e l start)+k` by
    (irule inline_keep_parameter_interval_cell >>
     conj_tac >- (qexists `LENGTH assigns + 1` >> simp[]) >>
     qexists `inline_make_cell e.ise_caller l (start+k) fields` >>
     simp[inline_make_cell_def]) >>
  `FST fields = ASSIGN \/ FST fields = JMP` by
    (irule inline_adapter_interval_class >> metis_tac[]) >>
  `d.ic_fields = fields /\ d.ic_function = e.ise_final` by
    (qpat_x_assum `inline_cell_frame _ _ _` mp_tac >>
     simp[inline_cell_frame_def, inline_make_cell_def] >> rpt strip_tac >>
     gvs[inline_edit_repair_def, inline_inst_fields_def]) >>
  drule inline_cell_frame_sound >> simp[inline_cell_at_def]
QED

Theorem inline_adapter_keep_transport:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  e.ise_index < LENGTH source_bb.bb_instructions /\
  (EL e.ise_index source_bb.bb_instructions).inst_opcode = INVOKE /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  inline_adapter_interval e.ise_caller l start assigns target ==>
  inline_adapter_interval e.ise_final
    (FST (inline_keep_boundary e l start))
    (SND (inline_keep_boundary e l start)) assigns target
Proof
  strip_tac >>
  `l = e.ise_block ==> !i. i < LENGTH assigns + 1 ==>
     start+i <> e.ise_index` by
    (metis_tac[inline_adapter_excludes_split]) >>
  `inline_keep_boundary e l (start+(LENGTH assigns+1)) =
    (FST (inline_keep_boundary e l start),
     SND (inline_keep_boundary e l start)+(LENGTH assigns+1))` by
    (Cases_on `l = e.ise_block` >-
      (irule inline_keep_boundary_interval >> qexists `LENGTH assigns + 1` >>
       gvs[arithmeticTheory.ADD_COMM]) >>
     simp[inline_keep_boundary_def]) >>
  `inline_parameter_boundary (InlineKeep e) e.ise_caller l
    (start+(LENGTH assigns+1)) e.ise_final
    (FST (inline_keep_boundary e l (start+(LENGTH assigns+1))))
    (SND (inline_keep_boundary e l (start+(LENGTH assigns+1))))` by
    (irule inline_keep_boundary_produce >>
     gvs[inline_adapter_interval_def]) >>
  simp[inline_adapter_interval_points] >>
  conj_tac >- gvs[inline_adapter_interval_def] >>
  qpat_x_assum `inline_parameter_boundary _ _ _ _ _ _ _` mp_tac >>
  simp[inline_parameter_boundary_def] >> strip_tac >>
  qexists `tb` >> simp[] >> rpt strip_tac >>
  irule (SRULE [arithmeticTheory.ADD_COMM] inline_adapter_keep_points) >>
  simp[] >> conj_tac >-
    (irule (SRULE [arithmeticTheory.ADD_COMM] inline_adapter_interval_fetched) >>
     simp[]) >> metis_tac[]
QED

Definition inline_adapter_clone_fields_def:
  inline_adapter_clone_fields p labels (opc,ops,outs) =
    (opc, MAP (clone_operand p labels) ops, MAP (STRCAT p) outs)
End

Theorem inline_adapter_enter_points:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  lookup_block l e.ise_callee.fn_blocks = SOME cb /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  ~MEM (STRCAT e.ise_prefix l) (fn_labels e.ise_caller) /\
  STRCAT e.ise_prefix l <> e.ise_return /\
  start+n <= LENGTH cb.bb_instructions /\
  (!i. i < n ==> (EL (start+i) cb.bb_instructions).inst_opcode = ASSIGN \/
                  (EL (start+i) cb.bb_instructions).inst_opcode = JMP) ==>
  !k fields. k < n /\ inline_fetched_fields e.ise_callee l (start+k) fields ==>
    inline_fetched_fields e.ise_final (STRCAT e.ise_prefix l)
      (LENGTH (FST (inline_cell_prefix e bb cb start))+k)
      (inline_adapter_clone_fields e.ise_prefix (fn_labels e.ise_callee) fields)
Proof
  strip_tac >> rpt strip_tac >>
  `inline_cell_at (inline_make_cell e.ise_callee l (start+k) fields)` by
    gvs[inline_cell_at_def, inline_make_cell_def] >>
  `LENGTH (FST (inline_cell_focus e bb cb (start+k))) = 1` by
    (irule inline_adapter_focus_length >> simp[]) >>
  `?d. inline_cell_frame (EnterCell e 0)
    (inline_make_cell e.ise_callee l (start+k) fields) d` by
    (irule inline_enter_cell_produce >> simp[inline_make_cell_def] >> gvs[]) >>
  `LENGTH (FST (inline_cell_prefix e bb cb (start+k))) =
    LENGTH (FST (inline_cell_prefix e bb cb start))+k` by
    (irule inline_adapter_prefix_length_interval >>
     reverse conj_tac >- decide_tac >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `(EL (start+k) cb.bb_instructions).inst_opcode = ASSIGN \/
   (EL (start+k) cb.bb_instructions).inst_opcode = JMP` by simp[] >>
  drule inline_cell_frame_sound >>
  qpat_x_assum `inline_cell_frame _ _ _` mp_tac >>
  simp[inline_cell_frame_def, inline_make_cell_def] >> rpt strip_tac >>
  gvs[inline_cell_at_def, inline_make_cell_def, inline_fetched_fields_def, get_instruction_def] >>
  gvs[inline_cell_focus_def, clone_instruction_def, rewrite_inline_inst_def,
      is_param_opcode_def, inline_edit_repair_def, inline_inst_fields_def,
      inline_adapter_clone_fields_def, SF ETA_ss]
QED

Theorem inline_adapter_interval_opcodes:
  inline_adapter_interval fn l start assigns target /\
  lookup_block l fn.fn_blocks = SOME cb ==>
  start + (LENGTH assigns+1) <= LENGTH cb.bb_instructions /\
  (!k. k < LENGTH assigns+1 ==>
    (EL (start+k) cb.bb_instructions).inst_opcode = ASSIGN \/
    (EL (start+k) cb.bb_instructions).inst_opcode = JMP)
Proof
  strip_tac >> conj_tac >- gvs[inline_adapter_interval_def] >>
  rpt strip_tac >>
  `inline_fetched_fields fn l (start+k)
    (inline_inst_fields (EL (start+k) cb.bb_instructions))` by
    (simp[inline_fetched_fields_def, get_instruction_def] >>
     gvs[inline_adapter_interval_def]) >>
  drule_all inline_adapter_interval_class >> simp[inline_inst_fields_def]
QED

Theorem inline_adapter_clone_opcode[simp]:
  FST (inline_adapter_clone_fields p labels fields) = FST fields
Proof
  PairCases_on `fields` >> simp[inline_adapter_clone_fields_def]
QED

Theorem inline_adapter_enter_transport:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  lookup_block l e.ise_callee.fn_blocks = SOME cb /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  ~MEM (STRCAT e.ise_prefix l) (fn_labels e.ise_caller) /\
  STRCAT e.ise_prefix l <> e.ise_return /\
  MEM target (fn_labels e.ise_callee) /\
  inline_adapter_interval e.ise_callee l start assigns target ==>
  inline_adapter_interval e.ise_final (STRCAT e.ise_prefix l)
    (LENGTH (FST (inline_cell_prefix e bb cb start)))
    (MAP (inline_adapter_clone_fields e.ise_prefix (fn_labels e.ise_callee)) assigns)
    (STRCAT e.ise_prefix target)
Proof
  strip_tac >> drule_all inline_adapter_interval_opcodes >> strip_tac >>
  `LENGTH (FST (inline_cell_prefix e bb cb (start+(LENGTH assigns+1)))) =
   LENGTH (FST (inline_cell_prefix e bb cb start))+(LENGTH assigns+1)` by
    (irule inline_adapter_prefix_length_interval >> simp[]) >>
  `inline_parameter_boundary (InlineEnter e) e.ise_callee l
    (start+(LENGTH assigns+1)) e.ise_final (STRCAT e.ise_prefix l)
    (LENGTH (FST (inline_cell_prefix e bb cb (start+(LENGTH assigns+1)))))` by
    (irule inline_enter_boundary_produce >> simp[]) >>
  simp[inline_adapter_interval_points] >> conj_tac >-
    gvs[inline_adapter_interval_def, EVERY_MAP] >>
  qpat_x_assum `inline_parameter_boundary _ _ _ _ _ _ _` mp_tac >>
  simp[inline_parameter_boundary_def] >> strip_tac >>
  qexists `tb` >> simp[] >> rpt strip_tac >>
  `EL k (MAP (inline_adapter_clone_fields e.ise_prefix (fn_labels e.ise_callee))
     assigns ++ [(JMP,[Label (STRCAT e.ise_prefix target)],[])]) =
   inline_adapter_clone_fields e.ise_prefix (fn_labels e.ise_callee)
     (EL k (assigns ++ [(JMP,[Label target],[])]))` by
    (Cases_on `k < LENGTH assigns` >>
     simp[EL_APPEND_EQN, EL_MAP, inline_adapter_clone_fields_def, clone_operand_def] >>
     `k = LENGTH assigns` by decide_tac >>
     simp[inline_adapter_clone_fields_def, clone_operand_def]) >>
  simp[] >> irule (SRULE [arithmeticTheory.ADD_COMM] inline_adapter_enter_points) >>
  simp[] >> conj_tac >-
    (qexists `LENGTH assigns+1` >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  irule (SRULE [arithmeticTheory.ADD_COMM] inline_adapter_interval_fetched) >> simp[]
QED

(* Entry labels survive even when the first instruction is selected later.
   This is deliberately not a statement about the cell at index zero. *)
Theorem inline_adapter_choice_label:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  ((choice = InlineKeep e /\ fn = e.ise_caller) \/
   (choice = InlineEnter e /\ fn = e.ise_callee)) /\
  MEM l (fn_labels fn) ==>
  MEM (inline_choice_rename choice l) (fn_labels e.ise_final)
Proof
  strip_tac >> drule inline_edit_final_labels >> simp[] >>
  drule functionInlinerWfTheory.inline_call_site_labels >>
  disch_then (qspecl_then [`e.ise_callee`, `e.ise_prefix`, `e.ise_return`,
    `e.ise_index`] assume_tac) >>
  gvs[inline_choice_rename_def, MEM_MAP] >> metis_tac[]
QED

Theorem inline_adapter_path_label:
  !path fn root l.
  inline_annotated_choice_path ctx path fn root /\ MEM l (fn_labels fn) ==>
  MEM (inline_path_rename path l) (fn_labels root)
Proof
  Induct >> simp[inline_annotated_choice_path_def, inline_path_rename_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all inline_annotated_edit_fetch_facts >> strip_tac >>
  first_x_assum irule >> simp[] >>
  metis_tac[inline_adapter_choice_label]
QED

Definition inline_adapter_choice_fields_def:
  (inline_adapter_choice_fields (InlineKeep e) fields = fields) /\
  (inline_adapter_choice_fields (InlineEnter e) fields =
    inline_adapter_clone_fields e.ise_prefix (fn_labels e.ise_callee) fields)
End

Theorem inline_adapter_choice_fields_functions[simp]:
  inline_adapter_choice_fields (InlineKeep e) = I /\
  inline_adapter_choice_fields (InlineEnter e) =
    inline_adapter_clone_fields e.ise_prefix (fn_labels e.ise_callee)
Proof
  simp[FUN_EQ_THM, inline_adapter_choice_fields_def]
QED

Definition inline_adapter_path_fields_def:
  (inline_adapter_path_fields [] fields = fields) /\
  (inline_adapter_path_fields (choice::rest) fields =
    inline_adapter_path_fields rest (MAP (inline_adapter_choice_fields choice) fields))
End

Theorem inline_adapter_choice_transport:
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_caller a /\
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_callee b /\
  inline_site_edit_valid e /\
  ((choice = InlineKeep e /\ fn = e.ise_caller) \/
   (choice = InlineEnter e /\ fn = e.ise_callee)) /\
  MEM target (fn_labels fn) /\
  inline_adapter_interval fn l start assigns target ==>
  ?ml mj.
    inline_adapter_interval e.ise_final ml mj
      (MAP (inline_adapter_choice_fields choice) assigns)
      (inline_choice_rename choice target) /\
    inline_parameter_boundary choice fn l start e.ise_final ml mj
Proof
  strip_tac >> drule_all inline_annotated_edit_fetch_facts >> strip_tac >>
  `(EL e.ise_index bb.bb_instructions).inst_opcode = INVOKE` by
    (`ALL_DISTINCT (fn_labels e.ise_caller)` by
       metis_tac[inline_annotated_origin_labels] >>
     gvs[inline_site_edit_valid_def] >>
     drule_all functionInlinerWfTheory.find_invoke_site_lookup >> gvs[]) >>
  gvs[]
  >- (qexistsl [`FST (inline_keep_boundary e l start)`,
               `SND (inline_keep_boundary e l start)`] >>
      simp[inline_adapter_choice_fields_def, inline_choice_rename_def,
           MAP_ID] >>
      conj_tac >- (irule inline_adapter_keep_transport >> metis_tac[]) >>
      irule inline_keep_boundary_produce >> gvs[inline_adapter_interval_def]) >>
  `?cb. lookup_block l e.ise_callee.fn_blocks = SOME cb /\
    start+(LENGTH assigns+1) <= LENGTH cb.bb_instructions` by
    gvs[inline_adapter_interval_def] >>
  `MEM l (fn_labels e.ise_callee)` by
    (simp[fn_labels_def, MEM_MAP] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM,
               venomExecPropsTheory.lookup_block_label]) >>
  first_x_assum (drule_then strip_assume_tac) >>
  qexistsl [`STRCAT e.ise_prefix l`,
            `LENGTH (FST (inline_cell_prefix e bb cb start))`] >>
  simp[inline_adapter_choice_fields_def, inline_choice_rename_def] >>
  conj_tac >- (irule inline_adapter_enter_transport >> metis_tac[]) >>
  irule inline_enter_boundary_produce >> simp[]
QED

Theorem inline_adapter_path_transport:
  !path fn root l start assigns target.
  inline_annotated_choice_path ctx path fn root /\
  MEM target (fn_labels fn) /\
  inline_adapter_interval fn l start assigns target ==>
  ?ml mj.
    inline_adapter_interval root ml mj (inline_adapter_path_fields path assigns)
      (inline_path_rename path target) /\
    inline_parameter_boundary_path path fn l start root ml mj /\
    MEM (inline_path_rename path target) (fn_labels root)
Proof
  Induct >-
    simp[inline_annotated_choice_path_def, inline_adapter_path_fields_def,
         inline_path_rename_def, inline_parameter_boundary_path_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `inline_annotated_choice_path _ _ _ _` mp_tac >>
  simp[inline_annotated_choice_path_def] >> strip_tac >>
  `?il ij. inline_adapter_interval e.ise_final il ij
      (MAP (inline_adapter_choice_fields h) assigns) (inline_choice_rename h target) /\
    inline_parameter_boundary h fn l start e.ise_final il ij` by
    metis_tac[inline_adapter_choice_transport] >>
  `MEM (inline_choice_rename h target) (fn_labels e.ise_final)` by
    (drule_all inline_annotated_edit_fetch_facts >> strip_tac >>
     metis_tac[inline_adapter_choice_label]) >>
  first_x_assum drule >> disch_then drule >> disch_then drule >> strip_tac >>
  qexistsl [`ml`,`mj`] >>
  simp[inline_adapter_path_fields_def, inline_path_rename_def,
       inline_parameter_boundary_path_def] >> metis_tac[]
QED
