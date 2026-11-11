(* Contiguous ASSIGN*;JMP adapters survive surrounding compiler edits.
   Fields, rather than instruction records, abstract over renumbering. *)
Theory functionInlinerReturnAdapterLayout
Ancestors
  functionInlinerParameterLocations functionInlinerParameterPropagation
  functionInlinerReachableCuts functionInlinerLocation functionInlinerSiteLayout
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
