(* Static cell expansion. No target fetch or execution in frame generation. *)
Theory functionInlinerReachableCuts
Ancestors
  functionInlinerLocation functionInlinerStackSupports functionInlinerActivation
  functionInlinerSiteLayout functionInlinerDefs venomInst list rich_list

Datatype:
  inline_cell = <| ic_function : ir_function; ic_block : string;
                   ic_index : num; ic_fields : opcode # operand list # string list |>
End

Datatype:
  inline_cell_frame = KeepCell inline_site_edit
                    | SelectedJump inline_site_edit
                    | EnterCell inline_site_edit num
End

Definition inline_cell_at_def:
  inline_cell_at c <=>
    inline_fetched_fields c.ic_function c.ic_block c.ic_index c.ic_fields
End

Definition inline_make_cell_def:
  inline_make_cell fn l j fields =
    <|ic_function := fn; ic_block := l; ic_index := j; ic_fields := fields|>
End

(* The prefix and focus are computed anew from the CURRENT source block. *)
Definition inline_cell_prefix_def:
  inline_cell_prefix e bb cb j =
    rewrite_inline_insts
      (rotate_invoke_ops (EL e.ise_index bb.bb_instructions).inst_operands)
      (EL e.ise_index bb.bb_instructions).inst_outputs e.ise_return
      (MAP (clone_instruction e.ise_prefix (fn_labels e.ise_callee))
        (TAKE j cb.bb_instructions)) 0
End

Definition inline_cell_focus_def:
  inline_cell_focus e bb cb j =
    rewrite_inline_inst
      (rotate_invoke_ops (EL e.ise_index bb.bb_instructions).inst_operands)
      (EL e.ise_index bb.bb_instructions).inst_outputs e.ise_return
      (clone_instruction e.ise_prefix (fn_labels e.ise_callee)
        (EL j cb.bb_instructions)) (SND (inline_cell_prefix e bb cb j))
End

Definition inline_cell_frame_def:
  (inline_cell_frame (KeepCell e) c d <=>
    inline_site_edit_valid e /\ c.ic_function = e.ise_caller /\
    ~MEM e.ise_return (fn_labels e.ise_caller) /\
    ?source_bb bb inst.
      lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
      e.ise_index < LENGTH source_bb.bb_instructions /\
      lookup_block c.ic_block e.ise_caller.fn_blocks = SOME bb /\
      get_instruction bb c.ic_index = SOME inst /\
      c.ic_fields = inline_inst_fields inst /\
      (c.ic_block <> e.ise_block \/ c.ic_index <> e.ise_index) /\
      d = inline_make_cell e.ise_final
        (if c.ic_block = e.ise_block /\ e.ise_index < c.ic_index
         then e.ise_return else c.ic_block)
        (if c.ic_block = e.ise_block /\ e.ise_index < c.ic_index
         then c.ic_index - (e.ise_index+1) else c.ic_index)
        (inline_inst_fields (inline_edit_repair e source_bb
          (if c.ic_block = e.ise_block /\ e.ise_index < c.ic_index
           then e.ise_return else bb.bb_label) inst))) /\
  (inline_cell_frame (SelectedJump e) c d <=>
    inline_site_edit_valid e /\ c.ic_function = e.ise_caller /\
    c.ic_block = e.ise_block /\ c.ic_index = e.ise_index /\
    ~MEM e.ise_return (fn_labels e.ise_caller) /\
    ?bb inst. lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
      get_instruction bb e.ise_index = SOME inst /\
      c.ic_fields = inline_inst_fields inst /\
      d = inline_make_cell e.ise_final e.ise_block e.ise_index
        (JMP, [Label (case (clone_function e.ise_prefix e.ise_callee).fn_blocks of
                       [] => "" | eb::_ => eb.bb_label)], [])) /\
  (inline_cell_frame (EnterCell e k) c d <=>
    inline_site_edit_valid e /\ c.ic_function = e.ise_callee /\
    ~MEM e.ise_return (fn_labels e.ise_caller) /\
    ~MEM (STRCAT e.ise_prefix c.ic_block) (fn_labels e.ise_caller) /\
    STRCAT e.ise_prefix c.ic_block <> e.ise_return /\
    ?bb cb inst.
      lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
      lookup_block c.ic_block e.ise_callee.fn_blocks = SOME cb /\
      get_instruction cb c.ic_index = SOME inst /\
      c.ic_fields = inline_inst_fields inst /\
      k < LENGTH (FST (inline_cell_focus e bb cb c.ic_index)) /\
      d = inline_make_cell e.ise_final (STRCAT e.ise_prefix c.ic_block)
        (LENGTH (FST (inline_cell_prefix e bb cb c.ic_index)) + k)
        (inline_inst_fields (inline_edit_repair e bb (STRCAT e.ise_prefix c.ic_block)
          (EL k (FST (inline_cell_focus e bb cb c.ic_index))))))
End

Theorem inline_cell_frame_source:
  inline_cell_frame tag c d ==> inline_cell_at c
Proof
  Cases_on `tag` >>
  simp[inline_cell_frame_def, inline_cell_at_def, inline_fetched_fields_def] >>
  metis_tac[]
QED

Theorem inline_cell_frame_sound:
  inline_cell_frame tag c d ==> inline_cell_at d
Proof
  Cases_on `tag` >>
  simp[inline_cell_frame_def, inline_cell_at_def, inline_make_cell_def] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `c.ic_block = i.ise_block` >> gvs[]
      >- (gvs[get_instruction_def] >>
          Cases_on `i.ise_index < c.ic_index` >> gvs[]
          >- (irule inline_edit_suffix_fetch >> simp[]) >>
          irule inline_edit_prefix_fetch >> simp[]) >>
      irule inline_edit_other_fetch >> metis_tac[])
  >- (irule inline_edit_selected_jump >> gvs[get_instruction_def]) >>
  `c.ic_index < LENGTH cb.bb_instructions` by gvs[get_instruction_def] >>
  drule_all inline_edit_enter_focus_fetch >>
  simp[inline_cell_prefix_def, inline_cell_focus_def, LET_THM,
       get_instruction_def] >>
  gvs[inline_cell_prefix_def, inline_cell_focus_def]
QED

(* Frames retain their emitted cell, so outer edits consume this cell rather
   than re-expanding the original instruction. *)
Definition inline_cell_zipper_def:
  (inline_cell_zipper c [] d <=> d = c) /\
  (inline_cell_zipper c ((tag,next)::rest) d <=>
    inline_cell_frame tag c next /\ inline_cell_zipper next rest d)
End

Theorem inline_cell_zipper_identity[simp]:
  inline_cell_zipper c [] d <=> d = c
Proof simp[inline_cell_zipper_def]
QED

Theorem inline_cell_zipper_append:
  !xs c ys d. inline_cell_zipper c (xs ++ ys) d <=>
    ?mid. inline_cell_zipper c xs mid /\ inline_cell_zipper mid ys d
Proof
  Induct >> simp[inline_cell_zipper_def] >>
  Cases_on `h` >> simp[inline_cell_zipper_def] >> metis_tac[]
QED

Theorem inline_cell_zipper_sound:
  !frames c d. inline_cell_at c /\ inline_cell_zipper c frames d ==>
    inline_cell_at d
Proof
  Induct >> simp[inline_cell_zipper_def] >>
  Cases_on `h` >> simp[inline_cell_zipper_def] >>
  metis_tac[inline_cell_frame_sound]
QED

Theorem inline_cell_zipper_last:
  inline_cell_zipper c (frames ++ [(tag,d)]) out <=>
    out = d /\ ?mid. inline_cell_zipper c frames mid /\ inline_cell_frame tag mid d
Proof
  simp[inline_cell_zipper_append, inline_cell_zipper_def] >> metis_tac[]
QED

Theorem inline_keep_cell_produce:
  inline_site_edit_valid e /\ c.ic_function = e.ise_caller /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  e.ise_index < LENGTH source_bb.bb_instructions /\ inline_cell_at c /\
  (c.ic_block <> e.ise_block \/ c.ic_index <> e.ise_index) ==>
  ?d. inline_cell_frame (KeepCell e) c d
Proof
  simp[inline_cell_at_def, inline_fetched_fields_def, inline_cell_frame_def] >>
  metis_tac[]
QED

Theorem inline_selected_cell_produce:
  inline_site_edit_valid e /\ c.ic_function = e.ise_caller /\
  c.ic_block = e.ise_block /\ c.ic_index = e.ise_index /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\ inline_cell_at c ==>
  ?d. inline_cell_frame (SelectedJump e) c d
Proof
  simp[inline_cell_at_def, inline_fetched_fields_def, inline_cell_frame_def] >>
  metis_tac[]
QED

Theorem inline_enter_cell_produce:
  inline_site_edit_valid e /\ c.ic_function = e.ise_callee /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  ~MEM (STRCAT e.ise_prefix c.ic_block) (fn_labels e.ise_caller) /\
  STRCAT e.ise_prefix c.ic_block <> e.ise_return /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  lookup_block c.ic_block e.ise_callee.fn_blocks = SOME cb /\
  inline_cell_at c /\ k < LENGTH (FST (inline_cell_focus e bb cb c.ic_index)) ==>
  ?d. inline_cell_frame (EnterCell e k) c d
Proof
  simp[inline_cell_at_def, inline_fetched_fields_def, inline_cell_frame_def] >>
  metis_tac[optionTheory.SOME_11]
QED

Theorem inline_cell_prefix_zero[simp]:
  inline_cell_prefix e bb cb 0 = ([],0)
Proof simp[inline_cell_prefix_def, rewrite_inline_insts_def]
QED

(* Exhausting the chosen source cell advances both offset AND parameter counter. *)
Theorem inline_cell_prefix_suc:
  j < LENGTH cb.bb_instructions ==>
  inline_cell_prefix e bb cb (SUC j) =
    (FST (inline_cell_prefix e bb cb j) ++ FST (inline_cell_focus e bb cb j),
     SND (inline_cell_focus e bb cb j))
Proof
  strip_tac >>
  simp[inline_cell_prefix_def, inline_cell_focus_def, TAKE_SUC_BY_TAKE,
       SNOC_APPEND, MAP_APPEND, rewrite_inline_insts_append,
       rewrite_inline_insts_def, LET_THM] >>
  pairarg_tac >> simp[]
QED

Definition inline_cell_location_def:
  inline_cell_location c counter =
    <|il_block := c.ic_block; il_phase := InlineAtInstruction c.ic_index;
      il_counter := counter|>
End

Theorem inline_keep_cell_projection:
  inline_cell_frame (KeepCell e) c d ==>
  inline_choice_location (InlineKeep e) (inline_cell_location c counter) =
    SOME (inline_cell_location d counter)
Proof
  simp[inline_cell_frame_def, inline_cell_location_def,
       inline_make_cell_def, inline_choice_location_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `c.ic_block = e.ise_block` >> simp[]
QED

Theorem inline_enter_cell_projection:
  inline_cell_frame (EnterCell e 0) c d /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  lookup_block c.ic_block e.ise_callee.fn_blocks = SOME cb /\
  e.ise_index < LENGTH bb.bb_instructions ==>
  inline_choice_location (InlineEnter e) (inline_cell_location c counter) =
    SOME (inline_cell_location d (SND (inline_cell_prefix e bb cb c.ic_index)))
Proof
  simp[inline_cell_frame_def, inline_cell_location_def,
       inline_make_cell_def, inline_choice_location_def] >>
  rpt strip_tac >> gvs[get_instruction_def, inline_cell_prefix_def]
QED

(* PHIs remain a batch boundary; this projection makes no operand reads. *)
Definition inline_before_phi_location_def:
  inline_before_phi_location l counter =
    <|il_block := l; il_phase := InlineBeforePhi; il_counter := counter|>
End

Theorem inline_before_phi_keep:
  inline_choice_location (InlineKeep e) (inline_before_phi_location l counter) =
    SOME (inline_before_phi_location l counter)
Proof simp[inline_before_phi_location_def, inline_choice_location_def]
QED

Theorem inline_before_phi_enter:
  inline_choice_location (InlineEnter e) (inline_before_phi_location l counter) =
    SOME (inline_before_phi_location (STRCAT e.ise_prefix l) counter)
Proof simp[inline_before_phi_location_def, inline_choice_location_def]
QED

Theorem inline_enter_cell_last_offset:
  inline_cell_zipper c (frames ++ [(EnterCell e k,d)]) out ==>
  ?mid bb cb inst.
    out = d /\ inline_cell_zipper c frames mid /\
    lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
    lookup_block mid.ic_block e.ise_callee.fn_blocks = SOME cb /\
    get_instruction cb mid.ic_index = SOME inst /\
    mid.ic_fields = inline_inst_fields inst /\
    k < LENGTH (FST (inline_cell_focus e bb cb mid.ic_index)) /\
    d.ic_index = LENGTH (FST (inline_cell_prefix e bb cb mid.ic_index)) + k /\
    d.ic_block = STRCAT e.ise_prefix mid.ic_block /\
    d.ic_function = e.ise_final
Proof
  simp[inline_cell_zipper_last, inline_cell_frame_def, inline_make_cell_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Datatype:
  inline_cell_phase = <| icp_source : inline_cell;
    icp_frames : (inline_cell_frame # inline_cell) list;
    icp_current : inline_cell |>
End

Definition inline_cell_phase_valid_def:
  inline_cell_phase_valid phase <=>
    inline_cell_at phase.icp_source /\
    inline_cell_zipper phase.icp_source phase.icp_frames phase.icp_current
End

Theorem inline_cell_phase_fetch:
  inline_cell_phase_valid phase ==> inline_cell_at phase.icp_current
Proof
  metis_tac[inline_cell_phase_valid_def, inline_cell_zipper_sound]
QED

Theorem inline_cell_phase_extend:
  inline_cell_phase_valid phase /\ inline_cell_frame tag phase.icp_current next ==>
  inline_cell_phase_valid
    (phase with <|icp_frames := phase.icp_frames ++ [(tag,next)];
                  icp_current := next|>)
Proof
  simp[inline_cell_phase_valid_def, inline_cell_zipper_append,
       inline_cell_zipper_def] >> metis_tac[]
QED

(* Ordinary cells are never expanded into adapters; each Enter contributes
   exactly one clone and each Keep preserves the current fields. *)
Theorem inline_cell_frame_ordinary_fields:
  inline_cell_frame tag c d /\ c.ic_fields = inline_inst_fields src /\
  ~MEM src.inst_opcode [PHI; PARAM; FMP_PARAM; RETPC_PARAM; RET; RETFMP] /\
  (!e. tag <> SelectedJump e) ==>
  d.ic_fields = inline_inst_fields
    (case tag of EnterCell e k => clone_instruction e.ise_prefix
                   (fn_labels e.ise_callee) src | _ => src)
Proof
  Cases_on `tag` >>
  simp[inline_cell_frame_def, inline_make_cell_def] >> rpt strip_tac >> gvs[]
  >- (gvs[inline_edit_repair_def, inline_inst_fields_def] >>
      Cases_on `inst` >> Cases_on `src` >> gvs[inline_inst_fields_def]) >>
  gvs[inline_cell_focus_def, rewrite_inline_inst_def,
      clone_instruction_def, is_param_opcode_def,
      inline_inst_fields_def, get_instruction_def] >>
  gvs[inline_edit_repair_def, inline_inst_fields_def, is_param_opcode_iff]
QED

Theorem inline_cell_zipper_ordinary_fields:
  !frames c d src.
  inline_cell_zipper c frames d /\ c.ic_fields = inline_inst_fields src /\
  ~MEM src.inst_opcode [PHI; PARAM; FMP_PARAM; RETPC_PARAM; RET; RETFMP] /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames ==>
  d.ic_fields = inline_inst_fields
    (FOLDL (\inst (tag,next). case tag of
       EnterCell e k => clone_instruction e.ise_prefix (fn_labels e.ise_callee) inst
     | _ => inst) src frames)
Proof
  Induct >> simp[inline_cell_zipper_def] >>
  qx_gen_tac `h` >> PairCases_on `h` >>
  simp[inline_cell_zipper_def] >> rpt strip_tac >>
  `h1.ic_fields = inline_inst_fields
     (case h0 of EnterCell e k =>
        clone_instruction e.ise_prefix (fn_labels e.ise_callee) src | _ => src)` by
    (irule inline_cell_frame_ordinary_fields >> simp[] >> metis_tac[]) >>
  first_x_assum irule >> simp[] >>
  Cases_on `h0` >> gvs[clone_instruction_def] >> metis_tac[]
QED
