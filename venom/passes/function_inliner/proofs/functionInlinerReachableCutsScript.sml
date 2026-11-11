(* Static cell expansion. No target fetch or execution in frame generation. *)
Theory functionInlinerReachableCuts
Ancestors
  functionInlinerLocation functionInlinerStackSupports functionInlinerActivation
  functionInlinerOccurrences functionInlinerRoutedProvenance
  functionInlinerSiteLayout functionInlinerDefs functionInlinerFrame venomInst list rich_list

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

(* All emitted prefix offsets and parameter counters are generated from zero,
   including empty expansions and multi-instruction return adapters. *)
Theorem inline_cell_prefix_positions:
  !j. j <= LENGTH cb.bb_instructions ==>
  inline_cell_prefix e bb cb j =
    FOLDL (\pre n.
      (FST pre ++ FST (inline_cell_focus e bb cb n),
       SND (inline_cell_focus e bb cb n))) ([],0) (GENLIST I j)
Proof
  Induct >> simp[GENLIST, FOLDL_SNOC] >> strip_tac >>
  rw[inline_cell_prefix_suc] >> gvs[]
QED

Theorem inline_cell_zipper_ordinary_fetch:
  inline_cell_at c /\ inline_cell_zipper c frames d /\
  c.ic_fields = inline_inst_fields src /\
  ~MEM src.inst_opcode [PHI; PARAM; FMP_PARAM; RETPC_PARAM; RET; RETFMP] /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames ==>
  inline_fetched_fields d.ic_function d.ic_block d.ic_index
    (inline_inst_fields
      (FOLDL (\inst (tag,next). case tag of
         EnterCell e k => clone_instruction e.ise_prefix (fn_labels e.ise_callee) inst
       | _ => inst) src frames))
Proof
  strip_tac >> drule_all inline_cell_zipper_ordinary_fields >>
  drule_all inline_cell_zipper_sound >> simp[inline_cell_at_def] >> metis_tac[]
QED

Theorem inline_before_phi_keep_path:
  !path. EVERY (\c. ?e. c = InlineKeep e) path ==>
  inline_path_location path (SOME (inline_before_phi_location l counter)) =
    SOME (inline_before_phi_location l counter)
Proof
  Induct >> simp[inline_path_location_def] >> rpt strip_tac >> gvs[] >>
  gvs[inline_location_step_def, inline_before_phi_keep,
      GSYM inline_path_location_def]
QED

(* Actions follow the execution order of the zipper, including conditional
   cloning of labels at each enclosing callee. *)
Definition inline_cell_var_action_def:
  (inline_cell_var_action [] v = v) /\
  (inline_cell_var_action ((tag,next)::frames) v =
    inline_cell_var_action frames
      (case tag of EnterCell e k => STRCAT e.ise_prefix v | _ => v))
End

Definition inline_cell_label_action_def:
  (inline_cell_label_action [] l = l) /\
  (inline_cell_label_action ((tag,next)::frames) l =
    inline_cell_label_action frames
      (case tag of EnterCell e k =>
        if MEM l (fn_labels e.ise_callee) then STRCAT e.ise_prefix l else l
       | _ => l))
End

Theorem inline_cell_fold_mapped_fields:
  !frames src.
  inline_inst_fields
    (FOLDL (\inst (tag,next). case tag of
       EnterCell e k => clone_instruction e.ise_prefix (fn_labels e.ise_callee) inst
     | _ => inst) src frames) =
  (src.inst_opcode,
   MAP (inline_rename_operand (inline_cell_var_action frames)
     (inline_cell_label_action frames)) src.inst_operands,
   MAP (inline_cell_var_action frames) src.inst_outputs)
Proof
  Induct
  >- (gen_tac >>
      `inline_cell_var_action [] = I` by simp[FUN_EQ_THM, inline_cell_var_action_def] >>
      `inline_cell_label_action [] = I` by simp[FUN_EQ_THM, inline_cell_label_action_def] >>
      `inline_rename_operand I I = I` by
        (simp[FUN_EQ_THM] >> Cases >> simp[inline_rename_operand_def]) >>
      simp[inline_inst_fields_def, MAP_ID]) >>
  qx_gen_tac `h` >> PairCases_on `h` >> gen_tac >>
  simp[FOLDL] >> Cases_on `h0` >>
  simp[clone_instruction_def, inline_cell_var_action_def,
    inline_cell_label_action_def, inline_inst_fields_def, MAP_MAP_o, combinTheory.o_DEF] >>
  (conj_tac
   >- (irule listTheory.MAP_CONG >> simp[] >> rpt strip_tac >>
       Cases_on `x` >> simp[clone_operand_def, inline_rename_operand_def,
         inline_cell_var_action_def, inline_cell_label_action_def] >>
       rw[inline_rename_operand_def]) >>
   irule listTheory.MAP_CONG >> simp[inline_cell_var_action_def])
QED

Theorem inline_cell_zipper_mapped_fields:
  inline_cell_zipper c frames d /\ c.ic_fields = inline_inst_fields src /\
  ~MEM src.inst_opcode [PHI; PARAM; FMP_PARAM; RETPC_PARAM; RET; RETFMP] /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames ==>
  d.ic_fields =
    (src.inst_opcode,
     MAP (inline_rename_operand (inline_cell_var_action frames)
       (inline_cell_label_action frames)) src.inst_operands,
     MAP (inline_cell_var_action frames) src.inst_outputs)
Proof
  strip_tac >> drule_all inline_cell_zipper_ordinary_fields >>
  simp[inline_cell_fold_mapped_fields]
QED

Theorem inline_cell_zipper_route_fetch:
  inline_cell_at c /\ inline_cell_zipper c frames d /\
  c.ic_fields = inline_inst_fields src /\
  ~MEM src.inst_opcode [PHI; PARAM; FMP_PARAM; RETPC_PARAM; RET; RETFMP] /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames /\
  inline_cell_var_action frames = route.ir_rename /\
  inline_cell_label_action frames = lab ==>
  ?bb dst.
    lookup_block d.ic_block d.ic_function.fn_blocks = SOME bb /\
    get_instruction bb d.ic_index = SOME dst /\
    dst.inst_opcode = src.inst_opcode /\
    dst.inst_operands = MAP (inline_rename_operand route.ir_rename lab) src.inst_operands /\
    dst.inst_outputs = MAP route.ir_rename src.inst_outputs
Proof
  strip_tac >> drule_all inline_cell_zipper_mapped_fields >>
  drule_all inline_cell_zipper_sound >>
  simp[inline_cell_at_def, inline_fetched_fields_def, inline_inst_fields_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* Existence of a block entry only depends on labels, not on its repaired
   instruction contents.  No collision-freshness premise is needed here. *)
Theorem inline_valid_edit_label_set:
  inline_site_edit_valid e ==>
  fn_labels e.ise_final = fn_labels e.ise_caller ++ [e.ise_return] ++
    MAP (STRCAT e.ise_prefix) (fn_labels e.ise_callee)
Proof
  strip_tac >> drule inline_edit_final_labels >> disch_then SUBST1_TAC >>
  irule functionInlinerWfTheory.inline_call_site_labels >>
  gvs[inline_site_edit_valid_def] >>
  drule functionInlinerWfTheory.find_invoke_site_member >> strip_tac >>
  `MEM e.ise_block (MAP (\b. b.bb_label) e.ise_caller.fn_blocks)` by
    (simp[listTheory.MEM_MAP] >> metis_tac[]) >>
  drule dfAnalyzeProofsTheory.lookup_block_exists >> metis_tac[]
QED

Theorem inline_routed_before_phi_labels:
  !cert root p fn path. inline_routed_leaf cert root p fn path ==>
    !l k. MEM l (fn_labels fn) ==>
      MEM (inline_path_rename path l) (fn_labels root) /\
      inline_path_location path (SOME (inline_before_phi_location l k)) =
        SOME (inline_before_phi_location (inline_path_rename path l) k)
Proof
  ho_match_mp_tac inline_routed_leaf_ind >> rpt conj_tac >>
  rpt strip_tac >>
  gvs[inline_path_rename_def, inline_path_rename_append,
    inline_choice_rename_def, inline_path_location_append,
    inline_path_location_def, inline_location_step_def,
    inline_before_phi_keep, inline_before_phi_enter, combinTheory.o_DEF] >>
  drule inline_valid_edit_label_set >> simp[] >> metis_tac[listTheory.MEM_MAP]
QED

Theorem inline_routed_before_phi_lookup:
  inline_routed_leaf cert root p fn path /\
  lookup_block l fn.fn_blocks = SOME bb ==>
  ?tb. lookup_block (inline_path_rename path l) root.fn_blocks = SOME tb /\
    inline_path_location path (SOME (inline_before_phi_location l k)) =
      SOME (inline_before_phi_location (inline_path_rename path l) k)
Proof
  strip_tac >>
  `MEM l (fn_labels fn)` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM,
      venomExecPropsTheory.lookup_block_label, fn_labels_def, listTheory.MEM_MAP] >>
  drule_all inline_routed_before_phi_labels >>
  disch_then (qspec_then `k` strip_assume_tac) >>
  gvs[fn_labels_def] >> metis_tac[dfAnalyzeProofsTheory.lookup_block_exists]
QED

Definition inline_cell_choice_def:
  (inline_cell_choice (KeepCell e) = InlineKeep e) /\
  (inline_cell_choice (SelectedJump e) = InlineKeep e) /\
  (inline_cell_choice (EnterCell e k) = InlineEnter e)
End

Theorem inline_cell_frame_entry_label:
  inline_cell_frame tag c d /\ MEM l (fn_labels c.ic_function) ==>
  MEM (inline_choice_rename (inline_cell_choice tag) l) (fn_labels d.ic_function) /\
  inline_cell_label_action [(tag,d)] l =
    inline_choice_rename (inline_cell_choice tag) l
Proof
  Cases_on `tag` >>
  simp[inline_cell_frame_def, inline_cell_choice_def,
    inline_choice_rename_def, inline_cell_label_action_def] >>
  rpt strip_tac >> gvs[inline_make_cell_def] >>
  drule inline_valid_edit_label_set >> simp[] >>
  metis_tac[listTheory.MEM_MAP]
QED

Theorem inline_cell_zipper_entry_label:
  !frames c d l. inline_cell_zipper c frames d /\
    MEM l (fn_labels c.ic_function) ==>
    MEM (inline_cell_label_action frames l) (fn_labels d.ic_function) /\
    inline_cell_label_action frames l =
      inline_path_rename (MAP (\(tag,next). inline_cell_choice tag) frames) l
Proof
  Induct >> simp[inline_cell_zipper_def, inline_cell_label_action_def,
    inline_path_rename_def] >>
  qx_gen_tac `h` >> PairCases_on `h` >> rpt gen_tac >>
  simp[inline_cell_zipper_def] >> strip_tac >>
  drule_all inline_cell_frame_entry_label >> strip_tac >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  Cases_on `h0` >>
  gvs[inline_cell_label_action_def, inline_path_rename_def,
    inline_cell_choice_def, inline_choice_rename_def, combinTheory.o_DEF]
QED

Theorem inline_cell_routed_before_phi:
  inline_routed_leaf cert root p c.ic_function
    (MAP (\(tag,next). inline_cell_choice tag) frames) /\
  inline_cell_zipper c frames d /\
  lookup_block l c.ic_function.fn_blocks = SOME bb ==>
  ?tb. lookup_block (inline_cell_label_action frames l) root.fn_blocks = SOME tb /\
    inline_path_location (MAP (\(tag,next). inline_cell_choice tag) frames)
      (SOME (inline_before_phi_location l k)) =
      SOME (inline_before_phi_location (inline_cell_label_action frames l) k)
Proof
  strip_tac >>
  `MEM l (fn_labels c.ic_function)` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM,
      venomExecPropsTheory.lookup_block_label, fn_labels_def, listTheory.MEM_MAP] >>
  drule_all inline_cell_zipper_entry_label >> strip_tac >>
  drule_all inline_routed_before_phi_lookup >> simp[]
QED

Theorem inline_cell_focus_singleton:
  get_instruction cb j = SOME src /\
  ~MEM src.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM; RET; RETFMP] ==>
  inline_cell_focus e bb cb j =
    ([clone_instruction e.ise_prefix (fn_labels e.ise_callee) src],
     SND (inline_cell_prefix e bb cb j))
Proof
  simp[get_instruction_def, inline_cell_focus_def] >> strip_tac >>
  gvs[] >>
  `~is_param_opcode (EL j cb.bb_instructions).inst_opcode` by
    (Cases_on `(EL j cb.bb_instructions).inst_opcode` >> gvs[is_param_opcode_def]) >>
  simp[rewrite_inline_inst_def, clone_instruction_def]
QED

Theorem inline_cell_prefix_singleton_suc:
  get_instruction cb j = SOME src /\
  ~MEM src.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM; RET; RETFMP] ==>
  LENGTH (FST (inline_cell_prefix e bb cb (SUC j))) =
    SUC (LENGTH (FST (inline_cell_prefix e bb cb j))) /\
  SND (inline_cell_prefix e bb cb (SUC j)) = SND (inline_cell_prefix e bb cb j)
Proof
  strip_tac >> drule_all inline_cell_focus_singleton >> strip_tac >>
  `j < LENGTH cb.bb_instructions` by gvs[get_instruction_def] >>
  drule inline_cell_prefix_suc >> simp[]
QED

Theorem inline_enter_singleton_successor_location:
  lookup_block c.ic_block e.ise_callee.fn_blocks = SOME cb /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  e.ise_index < LENGTH bb.bb_instructions /\
  get_instruction cb c.ic_index = SOME src /\
  ~MEM src.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM; RET; RETFMP] ==>
  inline_choice_location (InlineEnter e)
    (inline_cell_location (c with ic_index := SUC c.ic_index) counter) =
  SOME <|il_block := STRCAT e.ise_prefix c.ic_block;
    il_phase := InlineAtInstruction
      (SUC (LENGTH (FST (inline_cell_prefix e bb cb c.ic_index))));
    il_counter := SND (inline_cell_prefix e bb cb c.ic_index)|>
Proof
  strip_tac >> drule_all inline_cell_prefix_singleton_suc >> strip_tac >>
  `SUC c.ic_index <= LENGTH cb.bb_instructions` by gvs[get_instruction_def] >>
  simp[inline_cell_location_def, inline_choice_location_def,
    GSYM inline_cell_prefix_def]
QED

Theorem inline_keep_successor_location:
  (c.ic_block <> e.ise_block \/ c.ic_index <> e.ise_index) ==>
  inline_choice_location (InlineKeep e)
    (inline_cell_location (c with ic_index := SUC c.ic_index) counter) =
  if c.ic_block = e.ise_block /\ SUC c.ic_index = e.ise_index then NONE
  else SOME <|
    il_block := if c.ic_block = e.ise_block /\ e.ise_index < c.ic_index
                then e.ise_return else c.ic_block;
    il_phase := InlineAtInstruction
      (SUC (if c.ic_block = e.ise_block /\ e.ise_index < c.ic_index
            then c.ic_index - (e.ise_index + 1) else c.ic_index));
    il_counter := counter|>
Proof
  simp[inline_choice_location_def, inline_cell_location_def] >>
  rpt strip_tac >> Cases_on `c.ic_block = e.ise_block` >> simp[] >>
  Cases_on `c.ic_index < e.ise_index` >> simp[] >>
  Cases_on `SUC c.ic_index = e.ise_index` >> simp[] >>
  gvs[] >> decide_tac
QED

Theorem inline_cell_focus_nonempty:
  0 < LENGTH (FST (inline_cell_focus e bb cb j))
Proof
  simp[inline_cell_focus_def, rewrite_inline_inst_def] >>
  rpt IF_CASES_TAC >> simp[LET_THM]
QED

Theorem inline_cell_next_source:
  inline_cell_at c ==>
  (?src. inline_cell_at
    (inline_make_cell c.ic_function c.ic_block (SUC c.ic_index)
      (inline_inst_fields src))) \/
  (?bb. lookup_block c.ic_block c.ic_function.fn_blocks = SOME bb /\
    SUC c.ic_index = LENGTH bb.bb_instructions)
Proof
  simp[inline_cell_at_def, inline_fetched_fields_def, inline_make_cell_def,
    get_instruction_def] >> rpt strip_tac >>
  Cases_on `SUC c.ic_index < LENGTH bb.bb_instructions`
  >- (disj1_tac >> qexistsl_tac [`EL (SUC c.ic_index) bb.bb_instructions`, `bb`] >> simp[]) >>
  `SUC c.ic_index = LENGTH bb.bb_instructions` by decide_tac >>
  metis_tac[]
QED

(* The source successor may be the selected call itself.  Its emitted JMP is
   still fetched even though the ordinary path-location action is NONE. *)
Theorem inline_keep_next_produce:
  inline_cell_frame (KeepCell e) c d /\ inline_cell_at n /\
  n.ic_function = c.ic_function /\ n.ic_block = c.ic_block /\
  n.ic_index = SUC c.ic_index ==>
  ?tag out. (tag = KeepCell e \/ tag = SelectedJump e) /\
    inline_cell_frame tag n out /\ inline_cell_at out /\
    out.ic_function = d.ic_function /\ out.ic_block = d.ic_block /\
    out.ic_index = SUC d.ic_index
Proof
  strip_tac >>
  Cases_on `n.ic_block = e.ise_block /\ n.ic_index = e.ise_index`
  >- (`?out. inline_cell_frame (SelectedJump e) n out` by
        (irule inline_selected_cell_produce >>
         gvs[inline_cell_frame_def] >> metis_tac[]) >>
      qexistsl_tac [`SelectedJump e`, `out`] >>
      `inline_cell_at out` by metis_tac[inline_cell_frame_sound] >>
      gvs[inline_cell_frame_def, inline_make_cell_def]) >>
  `?out. inline_cell_frame (KeepCell e) n out` by
    (irule inline_keep_cell_produce >>
     gvs[inline_cell_frame_def] >> metis_tac[]) >>
  qexistsl_tac [`KeepCell e`, `out`] >>
  `inline_cell_at out` by metis_tac[inline_cell_frame_sound] >>
  gvs[inline_cell_frame_def, inline_make_cell_def] >>
  Cases_on `c.ic_block = e.ise_block` >> gvs[] >>
  Cases_on `e.ise_index < c.ic_index` >> gvs[] >> decide_tac
QED

Theorem inline_enter_next_produce:
  inline_cell_frame (EnterCell e k) c d /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  lookup_block c.ic_block e.ise_callee.fn_blocks = SOME cb /\
  get_instruction cb c.ic_index = SOME src /\
  ~MEM src.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM; RET; RETFMP] /\
  inline_cell_at n /\ n.ic_function = c.ic_function /\
  n.ic_block = c.ic_block /\ n.ic_index = SUC c.ic_index ==>
  ?out. inline_cell_frame (EnterCell e 0) n out /\ inline_cell_at out /\
    out.ic_function = d.ic_function /\ out.ic_block = d.ic_block /\
    out.ic_index = SUC d.ic_index
Proof
  strip_tac >>
  `?out. inline_cell_frame (EnterCell e 0) n out` by
    (irule inline_enter_cell_produce >>
     gvs[inline_cell_frame_def] >>
     metis_tac[inline_cell_focus_nonempty]) >>
  qexists_tac `out` >>
  `inline_cell_at out` by metis_tac[inline_cell_frame_sound] >>
  drule_all inline_cell_focus_singleton >> strip_tac >>
  drule_all inline_cell_prefix_singleton_suc >> strip_tac >>
  gvs[inline_cell_frame_def, inline_make_cell_def]
QED

Theorem inline_cell_frame_next_produce:
  inline_cell_frame tag c d /\ c.ic_fields = inline_inst_fields src /\
  ~MEM src.inst_opcode [PHI; PARAM; FMP_PARAM; RETPC_PARAM; RET; RETFMP] /\
  (!e. tag <> SelectedJump e) /\
  inline_cell_at n /\ n.ic_function = c.ic_function /\
  n.ic_block = c.ic_block /\ n.ic_index = SUC c.ic_index ==>
  ?next_tag out. inline_cell_choice next_tag = inline_cell_choice tag /\
    (!e k. next_tag = EnterCell e k ==> k = 0) /\
    inline_cell_frame next_tag n out /\ inline_cell_at out /\
    out.ic_function = d.ic_function /\ out.ic_block = d.ic_block /\
    out.ic_index = SUC d.ic_index
Proof
  strip_tac >> Cases_on `tag` >> gvs[]
  >- (drule_all inline_keep_next_produce >> strip_tac >>
      qexistsl_tac [`tag`, `out`] >>
      gvs[inline_cell_choice_def] >> metis_tac[inline_cell_choice_def]) >>
  `?bb cb inst. lookup_block i.ise_block i.ise_caller.fn_blocks = SOME bb /\
    lookup_block c.ic_block i.ise_callee.fn_blocks = SOME cb /\
    get_instruction cb c.ic_index = SOME inst /\
    inline_inst_fields inst = inline_inst_fields src` by
      (gvs[inline_cell_frame_def] >> metis_tac[]) >>
  `~MEM inst.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM; RET; RETFMP]` by
    gvs[inline_inst_fields_def] >>
  drule_all inline_enter_next_produce >> strip_tac >>
  qexistsl_tac [`EnterCell i 0`, `out`] >> simp[inline_cell_choice_def]
QED

(* Recompute every outer frame from the newly emitted successor, rather than
   reusing the source counter or incrementing saved frame indices. *)
Theorem inline_cell_zipper_next_produce:
  !frames c d src n.
  inline_cell_zipper c frames d /\ c.ic_fields = inline_inst_fields src /\
  ~MEM src.inst_opcode [PHI; PARAM; FMP_PARAM; RETPC_PARAM; RET; RETFMP] /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames /\
  inline_cell_at n /\ n.ic_function = c.ic_function /\
  n.ic_block = c.ic_block /\ n.ic_index = SUC c.ic_index ==>
  ?next_frames out. inline_cell_zipper n next_frames out /\ inline_cell_at out /\
    EVERY (\(tag,next). !e k. tag = EnterCell e k ==> k = 0) next_frames /\
    MAP (\(tag,next). inline_cell_choice tag) next_frames =
      MAP (\(tag,next). inline_cell_choice tag) frames /\
    out.ic_function = d.ic_function /\ out.ic_block = d.ic_block /\
    out.ic_index = SUC d.ic_index
Proof
  Induct
  >- (simp[inline_cell_zipper_def] >> rpt strip_tac >>
      qexistsl_tac [`[]`, `n`] >> simp[]) >>
  qx_gen_tac `h` >> PairCases_on `h` >>
  simp[inline_cell_zipper_def] >> rpt strip_tac >>
  `?next_tag mid. inline_cell_choice next_tag = inline_cell_choice h0 /\
    (!e k. next_tag = EnterCell e k ==> k = 0) /\
    inline_cell_frame next_tag n mid /\ inline_cell_at mid /\
    mid.ic_function = h1.ic_function /\ mid.ic_block = h1.ic_block /\
    mid.ic_index = SUC h1.ic_index` by
      (irule inline_cell_frame_next_produce >> simp[] >>
       qexistsl_tac [`c`, `src`] >> simp[]) >>
  `h1.ic_fields = inline_inst_fields
    (case h0 of EnterCell e k =>
      clone_instruction e.ise_prefix (fn_labels e.ise_callee) src | _ => src)` by
    (irule inline_cell_frame_ordinary_fields >> simp[] >>
     qexists_tac `c` >> simp[]) >>
  first_x_assum drule >>
  disch_then (qspec_then
    `case h0 of EnterCell e k =>
       clone_instruction e.ise_prefix (fn_labels e.ise_callee) src | _ => src`
    (qspec_then `mid` mp_tac)) >>
  impl_tac
  >- (Cases_on `h0` >> gvs[clone_instruction_def]) >>
  strip_tac >>
  qexistsl_tac [`(next_tag,mid)::next_frames`, `out`] >>
  simp[inline_cell_zipper_def]
QED

Theorem inline_cell_zipper_successor_cases:
  inline_cell_at c /\ inline_cell_zipper c frames d /\
  c.ic_fields = inline_inst_fields src /\
  ~MEM src.inst_opcode [PHI; PARAM; FMP_PARAM; RETPC_PARAM; RET; RETFMP] /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames ==>
  (?n next_frames out.
    inline_cell_at n /\ n.ic_function = c.ic_function /\
    n.ic_block = c.ic_block /\ n.ic_index = SUC c.ic_index /\
    inline_cell_zipper n next_frames out /\ inline_cell_at out /\
    EVERY (\(tag,next). !e k. tag = EnterCell e k ==> k = 0) next_frames /\
    MAP (\(tag,next). inline_cell_choice tag) next_frames =
      MAP (\(tag,next). inline_cell_choice tag) frames /\
    out.ic_function = d.ic_function /\ out.ic_block = d.ic_block /\
    out.ic_index = SUC d.ic_index) \/
  (?bb. lookup_block c.ic_block c.ic_function.fn_blocks = SOME bb /\
    SUC c.ic_index = LENGTH bb.bb_instructions)
Proof
  strip_tac >> drule inline_cell_next_source >> strip_tac
  >- (disj1_tac >>
      qmatch_asmsub_abbrev_tac `inline_cell_at n` >>
      `n.ic_function = c.ic_function /\ n.ic_block = c.ic_block /\
       n.ic_index = SUC c.ic_index` by simp[Abbr `n`, inline_make_cell_def] >>
      drule_all inline_cell_zipper_next_produce >> strip_tac >>
      qexistsl_tac [`n`, `next_frames`, `out`] >> simp[]) >>
  disj2_tac >> metis_tac[]
QED

Theorem inline_cell_selected_projection:
  inline_cell_frame (SelectedJump e) c d ==>
  inline_choice_location (InlineKeep e) (inline_cell_location c counter) = NONE
Proof
  simp[inline_cell_frame_def, inline_cell_location_def,
    inline_choice_location_def] >> rpt strip_tac >> simp[]
QED

Theorem inline_cell_frame_path_projection:
  inline_cell_frame tag c d /\
  (!e k. tag = EnterCell e k ==> k = 0 /\
    ALL_DISTINCT (fn_labels e.ise_caller)) ==>
  (!e. tag <> SelectedJump e) /\
    (?counter'. inline_choice_location (inline_cell_choice tag)
      (inline_cell_location c counter) = SOME (inline_cell_location d counter')) \/
  ((?e. tag = SelectedJump e) /\
    inline_choice_location (inline_cell_choice tag)
      (inline_cell_location c counter) = NONE)
Proof
  Cases_on `tag` >> simp[inline_cell_choice_def] >> strip_tac
  >- metis_tac[inline_keep_cell_projection]
  >- metis_tac[inline_cell_selected_projection] >>
  gvs[] >>
  `?bb cb. lookup_block i.ise_block i.ise_caller.fn_blocks = SOME bb /\
    lookup_block c.ic_block i.ise_callee.fn_blocks = SOME cb /\
    i.ise_index < LENGTH bb.bb_instructions` by
    (gvs[inline_cell_frame_def] >>
     qpat_x_assum `inline_site_edit_valid i` mp_tac >>
     simp[inline_site_edit_valid_def] >> strip_tac >>
     drule_all functionInlinerWfTheory.find_invoke_site_lookup >>
     simp[]) >>
  metis_tac[inline_enter_cell_projection]
QED

Theorem inline_cell_zipper_path_projection:
  !frames c d counter.
  inline_cell_zipper c frames d /\
  EVERY (\(tag,next). !e k. tag = EnterCell e k ==> k = 0 /\
    ALL_DISTINCT (fn_labels e.ise_caller)) frames ==>
  (EVERY (\(tag,next). !e. tag <> SelectedJump e) frames /\
    ?counter'. inline_path_location
      (MAP (\(tag,next). inline_cell_choice tag) frames)
      (SOME (inline_cell_location c counter)) = SOME (inline_cell_location d counter')) \/
  ((?tag next. MEM (tag,next) frames /\ ?e. tag = SelectedJump e) /\
    inline_path_location (MAP (\(tag,next). inline_cell_choice tag) frames)
      (SOME (inline_cell_location c counter)) = NONE)
Proof
  Induct >> simp[inline_cell_zipper_def, inline_path_location_def]
  >- metis_tac[] >>
  qx_gen_tac `h` >> PairCases_on `h` >>
  simp[inline_cell_zipper_def] >> rpt strip_tac >>
  drule_all inline_cell_frame_path_projection >>
  disch_then (qspec_then `counter` strip_assume_tac)
  >- (first_x_assum drule >> disch_then drule >>
      disch_then (qspec_then `counter'` mp_tac) >> strip_tac >>
      pure_rewrite_tac[inline_path_location_def, MAP, FOLDL] >>
      simp[inline_location_step_def, GSYM inline_path_location_def] >> metis_tac[]) >>
  pure_rewrite_tac[inline_path_location_def, MAP, FOLDL] >>
  simp[inline_location_step_def, GSYM inline_path_location_def] >> metis_tac[]
QED

(* Parameter focus is computed at the current block's prefix counter. *)
Theorem inline_cell_parameter_focus:
  args = rotate_invoke_ops (EL e.ise_index bb.bb_instructions).inst_operands /\
  ci = clone_instruction e.ise_prefix (fn_labels e.ise_callee)
    (EL j cb.bb_instructions) /\
  q = SND (inline_cell_prefix e bb cb j) /\
  is_param_opcode ci.inst_opcode ==>
  inline_cell_focus e bb cb j =
    (if q < LENGTH args then
       ([ci with <|inst_opcode := ASSIGN; inst_operands := [EL q args]|>],q+1)
     else ([ci],q))
Proof
  strip_tac >> gvs[inline_cell_focus_def, rewrite_inline_inst_def]
QED

Theorem inline_cell_parameter_prefix_suc:
  j < LENGTH cb.bb_instructions /\
  args = rotate_invoke_ops (EL e.ise_index bb.bb_instructions).inst_operands /\
  ci = clone_instruction e.ise_prefix (fn_labels e.ise_callee)
    (EL j cb.bb_instructions) /\
  q = SND (inline_cell_prefix e bb cb j) /\
  is_param_opcode ci.inst_opcode ==>
  LENGTH (FST (inline_cell_prefix e bb cb (SUC j))) =
    SUC (LENGTH (FST (inline_cell_prefix e bb cb j))) /\
  SND (inline_cell_prefix e bb cb (SUC j)) =
    (if q < LENGTH args then q+1 else q)
Proof
  strip_tac >> drule_all inline_cell_parameter_focus >> strip_tac >>
  simp[inline_cell_prefix_suc] >>
  Cases_on `q < LENGTH args` >> gvs[]
QED

(* After replacement the outer edit sees ASSIGN, not the original token. *)
Theorem inline_replaced_parameter_outer_rewrite:
  inst.inst_opcode = ASSIGN ==>
  rewrite_inline_inst args outs ret (clone_instruction pref labs inst) q =
    ([clone_instruction pref labs inst],q)
Proof
  simp[rewrite_inline_inst_def, clone_instruction_def, is_param_opcode_def]
QED

Theorem inline_surviving_token_outer_rewrite:
  inst.inst_opcode = RETPC_PARAM ==>
  rewrite_inline_inst args outs ret (clone_instruction pref labs inst) q =
    (if q < LENGTH args then
       ([(clone_instruction pref labs inst) with
          <|inst_opcode := ASSIGN; inst_operands := [EL q args]|>],q+1)
     else ([clone_instruction pref labs inst],q))
Proof
  simp[rewrite_inline_inst_def, clone_instruction_def, is_param_opcode_def]
QED

Theorem inline_enter_parameter_fields:
  inline_cell_frame (EnterCell e k) c mid /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  lookup_block c.ic_block e.ise_callee.fn_blocks = SOME cb /\
  args = rotate_invoke_ops (EL e.ise_index bb.bb_instructions).inst_operands /\
  ci = clone_instruction e.ise_prefix (fn_labels e.ise_callee)
    (EL c.ic_index cb.bb_instructions) /\
  q = SND (inline_cell_prefix e bb cb c.ic_index) /\
  is_param_opcode ci.inst_opcode /\ q < LENGTH args ==>
  k = 0 /\
  mid.ic_index = LENGTH (FST (inline_cell_prefix e bb cb c.ic_index)) /\
  mid.ic_fields = inline_inst_fields
    (ci with <|inst_opcode := ASSIGN; inst_operands := [EL q args]|>)
Proof
  strip_tac >> drule_all inline_cell_parameter_focus >> strip_tac >>
  gvs[inline_cell_frame_def, inline_make_cell_def, get_instruction_def,
      inline_edit_repair_def, inline_inst_fields_def]
QED

Theorem inline_parameter_residual_fetch:
  inline_cell_frame (EnterCell e k) c mid /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  lookup_block c.ic_block e.ise_callee.fn_blocks = SOME cb /\
  args = rotate_invoke_ops (EL e.ise_index bb.bb_instructions).inst_operands /\
  ci = clone_instruction e.ise_prefix (fn_labels e.ise_callee)
    (EL c.ic_index cb.bb_instructions) /\
  q = SND (inline_cell_prefix e bb cb c.ic_index) /\
  is_param_opcode ci.inst_opcode /\ q < LENGTH args /\
  inline_cell_zipper mid frames d /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames ==>
  ?tb dst.
    lookup_block d.ic_block d.ic_function.fn_blocks = SOME tb /\
    get_instruction tb d.ic_index = SOME dst /\
    dst.inst_opcode = ASSIGN /\
    dst.inst_operands =
      [inline_rename_operand (inline_cell_var_action frames)
        (inline_cell_label_action frames) (EL q args)] /\
    dst.inst_outputs = MAP (inline_cell_var_action frames) ci.inst_outputs
Proof
  strip_tac >> drule_all inline_enter_parameter_fields >> strip_tac >>
  `inline_cell_at mid` by metis_tac[inline_cell_frame_sound] >>
  drule_at (Pos hd) inline_cell_zipper_mapped_fields >>
  disch_then (drule_at (Pos hd)) >>
  simp[] >> strip_tac >>
  drule_all inline_cell_zipper_sound >>
  simp[inline_cell_at_def, inline_fetched_fields_def, inline_inst_fields_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem inline_selected_jump_residual_fetch:
  inline_cell_frame (SelectedJump e) c mid /\
  entry = (case (clone_function e.ise_prefix e.ise_callee).fn_blocks of
             [] => "" | eb::_ => eb.bb_label) /\
  inline_cell_zipper mid frames d /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames ==>
  ?tb dst.
    lookup_block d.ic_block d.ic_function.fn_blocks = SOME tb /\
    get_instruction tb d.ic_index = SOME dst /\
    dst.inst_opcode = JMP /\
    dst.inst_operands = [Label (inline_cell_label_action frames entry)] /\
    dst.inst_outputs = []
Proof
  strip_tac >>
  `mid.ic_fields = inline_inst_fields
     <|inst_opcode := JMP; inst_operands := [Label entry]; inst_outputs := []|>` by
    gvs[inline_cell_frame_def, inline_make_cell_def, inline_inst_fields_def] >>
  `inline_cell_at mid` by metis_tac[inline_cell_frame_sound] >>
  drule_at (Pos hd) inline_cell_zipper_mapped_fields >>
  disch_then (drule_at (Pos hd)) >>
  simp[] >> strip_tac >>
  drule_all inline_cell_zipper_sound >>
  simp[inline_cell_at_def, inline_fetched_fields_def, inline_inst_fields_def,
    inline_rename_operand_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem inline_selected_jump_residual_entry_label:
  inline_cell_frame (SelectedJump e) c mid /\
  (clone_function e.ise_prefix e.ise_callee).fn_blocks = eb::blocks /\
  inline_cell_zipper mid frames d ==>
  MEM (inline_cell_label_action frames eb.bb_label) (fn_labels d.ic_function)
Proof
  strip_tac >>
  `inline_site_edit_valid e /\ mid.ic_function = e.ise_final` by
    gvs[inline_cell_frame_def, inline_make_cell_def] >>
  `MEM eb.bb_label (fn_labels (clone_function e.ise_prefix e.ise_callee))` by
    simp[fn_labels_def] >>
  `MEM eb.bb_label (fn_labels mid.ic_function)` by
    (drule inline_valid_edit_label_set >>
     gvs[functionInlinerWfTheory.clone_function_labels]) >>
  drule_all inline_cell_zipper_entry_label >> simp[]
QED

Theorem inline_enter_parameter_exhausted_fields:
  inline_cell_frame (EnterCell e k) c mid /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  lookup_block c.ic_block e.ise_callee.fn_blocks = SOME cb /\
  args = rotate_invoke_ops (EL e.ise_index bb.bb_instructions).inst_operands /\
  ci = clone_instruction e.ise_prefix (fn_labels e.ise_callee)
    (EL c.ic_index cb.bb_instructions) /\
  q = SND (inline_cell_prefix e bb cb c.ic_index) /\
  is_param_opcode ci.inst_opcode /\ LENGTH args <= q ==>
  k = 0 /\
  mid.ic_index = LENGTH (FST (inline_cell_prefix e bb cb c.ic_index)) /\
  mid.ic_fields = inline_inst_fields ci
Proof
  strip_tac >> drule_all inline_cell_parameter_focus >> strip_tac >>
  gvs[inline_cell_frame_def, inline_make_cell_def, get_instruction_def,
      inline_edit_repair_def, inline_inst_fields_def, is_param_opcode_iff]
QED

(* Block-entry predecessor action is separate from variable/label renaming:
   an enclosing caller edit can repair an edge without renaming its target. *)
Definition inline_phi_entry_step_def:
  (inline_phi_entry_step (InlineKeep e) (l,prev) =
    case lookup_block e.ise_block e.ise_caller.fn_blocks of
      NONE => (l,prev)
    | SOME bb =>
      (l, if MEM l (bb_succs <|bb_label := e.ise_return;
          bb_instructions := DROP (e.ise_index+1) bb.bb_instructions|>) then
        OPTION_MAP (\q. if q = e.ise_block then e.ise_return else q) prev
      else prev)) /\
  (inline_phi_entry_step (InlineEnter e) (l,prev) =
    (STRCAT e.ise_prefix l, OPTION_MAP (STRCAT e.ise_prefix) prev))
End

Definition inline_phi_entry_path_def:
  inline_phi_entry_path path x = FOLDL (\x c. inline_phi_entry_step c x) x path
End

Theorem inline_phi_entry_path_append:
  inline_phi_entry_path (xs ++ ys) x =
    inline_phi_entry_path ys (inline_phi_entry_path xs x)
Proof simp[inline_phi_entry_path_def, FOLDL_APPEND]
QED

Theorem inline_phi_entry_step_label:
  FST (inline_phi_entry_step c (l,prev)) = inline_choice_rename c l
Proof
  Cases_on `c` >> simp[inline_phi_entry_step_def, inline_choice_rename_def] >>
  CASE_TAC >> simp[]
QED

Theorem inline_valid_edit_source_lookup:
  inline_site_edit_valid e ==>
  ?bb. lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb
Proof
  simp[inline_site_edit_valid_def] >> strip_tac >>
  drule functionInlinerWfTheory.find_invoke_site_member >> strip_tac >>
  `MEM e.ise_block (MAP (\b. b.bb_label) e.ise_caller.fn_blocks)` by
    (simp[listTheory.MEM_MAP] >> metis_tac[]) >>
  metis_tac[dfAnalyzeProofsTheory.lookup_block_exists]
QED

Theorem inline_phi_entry_keep_support:
  inline_site_edit_valid e /\ MEM l (fn_labels e.ise_caller) /\
  (!q. prev = SOME q ==> MEM q (fn_labels e.ise_caller)) ==>
  MEM (FST (inline_phi_entry_step (InlineKeep e) (l,prev)))
    (fn_labels e.ise_final) /\
  (!q. SND (inline_phi_entry_step (InlineKeep e) (l,prev)) = SOME q ==>
    MEM q (fn_labels e.ise_final))
Proof
  strip_tac >> drule inline_valid_edit_label_set >> strip_tac >>
  drule inline_valid_edit_source_lookup >> strip_tac >>
  simp[inline_phi_entry_step_def] >>
  Cases_on `prev` >> simp[] >> IF_CASES_TAC >> simp[] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem inline_phi_entry_enter_support:
  inline_site_edit_valid e /\ MEM l (fn_labels e.ise_callee) /\
  (!q. prev = SOME q ==> MEM q (fn_labels e.ise_callee)) ==>
  MEM (FST (inline_phi_entry_step (InlineEnter e) (l,prev)))
    (fn_labels e.ise_final) /\
  (!q. SND (inline_phi_entry_step (InlineEnter e) (l,prev)) = SOME q ==>
    MEM q (fn_labels e.ise_final))
Proof
  strip_tac >> drule inline_valid_edit_label_set >> strip_tac >>
  Cases_on `prev` >> simp[inline_phi_entry_step_def] >>
  metis_tac[listTheory.MEM_MAP]
QED

Theorem inline_phi_entry_path_label:
  !path l prev. FST (inline_phi_entry_path path (l,prev)) =
    inline_path_rename path l
Proof
  Induct >> simp[inline_phi_entry_path_def, inline_path_rename_def] >>
  rpt gen_tac >>
  Cases_on `inline_phi_entry_step h (l,prev)` >>
  simp[GSYM inline_phi_entry_path_def, combinTheory.o_DEF] >>
  metis_tac[inline_phi_entry_step_label, pairTheory.FST]
QED

Theorem inline_routed_phi_entry_support:
  !cert root p fn path. inline_routed_leaf cert root p fn path ==>
  !l prev. MEM l (fn_labels fn) /\
    (!q. prev = SOME q ==> MEM q (fn_labels fn)) ==>
  MEM (FST (inline_phi_entry_path path (l,prev))) (fn_labels root) /\
  (!q. SND (inline_phi_entry_path path (l,prev)) = SOME q ==>
    MEM q (fn_labels root))
Proof
  ho_match_mp_tac inline_routed_leaf_ind >> rpt conj_tac >>
  rpt strip_tac >>
  gvs[inline_phi_entry_path_append, inline_phi_entry_path_def] >>
  first_x_assum (qspecl_then [`l`, `prev`] mp_tac) >> simp[] >> strip_tac >>
  Cases_on `FOLDL (\x c. inline_phi_entry_step c x) (l,prev) path` >> gvs[] >>
  metis_tac[inline_phi_entry_keep_support, inline_phi_entry_enter_support]
QED

Theorem inline_phi_entry_step_none:
  inline_phi_entry_step c (l,NONE) = (inline_choice_rename c l,NONE)
Proof
  Cases_on `c` >> simp[inline_phi_entry_step_def, inline_choice_rename_def] >>
  CASE_TAC >> simp[]
QED

Theorem inline_phi_entry_path_none:
  !path l. inline_phi_entry_path path (l,NONE) =
    (inline_path_rename path l,NONE)
Proof
  Induct >- simp[inline_phi_entry_path_def, inline_path_rename_def] >>
  once_rewrite_tac[inline_phi_entry_path_def] >>
  simp[FOLDL, inline_phi_entry_step_none] >>
  simp[GSYM inline_phi_entry_path_def, inline_path_rename_def, combinTheory.o_DEF]
QED

Theorem inline_phi_entry_keep_some:
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb ==>
  inline_phi_entry_step (InlineKeep e) (l,SOME q) =
    (l, SOME (if MEM l (bb_succs <|bb_label := e.ise_return;
      bb_instructions := DROP (e.ise_index+1) bb.bb_instructions|>) /\
      q = e.ise_block then e.ise_return else q))
Proof
  simp[inline_phi_entry_step_def] >> rpt strip_tac >>
  rpt IF_CASES_TAC >> gvs[]
QED

(* Selection at the actual fields produced by a Keep edit.  Namespace support
   rules out capture by the new continuation without global injectivity. *)
Theorem inline_phi_entry_keep_selection:
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  inst.inst_opcode = PHI /\ phi_well_formed inst.inst_operands /\
  EVERY (\op. !l. op = Label l ==> MEM l (fn_labels e.ise_caller))
    inst.inst_operands /\
  MEM prev (fn_labels e.ise_caller) /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  inline_inst_fields target = inline_inst_fields
    (inline_edit_repair e source_bb dest inst) ==>
  ?q. SND (inline_phi_entry_step (InlineKeep e) (dest,SOME prev)) = SOME q /\
    resolve_phi q target.inst_operands = resolve_phi prev inst.inst_operands
Proof
  strip_tac >> drule inline_phi_entry_keep_some >>
  disch_then (qspecl_then [`prev`, `dest`] assume_tac) >>
  gvs[inline_edit_repair_def, inline_inst_fields_def] >>
  simp[COND_RAND, cfgTransformTheory.subst_label_inst_def] >>
  metis_tac[functionInlinerPhiTransportTheory.inline_resolve_phi_supported_repair]
QED

(* Prefixing is injective, including when source PHIs repeat a label. *)
Theorem inline_phi_entry_enter_selection:
  inline_inst_fields target = inline_inst_fields
    (inline_rename_inst (STRCAT e.ise_prefix) (STRCAT e.ise_prefix) inst) ==>
  ?q. SND (inline_phi_entry_step (InlineEnter e) (dest,SOME prev)) = SOME q /\
    resolve_phi q target.inst_operands =
      OPTION_MAP (inline_rename_operand (STRCAT e.ise_prefix) (STRCAT e.ise_prefix))
        (resolve_phi prev inst.inst_operands)
Proof
  simp[inline_inst_fields_def, inline_rename_inst_def, inline_phi_entry_step_def] >>
  strip_tac >> irule inline_rename_resolve_phi >> simp[]
QED

Theorem inline_routed_leaf_producer_origins:
  !cert root p fn path. inline_routed_leaf cert root p fn path ==>
  !C n. inline_annotated_origin C n root cert ==>
  EVERY (\choice. case choice of
      InlineKeep e => qualified_origin C e.ise_state.is_inline_count e.ise_caller /\
                      qualified_origin C e.ise_state.is_inline_count e.ise_callee
    | InlineEnter e => qualified_origin C e.ise_state.is_inline_count e.ise_caller /\
                       qualified_origin C e.ise_state.is_inline_count e.ise_callee) path
Proof
  ho_match_mp_tac inline_routed_leaf_ind >> rpt conj_tac
  >- simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  simp[EVERY_APPEND] >>
  drule functionInlinerOccurrencesTheory.inline_annotated_origin_edit_elim >>
  simp[] >> strip_tac >>
  gvs[] >> metis_tac[functionInlinerEnvelopesTheory.inline_annotated_origin_erasure]
QED

Theorem inline_routed_leaf_phi_producer_facts:
  inline_annotated_origin C n root cert /\ inline_routed_leaf cert root p fn path ==>
  EVERY (\choice. case choice of
      InlineKeep e => inliner_phi_labels_closed e.ise_caller /\
        inliner_phi_labels_closed e.ise_callee /\
        ~MEM e.ise_return (fn_labels e.ise_caller)
    | InlineEnter e => inliner_phi_labels_closed e.ise_caller /\
        inliner_phi_labels_closed e.ise_callee /\
        ~MEM e.ise_return (fn_labels e.ise_caller)) path
Proof
  strip_tac >> drule inline_routed_leaf_producer_origins >>
  disch_then (drule_then assume_tac) >>
  drule inline_routed_leaf_valid_choices >> strip_tac >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum (drule_then assume_tac) >>
  first_x_assum (drule_then assume_tac) >>
  Cases_on `choice` >> gvs[] >>
  metis_tac[functionInlinerOriginTheory.qualified_origin_phi_labels_closed,
    functionInlinerEnvelopesTheory.inline_annotated_origin_exists,
    functionInlinerOccurrencesTheory.inline_annotated_edit_fetch_facts]
QED

Theorem inline_edit_keep_phi_prefix_fields:
  inline_site_edit_valid e /\ ALL_DISTINCT (fn_labels e.ise_caller) /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  lookup_block l e.ise_caller.fn_blocks = SOME bb /\
  ~MEM e.ise_return (fn_labels e.ise_caller) ==>
  ?tb. lookup_block l e.ise_final.fn_blocks = SOME tb /\
    MAP inline_inst_fields
      (TAKE (phi_prefix_length tb.bb_instructions) tb.bb_instructions) =
    MAP (\inst. inline_inst_fields (inline_edit_repair e source_bb l inst))
      (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)
Proof
  strip_tac >>
  `e.ise_index < LENGTH source_bb.bb_instructions /\
   (EL e.ise_index source_bb.bb_instructions).inst_opcode = INVOKE` by
    (gvs[inline_site_edit_valid_def] >>
     drule_all functionInlinerWfTheory.find_invoke_site_lookup >> simp[]) >>
  `e.ise_final = renumber_fn_inst_ids
    (fix_inline_phis e.ise_block e.ise_return
      <|bb_label := e.ise_return;
        bb_instructions := DROP (e.ise_index+1) source_bb.bb_instructions|>
      (inline_call_site e.ise_prefix e.ise_return e.ise_caller e.ise_callee
        e.ise_block e.ise_index))` by
    (gvs[inline_site_edit_valid_def] >>
     metis_tac[functionInlinerSimulationTheory.inline_one_site_final_assembly]) >>
  drule_all functionInlinerPhiTransportTheory.inline_caller_produced_phi_prefix_fields >>
  disch_then (qspecl_then [`e.ise_return`,
    `<|bb_label := e.ise_return;
       bb_instructions := DROP (e.ise_index+1) source_bb.bb_instructions|>`,
    `e.ise_prefix`, `e.ise_callee`] strip_assume_tac) >>
  qexists `tb` >> simp[] >>
  `bb.bb_label = l` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  Cases_on `MEM l (bb_succs <|bb_label := e.ise_return;
       bb_instructions := DROP (e.ise_index+1) source_bb.bb_instructions|>)` >>
  gvs[MAP_MAP_o] >> irule MAP_CONG >> simp[inline_edit_repair_def] >>
  qspec_then `bb.bb_instructions` mp_tac
    analysisSimProofsBaseTheory.phi_prefix_all_phi >>
  simp[EVERY_MEM]
QED

Theorem inline_edit_enter_phi_prefix_fields:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  lookup_block l e.ise_callee.fn_blocks = SOME bb /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  ~MEM (STRCAT e.ise_prefix l) (fn_labels e.ise_caller) /\
  STRCAT e.ise_prefix l <> e.ise_return /\
  (!q. MEM q (bb_succs <|bb_label := e.ise_return;
        bb_instructions := DROP (e.ise_index+1) source_bb.bb_instructions|>) ==>
       MEM q (fn_labels e.ise_caller)) /\
  inliner_phi_labels_closed e.ise_callee ==>
  ?tb. lookup_block (STRCAT e.ise_prefix l) e.ise_final.fn_blocks = SOME tb /\
    MAP inline_inst_fields
      (TAKE (phi_prefix_length tb.bb_instructions) tb.bb_instructions) =
    MAP (\inst. inline_inst_fields
      (inline_rename_inst (STRCAT e.ise_prefix) (STRCAT e.ise_prefix) inst))
      (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)
Proof
  strip_tac >>
  `e.ise_final = renumber_fn_inst_ids
    (fix_inline_phis e.ise_block e.ise_return
      <|bb_label := e.ise_return;
        bb_instructions := DROP (e.ise_index+1) source_bb.bb_instructions|>
      (inline_call_site e.ise_prefix e.ise_return e.ise_caller e.ise_callee
        e.ise_block e.ise_index))` by
    (gvs[inline_site_edit_valid_def] >>
     metis_tac[functionInlinerSimulationTheory.inline_one_site_final_assembly]) >>
  drule_all functionInlinerSimulationTheory.inline_clone_produced_phi_prefix_fields >>
  disch_then (qspec_then `e.ise_index` strip_assume_tac) >>
  qexists `tb` >> simp[MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem inline_phi_rename_shape[local]:
  !ops. phi_well_formed ops ==>
    phi_well_formed (MAP (inline_rename_operand vr lr) ops)
Proof
  recInduct venomWfTheory.phi_well_formed_ind >>
  simp[venomWfTheory.phi_well_formed_def, inline_rename_operand_def]
QED

Theorem inline_edit_repair_phi_shape:
  phi_well_formed inst.inst_operands ==>
  phi_well_formed (inline_edit_repair e source_bb l inst).inst_operands
Proof
  strip_tac >> simp[inline_edit_repair_def] >> IF_CASES_TAC >> simp[] >>
  simp[cfgTransformTheory.subst_label_inst_def] >>
  `subst_label_op e.ise_block e.ise_return =
    inline_rename_operand I (\q. if q = e.ise_block then e.ise_return else q)` by
    (simp[FUN_EQ_THM] >> Cases >>
     simp[cfgTransformTheory.subst_label_op_def, inline_rename_operand_def,
       COND_RAND]) >>
  simp[inline_phi_rename_shape]
QED

Theorem inline_phi_prefix_fields_at[local]:
  MAP inline_inst_fields (TAKE (phi_prefix_length ys) ys) =
    MAP (\inst. inline_inst_fields (f inst)) (TAKE (phi_prefix_length xs) xs) /\
  k < phi_prefix_length xs ==>
  k < phi_prefix_length ys /\
  inline_inst_fields (EL k ys) = inline_inst_fields (f (EL k xs))
Proof
  strip_tac >>
  `phi_prefix_length xs <= LENGTH xs /\ phi_prefix_length ys <= LENGTH ys` by
    simp[venomExecProofsTheory.phi_prefix_length_le] >>
  `LENGTH (TAKE (phi_prefix_length ys) ys) =
   LENGTH (TAKE (phi_prefix_length xs) xs)` by metis_tac[LENGTH_MAP] >>
  gvs[LENGTH_TAKE] >>
  gvs[LIST_EQ_REWRITE, EL_MAP, EL_TAKE] >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[]
QED

Theorem inline_edit_keep_phi_at:
  inline_site_edit_valid e /\ ALL_DISTINCT (fn_labels e.ise_caller) /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  lookup_block l e.ise_caller.fn_blocks = SOME bb /\
  lookup_block l e.ise_final.fn_blocks = SOME tb /\
  inliner_phi_labels_closed e.ise_caller /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  MEM prev (fn_labels e.ise_caller) /\
  k < phi_prefix_length bb.bb_instructions /\
  phi_well_formed (EL k bb.bb_instructions).inst_operands ==>
  k < phi_prefix_length tb.bb_instructions /\
  (EL k tb.bb_instructions).inst_opcode = PHI /\
  phi_well_formed (EL k tb.bb_instructions).inst_operands /\
  (EL k tb.bb_instructions).inst_outputs = (EL k bb.bb_instructions).inst_outputs /\
  ?q. SND (inline_phi_entry_step (InlineKeep e) (l,SOME prev)) = SOME q /\
    resolve_phi q (EL k tb.bb_instructions).inst_operands =
      resolve_phi prev (EL k bb.bb_instructions).inst_operands
Proof
  strip_tac >> drule_all inline_edit_keep_phi_prefix_fields >> strip_tac >>
  gvs[] >> drule_all inline_phi_prefix_fields_at >> strip_tac >>
  `(EL k bb.bb_instructions).inst_opcode = PHI /\
   k < LENGTH bb.bb_instructions` by
    (qspec_then `bb.bb_instructions` assume_tac
       venomExecProofsTheory.phi_prefix_length_le >>
     qspec_then `bb.bb_instructions` mp_tac
       analysisSimProofsBaseTheory.phi_prefix_all_phi >>
     simp[EVERY_EL, LENGTH_TAKE, EL_TAKE] >>
     disch_then (qspec_then `k` mp_tac) >> simp[]) >>
  `EVERY (\op. !q. op = Label q ==> MEM q (fn_labels e.ise_caller))
    (EL k bb.bb_instructions).inst_operands` by
    (gvs[functionInlinerOriginTheory.inliner_phi_labels_closed_def, EVERY_MEM] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM,
       unitShapeDefsTheory.MEM_fn_insts_blocks_iff, venomInstTheory.fn_insts_def, MEM_EL]) >>
  drule_all inline_phi_entry_keep_selection >> strip_tac >>
  drule inline_edit_repair_phi_shape >>
  disch_then (qspecl_then [`source_bb`, `l`, `e`] assume_tac) >>
  gvs[inline_inst_fields_def, inline_edit_repair_def,
    cfgTransformTheory.subst_label_inst_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem inline_edit_enter_phi_at:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  lookup_block l e.ise_callee.fn_blocks = SOME bb /\
  lookup_block (STRCAT e.ise_prefix l) e.ise_final.fn_blocks = SOME tb /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  ~MEM (STRCAT e.ise_prefix l) (fn_labels e.ise_caller) /\
  STRCAT e.ise_prefix l <> e.ise_return /\
  (!q. MEM q (bb_succs <|bb_label := e.ise_return;
        bb_instructions := DROP (e.ise_index+1) source_bb.bb_instructions|>) ==>
       MEM q (fn_labels e.ise_caller)) /\
  inliner_phi_labels_closed e.ise_callee /\
  k < phi_prefix_length bb.bb_instructions /\
  phi_well_formed (EL k bb.bb_instructions).inst_operands ==>
  k < phi_prefix_length tb.bb_instructions /\
  (EL k tb.bb_instructions).inst_opcode = PHI /\
  phi_well_formed (EL k tb.bb_instructions).inst_operands /\
  (EL k tb.bb_instructions).inst_outputs =
    MAP (STRCAT e.ise_prefix) (EL k bb.bb_instructions).inst_outputs /\
  ?q. SND (inline_phi_entry_step (InlineEnter e) (l,SOME prev)) = SOME q /\
    resolve_phi q (EL k tb.bb_instructions).inst_operands =
      OPTION_MAP (inline_rename_operand (STRCAT e.ise_prefix) (STRCAT e.ise_prefix))
        (resolve_phi prev (EL k bb.bb_instructions).inst_operands)
Proof
  strip_tac >> drule_all inline_edit_enter_phi_prefix_fields >> strip_tac >>
  gvs[] >> drule_all inline_phi_prefix_fields_at >> strip_tac >>
  `(EL k bb.bb_instructions).inst_opcode = PHI` by
    (qspec_then `bb.bb_instructions` assume_tac
       venomExecProofsTheory.phi_prefix_length_le >>
     qspec_then `bb.bb_instructions` mp_tac
       analysisSimProofsBaseTheory.phi_prefix_all_phi >>
     simp[EVERY_EL, LENGTH_TAKE, EL_TAKE] >>
     disch_then (qspec_then `k` mp_tac) >> simp[]) >>
  drule inline_phi_entry_enter_selection >>
  disch_then (qspecl_then [`prev`, `l`] strip_assume_tac) >>
  gvs[inline_inst_fields_def, inline_rename_inst_def] >>
  simp[inline_phi_rename_shape]
QED

Theorem inline_routed_phi_at:
  !cert root p fn path. inline_routed_leaf cert root p fn path ==>
  !C n l prev bb k.
    inline_annotated_origin C n root cert /\
    lookup_block l fn.fn_blocks = SOME bb /\
    MEM prev (fn_labels fn) /\
    k < phi_prefix_length bb.bb_instructions /\
    phi_well_formed (EL k bb.bb_instructions).inst_operands ==>
    ?tb q. lookup_block (FST (inline_phi_entry_path path (l,SOME prev)))
             root.fn_blocks = SOME tb /\
      SND (inline_phi_entry_path path (l,SOME prev)) = SOME q /\
      k < phi_prefix_length tb.bb_instructions /\
      (EL k tb.bb_instructions).inst_opcode = PHI /\
      phi_well_formed (EL k tb.bb_instructions).inst_operands /\
      (EL k tb.bb_instructions).inst_outputs =
        MAP (inline_path_rename path) (EL k bb.bb_instructions).inst_outputs /\
      (!v. resolve_phi prev (EL k bb.bb_instructions).inst_operands = SOME (Var v) ==>
        resolve_phi q (EL k tb.bb_instructions).inst_operands =
          SOME (Var (inline_path_rename path v)))
Proof
  ho_match_mp_tac inline_routed_leaf_strongind >> rpt conj_tac
  >- (simp[inline_phi_entry_path_def, inline_path_rename_def] >>
      rpt strip_tac >>
      qspec_then `bb.bb_instructions` assume_tac
        venomExecProofsTheory.phi_prefix_length_le >>
      qspec_then `bb.bb_instructions` mp_tac
        analysisSimProofsBaseTheory.phi_prefix_all_phi >>
      simp[EVERY_EL, LENGTH_TAKE, EL_TAKE] >>
      disch_then (qspec_then `k` mp_tac) >> simp[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule functionInlinerOccurrencesTheory.inline_annotated_origin_edit_elim >>
  simp[] >> strip_tac >>
  first_x_assum (drule_then (drule_then assume_tac)) >>
  first_x_assum (qspecl_then [`prev`, `k`] mp_tac) >>
  simp[] >> strip_tac >>
  `MEM l (fn_labels fn)` by
    metis_tac[venomExecPropsTheory.lookup_block_label,
      venomExecPropsTheory.lookup_block_MEM, venomInstTheory.fn_labels_def, MEM_MAP] >>
  drule inline_routed_phi_entry_support >>
  disch_then (qspecl_then [`l`, `SOME prev`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[] >>
  drule_all functionInlinerOccurrencesTheory.inline_annotated_edit_fetch_facts >>
  strip_tac >>
  `wf_function e.ise_caller /\ inliner_phi_labels_closed e.ise_caller /\
   inliner_phi_labels_closed e.ise_callee` by
    metis_tac[functionInlinerEnvelopesTheory.inline_annotated_origin_erasure,
      functionInlinerOriginTheory.qualified_origin_erasure,
      functionInlinerOriginTheory.inliner_fn_origin_structure,
      functionInlinerOriginTheory.qualified_origin_phi_labels_closed] >>
  `ALL_DISTINCT (fn_labels e.ise_caller) /\ fn_succs_closed e.ise_caller` by
    gvs[venomWfTheory.wf_function_def] >>
  rename1 `lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb` >>
  `!z. MEM z (bb_succs <|bb_label := e.ise_return;
       bb_instructions := DROP (e.ise_index+1) source_bb.bb_instructions|>) ==>
      MEM z (fn_labels e.ise_caller)` by
    (Cases_on `e.ise_index+1 < LENGTH source_bb.bb_instructions`
     >- metis_tac[functionInlinerSimulationTheory.inline_saved_suffix_succs_closed] >>
     simp[DROP_LENGTH_TOO_LONG, venomInstTheory.bb_succs_def]) >>
  Cases_on `inline_phi_entry_path path (l,SOME prev)` >> gvs[]
  >- (qpat_assum `lookup_block _ e.ise_caller.fn_blocks = SOME tb`
        (mp_then (Pat `lookup_block l e.ise_caller.fn_blocks = SOME bb`)
          mp_tac inline_edit_keep_phi_prefix_fields) >>
      disch_then (qspec_then `source_bb` mp_tac) >> simp[] >> strip_tac >>
      drule_all inline_edit_keep_phi_at >> strip_tac >>
      simp[inline_phi_entry_path_append] >>
      simp[inline_phi_entry_path_def, inline_phi_entry_step_label,
        inline_choice_rename_def, inline_path_rename_append,
        inline_path_rename_def, combinTheory.o_DEF] >>
      metis_tac[]) >>
  `~MEM (STRCAT e.ise_prefix q') (fn_labels e.ise_caller) /\
   STRCAT e.ise_prefix q' <> e.ise_return` by metis_tac[] >>
  drule_all inline_edit_enter_phi_prefix_fields >> strip_tac >>
  drule_all inline_edit_enter_phi_at >>
  disch_then (qspec_then `q` strip_assume_tac) >>
  gvs[inline_phi_entry_step_def] >>
  simp[inline_phi_entry_path_append] >>
  simp[inline_phi_entry_path_def, inline_phi_entry_step_def,
    inline_path_rename_append, inline_path_rename_def,
    inline_choice_rename_def, combinTheory.o_DEF, MAP_MAP_o] >>
  rpt strip_tac >>
  qpat_x_assum `!v. resolve_phi _ _ = SOME (Var v) ==> _` drule >>
  simp[inline_rename_operand_def]
QED

Theorem inline_routed_phi_prefix_length:
  !cert root p fn path. inline_routed_leaf cert root p fn path ==>
  !C n l prev bb.
    inline_annotated_origin C n root cert /\
    lookup_block l fn.fn_blocks = SOME bb ==>
    ?tb. lookup_block (FST (inline_phi_entry_path path (l,prev)))
           root.fn_blocks = SOME tb /\
      phi_prefix_length tb.bb_instructions = phi_prefix_length bb.bb_instructions
Proof
  ho_match_mp_tac inline_routed_leaf_strongind >> rpt conj_tac
  >- simp[inline_phi_entry_path_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule functionInlinerOccurrencesTheory.inline_annotated_origin_edit_elim >>
  simp[] >> strip_tac >>
  first_x_assum (drule_then (drule_then assume_tac)) >>
  first_x_assum (qspec_then `prev` mp_tac) >> simp[] >> strip_tac >>
  gvs[] >>
  drule_all functionInlinerOccurrencesTheory.inline_annotated_edit_fetch_facts >>
  strip_tac >>
  `wf_function e.ise_caller /\ inliner_phi_labels_closed e.ise_caller /\
   inliner_phi_labels_closed e.ise_callee` by
    metis_tac[functionInlinerEnvelopesTheory.inline_annotated_origin_erasure,
      functionInlinerOriginTheory.qualified_origin_erasure,
      functionInlinerOriginTheory.inliner_fn_origin_structure,
      functionInlinerOriginTheory.qualified_origin_phi_labels_closed] >>
  `ALL_DISTINCT (fn_labels e.ise_caller) /\ fn_succs_closed e.ise_caller` by
    gvs[venomWfTheory.wf_function_def] >>
  rename1 `lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb` >>
  `!z. MEM z (bb_succs <|bb_label := e.ise_return;
       bb_instructions := DROP (e.ise_index+1) source_bb.bb_instructions|>) ==>
      MEM z (fn_labels e.ise_caller)` by
    (Cases_on `e.ise_index+1 < LENGTH source_bb.bb_instructions`
     >- metis_tac[functionInlinerSimulationTheory.inline_saved_suffix_succs_closed] >>
     simp[DROP_LENGTH_TOO_LONG, venomInstTheory.bb_succs_def]) >>
  Cases_on `inline_phi_entry_path path (l,prev)` >> gvs[]
  >- (qpat_assum `lookup_block _ e.ise_caller.fn_blocks = SOME tb`
        (mp_then (Pat `lookup_block l e.ise_caller.fn_blocks = SOME bb`)
          mp_tac inline_edit_keep_phi_prefix_fields) >>
      disch_then (qspec_then `source_bb` mp_tac) >> simp[] >> strip_tac >>
      simp[inline_phi_entry_path_append, inline_phi_entry_path_def,
        inline_phi_entry_step_label] >>
      `phi_prefix_length bb.bb_instructions <= LENGTH tb.bb_instructions` by
        metis_tac[venomExecProofsTheory.phi_prefix_length_le] >>
      qexists_tac `tb'` >> simp[inline_choice_rename_def] >>
      qpat_x_assum `MAP _ _ = MAP _ _` (mp_tac o Q.AP_TERM `LENGTH`) >>
      simp[LENGTH_TAKE, venomExecProofsTheory.phi_prefix_length_le]) >>
  `MEM q (fn_labels e.ise_callee)` by
    metis_tac[venomExecPropsTheory.lookup_block_label,
      venomExecPropsTheory.lookup_block_MEM, venomInstTheory.fn_labels_def, MEM_MAP] >>
  qpat_assum `lookup_block q e.ise_callee.fn_blocks = SOME tb`
    (mp_then (Pat `lookup_block l e.ise_callee.fn_blocks = SOME bb`)
      mp_tac inline_edit_enter_phi_prefix_fields) >>
  disch_then (qspec_then `source_bb` mp_tac) >> simp[] >> strip_tac >>
  simp[inline_phi_entry_path_append, inline_phi_entry_path_def,
    inline_phi_entry_step_label] >>
  `phi_prefix_length bb.bb_instructions <= LENGTH tb.bb_instructions` by
    metis_tac[venomExecProofsTheory.phi_prefix_length_le] >>
  qexists_tac `tb'` >> simp[inline_choice_rename_def] >>
  qpat_x_assum `MAP _ _ = MAP _ _` (mp_tac o Q.AP_TERM `LENGTH`) >>
  simp[LENGTH_TAKE, venomExecProofsTheory.phi_prefix_length_le]
QED

Theorem inline_routed_leaf_source_member:
  !cert root p fn path. inline_routed_leaf cert root p fn path ==>
  !C n. inline_annotated_origin C n root cert ==> MEM fn C.ctx_functions
Proof
  ho_match_mp_tac inline_routed_leaf_strongind >> rpt conj_tac
  >- (rpt strip_tac >>
      drule functionInlinerOccurrencesTheory.inline_annotated_entry_identity >>
      simp[functionInlinerOccurrencesTheory.inline_entry_function_def]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule functionInlinerOccurrencesTheory.inline_annotated_origin_edit_elim >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED
