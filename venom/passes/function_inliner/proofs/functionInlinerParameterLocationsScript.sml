(* Positions of parameter intervals, including their one-past-end boundary.
   In particular a boundary need not be a fetched ordinary instruction. *)
Theory functionInlinerParameterLocations
Ancestors
  functionInlinerSelectedParameterDescriptors functionInlinerSelectedParameters
  functionInlinerReachableCuts functionInlinerParameterPropagation
  functionInlinerLocation functionInlinerDefs venomInst list rich_list

Theorem inline_parameter_focus_length:
  is_param_opcode (EL j cb.bb_instructions).inst_opcode \/
  (EL j cb.bb_instructions).inst_opcode = ASSIGN ==>
  LENGTH (FST (inline_cell_focus e bb cb j)) = 1
Proof
  strip_tac >>
  gvs[inline_cell_focus_def, clone_instruction_def, rewrite_inline_inst_def,
      is_param_opcode_def] >>
  Cases_on `SND (inline_cell_prefix e bb cb j) <
    LENGTH (rotate_invoke_ops (EL e.ise_index bb.bb_instructions).inst_operands)` >>
  simp[]
QED

Theorem inline_parameter_prefix_length_suc:
  j < LENGTH cb.bb_instructions /\
  (is_param_opcode (EL j cb.bb_instructions).inst_opcode \/
   (EL j cb.bb_instructions).inst_opcode = ASSIGN) ==>
  LENGTH (FST (inline_cell_prefix e bb cb (SUC j))) =
    SUC (LENGTH (FST (inline_cell_prefix e bb cb j)))
Proof
  strip_tac >> drule inline_cell_prefix_suc >>
  disch_then (qspecl_then [`e`, `bb`] assume_tac) >>
  simp[inline_parameter_focus_length]
QED

Theorem inline_parameter_prefix_length_interval:
  !count start.
  start + count <= LENGTH cb.bb_instructions /\
  (!k. k < count ==>
    is_param_opcode (EL (start+k) cb.bb_instructions).inst_opcode \/
    (EL (start+k) cb.bb_instructions).inst_opcode = ASSIGN) ==>
  LENGTH (FST (inline_cell_prefix e bb cb (start+count))) =
    LENGTH (FST (inline_cell_prefix e bb cb start)) + count
Proof
  Induct >> simp[] >> qx_gen_tac `start` >> strip_tac >>
  rename1 `start + SUC n <= LENGTH cb.bb_instructions` >>
  `start + n < LENGTH cb.bb_instructions` by decide_tac >>
  `LENGTH (FST (inline_cell_prefix e bb cb (SUC (start+n)))) =
     SUC (LENGTH (FST (inline_cell_prefix e bb cb (start+n))))` by
    (irule inline_parameter_prefix_length_suc >> simp[arithmeticTheory.ADD_COMM]) >>
  qpat_x_assum `!start. _ /\ _ ==> LENGTH _ = _`
    (qspec_then `start` mp_tac) >>
  impl_tac >- (conj_tac >- decide_tac >> rpt strip_tac >>
    simp[]) >>
  strip_tac >> gvs[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD_COMM]
QED

Theorem inline_entry_parameter_prefix_length:
  cb.bb_instructions = params ++ tail /\ param_insts_from slot params /\
  j <= LENGTH params ==>
  LENGTH (FST (inline_cell_prefix e bb cb j)) = j
Proof
  strip_tac >>
  `LENGTH (FST (inline_cell_prefix e bb cb (0+j))) =
     LENGTH (FST (inline_cell_prefix e bb cb 0)) + j` suffices_by simp[] >>
  irule inline_parameter_prefix_length_interval >> reverse conj_tac >- simp[] >>
  rpt strip_tac >> disj1_tac >>
  `k < LENGTH params` by decide_tac >>
  drule_all callLayoutDefsTheory.param_insts_from_el >>
  simp[callLayoutDefsTheory.param_inst_at_def, EL_APPEND_EQN]
QED

(* Coordinates of every EnterCell are fixed by the current source block,
   independently of the parameter counter and the original source slot. *)
Theorem inline_enter_parameter_interval_cell:
  !e c d bb cb start k count.
  inline_cell_frame (EnterCell e 0) c d /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  lookup_block c.ic_block e.ise_callee.fn_blocks = SOME cb /\
  c.ic_index = start + k /\ k < (count:num) /\
  start + count <= LENGTH cb.bb_instructions /\
  (!i. i < count ==>
    is_param_opcode (EL (start+i) cb.bb_instructions).inst_opcode \/
    (EL (start+i) cb.bb_instructions).inst_opcode = ASSIGN) ==>
  d.ic_block = STRCAT e.ise_prefix c.ic_block /\
  d.ic_index = LENGTH (FST (inline_cell_prefix e bb cb start)) + k
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH (FST (inline_cell_prefix e bb cb (start+k))) =
    LENGTH (FST (inline_cell_prefix e bb cb start)) + k` by
    (irule inline_parameter_prefix_length_interval >> reverse conj_tac >- decide_tac >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  gvs[inline_cell_frame_def, inline_make_cell_def]
QED

(* Total boundary map: equality with the selected index denotes the new JMP,
   not the NONE returned by inline_choice_location for an ordinary Keep. *)
Definition inline_keep_boundary_def:
  inline_keep_boundary e l j =
    if l = e.ise_block /\ e.ise_index < j
    then (e.ise_return,j - (e.ise_index+1)) else (l,j)
End

Theorem inline_interval_excludes_split:
  !start n index:num.
  (!k. k < n ==> start+k <> index) ==>
  index < start \/ start+n <= index
Proof
  rpt strip_tac >> spose_not_then strip_assume_tac >>
  first_x_assum (qspec_then `index-start` mp_tac) >> simp[]
QED

Theorem inline_keep_boundary_interval:
  (!k. k < n ==> start+k <> e.ise_index) ==>
  !k. k <= n ==>
    inline_keep_boundary e l (start+k) =
      (FST (inline_keep_boundary e l start),
       SND (inline_keep_boundary e l start) + k)
Proof
  strip_tac >> drule inline_interval_excludes_split >> strip_tac >>
  simp[inline_keep_boundary_def] >> rpt strip_tac >>
  Cases_on `l = e.ise_block` >> simp[] >>
  Cases_on `e.ise_index < start` >> simp[] >>
  `~(e.ise_index < start+k)` by decide_tac >> simp[]
QED

Theorem inline_keep_cell_boundary:
  inline_cell_frame (KeepCell e) c d ==>
  (d.ic_block,d.ic_index) = inline_keep_boundary e c.ic_block c.ic_index
Proof
  simp[inline_cell_frame_def, inline_make_cell_def, inline_keep_boundary_def] >>
  rpt strip_tac >> gvs[] >> IF_CASES_TAC >> simp[]
QED

Theorem inline_keep_parameter_interval_cell:
  inline_cell_frame (KeepCell e) c d /\
  c.ic_block = l /\ c.ic_index = start+k /\ k < n /\
  (l = e.ise_block ==> !i. i < n ==> start+i <> e.ise_index) ==>
  d.ic_block = FST (inline_keep_boundary e l start) /\
  d.ic_index = SND (inline_keep_boundary e l start) + k
Proof
  strip_tac >>
  `inline_keep_boundary e l (start+k) =
    (FST (inline_keep_boundary e l start),
     SND (inline_keep_boundary e l start) + k)` by
    (Cases_on `l = e.ise_block` >-
      (irule inline_keep_boundary_interval >> qexists `n` >> simp[]) >>
     simp[inline_keep_boundary_def]) >>
  drule inline_keep_cell_boundary >> strip_tac >> gvs[]
QED

Theorem inline_selected_parameter_interval_endpoint:
  inline_cell_frame (SelectedJump e) c d /\
  c.ic_block = l /\ c.ic_index = start+n ==>
  (d.ic_block,d.ic_index) = inline_keep_boundary e l (start+n) /\
  FST d.ic_fields = JMP
Proof
  simp[inline_cell_frame_def, inline_make_cell_def, inline_keep_boundary_def] >>
  rpt strip_tac >> gvs[]
QED

Definition inline_parameter_interval_def:
  inline_parameter_interval fn l start n <=>
    ?bb. lookup_block l fn.fn_blocks = SOME bb /\
      start+n <= LENGTH bb.bb_instructions /\
      (!k. k < n ==>
        is_param_opcode (EL (start+k) bb.bb_instructions).inst_opcode \/
        (EL (start+k) bb.bb_instructions).inst_opcode = ASSIGN)
End

Definition inline_parameter_boundary_def:
  (inline_parameter_boundary (InlineKeep e) fn l j fn' l' j' <=>
    fn = e.ise_caller /\ fn' = e.ise_final /\
    (?cb. lookup_block l fn.fn_blocks = SOME cb /\
      j <= LENGTH cb.bb_instructions) /\
    (l',j') = inline_keep_boundary e l j /\
    (?tb. lookup_block l' fn'.fn_blocks = SOME tb /\
      j' <= LENGTH tb.bb_instructions)) /\
  (inline_parameter_boundary (InlineEnter e) fn l j fn' l' j' <=>
    fn = e.ise_callee /\ fn' = e.ise_final /\
    (?bb cb. lookup_block l fn.fn_blocks = SOME cb /\
      j <= LENGTH cb.bb_instructions /\
      lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
      l' = STRCAT e.ise_prefix l /\
      j' = LENGTH (FST (inline_cell_prefix e bb cb j))) /\
    (?tb. lookup_block l' fn'.fn_blocks = SOME tb /\
      j' <= LENGTH tb.bb_instructions))
End

Definition inline_parameter_boundary_path_def:
  (inline_parameter_boundary_path [] fn l j root l' j' <=>
    root = fn /\ l' = l /\ j' = j) /\
  (inline_parameter_boundary_path (choice::rest) fn l j root l' j' <=>
    ?mid ml mj. inline_parameter_boundary choice fn l j mid ml mj /\
      inline_parameter_boundary_path rest mid ml mj root l' j')
End

Theorem inline_parameter_boundary_functional:
  inline_parameter_boundary choice fn l j a al aj /\
  inline_parameter_boundary choice fn l j b bl bj ==>
  a = b /\ al = bl /\ aj = bj
Proof
  Cases_on `choice` >> simp[inline_parameter_boundary_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[pairTheory.PAIR_EQ]
QED

Theorem inline_parameter_boundary_path_functional:
  !path fn l j a al aj b bl bj.
  inline_parameter_boundary_path path fn l j a al aj /\
  inline_parameter_boundary_path path fn l j b bl bj ==>
  a = b /\ al = bl /\ aj = bj
Proof
  Induct >> simp[inline_parameter_boundary_path_def] >> rpt strip_tac >>
  `mid = mid' /\ ml = ml' /\ mj = mj'` by
    metis_tac[inline_parameter_boundary_functional] >>
  gvs[] >> metis_tac[]
QED

(* Repair and renumbering preserve block extent even when no next cell exists. *)
Theorem inline_edit_boundary_extent:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  lookup_block l
    (inline_call_site e.ise_prefix e.ise_return e.ise_caller e.ise_callee
      e.ise_block e.ise_index).fn_blocks = SOME bb ==>
  ?tb. lookup_block l e.ise_final.fn_blocks = SOME tb /\
    LENGTH tb.bb_instructions = LENGTH bb.bb_instructions
Proof
  strip_tac >>
  fs[functionInlinerActivationTheory.inline_site_edit_valid_def] >>
  drule_all functionInlinerPhiTransportTheory.inline_one_site_lookup_fields >>
  strip_tac >> qexists `tb` >> simp[] >>
  qpat_x_assum `MAP inline_inst_fields _ = _`
    (mp_tac o AP_TERM ``LENGTH : (opcode # operand list # string list) list -> num``) >>
  simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem inline_keep_boundary_produce:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  e.ise_index < LENGTH source_bb.bb_instructions /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  lookup_block l e.ise_caller.fn_blocks = SOME cb /\
  j <= LENGTH cb.bb_instructions ==>
  inline_parameter_boundary (InlineKeep e) e.ise_caller l j e.ise_final
    (FST (inline_keep_boundary e l j)) (SND (inline_keep_boundary e l j))
Proof
  strip_tac >>
  simp[inline_parameter_boundary_def] >>
  Cases_on `l = e.ise_block` >> gvs[inline_keep_boundary_def]
      >- (Cases_on `e.ise_index < j` >> gvs[]
          >- (drule_all functionInlinerSiteLayoutTheory.inline_call_site_lookup_return >>
              disch_then (qspecl_then [`e.ise_prefix`, `e.ise_index`, `e.ise_callee`] assume_tac) >>
              drule_all inline_edit_boundary_extent >> strip_tac >>
              qexists `tb` >> simp[])
          >> drule functionInlinerSiteLayoutTheory.inline_call_site_lookup_call >>
          disch_then (qspecl_then [`e.ise_return`, `e.ise_prefix`, `e.ise_index`, `e.ise_callee`] assume_tac) >>
          drule_all inline_edit_boundary_extent >> strip_tac >> qexists `tb` >> simp[])
      >> drule_all functionInlinerSiteLayoutTheory.inline_call_site_lookup_other >>
      disch_then (qspecl_then [`e.ise_return`, `e.ise_prefix`, `e.ise_index`, `e.ise_callee`] assume_tac) >>
      drule_all inline_edit_boundary_extent >> strip_tac >> qexists `tb` >> simp[]
QED

Theorem inline_cell_prefix_length_bound:
  j <= LENGTH cb.bb_instructions ==>
  LENGTH (FST (inline_cell_prefix e bb cb j)) <=
    LENGTH (FST (inline_cell_prefix e bb cb (LENGTH cb.bb_instructions)))
Proof
  strip_tac >>
  `cb.bb_instructions = TAKE j cb.bb_instructions ++ DROP j cb.bb_instructions`
    by simp[] >>
  simp[inline_cell_prefix_def] >>
  qpat_x_assum `cb.bb_instructions = _ ++ _` (fn th =>
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [th]) >>
  pure_rewrite_tac[MAP_APPEND,
    functionInlinerSiteLayoutTheory.rewrite_inline_insts_append] >> simp[]
QED

Theorem inline_enter_boundary_produce:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  lookup_block l e.ise_callee.fn_blocks = SOME cb /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  ~MEM (STRCAT e.ise_prefix l) (fn_labels e.ise_caller) /\
  STRCAT e.ise_prefix l <> e.ise_return /\
  j <= LENGTH cb.bb_instructions ==>
  inline_parameter_boundary (InlineEnter e) e.ise_callee l j e.ise_final
    (STRCAT e.ise_prefix l) (LENGTH (FST (inline_cell_prefix e bb cb j)))
Proof
  strip_tac >> simp[inline_parameter_boundary_def] >>
  drule_all functionInlinerSiteLayoutTheory.inline_call_site_lookup_clone >>
  disch_then (qspec_then `e.ise_index` assume_tac) >>
  drule_all inline_edit_boundary_extent >> strip_tac >>
  qexists `tb` >> simp[] >>
  `LENGTH (FST (inline_cell_prefix e bb cb j)) <=
    LENGTH (FST (inline_cell_prefix e bb cb (LENGTH cb.bb_instructions)))`
    by (irule inline_cell_prefix_length_bound >> simp[]) >>
  gvs[inline_cell_prefix_def, rewrite_inline_block_def, clone_basic_block_def,
       pairTheory.UNCURRY]
QED

(* Empty intervals use lookup and extent, never a fabricated first cell. *)
Theorem inline_keep_empty_selected_boundary:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  e.ise_index < LENGTH bb.bb_instructions /\
  ~MEM e.ise_return (fn_labels e.ise_caller) ==>
  inline_parameter_interval e.ise_caller e.ise_block e.ise_index 0 /\
  inline_parameter_boundary (InlineKeep e) e.ise_caller e.ise_block
    e.ise_index e.ise_final e.ise_block e.ise_index
Proof
  strip_tac >> conj_tac >- simp[inline_parameter_interval_def] >>
  `inline_parameter_boundary (InlineKeep e) e.ise_caller e.ise_block
    e.ise_index e.ise_final
    (FST (inline_keep_boundary e e.ise_block e.ise_index))
    (SND (inline_keep_boundary e e.ise_block e.ise_index))` by
    (irule inline_keep_boundary_produce >> simp[]) >>
  gvs[inline_keep_boundary_def]
QED

Theorem inline_keep_empty_end_boundary:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  e.ise_index < LENGTH source_bb.bb_instructions /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  lookup_block l e.ise_caller.fn_blocks = SOME cb ==>
  inline_parameter_interval e.ise_caller l (LENGTH cb.bb_instructions) 0 /\
  inline_parameter_boundary (InlineKeep e) e.ise_caller l
    (LENGTH cb.bb_instructions) e.ise_final
    (FST (inline_keep_boundary e l (LENGTH cb.bb_instructions)))
    (SND (inline_keep_boundary e l (LENGTH cb.bb_instructions)))
Proof
  strip_tac >> conj_tac >- simp[inline_parameter_interval_def] >>
  irule inline_keep_boundary_produce >> simp[]
QED
