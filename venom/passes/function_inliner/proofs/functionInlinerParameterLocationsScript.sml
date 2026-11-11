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

Theorem inline_parameter_frame_class:
  inline_cell_frame tag c d /\ (!e. tag <> SelectedJump e) /\
  (is_param_opcode (FST c.ic_fields) \/ FST c.ic_fields = ASSIGN) ==>
  is_param_opcode (FST d.ic_fields) \/ FST d.ic_fields = ASSIGN
Proof
  Cases_on `tag` >>
  simp[inline_cell_frame_def, inline_make_cell_def] >> rpt strip_tac >> gvs[] >>
  gvs[get_instruction_def] >>
  gvs[functionInlinerSiteLayoutTheory.inline_inst_fields_def, inline_edit_repair_def,
      clone_instruction_def, inline_cell_focus_def,
      rewrite_inline_inst_def, is_param_opcode_def] >>
  rpt IF_CASES_TAC >> gvs[]
QED

Theorem inline_keep_interval_points:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  e.ise_index < LENGTH source_bb.bb_instructions /\
  (EL e.ise_index source_bb.bb_instructions).inst_opcode = INVOKE /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  inline_parameter_interval e.ise_caller l start n ==>
  !k fields. k < n /\
    inline_fetched_fields e.ise_caller l (start+k) fields ==>
    ?d. inline_cell_frame (KeepCell e)
          (inline_make_cell e.ise_caller l (start+k) fields) d /\
        d.ic_function = e.ise_final /\
        d.ic_block = FST (inline_keep_boundary e l start) /\
        d.ic_index = SND (inline_keep_boundary e l start) + k /\
        inline_cell_at d /\
        (is_param_opcode (FST d.ic_fields) \/ FST d.ic_fields = ASSIGN)
Proof
  strip_tac >>
  `l = e.ise_block ==> !i. i < n ==> start+i <> e.ise_index` by
    (gvs[inline_parameter_interval_def] >> rpt strip_tac >>
     first_x_assum (qspec_then `i` mp_tac) >>
     gvs[is_param_opcode_def]) >>
  rpt strip_tac >>
  `inline_cell_at (inline_make_cell e.ise_caller l (start+k) fields)` by
    gvs[inline_cell_at_def, inline_make_cell_def] >>
  `?d. inline_cell_frame (KeepCell e)
    (inline_make_cell e.ise_caller l (start+k) fields) d` by
    (irule inline_keep_cell_produce >>
     simp[inline_make_cell_def] >> gvs[]) >>
  qexists `d` >> simp[] >>
  `d.ic_block = FST (inline_keep_boundary e l start) /\
   d.ic_index = SND (inline_keep_boundary e l start) + k` by
    (irule inline_keep_parameter_interval_cell >>
     conj_tac >- (qexists `n` >> simp[]) >>
     qexists `inline_make_cell e.ise_caller l (start+k) fields` >>
     simp[inline_make_cell_def]) >>
  `d.ic_function = e.ise_final` by
    gvs[inline_cell_frame_def, inline_make_cell_def] >>
  simp[] >> conj_tac >- metis_tac[inline_cell_frame_sound] >>
  irule inline_parameter_frame_class >>
  qexistsl [`inline_make_cell e.ise_caller l (start+k) fields`, `KeepCell e`] >>
  simp[inline_make_cell_def] >>
  gvs[inline_parameter_interval_def, functionInlinerSiteLayoutTheory.inline_fetched_fields_def,
      get_instruction_def, functionInlinerSiteLayoutTheory.inline_inst_fields_def] >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[]
QED

Theorem inline_enter_interval_points:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  lookup_block l e.ise_callee.fn_blocks = SOME cb /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  ~MEM (STRCAT e.ise_prefix l) (fn_labels e.ise_caller) /\
  STRCAT e.ise_prefix l <> e.ise_return /\
  start+n <= LENGTH cb.bb_instructions /\
  (!k. k < n ==> is_param_opcode (EL (start+k) cb.bb_instructions).inst_opcode \/
                   (EL (start+k) cb.bb_instructions).inst_opcode = ASSIGN) ==>
  !k fields. k < n /\
    inline_fetched_fields e.ise_callee l (start+k) fields ==>
    ?d. inline_cell_frame (EnterCell e 0)
          (inline_make_cell e.ise_callee l (start+k) fields) d /\
        d.ic_function = e.ise_final /\
        d.ic_block = STRCAT e.ise_prefix l /\
        d.ic_index = LENGTH (FST (inline_cell_prefix e bb cb start)) + k /\
        inline_cell_at d /\
        (is_param_opcode (FST d.ic_fields) \/ FST d.ic_fields = ASSIGN)
Proof
  strip_tac >> rpt strip_tac >>
  `inline_cell_at (inline_make_cell e.ise_callee l (start+k) fields)` by
    gvs[inline_cell_at_def, inline_make_cell_def] >>
  `?d. inline_cell_frame (EnterCell e 0)
    (inline_make_cell e.ise_callee l (start+k) fields) d` by
    (irule inline_enter_cell_produce >>
     simp[inline_make_cell_def] >>
     `LENGTH (FST (inline_cell_focus e bb cb (start+k))) = 1` by
       (irule inline_parameter_focus_length >> simp[]) >>
     gvs[]) >>
  qexists `d` >> simp[] >>
  `d.ic_block = STRCAT e.ise_prefix l /\
   d.ic_index = LENGTH (FST (inline_cell_prefix e bb cb start)) + k` by
    (drule inline_enter_parameter_interval_cell >>
     simp[inline_make_cell_def] >> disch_then irule >> simp[] >>
     qexists `n` >> gvs[]) >>
  `d.ic_function = e.ise_final` by
    gvs[inline_cell_frame_def, inline_make_cell_def] >>
  simp[] >> conj_tac >- metis_tac[inline_cell_frame_sound] >>
  irule inline_parameter_frame_class >>
  qexistsl [`inline_make_cell e.ise_callee l (start+k) fields`, `EnterCell e 0`] >>
  simp[inline_make_cell_def] >>
  gvs[functionInlinerSiteLayoutTheory.inline_fetched_fields_def,
      get_instruction_def, functionInlinerSiteLayoutTheory.inline_inst_fields_def]
QED

Theorem inline_parameter_interval_from_fetched:
  lookup_block l fn.fn_blocks = SOME bb /\ start+n <= LENGTH bb.bb_instructions /\
  (!k. k<n ==> ?fields. inline_fetched_fields fn l (start+k) fields /\
    (is_param_opcode (FST fields) \/ FST fields = ASSIGN)) ==>
  inline_parameter_interval fn l start n
Proof
  strip_tac >> simp[inline_parameter_interval_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[] >>
  gvs[functionInlinerSiteLayoutTheory.inline_fetched_fields_def,
      get_instruction_def, functionInlinerSiteLayoutTheory.inline_inst_fields_def]
QED

Theorem inline_parameter_interval_fetched:
  inline_parameter_interval fn l start n /\ k < n ==>
  ?fields. inline_fetched_fields fn l (start+k) fields /\
    (is_param_opcode (FST fields) \/ FST fields = ASSIGN)
Proof
  gvs[inline_parameter_interval_def,
      functionInlinerSiteLayoutTheory.inline_fetched_fields_def,
      get_instruction_def, functionInlinerSiteLayoutTheory.inline_inst_fields_def] >>
  rpt strip_tac >> simp[]
QED

Theorem inline_keep_interval_transport:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  e.ise_index < LENGTH source_bb.bb_instructions /\
  (EL e.ise_index source_bb.bb_instructions).inst_opcode = INVOKE /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  inline_parameter_interval e.ise_caller l start n ==>
  let ml = FST (inline_keep_boundary e l start);
      mj = SND (inline_keep_boundary e l start) in
  inline_parameter_interval e.ise_final ml mj n /\
  inline_parameter_boundary (InlineKeep e) e.ise_caller l start e.ise_final ml mj /\
  inline_parameter_boundary (InlineKeep e) e.ise_caller l (start+n) e.ise_final ml (mj+n)
Proof
  simp[LET_THM] >> strip_tac >>
  `l = e.ise_block ==> !i. i < n ==> start+i <> e.ise_index` by
    (gvs[inline_parameter_interval_def] >> rpt strip_tac >>
     first_x_assum (qspec_then `i` mp_tac) >> gvs[is_param_opcode_def]) >>
  `inline_keep_boundary e l (start+n) =
    (FST (inline_keep_boundary e l start), SND (inline_keep_boundary e l start)+n)` by
    (Cases_on `l = e.ise_block` >-
       (irule inline_keep_boundary_interval >> qexists `n` >> simp[]) >>
     simp[inline_keep_boundary_def]) >>
  `inline_parameter_boundary (InlineKeep e) e.ise_caller l start e.ise_final
    (FST (inline_keep_boundary e l start)) (SND (inline_keep_boundary e l start))` by
    (irule inline_keep_boundary_produce >> gvs[inline_parameter_interval_def] >>
     decide_tac) >>
  `inline_parameter_boundary (InlineKeep e) e.ise_caller l (start+n) e.ise_final
    (FST (inline_keep_boundary e l start)) (SND (inline_keep_boundary e l start)+n)` by
    (`inline_parameter_boundary (InlineKeep e) e.ise_caller l (start+n) e.ise_final
       (FST (inline_keep_boundary e l (start+n))) (SND (inline_keep_boundary e l (start+n)))`
       suffices_by simp[] >>
     irule inline_keep_boundary_produce >> gvs[inline_parameter_interval_def]) >>
  simp[] >>
  qpat_x_assum `inline_parameter_boundary _ _ _ (start+n) _ _ _` mp_tac >>
  simp[inline_parameter_boundary_def] >> strip_tac >>
  reverse conj_tac >- gvs[] >>
  irule inline_parameter_interval_from_fetched >>
  reverse conj_tac >- (qexists `tb` >> simp[]) >>
  rpt strip_tac >>
  `?fields. inline_fetched_fields e.ise_caller l (start+k) fields /\
    (is_param_opcode (FST fields) \/ FST fields = ASSIGN)` by
    (irule inline_parameter_interval_fetched >> metis_tac[]) >>
  drule_all inline_keep_interval_points >>
  strip_tac >>
  qexists `d.ic_fields` >>
  gvs[inline_cell_at_def]
QED

Theorem inline_enter_interval_transport:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  lookup_block l e.ise_callee.fn_blocks = SOME cb /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  ~MEM (STRCAT e.ise_prefix l) (fn_labels e.ise_caller) /\
  STRCAT e.ise_prefix l <> e.ise_return /\
  start+n <= LENGTH cb.bb_instructions /\
  (!k. k<n ==> is_param_opcode (EL (start+k) cb.bb_instructions).inst_opcode \/
    (EL (start+k) cb.bb_instructions).inst_opcode = ASSIGN) ==>
  let mj = LENGTH (FST (inline_cell_prefix e bb cb start)) in
  inline_parameter_interval e.ise_final (STRCAT e.ise_prefix l) mj n /\
  inline_parameter_boundary (InlineEnter e) e.ise_callee l start e.ise_final
    (STRCAT e.ise_prefix l) mj /\
  inline_parameter_boundary (InlineEnter e) e.ise_callee l (start+n) e.ise_final
    (STRCAT e.ise_prefix l) (mj+n)
Proof
  simp[LET_THM] >> strip_tac >>
  `LENGTH (FST (inline_cell_prefix e bb cb (start+n))) =
    LENGTH (FST (inline_cell_prefix e bb cb start)) + n` by
    (irule inline_parameter_prefix_length_interval >> simp[]) >>
  `inline_parameter_boundary (InlineEnter e) e.ise_callee l start e.ise_final
    (STRCAT e.ise_prefix l) (LENGTH (FST (inline_cell_prefix e bb cb start)))` by
    (irule inline_enter_boundary_produce >> simp[]) >>
  `inline_parameter_boundary (InlineEnter e) e.ise_callee l (start+n) e.ise_final
    (STRCAT e.ise_prefix l) (LENGTH (FST (inline_cell_prefix e bb cb start))+n)` by
    (qpat_x_assum `LENGTH _ = _` (fn th => rewrite_tac[GSYM th]) >>
     irule inline_enter_boundary_produce >> simp[]) >>
  simp[] >>
  qpat_x_assum `inline_parameter_boundary _ _ _ (start+n) _ _ _` mp_tac >>
  simp[inline_parameter_boundary_def] >> strip_tac >>
  irule inline_parameter_interval_from_fetched >>
  reverse conj_tac >- (qexists `tb` >> simp[]) >>
  rpt strip_tac >>
  `?fields. inline_fetched_fields e.ise_callee l (start+k) fields /\
    (is_param_opcode (FST fields) \/ FST fields = ASSIGN)` by
    (irule inline_parameter_interval_fetched >> simp[] >>
     simp[inline_parameter_interval_def] >> qexists `n` >> simp[]) >>
  drule inline_enter_interval_points >>
  disch_then (qspecl_then [`start`, `n`, `l`, `cb`, `bb`, `k`, `fields`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists `d.ic_fields` >> gvs[inline_cell_at_def]
QED

Theorem inline_parameter_choice_interval:
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_caller a /\
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_callee b /\
  inline_site_edit_valid e /\
  ((choice = InlineKeep e /\ fn = e.ise_caller) \/
   (choice = InlineEnter e /\ fn = e.ise_callee)) /\
  inline_parameter_interval fn l start n ==>
  ?ml mj. inline_parameter_interval e.ise_final ml mj n /\
    inline_parameter_boundary choice fn l start e.ise_final ml mj /\
    inline_parameter_boundary choice fn l (start+n) e.ise_final ml (mj+n) /\
    (!k fields. k<n /\ inline_fetched_fields fn l (start+k) fields ==>
      ?tag d. inline_cell_choice tag = choice /\
        inline_cell_frame tag (inline_make_cell fn l (start+k) fields) d /\
        d.ic_function = e.ise_final /\ d.ic_block = ml /\ d.ic_index = mj+k /\
        inline_cell_at d)
Proof
  strip_tac >>
  drule_all functionInlinerOccurrencesTheory.inline_annotated_edit_fetch_facts >> strip_tac >>
  `(EL e.ise_index bb.bb_instructions).inst_opcode = INVOKE` by
    (`ALL_DISTINCT (fn_labels e.ise_caller)` by
       metis_tac[functionInlinerOccurrencesTheory.inline_annotated_origin_labels] >>
     gvs[functionInlinerActivationTheory.inline_site_edit_valid_def] >>
     drule_all functionInlinerWfTheory.find_invoke_site_lookup >> gvs[]) >>
  gvs[]
  >- (drule_all inline_keep_interval_transport >> simp[LET_THM] >> strip_tac >>
      qexistsl [`FST (inline_keep_boundary e l start)`, `SND (inline_keep_boundary e l start)`] >>
      simp[] >> rpt strip_tac >>
      drule_all (SRULE [arithmeticTheory.ADD_COMM] inline_keep_interval_points) >> strip_tac >>
      qexistsl [`KeepCell e`, `d`] >> simp[inline_cell_choice_def]) >>
  `?cb. lookup_block l e.ise_callee.fn_blocks = SOME cb /\
    start+n <= LENGTH cb.bb_instructions /\
    (!k. k<n ==> is_param_opcode (EL (start+k) cb.bb_instructions).inst_opcode \/
      (EL (start+k) cb.bb_instructions).inst_opcode = ASSIGN)` by
    gvs[inline_parameter_interval_def] >>
  `MEM l (fn_labels e.ise_callee)` by
    (simp[fn_labels_def, MEM_MAP] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM, venomExecPropsTheory.lookup_block_label]) >>
  first_x_assum (drule_then strip_assume_tac) >>
  drule_all (SRULE [] inline_enter_interval_transport) >> simp[LET_THM] >> strip_tac >>
  qexistsl [`STRCAT e.ise_prefix l`, `LENGTH (FST (inline_cell_prefix e bb cb start))`] >>
  simp[] >> rpt strip_tac >>
  gvs[arithmeticTheory.ADD_COMM] >>
  drule_all (SRULE [arithmeticTheory.ADD_COMM] inline_enter_interval_points) >> strip_tac >>
  qexistsl [`EnterCell e 0`, `d`] >> simp[inline_cell_choice_def]
QED


Theorem inline_parameter_path_cons_interval:
  inline_annotated_choice_path ctx (choice::rest) fn root ==>
  inline_parameter_interval fn l start n ==>
  ?mid ml mj.
    inline_annotated_choice_path ctx rest mid root /\
    inline_parameter_interval mid ml mj n /\
    inline_parameter_boundary choice fn l start mid ml mj /\
    inline_parameter_boundary choice fn l (start+n) mid ml (mj+n) /\
    (!k fields. k<n /\ inline_fetched_fields fn l (start+k) fields ==>
      ?tag d. inline_cell_choice tag = choice /\
        inline_cell_frame tag (inline_make_cell fn l (start+k) fields) d /\
        d.ic_function=mid /\ d.ic_block=ml /\ d.ic_index=mj+k /\ inline_cell_at d)
Proof
  rewrite_tac[inline_annotated_choice_path_def] >>
  disch_then (qx_choosel_then [`e`,`a`,`b`] strip_assume_tac) >>
  strip_tac >> qexists `e.ise_final` >> simp[] >>
  irule (SRULE [arithmeticTheory.ADD_COMM] inline_parameter_choice_interval) >> metis_tac[]
QED

Theorem inline_parameter_interval_transport:
  !path fn root l start n.
  inline_annotated_choice_path ctx path fn root /\
  inline_parameter_interval fn l start n ==>
  ?ml mj. inline_parameter_interval root ml mj n /\
    inline_parameter_boundary_path path fn l start root ml mj /\
    inline_parameter_boundary_path path fn l (start+n) root ml (mj+n) /\
    (!k fields. k<n /\ inline_fetched_fields fn l (start+k) fields ==>
      ?frames d. inline_cell_zipper (inline_make_cell fn l (start+k) fields) frames d /\
        MAP (\(tag,next). inline_cell_choice tag) frames=path /\
        d.ic_function=root /\ d.ic_block=ml /\ d.ic_index=mj+k /\ inline_cell_at d)
Proof
  Induct
  >- simp[inline_annotated_choice_path_def, inline_parameter_boundary_path_def,
          inline_cell_zipper_def, inline_make_cell_def, inline_cell_at_def] >>
  rpt gen_tac >> strip_tac >>
  drule inline_parameter_path_cons_interval >> disch_then drule >>
  disch_then (qx_choosel_then [`mid`,`il`,`ij`] strip_assume_tac) >>
  qpat_x_assum `!fn root l start n. _` drule >> disch_then drule >>
  disch_then (qx_choosel_then [`ml`,`mj`] strip_assume_tac) >>
  qexistsl [`ml`,`mj`] >>
  conj_tac >- simp[] >>
  conj_tac >- (simp[inline_parameter_boundary_path_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  conj_tac >- (simp[inline_parameter_boundary_path_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  rpt strip_tac >>
  qpat_x_assum `!k fields. _ ==> ?tag d. _` drule_all >>
  disch_then (qx_choosel_then [`tag`,`c`] strip_assume_tac) >>
  `inline_fetched_fields mid il (ij+k) c.ic_fields` by gvs[inline_cell_at_def] >>
  qpat_x_assum `!k fields. _ ==> ?frames d. _` drule_all >>
  disch_then (qx_choosel_then [`frames`,`d`] strip_assume_tac) >>
  `inline_make_cell mid il (ij+k) c.ic_fields = c` by
    (simp[inline_make_cell_def, functionInlinerReachableCutsTheory.inline_cell_component_equality]) >>
  qexistsl [`(tag,c)::frames`,`d`] >> simp[inline_cell_zipper_def] >> metis_tac[]
QED

Theorem inline_parameter_frame_boundary:
  inline_cell_frame tag c d /\
  (is_param_opcode (FST c.ic_fields) \/ FST c.ic_fields = ASSIGN) ==>
  inline_parameter_boundary (inline_cell_choice tag)
    c.ic_function c.ic_block c.ic_index d.ic_function d.ic_block d.ic_index
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  `inline_cell_at d` by metis_tac[inline_cell_frame_sound] >>
  Cases_on `tag` >>
  gvs[inline_cell_frame_def, inline_cell_choice_def, inline_parameter_boundary_def,
      inline_cell_at_def, functionInlinerSiteLayoutTheory.inline_fetched_fields_def, inline_make_cell_def,
      inline_keep_boundary_def, venomInstTheory.get_instruction_def,
      functionInlinerSiteLayoutTheory.inline_inst_fields_def]
  >- (IF_CASES_TAC >> gvs[] >> decide_tac)
  >- (IF_CASES_TAC >> gvs[] >> decide_tac) >>
  `LENGTH (FST (inline_cell_focus i bb cb c.ic_index)) = 1` by
    (irule inline_parameter_focus_length >> simp[]) >> decide_tac
QED

Theorem inline_parameter_zipper_boundary:
  !frames c d path root l start n k.
  inline_cell_zipper c frames d /\
  MAP (\(tag,next). inline_cell_choice tag) frames = path /\
  inline_annotated_choice_path ctx path c.ic_function root /\
  inline_parameter_interval c.ic_function l start n /\
  c.ic_block = l /\ c.ic_index = start+k /\ k<n ==>
  inline_parameter_boundary_path path c.ic_function l (start+k)
    d.ic_function d.ic_block d.ic_index
Proof
  Induct
  >- simp[inline_cell_zipper_def, inline_parameter_boundary_path_def] >>
  qx_gen_tac `h` >> PairCases_on `h` >> rpt gen_tac >>
  simp[inline_cell_zipper_def] >> strip_tac >> gvs[] >>
  drule inline_parameter_path_cons_interval >> disch_then drule >>
  disch_then (qx_choosel_then [`mid`,`il`,`ij`] strip_assume_tac) >>
  `is_param_opcode (FST c.ic_fields) \/ FST c.ic_fields = ASSIGN` by
    (drule inline_cell_frame_source >>
     simp[inline_cell_at_def] >> strip_tac >>
     qpat_x_assum `inline_parameter_interval c.ic_function c.ic_block start n` mp_tac >>
     simp[inline_parameter_interval_def,
          functionInlinerSiteLayoutTheory.inline_fetched_fields_def,
          venomInstTheory.get_instruction_def] >> strip_tac >>
     gvs[functionInlinerSiteLayoutTheory.inline_fetched_fields_def,
         venomInstTheory.get_instruction_def,
         functionInlinerSiteLayoutTheory.inline_inst_fields_def,
         arithmeticTheory.ADD_COMM] >>
     qpat_x_assum `!k. k < n ==> _` (qspec_then `k` mp_tac) >>
     qpat_x_assum `(_,_,_) = c.ic_fields` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  drule inline_parameter_frame_boundary >> simp[] >> strip_tac >>
  `inline_fetched_fields c.ic_function c.ic_block (start+k) c.ic_fields` by
    (drule inline_cell_frame_source >> gvs[inline_cell_at_def, arithmeticTheory.ADD_COMM]) >>
  qpat_x_assum `!k fields. _ ==> ?tag d. _` drule_all >>
  disch_then (qx_choosel_then [`tag`,`next`] strip_assume_tac) >>
  `inline_make_cell c.ic_function c.ic_block (start+k) c.ic_fields = c` by
    simp[inline_make_cell_def, inline_cell_component_equality, arithmeticTheory.ADD_COMM] >>
  `inline_parameter_boundary (inline_cell_choice h0) c.ic_function c.ic_block (k+start)
      mid il (ij+k)` by
    (drule_at Any inline_parameter_frame_boundary >> simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `h1.ic_function = mid /\ h1.ic_block = il /\ h1.ic_index = ij+k` by
    metis_tac[inline_parameter_boundary_functional] >>
  simp[inline_parameter_boundary_path_def] >>
  qexistsl [`mid`,`il`,`ij+k`] >> conj_tac >- simp[arithmeticTheory.ADD_COMM] >>
  gvs[arithmeticTheory.ADD_COMM] >>
  qpat_x_assum `!c d root start n k. _`
    (drule o REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  disch_then (qspecl_then [`root`,`ij`,`n`,`k`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem inline_parameter_zipper_coordinates:
  inline_cell_zipper c frames d /\
  MAP (\(tag,next). inline_cell_choice tag) frames = path /\
  inline_annotated_choice_path ctx path c.ic_function root /\
  inline_parameter_interval c.ic_function l start n /\
  c.ic_block = l /\ c.ic_index = start+k /\ k<n /\
  inline_parameter_boundary_path path c.ic_function l (start+k) root ml mj ==>
  d.ic_function = root /\ d.ic_block = ml /\ d.ic_index = mj
Proof
  strip_tac >>
  drule_all inline_parameter_zipper_boundary >> strip_tac >>
  metis_tac[inline_parameter_boundary_path_functional]
QED

Theorem inline_parameter_zipper_unique:
  inline_cell_zipper c frames d /\ inline_cell_zipper c frames' d' /\
  MAP (\(tag,next). inline_cell_choice tag) frames = path /\
  MAP (\(tag,next). inline_cell_choice tag) frames' = path /\
  inline_annotated_choice_path ctx path c.ic_function root /\
  inline_parameter_interval c.ic_function c.ic_block start n /\
  c.ic_index = start+k /\ k<n ==>
  d.ic_function = d'.ic_function /\ d.ic_block = d'.ic_block /\
  d.ic_index = d'.ic_index
Proof
  strip_tac >>
  `inline_parameter_boundary_path path c.ic_function c.ic_block (start+k)
     d.ic_function d.ic_block d.ic_index` by
    (irule inline_parameter_zipper_boundary >> metis_tac[]) >>
  `inline_parameter_boundary_path path c.ic_function c.ic_block (start+k)
     d'.ic_function d'.ic_block d'.ic_index` by
    (irule inline_parameter_zipper_boundary >> metis_tac[]) >>
  metis_tac[inline_parameter_boundary_path_functional]
QED

Theorem inline_selected_parameter_interval:
  inline_annotated_origin ctx n root cert /\
  inline_call_incidence cert root p fn l j orig (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q sigma child /\
  child.fn_blocks = entry::rest /\ entry.bb_instructions = params ++ tail /\
  param_insts_from 0 params ==>
  ?ml mj.
    inline_parameter_interval root ml mj (LENGTH params) /\
    inline_parameter_boundary_path (InlineEnter e::zipper)
      e.ise_callee entry.bb_label 0 root ml mj /\
    inline_parameter_boundary_path (InlineEnter e::zipper)
      e.ise_callee entry.bb_label (LENGTH params) root ml (mj+LENGTH params) /\
    (!k c mid frames d.
      inline_selected_parameter_descriptor ctx n cert root p fn l j orig
        u q e zipper child entry rest params tail k c mid frames d ==>
      d.ic_block = ml /\ d.ic_index = mj+k)
Proof
  strip_tac >>
  drule functionInlinerPairedSelectionTheory.inline_selected_paired_separation >> simp[] >> disch_then drule >>
  simp[] >> strip_tac >>
  `child = inline_entry_function b` by metis_tac[inline_selected_child_identity] >>
  `inline_parameter_interval e.ise_callee entry.bb_label 0 (LENGTH params)` by
    (drule functionInlinerEntryParametersTheory.inline_annotated_entry_parameter_prefix >>
     disch_then (qspecl_then [`entry`,`rest`,`params`,`tail`] mp_tac) >>
     gvs[] >> strip_tac >> simp[inline_parameter_interval_def] >>
     rpt strip_tac >> disj1_tac >>
     qspecl_then [`ps`,`0`,`k`] mp_tac callLayoutDefsTheory.param_insts_from_el >>
     simp[callLayoutDefsTheory.param_inst_at_def, EL_APPEND_EQN]) >>
  `inline_annotated_choice_path ctx (InlineEnter e::zipper) e.ise_callee root` by
    (simp[inline_annotated_choice_path_def] >>
     qexistsl [`a`,`b`] >> simp[] >>
     metis_tac[inline_selected_annotated_choice_path]) >>
  drule_all inline_parameter_interval_transport >> simp[] >>
  disch_then (qx_choosel_then [`ml`,`mj`] strip_assume_tac) >>
  qexistsl [`ml`,`mj`] >> simp[] >> rpt gen_tac >> strip_tac >>
  `c = inline_make_cell e.ise_callee entry.bb_label k
       (inline_inst_fields (EL k params)) /\ k < LENGTH params` by
    gvs[inline_selected_parameter_descriptor_def] >>
  drule inline_selected_parameter_descriptor_projection >> strip_tac >>
  `inline_cell_zipper c ((EnterCell e 0,mid)::frames) d /\
   MAP (\(tag,next). inline_cell_choice tag) ((EnterCell e 0,mid)::frames) =
     InlineEnter e::zipper` by
    simp[inline_cell_zipper_def, inline_cell_choice_def] >>
  `inline_fetched_fields e.ise_callee entry.bb_label k c.ic_fields` by
    (drule inline_cell_frame_source >> gvs[inline_cell_at_def, inline_make_cell_def]) >>
  qpat_x_assum `!k fields. _ ==> ?frames d. _` drule_all >>
  disch_then (qx_choosel_then [`other`,`out`] strip_assume_tac) >>
  `inline_make_cell e.ise_callee entry.bb_label k c.ic_fields = c` by
    simp[inline_make_cell_def] >>
  `d.ic_function = out.ic_function /\ d.ic_block = out.ic_block /\
   d.ic_index = out.ic_index` by
    (irule inline_parameter_zipper_unique >>
     qexists `c` >> simp[inline_make_cell_def] >>
     metis_tac[inline_make_cell_def, arithmeticTheory.ADD_CLAUSES]) >> simp[]
QED
