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
