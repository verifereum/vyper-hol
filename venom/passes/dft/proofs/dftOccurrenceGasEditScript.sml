Theory dftOccurrenceGasEdit
Ancestors
  dftOccurrenceSquare dftOccurrenceReplay dftOccurrenceMachine dftOpenMachine
  venomExecSemantics venomInst venomState list arithmetic dftOpenErase

Definition dft_gas_edit_block_def:
  dft_gas_edit_block bb0 pre x y post bb =
    if bb = bb0 then bb with bb_instructions := pre ++ [y;x] ++ post else bb
End

Definition dft_gas_edit_fn_def:
  dft_gas_edit_fn bb0 pre x y post fn =
    fn with fn_blocks := MAP (dft_gas_edit_block bb0 pre x y post) fn.fn_blocks
End

Definition dft_gas_edit_ctx_def:
  dft_gas_edit_ctx bb0 pre x y post C =
    C with ctx_functions := MAP (dft_gas_edit_fn bb0 pre x y post) C.ctx_functions
End

Theorem dft_gas_edit_label[simp]:
  (dft_gas_edit_block bb0 pre x y post bb).bb_label = bb.bb_label
Proof
  simp[dft_gas_edit_block_def] >> IF_CASES_TAC >> simp[]
QED

Theorem dft_gas_edit_name[simp]:
  (dft_gas_edit_fn bb0 pre x y post fn).fn_name = fn.fn_name
Proof
  simp[dft_gas_edit_fn_def]
QED

Theorem dft_gas_edit_lookup_function:
  lookup_function nm (dft_gas_edit_ctx bb0 pre x y post C).ctx_functions =
  OPTION_MAP (dft_gas_edit_fn bb0 pre x y post)
    (lookup_function nm C.ctx_functions)
Proof
  simp[dft_gas_edit_ctx_def, lookup_function_map]
QED

Theorem dft_gas_edit_lookup_blocks:
  !bbs. lookup_block lbl (MAP (dft_gas_edit_block bb0 pre x y post) bbs) =
    OPTION_MAP (dft_gas_edit_block bb0 pre x y post) (lookup_block lbl bbs)
Proof
  Induct >> simp[lookup_block_def, FIND_thm] >> gen_tac >>
  IF_CASES_TAC >> gvs[lookup_block_def]
QED

Theorem dft_gas_edit_lookup_block:
  lookup_block lbl (dft_gas_edit_fn bb0 pre x y post fn).fn_blocks =
  OPTION_MAP (dft_gas_edit_block bb0 pre x y post) (lookup_block lbl fn.fn_blocks)
Proof
  simp[dft_gas_edit_fn_def, dft_gas_edit_lookup_blocks]
QED

Theorem dft_gas_edit_setup_callee:
  setup_callee (dft_gas_edit_fn bb0 pre x y post fn) args s = setup_callee fn args s
Proof
  Cases_on `fn.fn_blocks` >> simp[setup_callee_def, dft_gas_edit_fn_def]
QED

Theorem dft_gas_edit_phis_list:
  !pre. x.inst_opcode = GAS /\ y.inst_opcode = GAS ==>
  eval_phis s (pre ++ [y;x] ++ post) = eval_phis s (pre ++ [x;y] ++ post)
Proof
  Induct >> simp[eval_phis_def] >> rpt strip_tac >> simp[]
QED

Theorem dft_gas_edit_phi_length_list:
  !pre. x.inst_opcode = GAS /\ y.inst_opcode = GAS ==>
  phi_prefix_length (pre ++ [y;x] ++ post) =
  phi_prefix_length (pre ++ [x;y] ++ post)
Proof
  Induct >> simp[phi_prefix_length_def]
QED

Theorem dft_gas_edit_phi_bound:
  !pre. x.inst_opcode = GAS ==>
    phi_prefix_length (pre ++ [x;y] ++ post) <= LENGTH pre
Proof
  Induct >> simp[phi_prefix_length_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[]
QED

Theorem dft_gas_edit_phis:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS ==>
  eval_phis s (dft_gas_edit_block bb0 pre x y post bb).bb_instructions =
  eval_phis s bb.bb_instructions
Proof
  strip_tac >> simp[dft_gas_edit_block_def] >> IF_CASES_TAC >>
  gvs[dft_gas_edit_phis_list]
QED

Theorem dft_gas_edit_phi_length:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS ==>
  phi_prefix_length (dft_gas_edit_block bb0 pre x y post bb).bb_instructions =
  phi_prefix_length bb.bb_instructions
Proof
  strip_tac >> simp[dft_gas_edit_block_def] >> IF_CASES_TAC >>
  gvs[dft_gas_edit_phi_length_list]
QED

Theorem dft_gas_edit_instruction_pair:
  bb0.bb_instructions = pre ++ [x;y] ++ post ==>
  get_instruction bb0 (LENGTH pre) = SOME x /\
  get_instruction bb0 (SUC (LENGTH pre)) = SOME y /\
  get_instruction (dft_gas_edit_block bb0 pre x y post bb0) (LENGTH pre) = SOME y /\
  get_instruction (dft_gas_edit_block bb0 pre x y post bb0) (SUC (LENGTH pre)) = SOME x
Proof
  simp[get_instruction_def, dft_gas_edit_block_def, EL_APPEND_EQN,
       ADD1]
QED

Theorem dft_gas_edit_instruction_outside:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  (bb <> bb0 \/ (i <> LENGTH pre /\ i <> SUC (LENGTH pre))) ==>
  get_instruction (dft_gas_edit_block bb0 pre x y post bb) i = get_instruction bb i
Proof
  strip_tac >> Cases_on `bb = bb0` >> gvs[dft_gas_edit_block_def] >>
  simp[get_instruction_def, EL_APPEND_EQN] >>
  Cases_on `i < LENGTH pre` >> simp[] >>
  Cases_on `i - LENGTH pre` >> gvs[] >>
  Cases_on `n` >> gvs[]
QED

Theorem dft_gas_edit_entry_label:
  fn_entry_label (dft_gas_edit_fn bb0 pre x y post fn) = fn_entry_label fn
Proof
  Cases_on `fn.fn_blocks` >> simp[fn_entry_label_def, entry_block_def, dft_gas_edit_fn_def]
QED

Theorem dft_gas_edit_invoke_slot:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  get_instruction bb i = SOME inst /\ inst.inst_opcode = INVOKE ==>
  get_instruction (dft_gas_edit_block bb0 pre x y post bb) i = SOME inst
Proof
  strip_tac >> Cases_on `bb = bb0` >-
    (gvs[] >> drule dft_gas_edit_instruction_pair >> strip_tac >>
     `i <> LENGTH pre /\ i <> SUC (LENGTH pre)` by
       (rpt strip_tac >> gvs[]) >>
     simp[dft_gas_edit_instruction_outside]) >>
  gvs[dft_gas_edit_block_def]
QED

Definition dft_edit_control_def:
  (dft_edit_control fm bm (DftEnter fn b s) = DftEnter (fm fn) b s) /\
  (dft_edit_control fm bm (DftAt fn b bb s) = DftAt (fm fn) b (bm bb) s) /\
  (dft_edit_control fm bm (DftDone r) = DftDone r)
End

Definition dft_edit_frame_def:
  dft_edit_frame fm bm (DftCaller fn b bb inst s) = DftCaller (fm fn) b (bm bb) inst s
End

Definition dft_edit_core_def:
  dft_edit_core fm bm (DftOpen ctl stack n) =
    DftOpen (dft_edit_control fm bm ctl) (MAP (dft_edit_frame fm bm) stack) n
End

Definition dft_edit_occ_def:
  dft_edit_occ fm bm c = c with dft_occ_core := dft_edit_core fm bm c.dft_occ_core
End

Definition dft_edit_frame_safe_def:
  dft_edit_frame_safe (DftCaller fn b bb inst s) <=>
    b = 0 /\ inst.inst_opcode = INVOKE /\
    get_instruction bb s.vs_inst_idx = SOME inst
End

Definition dft_edit_control_safe_def:
  (dft_edit_control_safe (DftEnter fn b s) <=> b = 0) /\
  (dft_edit_control_safe (DftAt fn b bb s) <=> b = 0) /\
  (dft_edit_control_safe (DftDone r) <=> T)
End

Definition dft_edit_safe_core_def:
  dft_edit_safe_core (DftOpen ctl stack n) <=>
    dft_edit_control_safe ctl /\ EVERY dft_edit_frame_safe stack
End

Definition dft_edit_safe_def:
  dft_edit_safe c <=> dft_edit_safe_core c.dft_occ_core
End

Definition dft_edit_cut_def:
  dft_edit_cut bb0 k c <=>
    ~(?fn b s stack n. c.dft_occ_core = DftOpen (DftAt fn b bb0 s) stack n /\
                        s.vs_inst_idx = SUC k)
End

Definition dft_edit_before_def:
  dft_edit_before bb0 k c <=>
    ?fn s stack n. c.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n /\
                  s.vs_inst_idx = k
End

Definition dft_gas_edit_rel_def:
  dft_gas_edit_rel bb0 pre x y post w C l r <=>
    let fm = dft_gas_edit_fn bb0 pre x y post;
        bm = dft_gas_edit_block bb0 pre x y post;
        C' = dft_gas_edit_ctx bb0 pre x y post C in
    (dft_edit_safe l /\ dft_edit_cut bb0 (LENGTH pre) l /\ r = dft_edit_occ fm bm l) \/
    (?c. dft_edit_safe c /\ dft_edit_before bb0 (LENGTH pre) c /\
         l = dft_occ_oracle_next w C c /\
         r = dft_occ_oracle_next w C' (dft_edit_occ fm bm c))
End

Theorem dft_gas_edit_safe_frame:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\ dft_edit_frame_safe fr ==>
  dft_edit_frame_safe (dft_edit_frame (dft_gas_edit_fn bb0 pre x y post)
    (dft_gas_edit_block bb0 pre x y post) fr)
Proof
  Cases_on `fr` >> simp[dft_edit_frame_safe_def, dft_edit_frame_def] >>
  rpt strip_tac >> simp[] >> irule dft_gas_edit_invoke_slot >> simp[]
QED

Theorem dft_gas_edit_safe_stack:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\ EVERY dft_edit_frame_safe stack ==>
  EVERY dft_edit_frame_safe
    (MAP (dft_edit_frame (dft_gas_edit_fn bb0 pre x y post)
      (dft_gas_edit_block bb0 pre x y post)) stack)
Proof
  simp[EVERY_MAP, EVERY_MEM] >> metis_tac[dft_gas_edit_safe_frame]
QED

Theorem dft_edit_map_push:
  dft_edit_core fm bm (DftOpen ctl (DftCaller fn b bb inst s :: stack) n) =
  DftOpen (dft_edit_control fm bm ctl)
    (DftCaller (fm fn) b (bm bb) inst s :: MAP (dft_edit_frame fm bm) stack) n
Proof
  simp[dft_edit_core_def, dft_edit_frame_def]
QED

Theorem dft_gas_edit_init:
  dft_gas_edit_rel bb0 pre x y post w C
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter (dft_gas_edit_fn bb0 pre x y post fn) 0 s) [] n))
Proof
  simp[dft_gas_edit_rel_def, dft_edit_safe_def, dft_edit_safe_core_def,
       dft_edit_control_safe_def, dft_edit_cut_def, dft_edit_occ_def,
       dft_edit_core_def, dft_edit_control_def, dft_occ_init_def]
QED

Theorem dft_gas_edit_entry_cut:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\ x.inst_opcode = GAS ==>
  dft_edit_cut bb0 (LENGTH pre)
    (c with dft_occ_core := DftOpen (DftAt fn 0 bb0
       (s with vs_inst_idx := phi_prefix_length bb0.bb_instructions)) stack n)
Proof
  strip_tac >>
  `phi_prefix_length (pre ++ [x;y] ++ post) <= LENGTH pre` by
    simp[dft_gas_edit_phi_bound] >>
  simp[dft_edit_cut_def] >> decide_tac
QED

Theorem dft_gas_edit_middle_instance:
  let c = dft_occ_init (DftOpen (DftAt fn 0 bb0
             (s with vs_inst_idx := LENGTH pre)) [] n) in
  dft_gas_edit_rel bb0 pre x y post w C
    (dft_occ_oracle_next w C c)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)
      (dft_edit_occ (dft_gas_edit_fn bb0 pre x y post)
        (dft_gas_edit_block bb0 pre x y post) c))
Proof
  simp[dft_gas_edit_rel_def] >> disj2_tac >>
  qexists_tac `dft_occ_init (DftOpen (DftAt fn 0 bb0
    (s with vs_inst_idx := LENGTH pre)) [] n)` >>
  simp[dft_edit_safe_def, dft_edit_safe_core_def, dft_edit_control_safe_def,
       dft_edit_before_def, dft_occ_init_def]
QED

Theorem dft_edit_safe_pop:
  dft_edit_safe_core (DftOpen ctl (fr::stack) n) ==>
  EVERY dft_edit_frame_safe stack /\ dft_edit_frame_safe fr
Proof
  simp[dft_edit_safe_core_def]
QED

Theorem dft_gas_edit_saved_resume_cut:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  dft_edit_frame_safe (DftCaller fn b bb inst s) ==>
  dft_edit_cut bb0 (LENGTH pre)
    (c with dft_occ_core := DftOpen (DftAt fn b bb
      (after with vs_inst_idx := SUC s.vs_inst_idx)) stack n)
Proof
  simp[dft_edit_frame_safe_def, dft_edit_cut_def] >> rpt strip_tac >>
  gvs[] >> drule dft_gas_edit_instruction_pair >> simp[] >> rpt strip_tac >> gvs[]
QED

Theorem dft_gas_edit_middle_intro:
  dft_edit_safe c /\ dft_edit_before bb0 (LENGTH pre) c ==>
  dft_gas_edit_rel bb0 pre x y post w C
    (dft_occ_oracle_next w C c)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)
      (dft_edit_occ (dft_gas_edit_fn bb0 pre x y post)
        (dft_gas_edit_block bb0 pre x y post) c))
Proof
  strip_tac >> simp[dft_gas_edit_rel_def] >> disj2_tac >>
  qexists_tac `c` >> simp[]
QED

Theorem dft_gas_edit_reachable_middle:
  bb0.bb_instructions = [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  x.inst_operands = [] /\ y.inst_operands = [] ==>
  let fn0 = fn with fn_blocks := [bb0];
      s0 = s with vs_current_bb := bb0.bb_label;
      c0 = dft_occ_init (DftOpen (DftEnter fn0 0 s0) [] n);
      c1 = dft_occ_oracle_next w C c0 in
  dft_edit_before bb0 0 c1 /\
  dft_gas_edit_rel bb0 [] x y post w C
    (dft_occ_oracle_next w C c1)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 [] x y post C)
      (dft_edit_occ (dft_gas_edit_fn bb0 [] x y post)
        (dft_gas_edit_block bb0 [] x y post) c1))
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >>
  conj_tac >-
    simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
         dft_fill_def, dft_fill_control_def, dft_erase_def, dft_open_next_def,
         lookup_block_def, FIND_thm, eval_phis_def, phi_prefix_length_def,
         dft_occ_update_def, dft_occ_init_def, dft_edit_before_def] >>
  irule dft_gas_edit_middle_intro >>
  simp[dft_edit_safe_def, dft_edit_safe_core_def, dft_edit_control_safe_def,
       dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_erase_def, dft_open_next_def,
       lookup_block_def, FIND_thm, eval_phis_def, phi_prefix_length_def,
       dft_occ_update_def, dft_occ_init_def, dft_edit_before_def]
QED
