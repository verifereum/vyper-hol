Theory dftOccurrenceGasEdit
Ancestors
  dftOccurrenceSquare dftOccurrenceReplay dftOccurrenceMachine dftOpenMachine
  venomExecSemantics venomInst venomState list arithmetic dftOpenErase dftOpenFuel finite_map

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

Theorem dft_nonphi_edit_phis_list:
  !pre. x.inst_opcode <> PHI /\ y.inst_opcode <> PHI ==>
  eval_phis s (pre ++ [y;x] ++ post) = eval_phis s (pre ++ [x;y] ++ post)
Proof
  Induct >> simp[eval_phis_def] >> rpt strip_tac >> simp[]
QED

Theorem dft_nonphi_edit_phi_length_list:
  !pre. x.inst_opcode <> PHI /\ y.inst_opcode <> PHI ==>
  phi_prefix_length (pre ++ [y;x] ++ post) =
  phi_prefix_length (pre ++ [x;y] ++ post)
Proof
  Induct >> simp[phi_prefix_length_def]
QED

Theorem dft_nonphi_edit_phis:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode <> PHI /\ y.inst_opcode <> PHI ==>
  eval_phis s (dft_gas_edit_block bb0 pre x y post bb).bb_instructions =
  eval_phis s bb.bb_instructions
Proof
  strip_tac >> simp[dft_gas_edit_block_def] >> IF_CASES_TAC >>
  gvs[dft_nonphi_edit_phis_list]
QED

Theorem dft_nonphi_edit_phi_length:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode <> PHI /\ y.inst_opcode <> PHI ==>
  phi_prefix_length (dft_gas_edit_block bb0 pre x y post bb).bb_instructions =
  phi_prefix_length bb.bb_instructions
Proof
  strip_tac >> simp[dft_gas_edit_block_def] >> IF_CASES_TAC >>
  gvs[dft_nonphi_edit_phi_length_list]
QED

Theorem dft_gas_edit_phis_list:
  !pre. x.inst_opcode = GAS /\ y.inst_opcode = GAS ==>
  eval_phis s (pre ++ [y;x] ++ post) = eval_phis s (pre ++ [x;y] ++ post)
Proof
  rpt strip_tac >> irule dft_nonphi_edit_phis_list >> simp[]
QED

Theorem dft_gas_edit_phi_length_list:
  !pre. x.inst_opcode = GAS /\ y.inst_opcode = GAS ==>
  phi_prefix_length (pre ++ [y;x] ++ post) =
  phi_prefix_length (pre ++ [x;y] ++ post)
Proof
  rpt strip_tac >> irule dft_nonphi_edit_phi_length_list >> simp[]
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

Theorem dft_edit_safe_frame_erase[local]:
  dft_edit_frame_safe fr ==> dft_fill_frame 0 fr = fr
Proof
  Cases_on `fr` >> simp[dft_edit_frame_safe_def, dft_fill_frame_def]
QED

Theorem dft_edit_safe_stack_erase[local]:
  EVERY dft_edit_frame_safe stack ==> MAP (dft_fill_frame 0) stack = stack
Proof
  Induct_on `stack` >> simp[] >> metis_tac[dft_edit_safe_frame_erase]
QED

Theorem dft_edit_fill_frame_twice[local,simp]:
  dft_fill_frame k (dft_fill_frame j fr) = dft_fill_frame k fr
Proof
  Cases_on `fr` >> simp[dft_fill_frame_def]
QED

Theorem dft_edit_fill_stack_twice[local,simp]:
  MAP (dft_fill_frame k) (MAP (dft_fill_frame j) stack) =
  MAP (dft_fill_frame k) stack
Proof
  Induct_on `stack` >> simp[]
QED

Theorem dft_edit_fill_frame_commute[local,simp]:
  dft_fill_frame k (dft_edit_frame fm bm fr) =
  dft_edit_frame fm bm (dft_fill_frame k fr)
Proof
  Cases_on `fr` >> simp[dft_fill_frame_def, dft_edit_frame_def]
QED

Theorem dft_edit_fill_stack_commute[local,simp]:
  MAP (dft_fill_frame k) (MAP (dft_edit_frame fm bm) stack) =
  MAP (dft_edit_frame fm bm) (MAP (dft_fill_frame k) stack)
Proof
  Induct_on `stack` >> simp[]
QED

Theorem dft_gas_edit_middle_join:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  x.inst_operands = [] /\ y.inst_operands = [] /\ u <> v /\
  dft_edit_before bb0 (LENGTH pre) c ==>
  dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)
      (dft_edit_occ (dft_gas_edit_fn bb0 pre x y post)
        (dft_gas_edit_block bb0 pre x y post) c)) =
  dft_edit_occ (dft_gas_edit_fn bb0 pre x y post)
    (dft_gas_edit_block bb0 pre x y post)
    (dft_occ_oracle_next w C (dft_occ_oracle_next w C c))
Proof
  simp[dft_edit_before_def] >> rpt strip_tac >>
  Cases_on `c` >> gvs[] >> Cases_on `stack` >>
  simp[dft_edit_occ_def, dft_edit_core_def, dft_edit_control_def,
       dft_occ_oracle_next_def, dft_occ_next_def, dft_occ_address_def,
       dft_next_inf_def, dft_fill_def, dft_fill_control_def, dft_erase_def,
       dft_open_next_def, dft_open_deliver_def, dft_open_continue_def,
       get_instruction_def, dft_gas_edit_block_def, EL_APPEND_EQN,
       is_terminator_def, dft_occ_update_def, update_var_def,
       FUPDATE_COMMUTES, ADD1]
QED

Theorem dft_gas_edit_middle_safe_cut:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  x.inst_operands = [] /\ y.inst_operands = [] /\
  dft_edit_safe c /\ dft_edit_before bb0 (LENGTH pre) c ==>
  dft_edit_safe (dft_occ_oracle_next w C (dft_occ_oracle_next w C c)) /\
  dft_edit_cut bb0 (LENGTH pre)
    (dft_occ_oracle_next w C (dft_occ_oracle_next w C c))
Proof
  simp[dft_edit_before_def] >> rpt strip_tac >>
  Cases_on `c` >> gvs[dft_edit_safe_def, dft_edit_safe_core_def,
                        dft_edit_control_safe_def] >>
  drule dft_edit_safe_stack_erase >> strip_tac >> Cases_on `stack` >> gvs[] >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_occ_address_def,
       dft_next_inf_def, dft_fill_def, dft_fill_control_def, dft_erase_def,
       dft_open_next_def, dft_open_deliver_def, dft_open_continue_def,
       get_instruction_def, EL_APPEND_EQN, is_terminator_def,
       dft_occ_update_def, update_var_def, ADD1,
       dft_edit_safe_def, dft_edit_safe_core_def, dft_edit_control_safe_def,
       dft_edit_cut_def]
QED

Theorem dft_edit_continue:
  dft_edit_control fm bm (dft_open_continue fn b bb inst before after) =
  dft_open_continue (fm fn) b (bm bb) inst before after
Proof
  simp[dft_open_continue_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> Cases_on `after.vs_halted` >>
  simp[dft_edit_control_def]
QED

Theorem dft_edit_deliver:
  dft_edit_core fm bm (dft_open_deliver fn b bb inst before stack n r) =
  dft_open_deliver (fm fn) b (bm bb) inst before
    (MAP (dft_edit_frame fm bm) stack) n r
Proof
  Cases_on `r` >> simp[dft_open_deliver_def, dft_edit_core_def,
                       dft_edit_control_def, dft_edit_continue]
QED

Theorem dft_edit_return:
  dft_edit_core fm bm (dft_open_return r stack n) =
  dft_open_return r (MAP (dft_edit_frame fm bm) stack) n
Proof
  Cases_on `r` >> Cases_on `stack` >>
  simp[dft_open_return_def, dft_edit_core_def, dft_edit_control_def] >>
  Cases_on `h` >> simp[dft_open_return_def, dft_edit_frame_def] >>
  rename1 `bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs))` >>
  Cases_on `bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs))` >>
  simp[dft_edit_core_def, dft_edit_control_def, dft_edit_deliver]
QED

Theorem dft_edit_fill:
  dft_edit_core fm bm (dft_fill k core) = dft_fill k (dft_edit_core fm bm core)
Proof
  Cases_on `core` >> simp[dft_edit_core_def, dft_fill_def] >>
  Cases_on `d` >> simp[dft_edit_control_def, dft_fill_control_def]
QED

Theorem dft_gas_edit_invoke:
  dft_edit_core (dft_gas_edit_fn bb0 pre x y post)
    (dft_gas_edit_block bb0 pre x y post)
    (dft_open_invoke C fn b bb inst s stack n) =
  dft_open_invoke (dft_gas_edit_ctx bb0 pre x y post C)
    (dft_gas_edit_fn bb0 pre x y post fn) b
    (dft_gas_edit_block bb0 pre x y post bb) inst s
    (MAP (dft_edit_frame (dft_gas_edit_fn bb0 pre x y post)
      (dft_gas_edit_block bb0 pre x y post)) stack) n
Proof
  simp[dft_open_invoke_def, dft_gas_edit_lookup_function] >>
  Cases_on `decode_invoke inst` >> simp[dft_edit_core_def, dft_edit_control_def] >>
  PairCases_on `x'` >> simp[] >>
  Cases_on `lookup_function x'0 C.ctx_functions` >>
  simp[dft_edit_core_def, dft_edit_control_def] >>
  Cases_on `eval_operands x'1 s` >> simp[dft_edit_core_def, dft_edit_control_def] >>
  simp[dft_gas_edit_setup_callee] >>
  rename1 `setup_callee callee args s` >> Cases_on `setup_callee callee args s` >>
  simp[dft_edit_core_def, dft_edit_control_def, dft_edit_frame_def]
QED

Theorem dft_nonphi_edit_open_entry:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode <> PHI /\ y.inst_opcode <> PHI ==>
  dft_edit_core (dft_gas_edit_fn bb0 pre x y post)
    (dft_gas_edit_block bb0 pre x y post)
    (dft_open_next a C (DftOpen (DftEnter fn fuel s) stack n)) =
  dft_open_next a (dft_gas_edit_ctx bb0 pre x y post C)
    (dft_edit_core (dft_gas_edit_fn bb0 pre x y post)
      (dft_gas_edit_block bb0 pre x y post) (DftOpen (DftEnter fn fuel s) stack n))
Proof
  strip_tac >> Cases_on `fuel` >>
  simp[dft_open_next_def, dft_edit_core_def, dft_edit_control_def,
       dft_gas_edit_lookup_block] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[dft_edit_core_def, dft_edit_control_def] >>
  simp[dft_nonphi_edit_phis, dft_nonphi_edit_phi_length] >>
  rename1 `eval_phis s blk.bb_instructions` >>
  Cases_on `eval_phis s blk.bb_instructions` >>
  simp[dft_edit_core_def, dft_edit_control_def]
QED

Theorem dft_gas_edit_open_entry:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS ==>
  dft_edit_core (dft_gas_edit_fn bb0 pre x y post)
    (dft_gas_edit_block bb0 pre x y post)
    (dft_open_next a C (DftOpen (DftEnter fn fuel s) stack n)) =
  dft_open_next a (dft_gas_edit_ctx bb0 pre x y post C)
    (dft_edit_core (dft_gas_edit_fn bb0 pre x y post)
      (dft_gas_edit_block bb0 pre x y post) (DftOpen (DftEnter fn fuel s) stack n))
Proof
  strip_tac >> irule dft_nonphi_edit_open_entry >> simp[]
QED

Theorem dft_gas_edit_open_at:
  get_instruction (dft_gas_edit_block bb0 pre x y post bb) s.vs_inst_idx =
    get_instruction bb s.vs_inst_idx ==>
  dft_edit_core (dft_gas_edit_fn bb0 pre x y post)
    (dft_gas_edit_block bb0 pre x y post)
    (dft_open_next a C (DftOpen (DftAt fn b bb s) stack n)) =
  dft_open_next a (dft_gas_edit_ctx bb0 pre x y post C)
    (dft_edit_core (dft_gas_edit_fn bb0 pre x y post)
      (dft_gas_edit_block bb0 pre x y post) (DftOpen (DftAt fn b bb s) stack n))
Proof
  strip_tac >> simp[dft_edit_core_def, dft_edit_control_def, dft_open_next_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >>
  simp[dft_edit_core_def, dft_edit_control_def] >>
  rename1 `inst.inst_opcode` >>
  Cases_on `inst.inst_opcode = INVOKE` >> simp[dft_gas_edit_invoke] >>
  Cases_on `inst.inst_opcode = GAS` >> simp[dft_edit_deliver] >>
  Cases_on `inst.inst_outputs` >> simp[dft_edit_core_def, dft_edit_control_def] >>
  Cases_on `t` >> simp[dft_edit_core_def, dft_edit_control_def, dft_edit_deliver]
QED

Theorem dft_edit_occ_update:
  c.dft_occ_core = DftOpen ctl stack n /\
  (!fn b bb s. ctl = DftAt fn b bb s ==>
    get_instruction (bm bb) s.vs_inst_idx = get_instruction bb s.vs_inst_idx) ==>
  dft_occ_update (dft_edit_occ fm bm c)
    (dft_edit_core fm bm (DftOpen nextctl nextstack nextn)) =
  dft_edit_occ fm bm (dft_occ_update c (DftOpen nextctl nextstack nextn))
Proof
  strip_tac >> Cases_on `nextstack` >> Cases_on `c.dft_occ_saved` >>
  Cases_on `ctl` >> Cases_on `nextctl` >>
  gvs[dft_occ_update_def, dft_edit_occ_def, dft_edit_core_def,
      dft_edit_control_def] >>
  rpt CASE_TAC >> gvs[dft_edit_core_def, dft_edit_control_def]
QED

Theorem dft_nonphi_edit_open_next:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode <> PHI /\ y.inst_opcode <> PHI /\
  (!fn b bb s stack n. core = DftOpen (DftAt fn b bb s) stack n ==>
    get_instruction (dft_gas_edit_block bb0 pre x y post bb) s.vs_inst_idx =
      get_instruction bb s.vs_inst_idx) ==>
  dft_edit_core (dft_gas_edit_fn bb0 pre x y post)
    (dft_gas_edit_block bb0 pre x y post) (dft_open_next a C core) =
  dft_open_next a (dft_gas_edit_ctx bb0 pre x y post C)
    (dft_edit_core (dft_gas_edit_fn bb0 pre x y post)
      (dft_gas_edit_block bb0 pre x y post) core)
Proof
  Cases_on `core` >> rename1 `DftOpen ctl stack n` >> Cases_on `ctl` >>
  simp[] >> rpt strip_tac
  >- simp[dft_nonphi_edit_open_entry]
  >- simp[dft_gas_edit_open_at]
  >> simp[dft_open_next_def, dft_edit_core_def, dft_edit_control_def, dft_edit_return]
QED

Theorem dft_nonphi_edit_next_inf:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode <> PHI /\ y.inst_opcode <> PHI /\
  (!fn b bb s stack n. core = DftOpen (DftAt fn b bb s) stack n ==>
    get_instruction (dft_gas_edit_block bb0 pre x y post bb) s.vs_inst_idx =
      get_instruction bb s.vs_inst_idx) ==>
  dft_edit_core (dft_gas_edit_fn bb0 pre x y post)
    (dft_gas_edit_block bb0 pre x y post) (dft_next_inf a C core) =
  dft_next_inf a (dft_gas_edit_ctx bb0 pre x y post C)
    (dft_edit_core (dft_gas_edit_fn bb0 pre x y post)
      (dft_gas_edit_block bb0 pre x y post) core)
Proof
  strip_tac >>
  `!fn b bb s stack n. dft_fill 1 core = DftOpen (DftAt fn b bb s) stack n ==>
    get_instruction (dft_gas_edit_block bb0 pre x y post bb) s.vs_inst_idx =
      get_instruction bb s.vs_inst_idx` by
    (Cases_on `core` >> rename1 `DftOpen ctl stack n` >> Cases_on `ctl` >>
     gvs[dft_fill_def, dft_fill_control_def]) >>
  simp[dft_next_inf_def, dft_erase_def, dft_edit_fill, dft_nonphi_edit_open_next]
QED

Theorem dft_edit_occ_address:
  (!fn b bb s stack n. c.dft_occ_core = DftOpen (DftAt fn b bb s) stack n ==>
    get_instruction (bm bb) s.vs_inst_idx = get_instruction bb s.vs_inst_idx) ==>
  dft_occ_address (dft_edit_occ fm bm c) = dft_occ_address c
Proof
  strip_tac >> Cases_on `c.dft_occ_core` >>
  rename1 `c.dft_occ_core = DftOpen ctl stack n` >> Cases_on `ctl` >>
  gvs[dft_occ_address_def, dft_edit_occ_def, dft_edit_core_def, dft_edit_control_def]
QED

Theorem dft_nonphi_edit_occ_next:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode <> PHI /\ y.inst_opcode <> PHI /\
  (!fn b bb s stack n. c.dft_occ_core = DftOpen (DftAt fn b bb s) stack n ==>
    get_instruction (dft_gas_edit_block bb0 pre x y post bb) s.vs_inst_idx =
      get_instruction bb s.vs_inst_idx) ==>
  dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)
    (dft_edit_occ (dft_gas_edit_fn bb0 pre x y post)
      (dft_gas_edit_block bb0 pre x y post) c) =
  dft_edit_occ (dft_gas_edit_fn bb0 pre x y post)
    (dft_gas_edit_block bb0 pre x y post) (dft_occ_oracle_next w C c)
Proof
  strip_tac >> simp[dft_occ_oracle_next_def, dft_edit_occ_address] >>
  simp[dft_occ_next_def] >>
  qmatch_goalsub_abbrev_tac `dft_next_inf a` >>
  `dft_next_inf a (dft_gas_edit_ctx bb0 pre x y post C)
     (dft_edit_occ (dft_gas_edit_fn bb0 pre x y post)
       (dft_gas_edit_block bb0 pre x y post) c).dft_occ_core =
   dft_edit_core (dft_gas_edit_fn bb0 pre x y post)
     (dft_gas_edit_block bb0 pre x y post) (dft_next_inf a C c.dft_occ_core)` by
    simp[dft_edit_occ_def, dft_nonphi_edit_next_inf] >>
  simp[] >>
  Cases_on `c.dft_occ_core` >>
  rename1 `c.dft_occ_core = DftOpen ctl stack n` >>
  Cases_on `dft_next_inf a C (DftOpen ctl stack n)` >>
  simp[dft_edit_occ_update, dft_edit_occ_def]
QED

Theorem dft_gas_edit_open_next:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  (!fn b bb s stack n. core = DftOpen (DftAt fn b bb s) stack n ==>
    get_instruction (dft_gas_edit_block bb0 pre x y post bb) s.vs_inst_idx =
      get_instruction bb s.vs_inst_idx) ==>
  dft_edit_core (dft_gas_edit_fn bb0 pre x y post)
    (dft_gas_edit_block bb0 pre x y post) (dft_open_next a C core) =
  dft_open_next a (dft_gas_edit_ctx bb0 pre x y post C)
    (dft_edit_core (dft_gas_edit_fn bb0 pre x y post)
      (dft_gas_edit_block bb0 pre x y post) core)
Proof
  strip_tac >> irule dft_nonphi_edit_open_next >> simp[]
QED

Theorem dft_gas_edit_next_inf:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  (!fn b bb s stack n. core = DftOpen (DftAt fn b bb s) stack n ==>
    get_instruction (dft_gas_edit_block bb0 pre x y post bb) s.vs_inst_idx =
      get_instruction bb s.vs_inst_idx) ==>
  dft_edit_core (dft_gas_edit_fn bb0 pre x y post)
    (dft_gas_edit_block bb0 pre x y post) (dft_next_inf a C core) =
  dft_next_inf a (dft_gas_edit_ctx bb0 pre x y post C)
    (dft_edit_core (dft_gas_edit_fn bb0 pre x y post)
      (dft_gas_edit_block bb0 pre x y post) core)
Proof
  strip_tac >> irule dft_nonphi_edit_next_inf >> simp[]
QED

Theorem dft_gas_edit_occ_next:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  (!fn b bb s stack n. c.dft_occ_core = DftOpen (DftAt fn b bb s) stack n ==>
    get_instruction (dft_gas_edit_block bb0 pre x y post bb) s.vs_inst_idx =
      get_instruction bb s.vs_inst_idx) ==>
  dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)
    (dft_edit_occ (dft_gas_edit_fn bb0 pre x y post)
      (dft_gas_edit_block bb0 pre x y post) c) =
  dft_edit_occ (dft_gas_edit_fn bb0 pre x y post)
    (dft_gas_edit_block bb0 pre x y post) (dft_occ_oracle_next w C c)
Proof
  strip_tac >> irule dft_nonphi_edit_occ_next >> simp[]
QED

Theorem dft_nonphi_edit_occ_next_outside:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode <> PHI /\ y.inst_opcode <> PHI /\
  (!fn b bb s stack n. c.dft_occ_core = DftOpen (DftAt fn b bb s) stack n ==>
    bb <> bb0 \/ (s.vs_inst_idx <> LENGTH pre /\ s.vs_inst_idx <> SUC (LENGTH pre))) ==>
  dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)
    (dft_edit_occ (dft_gas_edit_fn bb0 pre x y post)
      (dft_gas_edit_block bb0 pre x y post) c) =
  dft_edit_occ (dft_gas_edit_fn bb0 pre x y post)
    (dft_gas_edit_block bb0 pre x y post) (dft_occ_oracle_next w C c)
Proof
  strip_tac >> irule dft_nonphi_edit_occ_next >> simp[] >>
  rpt strip_tac >> irule dft_gas_edit_instruction_outside >> metis_tac[]
QED

Theorem dft_edit_safe_control_fill[local,simp]:
  dft_edit_control_safe (dft_fill_control 0 ctl)
Proof
  Cases_on `ctl` >> simp[dft_fill_control_def, dft_edit_control_safe_def]
QED

Theorem dft_edit_safe_fill[local]:
  EVERY dft_edit_frame_safe stack ==>
  dft_edit_safe_core (dft_fill 0 (DftOpen ctl stack n))
Proof
  simp[dft_fill_def, dft_edit_safe_core_def, dft_edit_safe_stack_erase]
QED

Theorem dft_edit_safe_deliver[local]:
  EVERY dft_edit_frame_safe stack ==>
  dft_edit_safe_core
    (dft_fill 0 (dft_open_deliver fn b bb inst s stack n r))
Proof
  Cases_on `r` >> simp[dft_open_deliver_def, dft_edit_safe_fill]
QED

Theorem dft_edit_safe_return[local]:
  EVERY dft_edit_frame_safe stack ==>
  dft_edit_safe_core (dft_fill 0 (dft_open_return r stack n))
Proof
  Cases_on `r` >> Cases_on `stack` >>
  simp[dft_open_return_def, dft_edit_safe_fill] >>
  Cases_on `h` >> simp[dft_open_return_def] >> strip_tac >>
  rename1 `bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs))` >>
  Cases_on `bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs))` >>
  simp[dft_edit_safe_fill, dft_edit_safe_deliver]
QED

Theorem dft_edit_safe_invoke[local]:
  EVERY dft_edit_frame_safe stack /\ inst.inst_opcode = INVOKE /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  dft_edit_safe_core (dft_fill 0 (dft_open_invoke C fn b bb inst s stack n))
Proof
  strip_tac >> simp[dft_open_invoke_def] >>
  Cases_on `decode_invoke inst` >> simp[dft_edit_safe_fill] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `lookup_function x0 C.ctx_functions` >> simp[dft_edit_safe_fill] >>
  Cases_on `eval_operands x1 s` >> simp[dft_edit_safe_fill] >>
  rename1 `setup_callee callee args s` >> Cases_on `setup_callee callee args s` >>
  simp[dft_edit_safe_fill, dft_fill_def, dft_edit_safe_core_def,
       dft_fill_frame_def, dft_edit_safe_frame_erase, dft_edit_safe_stack_erase,
       dft_edit_frame_safe_def]
QED

Theorem dft_edit_next_at[local]:
  dft_next_inf a C (DftOpen (DftAt fn b bb s) stack n) =
  dft_fill 0 (dft_open_next a C (DftOpen (DftAt fn b bb s) stack n))
Proof
  simp[dft_next_inf_def, dft_erase_def, GSYM dft_fill_next, dft_zero_entry_def]
QED

Theorem dft_edit_next_done[local]:
  dft_next_inf a C (DftOpen (DftDone r) stack n) =
  dft_fill 0 (dft_open_return r stack n)
Proof
  simp[dft_next_inf_def, dft_erase_def, GSYM dft_fill_next,
       dft_zero_entry_def, dft_open_next_def]
QED

Theorem dft_edit_safe_next_core:
  dft_edit_safe_core core ==> dft_edit_safe_core (dft_next_inf a C core)
Proof
  Cases_on `core` >> rename1 `DftOpen ctl stack n` >> Cases_on `ctl` >>
  simp[dft_edit_safe_core_def, dft_edit_control_safe_def] >> rpt strip_tac
  >- (simp[dft_next_inf_def, dft_fill_def, dft_fill_control_def,
           dft_erase_def, dft_open_next_def] >>
      Cases_on `lookup_block v.vs_current_bb i.fn_blocks` >>
      simp[dft_fill_def, dft_edit_safe_core_def, dft_edit_safe_stack_erase] >>
      rename1 `eval_phis s bb.bb_instructions` >> Cases_on `eval_phis s bb.bb_instructions` >>
      simp[dft_fill_def, dft_edit_safe_core_def, dft_edit_safe_stack_erase])
  >- (simp[dft_edit_next_at, dft_open_next_def] >>
      Cases_on `get_instruction b v.vs_inst_idx` >> simp[dft_edit_safe_fill] >>
      rename1 `inst.inst_opcode` >> Cases_on `inst.inst_opcode = INVOKE` >>
      simp[dft_edit_safe_invoke] >>
      Cases_on `inst.inst_opcode = GAS` >> simp[dft_edit_safe_deliver] >>
      Cases_on `inst.inst_outputs` >> simp[dft_edit_safe_fill] >>
      Cases_on `t` >> simp[dft_edit_safe_fill, dft_edit_safe_deliver])
  >> simp[dft_edit_next_done, dft_edit_safe_return]
QED

Theorem dft_gas_edit_safe_next:
  dft_edit_safe c ==> dft_edit_safe (dft_occ_oracle_next w C c)
Proof
  simp[dft_edit_safe_def, dft_occ_oracle_next_def, dft_edit_safe_next_core]
QED

Theorem dft_edit_cut_fill[local,simp]:
  dft_edit_cut bb0 k (c with dft_occ_core := dft_fill j core) =
  dft_edit_cut bb0 k (c with dft_occ_core := core)
Proof
  Cases_on `core` >> rename1 `DftOpen ctl stack n` >> Cases_on `ctl` >>
  simp[dft_edit_cut_def, dft_fill_def, dft_fill_control_def]
QED

Theorem dft_edit_cut_deliver[local]:
  (bb = bb0 ==> s.vs_inst_idx <> k) ==>
  dft_edit_cut bb0 k
    (c with dft_occ_core := dft_open_deliver fn b bb inst s stack n r)
Proof
  strip_tac >> Cases_on `r` >>
  simp[dft_open_deliver_def, dft_open_continue_def] >>
  Cases_on `is_terminator inst.inst_opcode` >>
  simp[dft_edit_cut_def] >> Cases_on `v.vs_halted` >> simp[] >> metis_tac[]
QED

Theorem dft_edit_cut_invoke[local]:
  dft_edit_cut bb0 k
    (c with dft_occ_core := dft_open_invoke C fn b bb inst s stack n)
Proof
  simp[dft_open_invoke_def] >> Cases_on `decode_invoke inst` >>
  simp[dft_edit_cut_def] >> PairCases_on `x` >> simp[] >>
  Cases_on `lookup_function x0 C.ctx_functions` >> simp[dft_edit_cut_def] >>
  Cases_on `eval_operands x1 s` >> simp[dft_edit_cut_def] >>
  rename1 `setup_callee callee args s` >> Cases_on `setup_callee callee args s` >>
  simp[dft_edit_cut_def]
QED

Theorem dft_gas_edit_slot_not_start[local]:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\ x.inst_opcode = GAS /\
  dft_edit_frame_safe (DftCaller fn b bb inst s) ==>
  (bb = bb0 ==> s.vs_inst_idx <> LENGTH pre)
Proof
  simp[dft_edit_frame_safe_def] >> rpt strip_tac >> gvs[] >>
  drule dft_gas_edit_instruction_pair >> simp[] >> rpt strip_tac >> gvs[]
QED

Theorem dft_edit_cut_non_at[local,simp]:
  dft_edit_cut bb0 k (c with dft_occ_core := DftOpen (DftDone r) stack n) /\
  dft_edit_cut bb0 k (c with dft_occ_core := DftOpen (DftEnter fn b s) stack n)
Proof
  simp[dft_edit_cut_def]
QED

Theorem dft_gas_edit_cut_return[local]:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\ x.inst_opcode = GAS /\
  EVERY dft_edit_frame_safe stack ==>
  dft_edit_cut bb0 (LENGTH pre)
    (c with dft_occ_core := dft_open_return r stack n)
Proof
  Cases_on `r` >> Cases_on `stack` >>
  simp[dft_open_return_def] >>
  Cases_on `h` >> simp[dft_open_return_def] >> strip_tac >>
  rename1 `bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs))` >>
  Cases_on `bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs))`
  >- simp[dft_edit_cut_def] >>
  simp[] >> irule dft_edit_cut_deliver >>
  metis_tac[dft_gas_edit_slot_not_start]
QED

Theorem dft_gas_edit_cut_next:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\ x.inst_opcode = GAS /\
  dft_edit_safe c /\ ~dft_edit_before bb0 (LENGTH pre) c ==>
  dft_edit_cut bb0 (LENGTH pre) (dft_occ_oracle_next w C c)
Proof
  strip_tac >>
  `!core. dft_edit_cut bb0 (LENGTH pre) (c with dft_occ_core := core) ==>
     dft_edit_cut bb0 (LENGTH pre)
       ((dft_occ_update c core) with dft_occ_core := core)` by
    simp[dft_edit_cut_def] >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def] >> first_x_assum irule >>
  Cases_on `c.dft_occ_core` >>
  rename1 `c.dft_occ_core = DftOpen ctl stack n` >> Cases_on `ctl` >>
  gvs[dft_edit_safe_def, dft_edit_safe_core_def, dft_edit_control_safe_def,
      dft_edit_before_def]
  >- (simp[dft_next_inf_def, dft_fill_def, dft_fill_control_def,
           dft_erase_def, dft_open_next_def] >>
      Cases_on `lookup_block v.vs_current_bb i.fn_blocks` >>
      simp[dft_edit_cut_def, dft_fill_def, dft_fill_control_def] >>
      rename1 `eval_phis s bb.bb_instructions` >> Cases_on `eval_phis s bb.bb_instructions` >>
      simp[dft_edit_cut_def, dft_fill_def, dft_fill_control_def] >>
      rpt strip_tac >> gvs[] >>
      `phi_prefix_length (pre ++ [x;y] ++ post) <= LENGTH pre` by
        simp[dft_gas_edit_phi_bound] >> decide_tac)
  >- (simp[dft_edit_next_at, dft_open_next_def] >>
      Cases_on `get_instruction b v.vs_inst_idx` >> simp[] >>
      rename1 `inst.inst_opcode` >> Cases_on `inst.inst_opcode = INVOKE` >>
      simp[dft_edit_cut_invoke] >>
      Cases_on `inst.inst_opcode = GAS` >> simp[dft_edit_cut_deliver] >>
      Cases_on `inst.inst_outputs` >> simp[] >>
      Cases_on `t` >> simp[dft_edit_cut_deliver])
  >> simp[dft_edit_next_done, dft_gas_edit_cut_return]
QED

Theorem dft_gas_edit_sync_fetch:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  dft_edit_safe c /\ dft_edit_cut bb0 (LENGTH pre) c /\
  ~dft_edit_before bb0 (LENGTH pre) c ==>
  !fn b bb s stack n. c.dft_occ_core = DftOpen (DftAt fn b bb s) stack n ==>
    get_instruction (dft_gas_edit_block bb0 pre x y post bb) s.vs_inst_idx =
      get_instruction bb s.vs_inst_idx
Proof
  Cases_on `c.dft_occ_core` >>
  rename1 `c.dft_occ_core = DftOpen ctl stack n` >> Cases_on `ctl` >>
  simp[dft_edit_safe_def, dft_edit_safe_core_def, dft_edit_control_safe_def,
       dft_edit_cut_def, dft_edit_before_def] >> rpt strip_tac >>
  irule dft_gas_edit_instruction_outside >> simp[] >> metis_tac[]
QED

Theorem dft_gas_edit_rel_next:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  x.inst_operands = [] /\ y.inst_operands = [] /\
  u <> v /\ x.inst_id <> y.inst_id /\
  dft_gas_edit_rel bb0 pre x y post w C l r ==>
  dft_gas_edit_rel bb0 pre x y post w C
    (dft_occ_oracle_next w C l)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C) r)
Proof
  simp[dft_gas_edit_rel_def] >> strip_tac
  >- (Cases_on `dft_edit_before bb0 (LENGTH pre) l`
      >- (disj2_tac >> qexists_tac `l` >> simp[]) >>
      disj1_tac >>
      `!fn b bb s stack n. l.dft_occ_core = DftOpen (DftAt fn b bb s) stack n ==>
        get_instruction (dft_gas_edit_block bb0 pre x y post bb) s.vs_inst_idx =
          get_instruction bb s.vs_inst_idx` by
        metis_tac[dft_gas_edit_sync_fetch] >>
      simp[dft_gas_edit_safe_next, dft_gas_edit_cut_next, dft_gas_edit_occ_next]) >>
  disj1_tac >>
  simp[dft_gas_edit_middle_join, dft_gas_edit_middle_safe_cut, dft_gas_edit_safe_next]
QED

Definition dft_edit_gas_cut_def:
  dft_edit_gas_cut core <=>
    ?fn b bb s stack n inst.
      core = DftOpen (DftAt fn b bb s) stack n /\
      get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode = GAS
End

Theorem dft_gas_edit_middle_active:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  x.inst_operands = [] /\ y.inst_operands = [] /\
  dft_edit_before bb0 (LENGTH pre) c ==>
  dft_edit_gas_cut (dft_occ_oracle_next w C c).dft_occ_core /\
  dft_edit_gas_cut
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)
      (dft_edit_occ (dft_gas_edit_fn bb0 pre x y post)
        (dft_gas_edit_block bb0 pre x y post) c)).dft_occ_core
Proof
  simp[dft_edit_before_def] >> rpt strip_tac >> Cases_on `c` >> gvs[] >>
  simp[dft_edit_gas_cut_def, dft_edit_occ_def, dft_edit_core_def, dft_edit_control_def,
       dft_occ_oracle_next_def, dft_occ_next_def, dft_occ_address_def,
       dft_next_inf_def, dft_fill_def, dft_fill_control_def, dft_erase_def,
       dft_open_next_def, dft_open_deliver_def, dft_open_continue_def,
       get_instruction_def, dft_gas_edit_block_def, EL_APPEND_EQN,
       is_terminator_def, update_var_def, ADD1]
QED
