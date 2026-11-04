Theory dftRelationalEdit
Ancestors
  dftOpenMachine list option

Definition dft_rel_frame_def:
  dft_rel_frame R br (DftCaller f k b i s) (DftCaller g k' b' i' s') <=>
    R f g /\ br f g b b' /\ k = k' /\ i = i' /\ s = s'
End

Definition dft_rel_control_def:
  dft_rel_control R br c c' <=>
    case (c,c') of
      (DftEnter f k s, DftEnter g k' s') => R f g /\ k = k' /\ s = s'
    | (DftAt f k b s, DftAt g k' b' s') =>
        R f g /\ br f g b b' /\ k = k' /\ s = s'
    | (DftDone r, DftDone r') => r = r'
    | _ => F
End

Definition dft_rel_core_def:
  dft_rel_core R br (DftOpen c stk n) (DftOpen c' stk' n') <=>
    dft_rel_control R br c c' /\ LIST_REL (dft_rel_frame R br) stk stk' /\ n = n'
End

Definition dft_rel_interface_def:
  dft_rel_interface C C' R br <=>
    (!nm. OPTREL R (lookup_function nm C.ctx_functions)
      (lookup_function nm C'.ctx_functions)) /\
    (!f g. R f g ==>
      (!args s. setup_callee f args s = setup_callee g args s) /\
      (!lbl. OPTREL (br f g) (lookup_block lbl f.fn_blocks)
        (lookup_block lbl g.fn_blocks))) /\
    (!f g b b'. R f g /\ br f g b b' ==>
      (!s. eval_phis s b.bb_instructions = eval_phis s b'.bb_instructions) /\
      phi_prefix_length b.bb_instructions = phi_prefix_length b'.bb_instructions)
End

Theorem dft_rel_controls[simp]:
  (dft_rel_control R br (DftEnter f k s) (DftEnter g k' s') <=>
    R f g /\ k = k' /\ s = s') /\
  (dft_rel_control R br (DftAt f k b s) (DftAt g k' b' s') <=>
    R f g /\ br f g b b' /\ k = k' /\ s = s') /\
  (dft_rel_control R br (DftDone r) (DftDone r') <=> r = r')
Proof
  simp[dft_rel_control_def]
QED

Theorem dft_rel_deliver:
  R f g /\ br f g b b' /\ LIST_REL (dft_rel_frame R br) stk stk' ==>
  dft_rel_core R br
    (dft_open_deliver f k b i s stk n r)
    (dft_open_deliver g k b' i s stk' n r)
Proof
  strip_tac >> Cases_on `r` >>
  simp[dft_open_deliver_def, dft_rel_core_def] >>
  simp[dft_open_continue_def] >>
  Cases_on `is_terminator i.inst_opcode` >> simp[] >>
  Cases_on `v.vs_halted` >> simp[]
QED

Theorem dft_rel_return:
  LIST_REL (dft_rel_frame R br) stk stk' ==>
  dft_rel_core R br (dft_open_return r stk n) (dft_open_return r stk' n)
Proof
  strip_tac >> Cases_on `r` >> Cases_on `stk` >> Cases_on `stk'` >>
  gvs[dft_open_return_def, dft_rel_core_def] >>
  Cases_on `h` >> Cases_on `h'` >> gvs[dft_rel_frame_def] >>
  CASE_TAC >> simp[dft_rel_core_def] >>
  irule dft_rel_deliver >> simp[]
QED

Theorem dft_rel_invoke:
  dft_rel_interface C C' R br /\ R f g /\ br f g b b' /\
  LIST_REL (dft_rel_frame R br) stk stk' ==>
  dft_rel_core R br
    (dft_open_invoke C f k b i s stk n)
    (dft_open_invoke C' g k b' i s stk' n)
Proof
  strip_tac >> Cases_on `decode_invoke i` >>
  simp[dft_open_invoke_def, dft_rel_core_def] >>
  PairCases_on `x` >> gvs[] >>
  `OPTREL R (lookup_function x0 C.ctx_functions)
    (lookup_function x0 C'.ctx_functions)` by fs[dft_rel_interface_def] >>
  Cases_on `lookup_function x0 C.ctx_functions` >>
  Cases_on `lookup_function x0 C'.ctx_functions` >> gvs[dft_rel_core_def] >>
  `!args s. setup_callee x args s = setup_callee x' args s` by
    (fs[dft_rel_interface_def] >> metis_tac[]) >>
  Cases_on `eval_operands x1 s` >> simp[dft_rel_core_def] >>
  Cases_on `setup_callee x' x'' s` >>
  gvs[dft_rel_core_def, dft_rel_frame_def]
QED

Theorem dft_rel_enter:
  dft_rel_interface C C' R br /\ R f g /\
  LIST_REL (dft_rel_frame R br) stk stk' ==>
  dft_rel_core R br
    (dft_open_next a C (DftOpen (DftEnter f fuel s) stk n))
    (dft_open_next a C' (DftOpen (DftEnter g fuel s) stk' n))
Proof
  strip_tac >> Cases_on `fuel` >> simp[dft_open_next_def, dft_rel_core_def] >>
  `OPTREL (br f g) (lookup_block s.vs_current_bb f.fn_blocks)
    (lookup_block s.vs_current_bb g.fn_blocks)` by
    (fs[dft_rel_interface_def] >> metis_tac[]) >>
  Cases_on `lookup_block s.vs_current_bb f.fn_blocks` >>
  Cases_on `lookup_block s.vs_current_bb g.fn_blocks` >> gvs[dft_rel_core_def] >>
  `eval_phis s x.bb_instructions = eval_phis s x'.bb_instructions /\
   phi_prefix_length x.bb_instructions = phi_prefix_length x'.bb_instructions` by
    (fs[dft_rel_interface_def] >> metis_tac[]) >>
  simp[] >> Cases_on `eval_phis s x'.bb_instructions` >> simp[dft_rel_core_def]
QED

Theorem dft_rel_at:
  dft_rel_interface C C' R br /\ R f g /\ br f g b b' /\
  LIST_REL (dft_rel_frame R br) stk stk' /\
  get_instruction b s.vs_inst_idx = get_instruction b' s.vs_inst_idx ==>
  dft_rel_core R br
    (dft_open_next a C (DftOpen (DftAt f k b s) stk n))
    (dft_open_next a C' (DftOpen (DftAt g k b' s) stk' n))
Proof
  strip_tac >> simp[dft_open_next_def] >>
  Cases_on `get_instruction b' s.vs_inst_idx` >> simp[dft_rel_core_def] >>
  Cases_on `x.inst_opcode = INVOKE`
  >- (simp[] >> irule dft_rel_invoke >> simp[]) >>
  simp[] >> Cases_on `x.inst_opcode = GAS` >> simp[]
  >- (Cases_on `x.inst_outputs` >> simp[dft_rel_core_def] >>
      Cases_on `t` >> simp[dft_rel_core_def] >>
      irule dft_rel_deliver >> simp[]) >>
  irule dft_rel_deliver >> simp[]
QED
