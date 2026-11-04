Theory dftPositionalRuntime
Ancestors
  dftPositionalEdit dftRelationalEdit dftOccurrenceGasEdit
  venomExecSemantics venomInst list option

Definition dft_pos_functions_def:
  dft_pos_functions C C' f g <=>
    ?j. j < LENGTH C.ctx_functions /\
      f = EL j C.ctx_functions /\ g = EL j C'.ctx_functions
End

Definition dft_pos_blocks_def:
  dft_pos_blocks C C' f g b b' <=>
    ?j k. j < LENGTH C.ctx_functions /\
      f = EL j C.ctx_functions /\ g = EL j C'.ctx_functions /\
      k < LENGTH f.fn_blocks /\ b = EL k f.fn_blocks /\ b' = EL k g.fn_blocks
End

Theorem dft_rel_find:
  !xs ys. LIST_REL R xs ys /\ (!x y. R x y ==> (P x <=> Q y)) ==>
    OPTREL R (FIND P xs) (FIND Q ys)
Proof
  Induct >> Cases_on `ys` >> simp[FIND_thm] >> rpt strip_tac >>
  rename1 `R a b` >>
  `P a <=> Q b` by metis_tac[] >>
  Cases_on `P a` >> Cases_on `Q b` >> gvs[] >> metis_tac[]
QED

Theorem dft_pos_functions_list:
  LENGTH C'.ctx_functions = LENGTH C.ctx_functions ==>
  LIST_REL (dft_pos_functions C C') C.ctx_functions C'.ctx_functions
Proof
  simp[LIST_REL_EL_EQN, dft_pos_functions_def] >> metis_tac[]
QED

Theorem dft_pos_edit_function_name:
  dft_pos_functions C (dft_pos_edit_ctx fi bi pre x y post C) f g ==>
  g.fn_name = f.fn_name
Proof
  rw[dft_pos_functions_def, dft_pos_edit_ctx_def, dft_pos_replace_el] >>
  Cases_on `j = fi /\ fi < LENGTH C.ctx_functions` >>
  gvs[dft_pos_edit_fn_def]
QED

Theorem dft_pos_edit_function_lookup:
  OPTREL (dft_pos_functions C (dft_pos_edit_ctx fi bi pre x y post C))
    (lookup_function nm C.ctx_functions)
    (lookup_function nm (dft_pos_edit_ctx fi bi pre x y post C).ctx_functions)
Proof
  simp[lookup_function_def] >> irule dft_rel_find >> conj_tac
  >- (metis_tac[dft_pos_edit_function_name]) >>
  irule dft_pos_functions_list >> simp[dft_pos_edit_ctx_def]
QED

Theorem dft_pos_edit_blocks_length:
  dft_pos_functions C (dft_pos_edit_ctx fi bi pre x y post C) f g ==>
  LENGTH g.fn_blocks = LENGTH f.fn_blocks
Proof
  rw[dft_pos_functions_def, dft_pos_edit_ctx_def, dft_pos_replace_el] >>
  Cases_on `j = fi /\ fi < LENGTH C.ctx_functions` >>
  gvs[dft_pos_edit_fn_def]
QED

Theorem dft_pos_edit_blocks_list:
  dft_pos_functions C (dft_pos_edit_ctx fi bi pre x y post C) f g ==>
  LIST_REL (dft_pos_blocks C (dft_pos_edit_ctx fi bi pre x y post C) f g)
    f.fn_blocks g.fn_blocks
Proof
  strip_tac >> drule dft_pos_edit_blocks_length >> strip_tac >>
  simp[LIST_REL_EL_EQN, dft_pos_blocks_def] >>
  fs[dft_pos_functions_def] >> metis_tac[]
QED

Theorem dft_pos_edit_block_label:
  dft_pos_blocks C (dft_pos_edit_ctx fi bi pre x y post C) f g b b' ==>
  b'.bb_label = b.bb_label
Proof
  rw[dft_pos_blocks_def, dft_pos_edit_ctx_def, dft_pos_replace_el] >>
  Cases_on `j = fi /\ fi < LENGTH C.ctx_functions` >>
  gvs[dft_pos_edit_fn_def, dft_pos_replace_el] >>
  Cases_on `k = bi /\ bi < LENGTH (EL fi C.ctx_functions).fn_blocks` >> simp[]
QED

Theorem dft_pos_edit_block_lookup:
  dft_pos_functions C (dft_pos_edit_ctx fi bi pre x y post C) f g ==>
  OPTREL (dft_pos_blocks C (dft_pos_edit_ctx fi bi pre x y post C) f g)
    (lookup_block lbl f.fn_blocks) (lookup_block lbl g.fn_blocks)
Proof
  strip_tac >> simp[lookup_block_def] >> irule dft_rel_find >> conj_tac
  >- (metis_tac[dft_pos_edit_block_label]) >>
  irule dft_pos_edit_blocks_list >> simp[]
QED

Theorem dft_pos_edit_setup_fn:
  setup_callee (dft_pos_edit_fn bi pre x y post f) args s = setup_callee f args s
Proof
  Cases_on `f.fn_blocks` >> Cases_on `bi` >>
  simp[dft_pos_edit_fn_def, dft_pos_replace_lupdate, LUPDATE_def, setup_callee_def]
QED

Theorem dft_pos_edit_setup:
  dft_pos_functions C (dft_pos_edit_ctx fi bi pre x y post C) f g ==>
  setup_callee f args s = setup_callee g args s
Proof
  rw[dft_pos_functions_def, dft_pos_edit_ctx_def, dft_pos_replace_el] >>
  Cases_on `j = fi /\ fi < LENGTH C.ctx_functions` >>
  gvs[dft_pos_edit_setup_fn]
QED

Theorem dft_pos_edit_block_phis:
  fi < LENGTH C.ctx_functions /\
  bi < LENGTH (EL fi C.ctx_functions).fn_blocks /\
  (EL bi (EL fi C.ctx_functions).fn_blocks).bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode <> PHI /\ y.inst_opcode <> PHI /\
  dft_pos_blocks C (dft_pos_edit_ctx fi bi pre x y post C) f g b b' ==>
  eval_phis s b.bb_instructions = eval_phis s b'.bb_instructions /\
  phi_prefix_length b.bb_instructions = phi_prefix_length b'.bb_instructions
Proof
  rw[dft_pos_blocks_def, dft_pos_edit_ctx_def, dft_pos_replace_el] >>
  Cases_on `j = fi` >> gvs[dft_pos_edit_fn_def, dft_pos_replace_el] >>
  Cases_on `k = bi` >> gvs[] >>
  metis_tac[dft_nonphi_edit_phis_list, dft_nonphi_edit_phi_length_list]
QED

Theorem dft_pos_edit_interface:
  fi < LENGTH C.ctx_functions /\
  bi < LENGTH (EL fi C.ctx_functions).fn_blocks /\
  (EL bi (EL fi C.ctx_functions).fn_blocks).bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode <> PHI /\ y.inst_opcode <> PHI ==>
  dft_rel_interface C (dft_pos_edit_ctx fi bi pre x y post C)
    (dft_pos_functions C (dft_pos_edit_ctx fi bi pre x y post C))
    (dft_pos_blocks C (dft_pos_edit_ctx fi bi pre x y post C))
Proof
  simp[dft_rel_interface_def] >> rpt strip_tac
  >- metis_tac[dft_pos_edit_function_lookup]
  >- metis_tac[dft_pos_edit_setup]
  >- metis_tac[dft_pos_edit_block_lookup]
  >- metis_tac[dft_pos_edit_block_phis]
  >> metis_tac[dft_pos_edit_block_phis]
QED

Theorem dft_pos_edit_instruction_outside:
  fi < LENGTH C.ctx_functions /\ j < LENGTH C.ctx_functions /\
  bi < LENGTH (EL fi C.ctx_functions).fn_blocks /\
  (EL bi (EL fi C.ctx_functions).fn_blocks).bb_instructions = pre ++ [x;y] ++ post /\
  (j <> fi \/ k <> bi \/ (i <> LENGTH pre /\ i <> SUC (LENGTH pre))) ==>
  get_instruction
    (EL k (EL j (dft_pos_edit_ctx fi bi pre x y post C).ctx_functions).fn_blocks) i =
  get_instruction (EL k (EL j C.ctx_functions).fn_blocks) i
Proof
  strip_tac >> simp[dft_pos_edit_ctx_def, dft_pos_replace_el] >>
  Cases_on `j = fi` >> gvs[dft_pos_edit_fn_def, dft_pos_replace_el] >>
  Cases_on `k = bi` >> gvs[] >>
  drule dft_gas_edit_instruction_outside >>
  disch_then (qspecl_then [`i`, `EL bi (EL fi C.ctx_functions).fn_blocks`] mp_tac) >>
  simp[dft_gas_edit_block_def]
QED

Definition dft_pos_runtime_ready_def:
  dft_pos_runtime_ready C fi bi pre x y post <=>
    fi < LENGTH C.ctx_functions /\
    bi < LENGTH (EL fi C.ctx_functions).fn_blocks /\
    (EL bi (EL fi C.ctx_functions).fn_blocks).bb_instructions = pre ++ [x;y] ++ post /\
    x.inst_opcode <> PHI /\ y.inst_opcode <> PHI
End

Theorem dft_pos_runtime_ready_interface:
  dft_pos_runtime_ready C fi bi pre x y post ==>
  dft_rel_interface C (dft_pos_edit_ctx fi bi pre x y post C)
    (dft_pos_functions C (dft_pos_edit_ctx fi bi pre x y post C))
    (dft_pos_blocks C (dft_pos_edit_ctx fi bi pre x y post C))
Proof
  simp[dft_pos_runtime_ready_def, dft_pos_edit_interface]
QED

Theorem dft_pos_runtime_enter:
  C' = dft_pos_edit_ctx fi bi pre x y post C /\
  dft_pos_runtime_ready C fi bi pre x y post /\
  dft_pos_functions C C' f g /\
  LIST_REL (dft_rel_frame (dft_pos_functions C C') (dft_pos_blocks C C')) stk stk' ==>
  dft_rel_core (dft_pos_functions C C') (dft_pos_blocks C C')
    (dft_open_next a C (DftOpen (DftEnter f fuel s) stk n))
    (dft_open_next a C' (DftOpen (DftEnter g fuel s) stk' n))
Proof
  strip_tac >> gvs[] >> irule dft_rel_enter >> simp[] >>
  irule dft_pos_runtime_ready_interface >> simp[]
QED

Theorem dft_pos_runtime_invoke:
  C' = dft_pos_edit_ctx fi bi pre x y post C /\
  dft_pos_runtime_ready C fi bi pre x y post /\
  dft_pos_functions C C' f g /\ dft_pos_blocks C C' f g b b' /\
  LIST_REL (dft_rel_frame (dft_pos_functions C C') (dft_pos_blocks C C')) stk stk' ==>
  dft_rel_core (dft_pos_functions C C') (dft_pos_blocks C C')
    (dft_open_invoke C f k b i s stk n)
    (dft_open_invoke C' g k b' i s stk' n)
Proof
  strip_tac >> gvs[] >> irule dft_rel_invoke >> simp[] >>
  irule dft_pos_runtime_ready_interface >> simp[]
QED

Theorem dft_pos_runtime_return:
  LIST_REL (dft_rel_frame (dft_pos_functions C C') (dft_pos_blocks C C')) stk stk' ==>
  dft_rel_core (dft_pos_functions C C') (dft_pos_blocks C C')
    (dft_open_return r stk n) (dft_open_return r stk' n)
Proof
  strip_tac >> irule dft_rel_return >> simp[]
QED

Theorem dft_pos_runtime_at:
  C' = dft_pos_edit_ctx fi bi pre x y post C /\
  dft_pos_runtime_ready C fi bi pre x y post /\
  dft_pos_functions C C' f g /\ dft_pos_blocks C C' f g b b' /\
  LIST_REL (dft_rel_frame (dft_pos_functions C C') (dft_pos_blocks C C')) stk stk' /\
  get_instruction b s.vs_inst_idx = get_instruction b' s.vs_inst_idx ==>
  dft_rel_core (dft_pos_functions C C') (dft_pos_blocks C C')
    (dft_open_next a C (DftOpen (DftAt f k b s) stk n))
    (dft_open_next a C' (DftOpen (DftAt g k b' s) stk' n))
Proof
  strip_tac >> gvs[] >> irule dft_rel_at >> simp[] >>
  irule dft_pos_runtime_ready_interface >> simp[]
QED
