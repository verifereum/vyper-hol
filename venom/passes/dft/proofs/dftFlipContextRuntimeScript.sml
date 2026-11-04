Theory dftFlipContextRuntime
Ancestors
  dftFlipRuntime dftPositionalRuntime dftRelationalEdit dftOpenMachine
  venomExecSemantics venomInst venomEffects passSharedDefs dftDefs list option arithmetic

Definition dft_flip_block_def:
  dft_flip_block b b' <=> b'.bb_label = b.bb_label /\
    LIST_REL flip_rel b.bb_instructions b'.bb_instructions
End

Definition dft_flip_function_def:
  dft_flip_function f g <=> g = f with fn_blocks := g.fn_blocks /\
    LIST_REL dft_flip_block f.fn_blocks g.fn_blocks
End

Theorem dft_flip_phi:
  flip_rel i j ==> (i.inst_opcode = PHI <=> j.inst_opcode = PHI) /\
    (i.inst_opcode = PHI ==> j = i)
Proof
  simp[flip_rel_def] >> rpt strip_tac >> simp[] >>
  Cases_on `i.inst_opcode` >>
  gvs[is_flippable_def, is_commutative_def, is_comparator_def] >>
  Cases_on `i.inst_operands` >> gvs[flip_operands_def] >>
  Cases_on `t` >> gvs[flip_operands_def] >>
  Cases_on `t'` >> gvs[flip_operands_def, is_comparator_def,
    flip_comparison_opcode_def]
QED

Theorem dft_flip_phis:
  !xs ys. LIST_REL flip_rel xs ys ==>
    (!s. eval_phis s xs = eval_phis s ys) /\
    phi_prefix_length xs = phi_prefix_length ys
Proof
  Induct >> Cases_on `ys` >> simp[eval_phis_def, phi_prefix_length_def] >>
  rpt strip_tac >>
  `(!s. eval_phis s xs = eval_phis s t) /\
    phi_prefix_length xs = phi_prefix_length t` by metis_tac[] >>
  drule dft_flip_phi >> strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[eval_phis_def, phi_prefix_length_def]
QED

Theorem dft_flip_function_name:
  dft_flip_function f g ==> g.fn_name = f.fn_name
Proof
  simp[dft_flip_function_def] >> strip_tac >>
  once_asm_rewrite_tac[] >> simp[]
QED

Theorem dft_flip_function_lookup:
  LIST_REL dft_flip_function C.ctx_functions C'.ctx_functions ==>
  OPTREL dft_flip_function (lookup_function nm C.ctx_functions)
    (lookup_function nm C'.ctx_functions)
Proof
  strip_tac >> simp[lookup_function_def] >> irule dft_rel_find >>
  simp[] >> metis_tac[dft_flip_function_name]
QED

Theorem dft_flip_block_lookup:
  dft_flip_function f g ==>
  OPTREL dft_flip_block (lookup_block lbl f.fn_blocks)
    (lookup_block lbl g.fn_blocks)
Proof
  strip_tac >> simp[lookup_block_def] >> irule dft_rel_find >>
  fs[dft_flip_function_def, dft_flip_block_def] >> metis_tac[]
QED

Theorem dft_flip_setup:
  dft_flip_function f g ==> setup_callee f args s = setup_callee g args s
Proof
  simp[dft_flip_function_def] >> strip_tac >>
  Cases_on `f.fn_blocks` >> Cases_on `g.fn_blocks` >>
  gvs[setup_callee_def, dft_flip_block_def]
QED

Theorem dft_flip_context_interface:
  LIST_REL dft_flip_function C.ctx_functions C'.ctx_functions ==>
  dft_rel_interface C C' dft_flip_function (\f g. dft_flip_block)
Proof
  strip_tac >> simp[dft_rel_interface_def] >> rpt conj_tac
  >- metis_tac[dft_flip_function_lookup]
  >- metis_tac[dft_flip_setup, dft_flip_block_lookup] >>
  simp[dft_flip_block_def] >> metis_tac[dft_flip_phis]
QED

Theorem dft_flip_context_prefix:
  LIST_REL dft_flip_function C.ctx_functions C'.ctx_functions /\
  dft_rel_core dft_flip_function (\f g. dft_flip_block) q q' ==>
  !steps. dft_rel_core dft_flip_function (\f g. dft_flip_block)
    (FUNPOW (dft_open_next a C) steps q)
    (FUNPOW (dft_open_next a C') steps q')
Proof
  strip_tac >> Induct >> simp[FUNPOW_SUC] >>
  irule dft_flip_next >> simp[] >> conj_tac
  >- simp[dft_flip_block_def] >>
  irule dft_flip_context_interface >> simp[]
QED

Theorem dft_flip_context_entry:
  LIST_REL dft_flip_function C.ctx_functions C'.ctx_functions /\
  dft_flip_function f g ==>
  !steps. dft_rel_core dft_flip_function (\f g. dft_flip_block)
    (FUNPOW (dft_open_next a C) steps (DftOpen (DftEnter f fuel s) [] n))
    (FUNPOW (dft_open_next a C') steps (DftOpen (DftEnter g fuel s) [] n))
Proof
  strip_tac >> irule dft_flip_context_prefix >>
  simp[dft_rel_core_def]
QED

Theorem dft_flip_core_terminal:
  dft_rel_core dft_flip_function (\f g. dft_flip_block) q q' ==>
  (q = DftOpen (DftDone r) [] m <=> q' = DftOpen (DftDone r) [] m)
Proof
  Cases_on `q` >> Cases_on `q'` >>
  rename1 `dft_rel_core _ _ (DftOpen c stk n) (DftOpen c' stk' n')` >>
  Cases_on `c` >> Cases_on `c'` >>
  simp[dft_rel_core_def, dft_rel_control_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `stk` >> Cases_on `stk'` >> gvs[]
QED

Theorem dft_flip_core_observe:
  dft_rel_core dft_flip_function (\f g. dft_flip_block) q q' ==>
  (!f i s. dft_open_observe f i s q ==>
    ?g j. dft_flip_function f g /\ flip_rel i j /\ dft_open_observe g j s q') /\
  (!g j s. dft_open_observe g j s q' ==>
    ?f i. dft_flip_function f g /\ flip_rel i j /\ dft_open_observe f i s q)
Proof
  Cases_on `q` >> Cases_on `q'` >>
  rename1 `dft_rel_core _ _ (DftOpen c stk n) (DftOpen c' stk' n')` >>
  Cases_on `c` >> Cases_on `c'` >>
  simp[dft_rel_core_def, dft_rel_control_def, dft_open_observe_def] >>
  rpt strip_tac >> gvs[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  rename1 `dft_flip_block b b'` >>
  `OPTREL flip_rel (get_instruction b s.vs_inst_idx)
    (get_instruction b' s.vs_inst_idx)` by
    (irule dft_flip_get_instruction >> fs[dft_flip_block_def]) >>
  Cases_on `get_instruction b s.vs_inst_idx` >>
  Cases_on `get_instruction b' s.vs_inst_idx` >> gvs[] >> metis_tac[]
QED

Theorem dft_flip_context_terminal:
  LIST_REL dft_flip_function C.ctx_functions C'.ctx_functions /\
  dft_rel_core dft_flip_function (\f g. dft_flip_block) q q' ==>
  (FUNPOW (dft_open_next a C) steps q = DftOpen (DftDone r) [] m <=>
   FUNPOW (dft_open_next a C') steps q' = DftOpen (DftDone r) [] m)
Proof
  strip_tac >> irule dft_flip_core_terminal >>
  irule dft_flip_context_prefix >> simp[]
QED

Theorem dft_flip_context_observe:
  LIST_REL dft_flip_function C.ctx_functions C'.ctx_functions /\
  dft_rel_core dft_flip_function (\f g. dft_flip_block) q q' ==>
  (!f i s. dft_open_observe f i s (FUNPOW (dft_open_next a C) steps q) ==>
    ?g j. dft_flip_function f g /\ flip_rel i j /\
      dft_open_observe g j s (FUNPOW (dft_open_next a C') steps q')) /\
  (!g j s. dft_open_observe g j s (FUNPOW (dft_open_next a C') steps q') ==>
    ?f i. dft_flip_function f g /\ flip_rel i j /\
      dft_open_observe f i s (FUNPOW (dft_open_next a C) steps q))
Proof
  strip_tac >> irule dft_flip_core_observe >>
  irule dft_flip_context_prefix >> simp[]
QED
