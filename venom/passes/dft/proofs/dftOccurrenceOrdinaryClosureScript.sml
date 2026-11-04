Theory dftOccurrenceOrdinaryClosure
Ancestors
  dftOccurrenceOrdinaryEdit dftOccurrenceOrdinaryObserve dftOccurrenceOrdinaryStop
  dftOccurrenceGasEdit dftOccurrenceEditRuntime dftOccurrenceRuntime
  dftOccurrenceReplay dftOccurrenceMachine dftOpenErase dftOpenMachine dftOpenFuel
  venomExecSemantics venomInst dftAvailability dftOccurrenceAvailability
  dftScheduleOrder dftCorrectness dftOrdinarySwap venomWf venomState sccpCorrectnessProofs finite_map
  list arithmetic allocaRemapSSA venomExecProofs venomExecProps dftOrdinaryStop opcodeClass
  dftOccurrenceCallTrace

Theorem dft_nonphi_edit_phi_bound:
  !pre. x.inst_opcode <> PHI ==>
    phi_prefix_length (pre ++ [x;y] ++ post) <= LENGTH pre
Proof
  Induct >> simp[phi_prefix_length_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >> metis_tac[]
QED

Theorem dft_ordinary_edit_init:
  dft_edit_safe (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n)) /\
  dft_edit_cut bb0 k (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n)) /\
  dft_occ_init (DftOpen (DftEnter (fm fn) 0 s) [] n) =
    dft_edit_occ fm bm (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))
Proof
  simp[dft_edit_safe_def, dft_edit_safe_core_def, dft_edit_control_safe_def,
    dft_edit_cut_def, dft_edit_occ_def, dft_edit_core_def,
    dft_edit_control_def, dft_occ_init_def]
QED

Theorem dft_ordinary_edit_slot_not_start:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\ x.inst_opcode <> INVOKE /\
  dft_edit_frame_safe (DftCaller fn b bb inst s) ==>
  (bb = bb0 ==> s.vs_inst_idx <> LENGTH pre)
Proof
  simp[dft_edit_frame_safe_def] >> rpt strip_tac >> gvs[] >>
  drule dft_gas_edit_instruction_pair >> simp[] >> rpt strip_tac >> gvs[]
QED

Theorem dft_ordinary_cut_fill[local,simp]:
  dft_edit_cut bb0 k (c with dft_occ_core := dft_fill j core) =
  dft_edit_cut bb0 k (c with dft_occ_core := core)
Proof
  Cases_on `core` >> rename1 `DftOpen ctl stack n` >> Cases_on `ctl` >>
  simp[dft_edit_cut_def, dft_fill_def, dft_fill_control_def]
QED

Theorem dft_ordinary_cut_deliver[local]:
  (bb = bb0 ==> s.vs_inst_idx <> k) ==>
  dft_edit_cut bb0 k
    (c with dft_occ_core := dft_open_deliver fn b bb inst s stack n r)
Proof
  strip_tac >> Cases_on `r` >>
  simp[dft_open_deliver_def, dft_open_continue_def] >>
  Cases_on `is_terminator inst.inst_opcode` >>
  simp[dft_edit_cut_def] >> Cases_on `v.vs_halted` >> simp[] >> metis_tac[]
QED

Theorem dft_ordinary_cut_non_at[local,simp]:
  dft_edit_cut bb0 k (c with dft_occ_core := DftOpen (DftDone r) stack n) /\
  dft_edit_cut bb0 k (c with dft_occ_core := DftOpen (DftEnter fn b s) stack n)
Proof
  simp[dft_edit_cut_def]
QED

Theorem dft_ordinary_cut_return[local]:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\ x.inst_opcode <> INVOKE /\
  EVERY dft_edit_frame_safe stack ==>
  dft_edit_cut bb0 (LENGTH pre)
    (c with dft_occ_core := dft_open_return r stack n)
Proof
  Cases_on `r` >> Cases_on `stack` >> simp[dft_open_return_def] >>
  Cases_on `h` >> simp[dft_open_return_def] >> strip_tac >>
  rename1 `bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs))` >>
  Cases_on `bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs))`
  >- simp[dft_edit_cut_def] >>
  simp[] >> irule dft_ordinary_cut_deliver >>
  metis_tac[dft_ordinary_edit_slot_not_start]
QED

Theorem dft_ordinary_cut_invoke[local]:
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

Theorem dft_ordinary_next_at[local]:
  dft_next_inf a C (DftOpen (DftAt fn b bb s) stack n) =
  dft_fill 0 (dft_open_next a C (DftOpen (DftAt fn b bb s) stack n))
Proof
  simp[dft_next_inf_def, dft_erase_def, GSYM dft_fill_next, dft_zero_entry_def]
QED

Theorem dft_ordinary_next_done[local]:
  dft_next_inf a C (DftOpen (DftDone r) stack n) =
  dft_fill 0 (dft_open_return r stack n)
Proof
  simp[dft_next_inf_def, dft_erase_def, GSYM dft_fill_next,
    dft_zero_entry_def, dft_open_next_def]
QED

Theorem dft_ordinary_edit_cut_next:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode <> PHI /\ x.inst_opcode <> INVOKE /\
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
        simp[dft_nonphi_edit_phi_bound] >> decide_tac)
  >- (simp[dft_ordinary_next_at, dft_open_next_def] >>
      Cases_on `get_instruction b v.vs_inst_idx` >> simp[] >>
      rename1 `inst.inst_opcode` >> Cases_on `inst.inst_opcode = INVOKE` >>
      simp[dft_ordinary_cut_invoke] >>
      Cases_on `inst.inst_opcode = GAS` >> simp[dft_ordinary_cut_deliver] >>
      Cases_on `inst.inst_outputs` >> simp[] >>
      Cases_on `t` >> simp[dft_ordinary_cut_deliver]) >>
  simp[dft_ordinary_next_done, dft_ordinary_cut_return]
QED

Definition dft_ordinary_sync_def:
  dft_ordinary_sync bb0 pre x y post c d <=>
    dft_edit_safe c /\ dft_edit_cut bb0 (LENGTH pre) c /\
    d = dft_edit_occ (dft_gas_edit_fn bb0 pre x y post)
          (dft_gas_edit_block bb0 pre x y post) c
End

Theorem dft_ordinary_sync_init:
  dft_ordinary_sync bb0 pre x y post
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))
    (dft_occ_init (DftOpen
      (DftEnter (dft_gas_edit_fn bb0 pre x y post fn) 0 s) [] n))
Proof
  simp[dft_ordinary_sync_def, dft_ordinary_edit_init]
QED

Theorem dft_ordinary_sync_outside:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode <> PHI /\ y.inst_opcode <> PHI /\ x.inst_opcode <> INVOKE /\
  dft_ordinary_sync bb0 pre x y post c d /\
  ~dft_edit_before bb0 (LENGTH pre) c ==>
  dft_ordinary_sync bb0 pre x y post
    (dft_occ_oracle_next w C c)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C) d)
Proof
  simp[dft_ordinary_sync_def] >> strip_tac >>
  conj_tac >- metis_tac[dft_gas_edit_safe_next] >>
  conj_tac >- (irule dft_ordinary_edit_cut_next >> simp[]) >>
  irule dft_nonphi_edit_occ_next_outside >> simp[] >>
  fs[dft_edit_cut_def, dft_edit_before_def] >> rpt strip_tac >>
  gvs[dft_edit_safe_def, dft_edit_safe_core_def, dft_edit_control_safe_def] >>
  metis_tac[]
QED

Theorem dft_ordinary_sync_fetch:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  dft_ordinary_sync bb0 pre x y post c d /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n /\
  s.vs_inst_idx = LENGTH pre ==>
  get_instruction bb0 s.vs_inst_idx = SOME x /\
  get_instruction bb0 (SUC s.vs_inst_idx) = SOME y /\
  get_instruction (dft_gas_edit_block bb0 pre x y post bb0) s.vs_inst_idx = SOME y /\
  get_instruction (dft_gas_edit_block bb0 pre x y post bb0) (SUC s.vs_inst_idx) = SOME x /\
  d.dft_occ_core = DftOpen
    (DftAt (dft_gas_edit_fn bb0 pre x y post fn) 0
      (dft_gas_edit_block bb0 pre x y post bb0) s)
    (MAP (dft_edit_frame (dft_gas_edit_fn bb0 pre x y post)
       (dft_gas_edit_block bb0 pre x y post)) stack) n
Proof
  simp[dft_ordinary_sync_def, dft_edit_occ_def, dft_edit_core_def,
    dft_edit_control_def] >> rpt strip_tac >> simp[] >>
  metis_tac[dft_gas_edit_instruction_pair]
QED

Theorem dft_ordinary_edit_fill_frame[local]:
  dft_fill_frame 0 (dft_edit_frame fm bm fr) =
  dft_edit_frame fm bm (dft_fill_frame 0 fr)
Proof
  Cases_on `fr` >> simp[dft_fill_frame_def, dft_edit_frame_def]
QED

Theorem dft_ordinary_sync_success:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  dft_ordinary_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  dft_ordinary_sync bb0 pre x y post c d /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n /\
  s.vs_inst_idx = LENGTH pre /\
  step_inst_base x s = OK sx /\
  step_inst_base y (sx with vs_inst_idx := SUC s.vs_inst_idx) = OK sxy ==>
  dft_ordinary_sync bb0 pre x y post
    (FUNPOW (dft_occ_oracle_next w C) 2 c)
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) 2 d)
Proof
  strip_tac >> drule_all dft_ordinary_sync_fetch >> strip_tac >>
  drule_all dft_occ_ordinary_swap_ok >>
  disch_then (qspecl_then [`w`, `dft_gas_edit_ctx bb0 pre x y post C`, `C`]
    strip_assume_tac) >>
  simp[FUNPOW_2, FUNPOW, dft_ordinary_sync_def] >>
  conj_tac
  >- (fs[dft_ordinary_sync_def] >>
      metis_tac[dft_gas_edit_safe_next]) >>
  conj_tac >- simp[dft_edit_cut_def] >>
  fs[dft_ordinary_sync_def, dft_edit_occ_def, dft_edit_core_def,
    dft_edit_control_def, MAP_MAP_o, combinTheory.o_DEF,
    dft_ordinary_edit_fill_frame]
QED

Theorem dft_ordinary_id_predecessor[local]:
  !pre. ALL_DISTINCT (pre ++ [a;b] ++ post) /\
    id_before (pre ++ [a;b] ++ post) v b ==> MEM v pre \/ v = a
Proof
  Induct >> simp[id_before_cons] >> metis_tac[id_before_mem]
QED

Theorem dft_ordinary_predecessor_prefix[local]:
  ALL_DISTINCT (MAP (\i. i.inst_id) (pre ++ [x;y] ++ post)) /\
  MEM d (pre ++ [x;y] ++ post) /\
  id_before (MAP (\i. i.inst_id) (pre ++ [x;y] ++ post)) d.inst_id y.inst_id ==>
  MEM d pre \/ d = x
Proof
  strip_tac >>
  `!u v. MEM u (pre ++ [x;y] ++ post) /\ MEM v (pre ++ [x;y] ++ post) /\
    u.inst_id = v.inst_id ==> u = v` by
    metis_tac[all_distinct_map_mem_inj] >>
  `MEM d.inst_id (MAP (\i. i.inst_id) pre) \/ d.inst_id = x.inst_id` by
    (irule dft_ordinary_id_predecessor >> qexistsl_tac [`y.inst_id`, `MAP (\i. i.inst_id) post`] >>
     qpat_x_assum `!u v. _` kall_tac >> fs[MAP_APPEND])
  >- (disj1_tac >> qpat_x_assum `MEM _ (MAP _ pre)` mp_tac >>
      pure_rewrite_tac[MEM_MAP] >>
      disch_then (qx_choose_then `z` strip_assume_tac) >>
      `d = z` by (qpat_x_assum `!u v. _` irule >> simp[]) >> metis_tac[]) >>
  disj2_tac >> qpat_x_assum `!u v. _` irule >> simp[]

QED

Theorem dft_ordinary_crossed_operands:
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  bb.bb_instructions = pre ++ [x;y] ++ post /\
  dft_activation_cut fn bb s /\ s.vs_inst_idx = LENGTH pre /\
  dft_ordinary_swap_pair x y /\
  (!l. MEM (Label l) y.inst_operands ==> l IN FDOM s.vs_labels) ==>
  !op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v
Proof
  strip_tac >>
  `y.inst_opcode <> PHI` by
    (fs[dft_ordinary_swap_pair_def] >> metis_tac[is_pseudo_def]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[bb_inst_ids_distinct] >>
  `!d v. MEM d pre /\ MEM v d.inst_outputs ==> v IN FDOM s.vs_vars` by
    (fs[dft_activation_cut_def] >>
     qpat_x_assum `!d v. MEM d (TAKE _ _) /\ _ ==> _` mp_tac >>
     simp[TAKE_APPEND1]) >>
  `!v. MEM (Var v) y.inst_operands ==> v IN FDOM s.vs_vars` by
    (rpt strip_tac >> irule dft_ready_operand_defined >> simp[] >>
     qexistsl_tac [`bb`, `fn`, `y`] >>
     `strict_dom_vars_defined fn s` by fs[dft_activation_cut_def] >>
     `bb.bb_label = s.vs_current_bb` by fs[dft_activation_cut_def] >>
     `MEM y bb.bb_instructions` by simp[] >>
     asm_rewrite_tac[] >> rpt strip_tac >>
     Cases_on `MEM d pre` >- metis_tac[] >>
     `MEM d pre \/ d = x` by
       (irule dft_ordinary_predecessor_prefix >>
        qexistsl_tac [`post`, `y`] >>
        conj_tac >- (qpat_x_assum `ALL_DISTINCT _` mp_tac >> simp[]) >>
        asm_rewrite_tac[]) >>
     gvs[dft_ordinary_swap_pair_def, inst_defs_def, inst_uses_def,
       pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION,
       MEM_operand_vars_iff] >> metis_tac[]) >>
  Cases >> simp[eval_operand_def, lookup_var_def] >>
  strip_tac >> simp[finite_mapTheory.FLOOKUP_DEF]
QED

Theorem dft_ordinary_crossed_labels:
  MEM fn C.ctx_functions /\ MEM bb fn.fn_blocks /\
  bb.bb_instructions = pre ++ [x;y] ++ post /\
  dft_ordinary_swap_pair x y /\
  (!f i l. MEM f C.ctx_functions /\ MEM i (fn_insts f) /\
    MEM (Label l) i.inst_operands /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode /\ ~is_pseudo i.inst_opcode ==>
    l IN FDOM s.vs_labels) ==>
  !l. MEM (Label l) y.inst_operands ==> l IN FDOM s.vs_labels
Proof
  strip_tac >>
  `MEM y (fn_insts fn)` by
    (irule mem_fn_insts_intro >> qexists `bb` >> simp[]) >>
  fs[dft_ordinary_swap_pair_def] >> metis_tac[]
QED

Definition dft_source_control_def:
  (dft_source_control C L (DftEnter fn b s) <=>
    MEM fn C.ctx_functions /\ s.vs_labels = L) /\
  (dft_source_control C L (DftAt fn b bb s) <=>
    MEM fn C.ctx_functions /\ s.vs_labels = L) /\
  (dft_source_control C L (DftDone r) <=> T)
End

Definition dft_source_frame_def:
  dft_source_frame C L (DftCaller fn b bb inst s) <=>
    MEM fn C.ctx_functions /\ s.vs_labels = L
End

Definition dft_source_core_def:
  dft_source_core C L (DftOpen ctl stack n) <=>
    dft_source_control C L ctl /\ EVERY (dft_source_frame C L) stack
End

Definition dft_source_provenance_def:
  dft_source_provenance C L c <=> dft_source_core C L c.dft_occ_core
End

Theorem dft_source_root:
  MEM fn C.ctx_functions /\ s.vs_labels = L ==>
  dft_source_provenance C L (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))
Proof
  simp[dft_source_provenance_def, dft_occ_init_def, dft_source_core_def,
       dft_source_control_def]
QED

Theorem dft_source_frame_fill[local,simp]:
  dft_source_frame C L (dft_fill_frame b f) = dft_source_frame C L f
Proof
  Cases_on `f` >> simp[dft_source_frame_def, dft_fill_frame_def]
QED

Theorem dft_source_fill[local,simp]:
  dft_source_core C L (dft_fill b c) = dft_source_core C L c
Proof
  Cases_on `c` >> rename1 `DftOpen ctl stack n` >> Cases_on `ctl` >>
  simp[dft_fill_def, dft_fill_control_def, dft_source_core_def,
       dft_source_control_def, EVERY_MAP, combinTheory.o_DEF, SF ETA_ss]
QED

Theorem dft_source_base_labels[local]:
  step_inst_base inst s = OK t ==> t.vs_labels = s.vs_labels
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by metis_tac[step_inst_base_OK_not_INVOKE] >>
  `step_inst 0 ARB inst s = OK t` by simp[step_inst_non_invoke] >>
  metis_tac[step_inst_preserves_labels_always]
QED

Theorem dft_source_continue[local]:
  MEM fn C.ctx_functions /\ t.vs_labels = L ==>
  dft_source_control C L (dft_open_continue fn b bb inst s t)
Proof
  simp[dft_open_continue_def] >> rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[dft_source_control_def] >>
  Cases_on `t.vs_halted` >> simp[dft_source_control_def]
QED

Theorem dft_source_deliver[local]:
  MEM fn C.ctx_functions /\ EVERY (dft_source_frame C L) stack /\
  (!t. result = OK t ==> t.vs_labels = L) ==>
  dft_source_core C L (dft_open_deliver fn b bb inst s stack n result)
Proof
  Cases_on `result` >> simp[dft_open_deliver_def, dft_source_core_def,
    dft_source_control_def, dft_source_continue]
QED

Theorem dft_source_entry[local]:
  dft_source_core C L (DftOpen (DftEnter fn b s) stack n) ==>
  dft_source_core C L (dft_open_next a C (DftOpen (DftEnter fn b s) stack n))
Proof
  simp[dft_source_core_def, dft_source_control_def] >> strip_tac >>
  Cases_on `b` >> simp[dft_open_next_def, dft_source_core_def, dft_source_control_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[dft_source_core_def, dft_source_control_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  simp[dft_source_core_def, dft_source_control_def] >>
  metis_tac[eval_phis_preserves_labels]
QED

Theorem dft_source_invoke[local]:
  MEM fn C.ctx_functions /\ s.vs_labels = L /\
  EVERY (dft_source_frame C L) stack ==>
  dft_source_core C L (dft_open_invoke C fn b bb inst s stack n)
Proof
  strip_tac >> simp[dft_open_invoke_def] >>
  Cases_on `decode_invoke inst` >>
  simp[dft_source_core_def, dft_source_control_def] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `lookup_function x0 C.ctx_functions` >>
  simp[dft_source_core_def, dft_source_control_def] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  `MEM callee C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  Cases_on `eval_operands x1 s` >>
  simp[dft_source_core_def, dft_source_control_def] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >>
  simp[dft_source_core_def, dft_source_control_def, dft_source_frame_def] >>
  gvs[setup_callee_def, AllCaseEqs()]
QED

Theorem dft_source_at[local]:
  dft_source_core C L (DftOpen (DftAt fn b bb s) stack n) ==>
  dft_source_core C L (dft_open_next a C (DftOpen (DftAt fn b bb s) stack n))
Proof
  simp[dft_source_core_def, dft_source_control_def] >> strip_tac >>
  simp[dft_open_next_def] >> Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[dft_source_core_def, dft_source_control_def] >>
  rename1 `get_instruction _ _ = SOME inst` >>
  Cases_on `inst.inst_opcode = INVOKE` >- simp[dft_source_invoke] >>
  Cases_on `inst.inst_opcode = GAS`
  >- (Cases_on `inst.inst_outputs` >>
      simp[dft_source_core_def, dft_source_control_def] >>
      Cases_on `t` >> simp[dft_source_core_def, dft_source_control_def] >>
      irule dft_source_deliver >> simp[update_var_def]) >>
  simp[] >> irule dft_source_deliver >> simp[] >> rpt strip_tac >>
  metis_tac[dft_source_base_labels]
QED

Theorem dft_source_fold_labels[local]:
  !xs s. (FOLDL (\s' (out,v). update_var out v s') s xs).vs_labels = s.vs_labels
Proof
  Induct >> simp[] >> Cases_on `h` >> simp[update_var_def]
QED

Theorem dft_source_bind_labels[local]:
  bind_outputs outs vals s = SOME t ==> t.vs_labels = s.vs_labels
Proof
  simp[bind_outputs_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[dft_source_fold_labels]
QED

Theorem dft_source_return[local]:
  EVERY (dft_source_frame C L) stack ==>
  dft_source_core C L (dft_open_return result stack n)
Proof
  Cases_on `result` >> Cases_on `stack` >>
  simp[dft_open_return_def, dft_source_core_def, dft_source_control_def] >>
  Cases_on `h` >> simp[dft_source_frame_def] >> strip_tac >>
  rename1 `bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs))` >>
  Cases_on `bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs))` >>
  simp[dft_source_core_def, dft_source_control_def] >>
  irule dft_source_deliver >> simp[] >>
  drule dft_source_bind_labels >>
  simp[adopt_return_fmp_def, merge_callee_state_def] >>
  Cases_on `ret.iret_adopt_fmp` >> simp[]
QED

Theorem dft_source_open_next[local]:
  dft_source_core C L c ==> dft_source_core C L (dft_open_next a C c)
Proof
  Cases_on `c` >> rename1 `DftOpen ctl stack n` >> Cases_on `ctl`
  >- metis_tac[dft_source_entry]
  >- metis_tac[dft_source_at] >>
  simp[dft_source_core_def, dft_source_control_def, dft_open_next_def,
       dft_source_return]
QED

Theorem dft_source_step:
  dft_source_provenance C L c ==>
  dft_source_provenance C L (dft_occ_oracle_next w C c)
Proof
  simp[dft_source_provenance_def, dft_occ_oracle_next_def,
       dft_next_inf_def, dft_erase_def] >>
  metis_tac[dft_source_fill, dft_source_open_next]
QED

Theorem dft_source_run:
  !k c. dft_source_provenance C L c ==>
    dft_source_provenance C L (FUNPOW (dft_occ_oracle_next w C) k c)
Proof
  Induct >> simp[FUNPOW_SUC] >> metis_tac[dft_source_step]
QED

Theorem dft_source_active_at:
  dft_source_provenance C L c /\
  c.dft_occ_core = DftOpen (DftAt fn b bb s) stack n ==>
  MEM fn C.ctx_functions /\ s.vs_labels = L
Proof
  strip_tac >> fs[dft_source_provenance_def] >>
  gvs[dft_source_core_def, dft_source_control_def]
QED

Theorem dft_source_saved_caller:
  dft_source_provenance C L c /\
  c.dft_occ_core = DftOpen ctl stack n /\
  MEM (DftCaller fn b bb inst s) stack ==>
  MEM fn C.ctx_functions /\ s.vs_labels = L
Proof
  strip_tac >> fs[dft_source_provenance_def] >>
  gvs[dft_source_core_def, EVERY_MEM] >>
  metis_tac[dft_source_frame_def]
QED

Theorem dft_source_ready_crossed_operands:
  dft_source_provenance C L c /\ dft_runtime_ready c /\
  EVERY wf_ssa C.ctx_functions /\
  c.dft_occ_core = DftOpen (DftAt fn b bb s) stack n /\
  bb.bb_instructions = pre ++ [x;y] ++ post /\
  s.vs_inst_idx = LENGTH pre /\ dft_ordinary_swap_pair x y /\
  (!f i l. MEM f C.ctx_functions /\ MEM i (fn_insts f) /\
    MEM (Label l) i.inst_operands /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode /\ ~is_pseudo i.inst_opcode ==>
    l IN FDOM L) ==>
  !op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v
Proof
  strip_tac >>
  `MEM fn C.ctx_functions /\ s.vs_labels = L` by
    metis_tac[dft_source_active_at] >>
  `wf_ssa fn` by fs[EVERY_MEM] >>
  `wf_function fn /\ MEM bb fn.fn_blocks /\ dft_activation_cut fn bb s` by
    (fs[dft_runtime_ready_def] >>
     gvs[dft_runtime_core_ready_def, dft_runtime_control_ready_def,
         dft_runtime_fn_ok_def]) >>
  `!l. MEM (Label l) y.inst_operands ==> l IN FDOM s.vs_labels` by
    (rpt strip_tac >> irule dft_ordinary_crossed_labels >> metis_tac[]) >>
  rpt strip_tac >> irule dft_ordinary_crossed_operands >> metis_tac[]
QED

Theorem dft_source_active_enter:
  dft_source_provenance C L c /\
  c.dft_occ_core = DftOpen (DftEnter fn b s) stack n ==>
  MEM fn C.ctx_functions /\ s.vs_labels = L
Proof
  strip_tac >> fs[dft_source_provenance_def] >>
  gvs[dft_source_core_def, dft_source_control_def]
QED

(* Abort endpoints agree on the observable tag and the entry counter, not
   on the state left by a crossed instruction.  The stack has been cleared. *)
Definition dft_ordinary_stopped_def:
  dft_ordinary_stopped c d <=>
    ?a s t n.
      c.dft_occ_core = DftOpen (DftDone (Abort a s)) [] n /\
      d.dft_occ_core = DftOpen (DftDone (Abort a t)) [] n
End

Theorem dft_ordinary_sync_first_abort:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  dft_ordinary_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ~dft_must_order x y /\
  (!op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  dft_ordinary_sync bb0 pre x y post c d /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n /\
  s.vs_inst_idx = LENGTH pre /\ step_inst_base x s = Abort a t ==>
  ?j. 2 <= j /\ j <= 3 /\
    dft_ordinary_stopped
      (FUNPOW (dft_occ_oracle_next w C) 2 c)
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) j d)
Proof
  strip_tac >> drule_all dft_ordinary_sync_fetch >> strip_tac >>
  `~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
      write_effects x.inst_opcode = empty_effects)` by fs[dft_must_order_def] >>
  drule_all dft_occ_ordinary_first_abort >>
  disch_then (qspecl_then [`w`, `dft_gas_edit_ctx bb0 pre x y post C`, `C`]
    strip_assume_tac) >>
  qexists_tac `SUC j` >> simp[] >>
  simp[dft_ordinary_stopped_def] >>
  qexistsl_tac [`a`, `t`, `u`, `n`] >> conj_tac
  >- (simp[FUNPOW_2, FUNPOW] >> irule dft_occ_abort_clear >> metis_tac[]) >>
  irule dft_occ_abort_prefix_clear >> metis_tac[]
QED

Theorem dft_ordinary_sync_second_abort:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  dft_ordinary_swap_pair x y /\
  dft_ordinary_sync bb0 pre x y post c d /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n /\
  s.vs_inst_idx = LENGTH pre /\ step_inst_base x s = OK sx /\
  step_inst_base y (sx with vs_inst_idx := SUC s.vs_inst_idx) = Abort a t ==>
  dft_ordinary_stopped
    (FUNPOW (dft_occ_oracle_next w C) 3 c)
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) 2 d)
Proof
  strip_tac >> drule_all dft_ordinary_sync_fetch >> strip_tac >>
  drule_all dft_occ_ordinary_second_abort >>
  disch_then (qspecl_then [`w`, `dft_gas_edit_ctx bb0 pre x y post C`, `C`]
    strip_assume_tac) >>
  simp[dft_ordinary_stopped_def] >> qexistsl_tac [`a`, `t`, `u`, `n`] >>
  conj_tac
  >- (`3 = SUC 2` by simp[] >> once_asm_rewrite_tac[] >>
      rewrite_tac[FUNPOW_SUC] >>
      irule dft_occ_abort_clear >> metis_tac[]) >>
  simp[FUNPOW_2, FUNPOW] >> irule dft_occ_abort_clear >> metis_tac[]
QED

Theorem dft_ordinary_stopped_next:
  dft_ordinary_stopped c d ==>
  dft_ordinary_stopped (dft_occ_oracle_next w C c)
    (dft_occ_oracle_next w C' d)
Proof
  simp[dft_ordinary_stopped_def] >> strip_tac >>
  qexistsl_tac [`a`, `s`, `t`, `n`] >>
  metis_tac[dft_occ_abort_clear]
QED

Theorem dft_ordinary_abort_no_observe:
  c.dft_occ_core = DftOpen (DftDone (Abort a t)) stack n ==>
  !h f i s. ~dft_open_observe f i s
    (FUNPOW (dft_occ_oracle_next w C) h c).dft_occ_core
Proof
  strip_tac >>
  `!k. ?st. (FUNPOW (dft_occ_oracle_next w C) k c).dft_occ_core =
     DftOpen (DftDone (Abort a t)) st n` by
    (Induct >- (simp[FUNPOW] >> metis_tac[]) >>
     rewrite_tac[FUNPOW_SUC] >> metis_tac[dft_occ_abort_clear]) >>
  rpt gen_tac >> first_x_assum (qspec_then `h` strip_assume_tac) >>
  simp[dft_open_observe_def]
QED

Definition dft_ordinary_prefix_cover_def:
  dft_ordinary_prefix_cover fm w C C' c d k j <=>
    !h f i t. h < j /\
      dft_open_observe f i t
        (FUNPOW (dft_occ_oracle_next w C') h d).dft_occ_core /\
      inst_mem_ranges i t <> [] ==>
      ?l g s. l < k /\ f = fm g /\
        dft_open_observe g i s
          (FUNPOW (dft_occ_oracle_next w C) l c).dft_occ_core /\
        (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) /\
        inst_mem_ranges i s = inst_mem_ranges i t /\ s.vs_memory = t.vs_memory
End

Theorem dft_ordinary_sync_first_abort_cover:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  dft_ordinary_swap_pair x y /\ inst_wf x /\ ~dft_must_order x y /\
  dft_ordinary_sync bb0 pre x y post c d /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n /\
  s.vs_inst_idx = LENGTH pre /\ step_inst_base x s = Abort a t ==>
  dft_ordinary_prefix_cover (dft_gas_edit_fn bb0 pre x y post) w C
    (dft_gas_edit_ctx bb0 pre x y post C) c d 2 2
Proof
  strip_tac >> drule_all dft_ordinary_sync_fetch >> strip_tac >>
  simp[dft_ordinary_prefix_cover_def] >> rpt strip_tac >>
  drule_all dft_occ_ordinary_first_abort_observe >> strip_tac >>
  qexistsl_tac [`0`, `fn`, `s`] >> simp[FUNPOW] >> metis_tac[]
QED

Theorem dft_ordinary_sync_second_abort_cover:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  dft_ordinary_swap_pair x y /\
  dft_ordinary_sync bb0 pre x y post c d /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n /\
  s.vs_inst_idx = LENGTH pre /\ step_inst_base x s = OK sx ==>
  dft_ordinary_prefix_cover (dft_gas_edit_fn bb0 pre x y post) w C
    (dft_gas_edit_ctx bb0 pre x y post C) c d 3 1
Proof
  strip_tac >> drule_all dft_ordinary_sync_fetch >> strip_tac >>
  simp[dft_ordinary_prefix_cover_def] >> rpt strip_tac >>
  `dft_open_observe f i t d.dft_occ_core` by metis_tac[] >>
  drule_all dft_occ_ordinary_second_abort_observe >>
  disch_then (qspecl_then [`w`, `C`] strip_assume_tac) >>
  qexistsl_tac [`1`, `fn`, `sx with vs_inst_idx := SUC s.vs_inst_idx`] >>
  simp[FUNPOW] >> metis_tac[]
QED

Theorem dft_ordinary_prefix_cover_abort_pad:
  dft_ordinary_prefix_cover fm w C C' c d k b /\ j <= b /\
  (FUNPOW (dft_occ_oracle_next w C') j d).dft_occ_core =
    DftOpen (DftDone (Abort a t)) stack n ==>
  dft_ordinary_prefix_cover fm w C C' c d k (SUC j)
Proof
  pure_rewrite_tac[dft_ordinary_prefix_cover_def] >> rpt strip_tac >>
  Cases_on `h < b` >- metis_tac[] >>
  `h = j` by decide_tac >> gvs[dft_open_observe_def]
QED

Theorem dft_ordinary_sync_success_cover:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  dft_ordinary_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  dft_ordinary_sync bb0 pre x y post c d /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n /\
  s.vs_inst_idx = LENGTH pre /\ step_inst_base x s = OK sx /\
  step_inst_base y (sx with vs_inst_idx := SUC s.vs_inst_idx) = OK sxy ==>
  dft_ordinary_prefix_cover (dft_gas_edit_fn bb0 pre x y post) w C
    (dft_gas_edit_ctx bb0 pre x y post C) c d 2 2
Proof
  strip_tac >> drule_all dft_ordinary_sync_fetch >> strip_tac >>
  drule_all dft_occ_ordinary_observe_source_prefix >>
  disch_then (qspecl_then [`w`, `dft_gas_edit_ctx bb0 pre x y post C`, `C`]
    strip_assume_tac) >>
  pure_rewrite_tac[dft_ordinary_prefix_cover_def] >> rpt strip_tac >>
  `h = 0 \/ h = 1` by decide_tac
  >- (gvs[FUNPOW, dft_open_observe_def] >>
      qexistsl_tac [`1`, `fn`, `sx with vs_inst_idx := SUC s.vs_inst_idx`] >>
      simp[FUNPOW] >> metis_tac[]) >>
  gvs[FUNPOW] >>
  `f = dft_gas_edit_fn bb0 pre x y post fn /\ i = x /\ t = sy` by
    (gvs[dft_open_observe_def]) >>
  gvs[] >> qexistsl_tac [`0`, `fn`, `s`] >>
  simp[FUNPOW, dft_open_observe_def] >> metis_tac[]
QED

Theorem dft_ordinary_sync_outside_observe:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  dft_ordinary_sync bb0 pre x y post c d /\
  ~dft_edit_before bb0 (LENGTH pre) c /\
  dft_open_observe f i t d.dft_occ_core ==>
  ?g. f = dft_gas_edit_fn bb0 pre x y post g /\
    dft_open_observe g i t c.dft_occ_core
Proof
  simp[dft_ordinary_sync_def] >> strip_tac >>
  Cases_on `c.dft_occ_core` >> rename1 `c.dft_occ_core = DftOpen ctl stack n` >>
  Cases_on `ctl` >>
  gvs[dft_edit_occ_def, dft_edit_core_def, dft_edit_control_def,
      dft_open_observe_def] >>
  rename1 `get_instruction (dft_gas_edit_block bb0 pre x y post bb) t.vs_inst_idx = SOME i` >>
  `bb <> bb0 \/ (t.vs_inst_idx <> LENGTH pre /\
                  t.vs_inst_idx <> SUC (LENGTH pre))` by
    (fs[dft_edit_safe_def, dft_edit_safe_core_def, dft_edit_control_safe_def,
        dft_edit_cut_def, dft_edit_before_def] >> metis_tac[]) >>
  metis_tac[dft_gas_edit_instruction_outside]
QED

Theorem dft_ordinary_sync_outside_cover:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  dft_ordinary_sync bb0 pre x y post c d /\
  ~dft_edit_before bb0 (LENGTH pre) c ==>
  dft_ordinary_prefix_cover (dft_gas_edit_fn bb0 pre x y post) w C
    (dft_gas_edit_ctx bb0 pre x y post C) c d 1 1
Proof
  strip_tac >> simp[dft_ordinary_prefix_cover_def] >> rpt strip_tac >>
  `dft_open_observe f i t d.dft_occ_core` by metis_tac[] >>
  drule_all dft_ordinary_sync_outside_observe >> strip_tac >>
  qexistsl_tac [`g`, `t`] >> simp[FUNPOW]
QED

Definition dft_ordinary_no_error_def:
  dft_ordinary_no_error w C c <=>
    !h e stack n. (FUNPOW (dft_occ_oracle_next w C) h c).dft_occ_core <>
      DftOpen (DftDone (Error e)) stack n
End

Theorem dft_ordinary_no_error_shift:
  dft_ordinary_no_error w C c ==>
  dft_ordinary_no_error w C (FUNPOW (dft_occ_oracle_next w C) k c)
Proof
  simp[dft_ordinary_no_error_def, GSYM FUNPOW_ADD] >> metis_tac[]
QED

Theorem dft_occ_ordinary_error:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  step_inst_base inst s = Error e ==>
  (dft_occ_oracle_next w C c).dft_occ_core =
    DftOpen (DftDone (Error e)) (MAP (dft_fill_frame 0) stack) n
Proof
  strip_tac >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_deliver_def, dft_erase_def] >>
  `!f. dft_fill_frame 0 (dft_fill_frame 1 f) = dft_fill_frame 0 f` by
    (Cases >> simp[dft_fill_frame_def]) >>
  simp[MAP_MAP_o, combinTheory.o_DEF] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC
QED

Theorem dft_ordinary_no_error_step:
  dft_ordinary_no_error w C c /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE ==>
  !e. step_inst_base inst s <> Error e
Proof
  rpt strip_tac >> drule_all dft_occ_ordinary_error >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  fs[dft_ordinary_no_error_def] >>
  first_x_assum (qspec_then `1` mp_tac) >> simp[FUNPOW] >> metis_tac[]
QED

Theorem dft_ordinary_first_abort_segment:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  dft_ordinary_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ~dft_must_order x y /\
  (!op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  dft_ordinary_sync bb0 pre x y post c d /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n /\
  s.vs_inst_idx = LENGTH pre /\ step_inst_base x s = Abort a t ==>
  ?j. 2 <= j /\ j <= 3 /\
    dft_ordinary_stopped
      (FUNPOW (dft_occ_oracle_next w C) 2 c)
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) j d) /\
    dft_ordinary_prefix_cover (dft_gas_edit_fn bb0 pre x y post) w C
      (dft_gas_edit_ctx bb0 pre x y post C) c d 2 j
Proof
  strip_tac >> drule_all dft_ordinary_sync_first_abort_cover >> strip_tac >>
  drule_all dft_ordinary_sync_fetch >> strip_tac >>
  `~(x.inst_outputs = [] /\ read_effects x.inst_opcode = empty_effects /\
      write_effects x.inst_opcode = empty_effects)` by fs[dft_must_order_def] >>
  drule_all dft_occ_ordinary_first_abort >>
  disch_then (qspecl_then [`w`, `dft_gas_edit_ctx bb0 pre x y post C`, `C`]
    strip_assume_tac) >>
  qexists_tac `SUC j` >> simp[] >> conj_tac
  >- (simp[dft_ordinary_stopped_def] >>
      qexistsl_tac [`a`, `t`, `u`, `n`] >> conj_tac
      >- (simp[FUNPOW_2, FUNPOW] >> irule dft_occ_abort_clear >> metis_tac[]) >>
      irule dft_occ_abort_prefix_clear >> metis_tac[]) >>
  irule dft_ordinary_prefix_cover_abort_pad >> metis_tac[]
QED

Theorem dft_ordinary_second_abort_segment:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  dft_ordinary_swap_pair x y /\
  dft_ordinary_sync bb0 pre x y post c d /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n /\
  s.vs_inst_idx = LENGTH pre /\ step_inst_base x s = OK sx /\
  step_inst_base y (sx with vs_inst_idx := SUC s.vs_inst_idx) = Abort a t ==>
  dft_ordinary_stopped
    (FUNPOW (dft_occ_oracle_next w C) 3 c)
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) 2 d) /\
  dft_ordinary_prefix_cover (dft_gas_edit_fn bb0 pre x y post) w C
    (dft_gas_edit_ctx bb0 pre x y post C) c d 3 2
Proof
  strip_tac >> conj_tac >- (irule dft_ordinary_sync_second_abort >> metis_tac[]) >>
  drule_all dft_ordinary_sync_second_abort_cover >> strip_tac >>
  drule_all dft_ordinary_sync_fetch >> strip_tac >>
  drule_all dft_occ_ordinary_second_abort >>
  disch_then (qspecl_then [`w`, `dft_gas_edit_ctx bb0 pre x y post C`, `C`]
    strip_assume_tac) >>
  `2 = SUC 1` by simp[] >> once_asm_rewrite_tac[] >>
  irule dft_ordinary_prefix_cover_abort_pad >>
  conj_tac >- (simp[FUNPOW] >> metis_tac[]) >>
  qexists_tac `1` >> simp[]
QED

Theorem dft_ordinary_result_cases:
  ~is_terminator inst.inst_opcode /\
  (!e. step_inst_base inst s <> Error e) ==>
  (?t. step_inst_base inst s = OK t) \/
  (?a t. step_inst_base inst s = Abort a t)
Proof
  strip_tac >> Cases_on `step_inst_base inst s` >> gvs[]
  >- metis_tac[dft_ordinary_no_halt] >>
  drule step_inst_base_intret_opcodes >> strip_tac >> gvs[is_terminator_def]
QED

Theorem dft_ordinary_sync_pair_segment:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  dft_ordinary_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ~dft_must_order x y /\ dft_ordinary_no_error w C c /\
  (!op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  dft_ordinary_sync bb0 pre x y post c d /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n /\
  s.vs_inst_idx = LENGTH pre ==>
  ?k j. 0 < k /\ k <= 3 /\ 0 < j /\ j <= 3 /\
    (dft_ordinary_sync bb0 pre x y post
       (FUNPOW (dft_occ_oracle_next w C) k c)
       (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) j d) \/
     dft_ordinary_stopped
       (FUNPOW (dft_occ_oracle_next w C) k c)
       (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) j d)) /\
    dft_ordinary_prefix_cover (dft_gas_edit_fn bb0 pre x y post) w C
      (dft_gas_edit_ctx bb0 pre x y post C) c d k j
Proof
  strip_tac >> drule_all dft_ordinary_sync_fetch >> strip_tac >>
  `x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE /\
   ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
   y.inst_opcode <> GAS /\ y.inst_opcode <> INVOKE` by
    fs[dft_ordinary_swap_pair_def] >>
  `(!e. step_inst_base x s <> Error e)` by
    (irule dft_ordinary_no_error_step >> metis_tac[]) >>
  drule_all dft_ordinary_result_cases >> strip_tac
  >- (rename1 `step_inst_base x s = OK sx` >>
      `dft_ordinary_no_error w C (dft_occ_oracle_next w C c)` by
        (drule dft_ordinary_no_error_shift >>
         disch_then (qspec_then `1` mp_tac) >> simp[FUNPOW]) >>
      drule_all dft_occ_ordinary_next >>
      disch_then (qspecl_then [`w`, `C`] assume_tac) >>
      `(dft_occ_oracle_next w C c).dft_occ_core = DftOpen
         (DftAt fn 0 bb0 (sx with vs_inst_idx := SUC s.vs_inst_idx))
         (MAP (dft_fill_frame 0) stack) n` by simp[] >>
      `!e. step_inst_base y (sx with vs_inst_idx := SUC s.vs_inst_idx) <> Error e` by
        (irule dft_ordinary_no_error_step >> simp[] >> metis_tac[]) >>
      drule_all dft_ordinary_result_cases >> strip_tac
      >- (qexistsl_tac [`2`, `2`] >> simp[] >> conj_tac
          >- (disj1_tac >> irule dft_ordinary_sync_success >> metis_tac[]) >>
          irule dft_ordinary_sync_success_cover >> metis_tac[]) >>
      qexistsl_tac [`3`, `2`] >> simp[] >>
      drule_all dft_ordinary_second_abort_segment >> strip_tac >> simp[]) >>
  drule_all dft_ordinary_first_abort_segment >>
  disch_then (qspecl_then [`w`, `C`] strip_assume_tac) >>
  qexistsl_tac [`2`, `j`] >> simp[]
QED

Theorem dft_ordinary_sync_segment:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  dft_ordinary_swap_pair x y /\ ~dft_must_order x y /\
  dft_ordinary_no_error w C c /\ dft_runtime_ready c /\
  dft_source_provenance C L c /\ EVERY wf_ssa C.ctx_functions /\
  (!f i l. MEM f C.ctx_functions /\ MEM i (fn_insts f) /\
    MEM (Label l) i.inst_operands /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode /\ ~is_pseudo i.inst_opcode ==>
    l IN FDOM L) /\
  dft_ordinary_sync bb0 pre x y post c d ==>
  ?k j. 0 < k /\ k <= 3 /\ 0 < j /\ j <= 3 /\
    (dft_ordinary_sync bb0 pre x y post
       (FUNPOW (dft_occ_oracle_next w C) k c)
       (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) j d) \/
     dft_ordinary_stopped
       (FUNPOW (dft_occ_oracle_next w C) k c)
       (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) j d)) /\
    dft_ordinary_prefix_cover (dft_gas_edit_fn bb0 pre x y post) w C
      (dft_gas_edit_ctx bb0 pre x y post C) c d k j
Proof
  strip_tac >> Cases_on `dft_edit_before bb0 (LENGTH pre) c`
  >- (fs[dft_edit_before_def] >>
      `inst_wf x /\ inst_wf y` by
        (fs[dft_runtime_ready_def, dft_runtime_core_ready_def,
            dft_runtime_control_ready_def, dft_runtime_fn_ok_def, EVERY_MEM] >>
         metis_tac[MEM_APPEND, MEM]) >>
      `!op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v` by
        (rpt strip_tac >> irule dft_source_ready_crossed_operands >> metis_tac[]) >>
      irule dft_ordinary_sync_pair_segment >> metis_tac[]) >>
  qexistsl_tac [`1`, `1`] >> simp[FUNPOW] >> conj_tac
  >- (disj1_tac >> irule dft_ordinary_sync_outside >>
      fs[dft_ordinary_swap_pair_def] >> metis_tac[is_pseudo_def]) >>
  irule dft_ordinary_sync_outside_cover >> metis_tac[]
QED

Definition dft_ordinary_endpoint_def:
  dft_ordinary_endpoint bb0 pre x y post c d <=>
    dft_ordinary_sync bb0 pre x y post c d \/ dft_ordinary_stopped c d
End

Theorem dft_ordinary_stopped_cover:
  dft_ordinary_stopped c d ==>
  dft_ordinary_prefix_cover fm w C C' c d 1 1
Proof
  simp[dft_ordinary_stopped_def, dft_ordinary_prefix_cover_def,
       dft_open_observe_def] >> rpt strip_tac >> gvs[]
QED

Theorem dft_ordinary_endpoint_segment:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  dft_ordinary_swap_pair x y /\ ~dft_must_order x y /\
  dft_ordinary_no_error w C c /\ dft_runtime_ready c /\
  dft_source_provenance C L c /\ EVERY wf_ssa C.ctx_functions /\
  (!f i l. MEM f C.ctx_functions /\ MEM i (fn_insts f) /\
    MEM (Label l) i.inst_operands /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode /\ ~is_pseudo i.inst_opcode ==>
    l IN FDOM L) /\
  dft_ordinary_endpoint bb0 pre x y post c d ==>
  ?k j. 0 < k /\ k <= 3 /\ 0 < j /\ j <= 3 /\
    dft_ordinary_endpoint bb0 pre x y post
       (FUNPOW (dft_occ_oracle_next w C) k c)
       (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) j d) /\
    dft_ordinary_prefix_cover (dft_gas_edit_fn bb0 pre x y post) w C
      (dft_gas_edit_ctx bb0 pre x y post C) c d k j
Proof
  simp[dft_ordinary_endpoint_def] >> strip_tac
  >- (drule_all dft_ordinary_sync_segment >> metis_tac[]) >>
  qexistsl_tac [`1`, `1`] >> simp[FUNPOW] >> conj_tac
  >- (disj2_tac >> irule dft_ordinary_stopped_next >> simp[]) >>
  irule dft_ordinary_stopped_cover >> simp[]
QED

Theorem dft_ordinary_prefix_cover_shift:
  dft_ordinary_prefix_cover fm w C C' c d k j /\ h < j /\
  dft_open_observe f i t (FUNPOW (dft_occ_oracle_next w C') h d).dft_occ_core /\
  inst_mem_ranges i t <> [] ==>
  ?l g s. l < k /\ f = fm g /\
    dft_open_observe g i s (FUNPOW (dft_occ_oracle_next w C) l c).dft_occ_core /\
    (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) /\
    inst_mem_ranges i s = inst_mem_ranges i t /\ s.vs_memory = t.vs_memory
Proof
  simp[dft_ordinary_prefix_cover_def] >> metis_tac[]
QED

Definition dft_ordinary_environment_def:
  dft_ordinary_environment bb0 pre x y post C L <=>
    bb0.bb_instructions = pre ++ [x;y] ++ post /\
    dft_ordinary_swap_pair x y /\ ~dft_must_order x y /\
    EVERY wf_ssa C.ctx_functions /\ EVERY dft_runtime_fn_ok C.ctx_functions /\
    (!f i l. MEM f C.ctx_functions /\ MEM i (fn_insts f) /\
      MEM (Label l) i.inst_operands /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode /\ ~is_pseudo i.inst_opcode ==> l IN FDOM L)
End

Definition dft_ordinary_live_def:
  dft_ordinary_live w C L c <=>
    dft_ordinary_no_error w C c /\ dft_runtime_ready c /\
    dft_source_provenance C L c
End

Theorem dft_ordinary_live_shift:
  EVERY dft_runtime_fn_ok C.ctx_functions /\ dft_ordinary_live w C L c ==>
  dft_ordinary_live w C L (FUNPOW (dft_occ_oracle_next w C) k c)
Proof
  simp[dft_ordinary_live_def] >> strip_tac >>
  metis_tac[dft_ordinary_no_error_shift, dft_runtime_iter, dft_source_run]
QED

Theorem dft_ordinary_live_segment:
  dft_ordinary_environment bb0 pre x y post C L /\
  dft_ordinary_live w C L c /\ dft_ordinary_endpoint bb0 pre x y post c d ==>
  ?k j. 0 < k /\ k <= 3 /\ 0 < j /\ j <= 3 /\
    dft_ordinary_endpoint bb0 pre x y post
       (FUNPOW (dft_occ_oracle_next w C) k c)
       (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) j d) /\
    dft_ordinary_live w C L (FUNPOW (dft_occ_oracle_next w C) k c) /\
    dft_ordinary_prefix_cover (dft_gas_edit_fn bb0 pre x y post) w C
      (dft_gas_edit_ctx bb0 pre x y post C) c d k j
Proof
  strip_tac >>
  `EVERY dft_runtime_fn_ok C.ctx_functions` by fs[dft_ordinary_environment_def] >>
  `?k j. 0 < k /\ k <= 3 /\ 0 < j /\ j <= 3 /\
    dft_ordinary_endpoint bb0 pre x y post
       (FUNPOW (dft_occ_oracle_next w C) k c)
       (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) j d) /\
    dft_ordinary_prefix_cover (dft_gas_edit_fn bb0 pre x y post) w C
      (dft_gas_edit_ctx bb0 pre x y post C) c d k j` by
    (irule dft_ordinary_endpoint_segment >>
     fs[dft_ordinary_environment_def, dft_ordinary_live_def] >> metis_tac[]) >>
  qexistsl_tac [`k`, `j`] >> simp[] >> irule dft_ordinary_live_shift >> simp[]
QED

Theorem dft_ordinary_orbit_observe:
  !h c d f i t.
  dft_ordinary_environment bb0 pre x y post C L /\
  dft_ordinary_live w C L c /\ dft_ordinary_endpoint bb0 pre x y post c d /\
  dft_open_observe f i t
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) h d).dft_occ_core /\
  inst_mem_ranges i t <> [] ==>
  ?l g s. f = dft_gas_edit_fn bb0 pre x y post g /\
    dft_open_observe g i s (FUNPOW (dft_occ_oracle_next w C) l c).dft_occ_core /\
    (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) /\
    inst_mem_ranges i s = inst_mem_ranges i t /\ s.vs_memory = t.vs_memory
Proof
  completeInduct_on `h` >> rpt strip_tac >>
  drule_all dft_ordinary_live_segment >> strip_tac >>
  Cases_on `h < j`
  >- (drule_all dft_ordinary_prefix_cover_shift >> metis_tac[]) >>
  `h - j < h /\ h = (h - j) + j` by decide_tac >>
  first_x_assum (qspec_then `h - j` mp_tac) >> simp[] >>
  disch_then (qspecl_then
    [`FUNPOW (dft_occ_oracle_next w C) k c`,
     `FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) j d`,
     `f`, `i`, `t`] mp_tac) >>
  simp[GSYM FUNPOW_ADD] >> strip_tac >>
  qexistsl_tac [`k + l`, `g`, `s`] >> simp[]
QED

Theorem dft_ordinary_orbit_cofinal:
  !m c d.
  dft_ordinary_environment bb0 pre x y post C L /\
  dft_ordinary_live w C L c /\ dft_ordinary_endpoint bb0 pre x y post c d ==>
  ?p q. m <= p /\ m <= q /\
    dft_ordinary_endpoint bb0 pre x y post
      (FUNPOW (dft_occ_oracle_next w C) p c)
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) q d) /\
    dft_ordinary_live w C L (FUNPOW (dft_occ_oracle_next w C) p c)
Proof
  Induct
  >- (rpt strip_tac >> qexistsl_tac [`0`, `0`] >> simp[FUNPOW]) >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  drule_all dft_ordinary_live_segment >> strip_tac >>
  qexistsl_tac [`p + k`, `q + j`] >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >>
  gvs[GSYM FUNPOW_ADD, ADD_COMM]
QED

Definition dft_ordinary_result_rel_def:
  dft_ordinary_result_rel r r' <=>
    r = r' \/ ?a s t. r = Abort a s /\ r' = Abort a t
End

Theorem dft_ordinary_endpoint_root:
  dft_ordinary_endpoint bb0 pre x y post c d /\
  c.dft_occ_core = DftOpen (DftDone r) [] n ==>
  ?r' n'. d.dft_occ_core = DftOpen (DftDone r') [] n' /\
    dft_ordinary_result_rel r r'
Proof
  simp[dft_ordinary_endpoint_def] >> strip_tac
  >- (fs[dft_ordinary_sync_def] >>
      simp[dft_edit_occ_def, dft_edit_core_def, dft_edit_control_def] >>
      metis_tac[dft_ordinary_result_rel_def]) >>
  fs[dft_ordinary_stopped_def] >> gvs[] >>
  metis_tac[dft_ordinary_result_rel_def]
QED

Theorem dft_ordinary_orbit_terminal:
  dft_ordinary_environment bb0 pre x y post C L /\
  dft_ordinary_live w C L c /\ dft_ordinary_endpoint bb0 pre x y post c d /\
  (FUNPOW (dft_occ_oracle_next w C) h c).dft_occ_core =
    DftOpen (DftDone r) [] n ==>
  ?q r' n'.
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) q d).dft_occ_core =
      DftOpen (DftDone r') [] n' /\ dft_ordinary_result_rel r r'
Proof
  strip_tac >> drule_all dft_ordinary_orbit_cofinal >>
  disch_then (qspec_then `h` strip_assume_tac) >>
  `?delta. p = delta + h` by (qexists_tac `p - h` >> decide_tac) >>
  `?n. (FUNPOW (dft_occ_oracle_next w C) p c).dft_occ_core =
     DftOpen (DftDone r) [] n` by
    (gvs[FUNPOW_ADD] >> irule dft_occ_oracle_root_absorb >> metis_tac[]) >>
  drule_all dft_ordinary_endpoint_root >> metis_tac[]
QED

Theorem dft_ordinary_root_init:
  dft_ordinary_environment bb0 pre x y post C s.vs_labels /\
  MEM fn C.ctx_functions /\ fn_reachable fn s.vs_current_bb /\
  strict_dom_vars_defined fn s /\
  dft_ordinary_no_error w C (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n)) ==>
  dft_ordinary_live w C s.vs_labels
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n)) /\
  dft_ordinary_endpoint bb0 pre x y post
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))
    (dft_occ_init (DftOpen
      (DftEnter (dft_gas_edit_fn bb0 pre x y post fn) 0 s) [] n))
Proof
  strip_tac >>
  `dft_runtime_fn_ok fn` by fs[dft_ordinary_environment_def, EVERY_MEM] >>
  conj_tac
  >- (simp[dft_ordinary_live_def] >> conj_tac
      >- (irule dft_runtime_root >> simp[]) >>
      irule dft_source_root >> simp[]) >>
  simp[dft_ordinary_endpoint_def, dft_ordinary_sync_init]
QED
