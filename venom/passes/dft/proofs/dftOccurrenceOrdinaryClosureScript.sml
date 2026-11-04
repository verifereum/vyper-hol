Theory dftOccurrenceOrdinaryClosure
Ancestors
  dftOccurrenceOrdinaryEdit dftOccurrenceOrdinaryObserve dftOccurrenceOrdinaryStop
  dftOccurrenceGasEdit dftOccurrenceEditRuntime dftOccurrenceRuntime
  dftOccurrenceReplay dftOccurrenceMachine dftOpenErase dftOpenMachine dftOpenFuel
  venomExecSemantics venomInst dftAvailability dftOccurrenceAvailability
  dftScheduleOrder dftCorrectness dftOrdinarySwap venomWf venomState sccpCorrectnessProofs finite_map
  list arithmetic allocaRemapSSA

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
