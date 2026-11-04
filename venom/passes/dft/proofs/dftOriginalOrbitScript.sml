Theory dftOriginalOrbit
Ancestors
  dftOriginalSegment dftOriginalRuntime dftOccurrenceOrdinaryClosure
  dftOriginalScheduleRuntime dftProtectedRuntime dftOccurrenceGasEdit
  dftOrdinarySwap dftScheduleEdits dftOccurrenceCallTrace venomInst list sorting arithmetic

(* A crossed nonpseudo instruction lies after the fixed pseudo prefix. *)
Theorem dft_original_prefix_split[local]:
  !pp pre body. EVERY P pp /\ pp ++ body = pre ++ x::rest /\ ~P x ==>
    ?done. pre = pp ++ done
Proof
  Induct
  >- (simp[] >> metis_tac[]) >>
  rpt gen_tac >> Cases_on `pre`
  >- (simp[] >> metis_tac[]) >>
  simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`t`, `body'`] mp_tac) >>
  simp[APPEND_ASSOC]
QED

Theorem dft_original_crossing_cut:
  dft_original_block f b q /\ dft_original_cut f b q s /\
  q.bb_instructions = pre ++ [x;y] ++ post /\
  s.vs_inst_idx = LENGTH pre /\ ~is_pseudo x.inst_opcode ==>
  ?done. pre = FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions ++ done
Proof
  strip_tac >>
  fs[dft_original_cut_def, dft_original_schedule_def] >>
  irule dft_original_prefix_split >>
  qexistsl_tac [`\i. is_pseudo i.inst_opcode`, `body'`, `y::post`, `x`] >>
  simp[EVERY_FILTER, APPEND_ASSOC]
QED

Definition dft_original_ordinary_environment_def:
  dft_original_ordinary_environment Corig C L q pre x y post <=>
    dft_original_context Corig C /\
    q.bb_instructions = pre ++ [x;y] ++ post /\
    dft_ordinary_swap_pair x y /\ ~dft_must_order x y /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
    x.inst_opcode <> ALLOCA /\ y.inst_opcode <> ALLOCA /\
    ~MEM x.inst_opcode [DELEGATECALL; CREATE; CREATE2] /\
    ~MEM y.inst_opcode [DELEGATECALL; CREATE; CREATE2] /\
    (!f b. dft_original_block f b q ==>
      schedule_edges b.bb_instructions dft_must_order (pre ++ [y;x] ++ post)) /\
    (!fn i l. MEM fn C.ctx_functions /\ MEM i (fn_insts fn) /\
      MEM (Label l) i.inst_operands /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode /\ ~is_pseudo i.inst_opcode ==> l IN FDOM L)
End

Theorem dft_original_sync_segment:
  dft_original_ordinary_environment Corig C L q pre x y post /\
  dft_original_label_ready C L c /\ dft_ordinary_sync q pre x y post c d ==>
  ?k j. 0 < k /\ k <= 3 /\ 0 < j /\ j <= 3 /\
    dft_ordinary_endpoint q pre x y post
      (FUNPOW (dft_occ_oracle_next w C) k c)
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) j d) /\
    dft_ordinary_prefix_cover (dft_gas_edit_fn q pre x y post) w C
      (dft_gas_edit_ctx q pre x y post C) c d k j
Proof
  strip_tac >> Cases_on `dft_edit_before q (LENGTH pre) c`
  >- (fs[dft_edit_before_def] >>
      `?f b. dft_original_block f b q /\ dft_original_cut f b q s` by
        (fs[dft_original_label_ready_def] >>
         drule_all dft_original_runtime_at_projection >> metis_tac[]) >>
      `?done. pre = FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions ++ done` by
        (irule dft_original_crossing_cut >>
         fs[dft_original_ordinary_environment_def] >> metis_tac[]) >>
      `MEM x b.bb_instructions /\ MEM y b.bb_instructions` by
        (drule dft_original_block_mem >>
         fs[dft_original_ordinary_environment_def] >>
         metis_tac[MEM_APPEND, MEM]) >>
      `inst_wf x /\ inst_wf y` by
        (fs[dft_original_block_def, dft_original_schedule_def, EVERY_MEM] >>
         metis_tac[]) >>
      `?k j. 0 < k /\ k <= 3 /\ 0 < j /\ j <= 3 /\
        (dft_ordinary_sync q pre x y post
          (FUNPOW (dft_occ_oracle_next w C) k c)
          (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) j d) \/
         dft_ordinary_stopped
          (FUNPOW (dft_occ_oracle_next w C) k c)
          (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) j d)) /\
        dft_ordinary_prefix_cover (dft_gas_edit_fn q pre x y post) w C
          (dft_gas_edit_ctx q pre x y post C) c d k j` by
        (gvs[] >> irule dft_original_sync_pair_segment >>
         fs[dft_original_ordinary_environment_def] >> metis_tac[]) >>
      metis_tac[dft_ordinary_endpoint_def]) >>
  qexistsl_tac [`1`, `1`] >> simp[FUNPOW] >> conj_tac
  >- (simp[dft_ordinary_endpoint_def] >> disj1_tac >>
      irule dft_ordinary_sync_outside >>
      fs[dft_original_ordinary_environment_def, dft_ordinary_swap_pair_def] >>
      metis_tac[is_pseudo_def]) >>
  irule dft_ordinary_sync_outside_cover >>
  fs[dft_original_ordinary_environment_def]
QED

Theorem dft_original_endpoint_segment:
  dft_original_ordinary_environment Corig C L q pre x y post /\
  dft_original_label_ready C L c /\ dft_ordinary_endpoint q pre x y post c d ==>
  ?k j. 0 < k /\ k <= 3 /\ 0 < j /\ j <= 3 /\
    dft_ordinary_endpoint q pre x y post
      (FUNPOW (dft_occ_oracle_next w C) k c)
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) j d) /\
    dft_original_label_ready C L (FUNPOW (dft_occ_oracle_next w C) k c) /\
    dft_ordinary_prefix_cover (dft_gas_edit_fn q pre x y post) w C
      (dft_gas_edit_ctx q pre x y post C) c d k j
Proof
  strip_tac >>
  `dft_original_context Corig C` by fs[dft_original_ordinary_environment_def] >>
  `!k. dft_original_label_ready C L (FUNPOW (dft_occ_oracle_next w C) k c)` by
    metis_tac[dft_original_label_iter] >>
  fs[dft_ordinary_endpoint_def]
  >- (drule_all dft_original_sync_segment >>
      metis_tac[dft_ordinary_endpoint_def]) >>
  qexistsl_tac [`1`, `1`] >> simp[FUNPOW] >> conj_tac
  >- (disj2_tac >> irule dft_ordinary_stopped_next >> simp[]) >>
  irule dft_ordinary_stopped_cover >> simp[]
QED

Theorem dft_original_orbit_observe:
  !h c d f i t.
  dft_original_ordinary_environment Corig C L q pre x y post /\
  dft_original_label_ready C L c /\ dft_ordinary_endpoint q pre x y post c d /\
  dft_open_observe f i t
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) h d).dft_occ_core /\
  inst_mem_ranges i t <> [] ==>
  ?l g s. f = dft_gas_edit_fn q pre x y post g /\
    dft_open_observe g i s (FUNPOW (dft_occ_oracle_next w C) l c).dft_occ_core /\
    (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) /\
    inst_mem_ranges i s = inst_mem_ranges i t /\ s.vs_memory = t.vs_memory
Proof
  completeInduct_on `h` >> rpt strip_tac >>
  drule_all dft_original_endpoint_segment >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  Cases_on `h < j`
  >- (drule_all dft_ordinary_prefix_cover_shift >> metis_tac[]) >>
  `h - j < h /\ h = (h - j) + j` by decide_tac >>
  first_x_assum (qspec_then `h - j` mp_tac) >> simp[] >>
  disch_then (qspecl_then
    [`FUNPOW (dft_occ_oracle_next w C) k c`,
     `FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) j d`,
     `f`, `i`, `t`] mp_tac) >>
  simp[GSYM FUNPOW_ADD] >> strip_tac >>
  qexistsl_tac [`k + l`, `g`, `s`] >> simp[]
QED

Theorem dft_original_orbit_cofinal:
  !m c d.
  dft_original_ordinary_environment Corig C L q pre x y post /\
  dft_original_label_ready C L c /\ dft_ordinary_endpoint q pre x y post c d ==>
  ?p r. m <= p /\ m <= r /\
    dft_ordinary_endpoint q pre x y post
      (FUNPOW (dft_occ_oracle_next w C) p c)
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) r d) /\
    dft_original_label_ready C L (FUNPOW (dft_occ_oracle_next w C) p c)
Proof
  Induct
  >- (rpt strip_tac >> qexistsl_tac [`0`, `0`] >> simp[FUNPOW]) >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  drule_all dft_original_endpoint_segment >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  qexistsl_tac [`p + k`, `r + j`] >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >>
  gvs[GSYM FUNPOW_ADD, ADD_COMM]
QED

Theorem dft_original_orbit_terminal:
  dft_original_ordinary_environment Corig C L q pre x y post /\
  dft_original_label_ready C L c /\ dft_ordinary_endpoint q pre x y post c d /\
  (FUNPOW (dft_occ_oracle_next w C) h c).dft_occ_core =
    DftOpen (DftDone r) [] n ==>
  ?j r' n'.
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) j d).dft_occ_core =
      DftOpen (DftDone r') [] n' /\ dft_ordinary_result_rel r r'
Proof
  strip_tac >> drule_all dft_original_orbit_cofinal >>
  disch_then (qspecl_then [`w`, `h`] strip_assume_tac) >>
  `?delta. p = delta + h` by (qexists_tac `p - h` >> decide_tac) >>
  `?n. (FUNPOW (dft_occ_oracle_next w C) p c).dft_occ_core =
     DftOpen (DftDone r) [] n` by
    (gvs[FUNPOW_ADD] >> irule dft_occ_oracle_root_absorb >> metis_tac[]) >>
  drule_all dft_ordinary_endpoint_root >> metis_tac[]
QED

Theorem dft_original_ordinary_root:
  dft_original_function f fn /\ fn_reachable f s.vs_current_bb /\
  strict_dom_vars_defined f s /\ MEM fn C.ctx_functions /\ s.vs_labels = L ==>
  dft_original_label_ready C L
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n)) /\
  dft_ordinary_endpoint q pre x y post
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))
    (dft_occ_init (DftOpen
      (DftEnter (dft_gas_edit_fn q pre x y post fn) 0 s) [] n))
Proof
  strip_tac >> conj_tac
  >- (irule dft_original_label_root >> metis_tac[]) >>
  simp[dft_ordinary_endpoint_def, dft_ordinary_sync_init]
QED

Theorem dft_original_ordinary_root_transport:
  dft_original_ordinary_environment Corig C s.vs_labels q pre x y post /\
  dft_original_function f fn /\ fn_reachable f s.vs_current_bb /\
  strict_dom_vars_defined f s /\ MEM fn C.ctx_functions ==>
  (!h r n'.
    (FUNPOW (dft_occ_oracle_next w C) h
      (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))).dft_occ_core =
        DftOpen (DftDone r) [] n' ==>
    ?j r' n''.
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) j
        (dft_occ_init (DftOpen
          (DftEnter (dft_gas_edit_fn q pre x y post fn) 0 s) [] n))).dft_occ_core =
        DftOpen (DftDone r') [] n'' /\ dft_ordinary_result_rel r r') /\
  (!h g i t.
    dft_open_observe g i t
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) h
        (dft_occ_init (DftOpen
          (DftEnter (dft_gas_edit_fn q pre x y post fn) 0 s) [] n))).dft_occ_core /\
    inst_mem_ranges i t <> [] ==>
    ?l g' u. g = dft_gas_edit_fn q pre x y post g' /\
      dft_open_observe g' i u
        (FUNPOW (dft_occ_oracle_next w C) l
          (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))).dft_occ_core /\
      (!op. MEM op i.inst_operands ==> eval_operand op u = eval_operand op t) /\
      inst_mem_ranges i u = inst_mem_ranges i t /\ u.vs_memory = t.vs_memory)
Proof
  strip_tac >>
  `dft_original_label_ready C s.vs_labels
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))` by
    (irule dft_original_label_root >> metis_tac[]) >>
  `dft_ordinary_endpoint q pre x y post
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))
    (dft_occ_init (DftOpen
      (DftEnter (dft_gas_edit_fn q pre x y post fn) 0 s) [] n))` by
    simp[dft_ordinary_endpoint_def, dft_ordinary_sync_init] >>
  conj_tac
  >- (rpt strip_tac >> irule dft_original_orbit_terminal >> metis_tac[]) >>
  rpt strip_tac >> irule dft_original_orbit_observe >> metis_tac[]
QED
