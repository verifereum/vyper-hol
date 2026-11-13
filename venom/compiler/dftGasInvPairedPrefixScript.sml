Theory dftGasInvPairedPrefix
Ancestors
  dftGasInvCallerExtract dftGasInvBlockInit dftGasInvReachSlice
  dftGasInvPrefixRun dftGasInvPrefixReach dftGasInvFlexibleTrace
  dftGasOracleDefs dftRunRel dftScheduleOrder dftFrontEquiv dftStructural
  dftCorrectness dftShape venomExecSemantics venomExecProofs venomInst venomWf
  o1PassContract dftGasInvOracleFrame
  venomState contextCodegenRel list rich_list

Theorem inv_prefix_position[local]:
  !n a b. inv_ev_prefix orc p d ctx bb n a b ==>
    b.vs_inst_idx = a.vs_inst_idx + n /\
    b.vs_current_bb = a.vs_current_bb
Proof
  Induct >> simp[inv_ev_prefix_suc] >> rpt strip_tac >>
  drule_all ev_step_nonterm_current_bb >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem inv_prefix_common_cut[local]:
  !m n a b.
    m <= n /\ inv_ev_prefix orc p d ctx bb' n a b /\
    (!j. a.vs_inst_idx <= j /\ j < a.vs_inst_idx + m ==>
      get_instruction bb j = get_instruction bb' j) ==>
    ?u. inv_ev_prefix orc p d ctx bb m a u /\
      inv_ev_prefix orc p d ctx bb' (n-m) u b
Proof
  Induct >- (rpt strip_tac >> qexists_tac `a` >> simp[]) >>
  Cases_on `n` >> simp[inv_ev_prefix_suc] >> rpt strip_tac >>
  `get_instruction bb a.vs_inst_idx = SOME inst` by simp[] >>
  first_x_assum (qspecl_then [`n'`, `u with vs_inst_idx := SUC a.vs_inst_idx`, `b`] mp_tac) >>
  simp[] >> strip_tac >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem inv_phi_prefix_pseudo_bound[local]:
  !pre xs. EVERY (\i. ~is_pseudo i.inst_opcode) xs ==>
    phi_prefix_length (pre ++ xs) <= LENGTH pre
Proof
  Induct >> simp[phi_prefix_length_def] >-
    (Cases_on `xs` >> simp[phi_prefix_length_def] >>
     rpt strip_tac >> `h.inst_opcode <> PHI` by metis_tac[is_pseudo_def] >> simp[]) >>
  rpt strip_tac >> Cases_on `h.inst_opcode = PHI` >>
  simp[phi_prefix_length_def]
QED

Theorem inv_list_index_cut[local]:
  !xs k. k < LENGTH xs ==>
    xs = TAKE k xs ++ [EL k xs] ++ DROP (SUC k) xs /\ LENGTH (TAKE k xs) = k
Proof
  Induct >> simp[] >> Cases_on `k` >> simp[TAKE_def, DROP_def]
QED

Theorem inv_paired_prefix_cut:
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  dft_fn_rel fn fn' /\
  lookup_block entry.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block entry.vs_current_bb fn'.fn_blocks = SOME bb' /\
  entry.vs_inst_idx = phi_prefix_length bb.bb_instructions /\
  ev_reachable orc initial C p d fn first entry /\
  inv_ev_prefix orc p d C' bb' n entry t /\
  get_instruction bb' t.vs_inst_idx = SOME targetobs ==>
  (is_pseudo targetobs.inst_opcode /\ ev_reachable orc initial C p d fn targetobs t) \/
  ?pseudos sourcebody scheduled targetpost s0 startinst.
    bb.bb_instructions = pseudos ++ sourcebody /\
    bb'.bb_instructions = pseudos ++ (scheduled ++ targetobs::targetpost) /\
    EVERY (\i. is_pseudo i.inst_opcode) pseudos /\
    EVERY (\i. ~is_pseudo i.inst_opcode) sourcebody /\
    EVERY (\i. ~is_pseudo i.inst_opcode) (scheduled ++ targetobs::targetpost) /\
    s0.vs_inst_idx = LENGTH pseudos /\
    lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block s0.vs_current_bb fn'.fn_blocks = SOME bb' /\
    get_instruction bb s0.vs_inst_idx = SOME startinst /\
    ev_reachable orc initial C p d fn startinst s0 /\
    inv_ev_ftrace orc p d C scheduled s0 t
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by
    metis_tac[venomExecPropsTheory.FIND_MEM, lookup_block_def] >>
  `dft_block_rel bb bb'` by metis_tac[dft_fn_rel_lookup_order] >>
  `pseudos_prefix bb /\ bb_well_formed bb` by
    (gvs[dft_fn_rel_def, fn_pseudos_prefix_def, wf_function_def, EVERY_MEM]) >>
  drule_all pseudos_prefix_front_decomposition >> strip_tac >>
  `bb.bb_instructions <> [] /\ is_terminator (LAST bb.bb_instructions).inst_opcode` by
    gvs[bb_well_formed_def] >>
  `~is_pseudo (LAST bb.bb_instructions).inst_opcode` by
    (Cases_on `(LAST bb.bb_instructions).inst_opcode` >>
     gvs[is_terminator_def, is_pseudo_def]) >>
  qpat_x_assum `dft_block_rel _ _` mp_tac >>
  simp[dft_block_rel_def] >> strip_tac >>
  rename1 `EVERY (from_block bb.bb_instructions) ys` >>
  qmatch_asmsub_abbrev_tac `FRONT bb.bb_instructions = pre ++ mid` >>
  qabbrev_tac `last = LAST bb.bb_instructions` >>
  `bb.bb_instructions = pre ++ (mid ++ [last])` by
    metis_tac[APPEND_FRONT_LAST, APPEND_ASSOC] >>
  `EVERY (\i. is_pseudo i.inst_opcode) pre /\
   EVERY (\i. ~is_pseudo i.inst_opcode) (mid ++ [last]) /\
   EVERY (\i. ~is_pseudo i.inst_opcode) ys` by
    (simp[Abbr `pre`, Abbr `mid`, Abbr `last`, EVERY_APPEND, EVERY_FILTER, EVERY_MEM] >>
     gvs[EVERY_MEM, from_block_def] >> metis_tac[flip_operands_is_pseudo]) >>
  suspend "cut"
QED

Resume inv_paired_prefix_cut[cut]:
  `entry.vs_inst_idx <= LENGTH pre` by
    (asm_rewrite_tac[] >> irule inv_phi_prefix_pseudo_bound >> simp[]) >>
  `inv_ev_prefix orc p d C bb' n entry t` by
    metis_tac[inv_ev_prefix_context_reflect] >>
  `t.vs_inst_idx = entry.vs_inst_idx + n /\ t.vs_current_bb = entry.vs_current_bb` by
    metis_tac[inv_prefix_position] >>
  `bb.bb_label = entry.vs_current_bb` by metis_tac[lookup_block_label] >>
  `get_instruction bb entry.vs_inst_idx = SOME first` by
    (`active_inst fn first entry` by metis_tac[ev_reachable_cases] >>
     qpat_x_assum `active_inst fn first entry` mp_tac >> simp[active_inst_def] >> strip_tac >>
     rename1 `MEM activebb fn.fn_blocks` >>
     `wf_function fn` by gvs[dft_fn_rel_def] >>
     `lookup_block entry.vs_current_bb fn.fn_blocks = SOME activebb` by
       (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
     gvs[get_instruction_def]) >>
  Cases_on `t.vs_inst_idx < LENGTH pre`
  >- (disj1_tac >> conj_tac
      >- (`targetobs = EL t.vs_inst_idx pre` by
            gvs[get_instruction_def, EL_APPEND] >>
          gvs[EVERY_EL] ) >>
      `inv_ev_prefix orc p d C bb n entry t` by
        (drule_at (Pat `inv_ev_prefix _ _ _ C bb' _ _ _`) inv_prefix_common_cut >>
         disch_then (qspecl_then [`bb`, `n`] mp_tac) >>
         (impl_tac >- (simp[NoAsms] >> rpt strip_tac >>
           `j < LENGTH pre` by decide_tac >> simp[get_instruction_def, EL_APPEND])) >>
         simp[] ) >>
      irule inv_ev_prefix_reachable >> goal_assum (drule_at Any) >> simp[] >>
      gvs[get_instruction_def, EL_APPEND]) >>
  disj2_tac >>
  `LENGTH pre - entry.vs_inst_idx <= n` by decide_tac >>
  `?s0. inv_ev_prefix orc p d C bb (LENGTH pre - entry.vs_inst_idx) entry s0 /\
    inv_ev_prefix orc p d C bb' (n - (LENGTH pre - entry.vs_inst_idx)) s0 t` by
    (drule_at (Pat `inv_ev_prefix _ _ _ C bb' _ _ _`) inv_prefix_common_cut >>
     disch_then (qspecl_then [`bb`, `LENGTH pre - entry.vs_inst_idx`] mp_tac) >>
     (impl_tac >- (conj_tac >- decide_tac >> rpt strip_tac >>
       `j < LENGTH pre` by decide_tac >> simp[get_instruction_def, EL_APPEND])) >>
     simp[]) >>
  `s0.vs_inst_idx = LENGTH pre /\ s0.vs_current_bb = entry.vs_current_bb` by
    (qpat_assum `inv_ev_prefix _ _ _ _ bb _ entry s0`
       (mp_tac o MATCH_MP inv_prefix_position) >> strip_tac >> conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
  `?scheduled targetpost. ys = scheduled ++ targetobs::targetpost /\
    LENGTH scheduled = t.vs_inst_idx - LENGTH pre` by
    (qexistsl_tac [`TAKE (t.vs_inst_idx - LENGTH pre) ys`,
      `DROP (SUC (t.vs_inst_idx - LENGTH pre)) ys`] >>
     qpat_x_assum `get_instruction bb' t.vs_inst_idx = SOME targetobs` mp_tac >>
     simp[get_instruction_def, EL_APPEND_EQN] >> strip_tac >>
     gvs[] >> irule (cj 1 inv_list_index_cut) >> decide_tac) >>
  suspend "post"
QED

Resume inv_paired_prefix_cut[post]:
  `get_instruction bb s0.vs_inst_idx = SOME (HD (mid ++ [last]))` by
    (simp[get_instruction_def, EL_APPEND_EQN] >> Cases_on `mid` >> simp[]) >>
  `ev_reachable orc initial C p d fn (HD (mid ++ [last])) s0` by
    (irule inv_ev_prefix_reachable >>
     goal_assum (drule_at (Pat `ev_reachable _ _ _ _ _ _ _ _`)) >> simp[] >>
     goal_assum (drule_at Any) >> gvs[]) >>
  `inv_ev_ftrace orc p d C scheduled s0 t` by
    (qpat_assum `inv_ev_prefix _ _ _ C bb' _ s0 t`
       (mp_tac o MATCH_MP inv_ev_prefix_ftrace) >>
     `n - (LENGTH pre - entry.vs_inst_idx) = LENGTH scheduled` by decide_tac >>
     qpat_x_assum `entry.vs_inst_idx = _` kall_tac >>
     qpat_x_assum `LENGTH scheduled = _` kall_tac >>
     simp[DROP_APPEND, TAKE_APPEND]) >>
  qexistsl_tac [`pre`, `mid ++ [last]`, `scheduled`, `targetpost`, `s0`, `HD (mid ++ [last])`] >>
  simp[] >> gvs[EVERY_APPEND]
QED

Finalise inv_paired_prefix_cut

Theorem inv_paired_prefix_invoke:
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\ ctx_labels_bound C initial.vs_labels /\ o1_run_state_ok initial /\
  dft_fn_rel fn fn' /\
  lookup_block entry.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block entry.vs_current_bb fn'.fn_blocks = SOME bb' /\
  EVERY inst_shape_ok bb.bb_instructions /\
  entry.vs_inst_idx = phi_prefix_length bb.bb_instructions /\
  ev_reachable orc initial C p d fn first entry /\
  inv_ev_prefix orc p d C' bb' n entry t /\
  get_instruction bb' t.vs_inst_idx = SOME targetobs /\
  targetobs.inst_opcode = INVOKE ==>
  ?sS. ev_reachable orc initial C p d fn targetobs sS /\
    (!op. MEM op targetobs.inst_operands ==> eval_operand op sS = eval_operand op t) /\
    (!callee args. setup_callee callee args sS = setup_callee callee args t)
Proof
  strip_tac >> drule_all inv_paired_prefix_cut >> strip_tac
  >- gvs[is_pseudo_def] >>
  `MEM bb fn.fn_blocks` by
    metis_tac[venomExecPropsTheory.FIND_MEM, lookup_block_def] >>
  `from_block bb.bb_instructions targetobs` by
    (`FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions = pseudos` by
       (asm_rewrite_tac[FILTER_APPEND_DISTRIB] >>
        `FILTER (\i. is_pseudo i.inst_opcode) pseudos = pseudos /\
         FILTER (\i. is_pseudo i.inst_opcode) sourcebody = []` by
          (simp[FILTER_EQ_ID, FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >> simp[]) >>
     drule_all dft_fn_rel_lookup_order >> simp[dft_block_rel_def] >>
     strip_tac >> gvs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
  `MEM targetobs bb.bb_instructions` by
    (gvs[from_block_def] >> drule flip_operands_special_opcode >> simp[]) >>
  `MEM targetobs sourcebody` by
    (gvs[EVERY_MEM] >> metis_tac[MEM_APPEND, is_pseudo_def]) >>
  `?srcpre srcpost. sourcebody = srcpre ++ targetobs::srcpost` by
    metis_tac[MEM_SPLIT] >>
  `~s0.vs_call_ctx.cc_static` by
    (irule inv_ev_reachable_nonstatic >> goal_assum (drule_at Any) >>
     gvs[o1_run_state_ok_def]) >>
  irule inv_source_reachable_invoke >> simp[] >>
  conj_tac >- metis_tac[] >>
  goal_assum (drule_at (Pat `ev_reachable _ _ _ _ _ _ _ _`)) >> simp[] >>
  goal_assum (drule_at (Pat `dft_fn_rel _ _`)) >> simp[] >>
  goal_assum (drule_at (Pat `inv_ev_ftrace _ _ _ _ _ _ _`)) >> simp[] >>
  qexistsl_tac [`pseudos`, `srcpost`, `srcpre`, `targetobs`, `targetpost`] >> gvs[]
QED
