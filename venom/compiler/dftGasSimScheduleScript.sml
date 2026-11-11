Theory dftGasSimSchedule
Ancestors
  dftGasSimSwap dftGasSimInvariant dftGasSimBoundary dftGasSimLocalBoundary
  dftRunRel dftIndexedExec dftScheduleOrder dftStructural dftCorrectness dftDefs
  dftGasOracleDefs venomExecSemantics
  venomState venomInst venomEffects venomWf venomExecProofs list rich_list sorting finite_map

Theorem ev_suffix_cons_rel:
  (!t. ev_step orc p d fuel C h s = OK t ==>
    dft_res_rel
      (ev_suffix orc p d fuel C xs (t with vs_inst_idx := SUC s.vs_inst_idx))
      (ev_suffix orc p d fuel C ys (t with vs_inst_idx := SUC s.vs_inst_idx))) ==>
  dft_res_rel (ev_suffix orc p d fuel C (h::xs) s)
              (ev_suffix orc p d fuel C (h::ys) s)
Proof
  strip_tac >> Cases_on `ev_step orc p d fuel C h s` >>
  simp[ev_suffix_def] >> Cases_on `is_terminator h.inst_opcode` >> simp[] >>
  Cases_on `v.vs_halted` >> simp[]
QED

Theorem ev_extract_head:
  !pre s.
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
  dft_remaining_inv fn bb (pre ++ y::post) s /\ ~s.vs_call_ctx.cc_static /\
  EVERY (\x. MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
    ~dft_must_order x y /\ dft_abort_compatible x.inst_opcode y.inst_opcode) pre ==>
  dft_res_rel (ev_suffix orc p d fuel C (pre ++ y::post) s)
              (ev_suffix orc p d fuel C (y::(pre ++ post)) s)
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  `dft_gas_swap_pair h y /\ inst_wf h /\ inst_wf y /\
   ~(h.inst_outputs = [] /\ read_effects h.inst_opcode = empty_effects /\
     write_effects h.inst_opcode = empty_effects)` by
    (irule dft_crossing_swap_pair >> fs[] >> metis_tac[]) >>
  `(!v. MEM (Var v) y.inst_operands ==> v IN FDOM s.vs_vars) /\
   (y.inst_opcode <> INVOKE /\ y.inst_opcode <> CODECOPY ==>
    !l. MEM (Label l) y.inst_operands ==> l IN FDOM s.vs_labels)` by
    (irule dft_remaining_inv_ready >> qexistsl_tac [`bb`, `fn`, `post`, `h::pre`] >>
     simp[] >> fs[EVERY_MEM] >> metis_tac[]) >>
  `dft_res_rel (ev_suffix orc p d fuel C (h::(pre ++ y::post)) s)
    (ev_suffix orc p d fuel C (h::y::(pre ++ post)) s)` by
    (irule ev_suffix_cons_rel >> rpt strip_tac >>
     `~is_terminator h.inst_opcode` by gvs[dft_gas_swap_pair_def] >>
     `~t.vs_call_ctx.cc_static` by metis_tac[ev_step_call_ctx] >>
     `dft_remaining_inv fn bb (pre ++ y::post)
       (t with vs_inst_idx := SUC s.vs_inst_idx)` by
       (drule_at (Pat `ev_step _ _ _ _ _ _ _ = OK _`) ev_remaining_inv_step >>
        disch_then (qspecl_then [`[]`, `pre ++ y::post`] mp_tac) >> simp[] >>
        disch_then (qspecl_then [`fn`, `bb`] mp_tac) >> fs[APPEND]) >>
     first_x_assum irule >> fs[]) >>
  `dft_res_rel (ev_suffix orc p d fuel C (h::y::(pre ++ post)) s)
    (ev_suffix orc p d fuel C (y::h::(pre ++ post)) s)` by
    (irule ev_suffix_swap >> fs[] >> strip_tac >>
     metis_tac[dft_swap_operand_defined]) >>
  fs[] >> metis_tac[dft_res_rel_trans]
QED

Theorem ev_head_bubbles:
  !todo scheduled.
  dft_head_bubbles
    (\x y. MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
      ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
      id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
      ~dft_must_order x y /\ dft_abort_compatible x.inst_opcode y.inst_opcode)
    todo scheduled ==>
  !s. wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
    EVERY inst_wf bb.bb_instructions /\
    EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
    dft_remaining_inv fn bb todo s /\ ~s.vs_call_ctx.cc_static ==>
    dft_res_rel (ev_suffix orc p d fuel C todo s)
                (ev_suffix orc p d fuel C scheduled s)
Proof
  ho_match_mp_tac dft_head_bubbles_ind >> conj_tac
  >- simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `ev_suffix orc p d fuel C (y::rest) s` >>
  Cases_on `is_terminator y.inst_opcode`
  >- (`pre = []` by (Cases_on `pre` >> fs[dft_must_order_def]) >> gvs[] >>
      `post = []` by metis_tac[dft_remaining_inv_terminal] >> gvs[] >>
      simp[ev_suffix_def]) >>
  `dft_res_rel (ev_suffix orc p d fuel C (y::(pre ++ post)) s)
    (ev_suffix orc p d fuel C (y::rest) s)` by
    (irule ev_suffix_cons_rel >> rpt strip_tac >>
     `~t.vs_call_ctx.cc_static` by metis_tac[ev_step_call_ctx] >>
     `dft_remaining_inv fn bb (pre ++ post)
       (t with vs_inst_idx := SUC s.vs_inst_idx)` by
       (drule_at (Pat `ev_step _ _ _ _ _ _ _ = OK _`) ev_remaining_inv_step >>
        disch_then (qspecl_then [`pre`, `post`, `fn`, `bb`] mp_tac) >> simp[]) >>
     first_x_assum irule >> simp[]) >>
  `dft_res_rel (ev_suffix orc p d fuel C (pre ++ y::post) s)
    (ev_suffix orc p d fuel C (y::(pre ++ post)) s)` by
    (irule ev_extract_head >> metis_tac[]) >>
  metis_tac[dft_res_rel_trans]
QED

Theorem ev_from_block_step:
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\ MEM j bi /\
  from_block bi i /\ j.inst_id = i.inst_id ==>
  ev_step orc p d fuel C j s = ev_step orc p d fuel C i s
Proof
  strip_tac >> fs[from_block_def]
  >- metis_tac[all_distinct_map_mem_inj] >>
  rename1 `i = flip_operands original` >>
  `j = original` by
    metis_tac[all_distinct_map_mem_inj, flip_operands_inst_id] >>
  gvs[flip_operands_ev_step]
QED

Theorem ev_normalized_suffix_eq:
  !norm scheduled s.
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
  EVERY (\j. MEM j bi) norm /\ EVERY (from_block bi) scheduled /\
  LIST_REL (\j i. j.inst_id = i.inst_id) norm scheduled ==>
  ev_suffix orc p d fuel C norm s = ev_suffix orc p d fuel C scheduled s
Proof
  Induct >> Cases_on `scheduled` >> simp[] >> rpt gen_tac >> strip_tac >>
  rename1 `MEM source bi` >> rename1 `from_block bi target` >>
  `is_terminator source.inst_opcode = is_terminator target.inst_opcode` by
    (irule dft_from_block_terminator >> metis_tac[]) >>
  `ev_step orc p d fuel C source s = ev_step orc p d fuel C target s` by
    (irule ev_from_block_step >> metis_tac[]) >>
  simp[ev_suffix_def] >> Cases_on `ev_step orc p d fuel C target s` >> simp[] >>
  Cases_on `is_terminator target.inst_opcode` >> simp[] >>
  first_x_assum irule >> simp[]
QED

Theorem ev_suffix_pseudo_prefix:
  !pre s.
  EVERY (\i. is_pseudo i.inst_opcode) pre ==>
  ev_suffix orc p d fuel C (pre ++ rest) s =
    FOLDR (dft_exec_cons fuel C) (ev_suffix orc p d fuel C rest) pre s
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `h.inst_opcode <> GAS /\ h.inst_opcode <> INVOKE /\
   ~is_terminator h.inst_opcode` by
    (Cases_on `h.inst_opcode` >> gvs[is_pseudo_def, is_terminator_def]) >>
  simp[ev_suffix_def, dft_exec_cons_def, ev_step_ordinary] >>
  Cases_on `step_inst fuel C h s` >> simp[]
QED

Theorem ev_block_prefix:
  bb.bb_instructions = pre ++ rest /\
  EVERY (\i. is_pseudo i.inst_opcode) pre /\
  EVERY (\i. ~is_pseudo i.inst_opcode) rest ==>
  (case eval_phis s bb.bb_instructions of
     OK u => ev_block orc p d fuel C bb
       (u with vs_inst_idx := phi_prefix_length bb.bb_instructions)
   | Error e => Error e) =
  (case eval_phis s pre of
     OK u => FOLDR (dft_exec_cons fuel C) (ev_suffix orc p d fuel C rest)
       (DROP (phi_prefix_length pre) pre)
       (u with vs_inst_idx := phi_prefix_length pre)
   | Error e => Error e)
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) rest` by
    (fs[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
  simp[dft_phi_prefix_append, dft_eval_phis_append] >>
  qspecl_then [`s`, `pre`] strip_assume_tac eval_phis_ok_or_error_defs >> simp[] >>
  `ev_block orc p d fuel C bb (s' with vs_inst_idx := phi_prefix_length pre) =
   ev_suffix orc p d fuel C (DROP (phi_prefix_length pre) (pre ++ rest))
     (s' with vs_inst_idx := phi_prefix_length pre)` by
    (sym_tac >> irule ev_suffix_block >> simp[]) >>
  `phi_prefix_length pre - LENGTH pre = 0` by
    (mp_tac (Q.SPEC `pre` phi_prefix_length_le) >> decide_tac) >>
  simp[DROP_APPEND, ev_suffix_pseudo_prefix, EVERY_DROP]
QED

Theorem ev_block_schedule:
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  dft_block_rel bb bb' /\ pseudos_prefix bb /\
  bb.bb_label = s.vs_current_bb /\ strict_dom_vars_defined fn s /\
  ~s.vs_call_ctx.cc_static /\
  (!i l. MEM i bb.bb_instructions /\ ~is_pseudo i.inst_opcode /\
    ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> CODECOPY /\ MEM (Label l) i.inst_operands ==>
    l IN FDOM s.vs_labels) /\
  (!x y. MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
    ~dft_abort_compatible x.inst_opcode y.inst_opcode /\
    id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id ==>
    id_before (MAP (\i. i.inst_id) bb'.bb_instructions) x.inst_id y.inst_id) ==>
  dft_res_rel
    (case eval_phis s bb.bb_instructions of
       OK u => ev_block orc p d fuel C bb
         (u with vs_inst_idx := phi_prefix_length bb.bb_instructions)
     | Error e => Error e)
    (case eval_phis s bb'.bb_instructions of
       OK u => ev_block orc p d fuel C bb'
         (u with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
     | Error e => Error e)
Proof
  strip_tac >> drule_all dft_block_head_bubbles >> strip_tac >>
  rename1 `bb'.bb_instructions = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions ++ scheduled_body` >>
  `bb.bb_instructions = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions ++
     FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions` by
    (qpat_x_assum `pseudos_prefix bb` mp_tac >>
     simp[pseudos_prefix_def] >>
     qspec_tac (`bb.bb_instructions`, `bi`) >> Induct >> simp[] >> rpt strip_tac >>
     Cases_on `is_pseudo h.inst_opcode` >> simp[]
     >- (first_x_assum irule >> rpt strip_tac >>
         first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
     `EVERY (\i. ~is_pseudo i.inst_opcode) bi` by
       (simp[EVERY_EL] >> rpt strip_tac >>
        first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
     `FILTER (\i. is_pseudo i.inst_opcode) bi = []` by
       fs[FILTER_EQ_NIL] >>
     `FILTER (\i. ~is_pseudo i.inst_opcode) bi = bi` by
       fs[FILTER_EQ_ID] >> simp[]) >>
  qmatch_asmsub_abbrev_tac `bb'.bb_instructions = pre ++ scheduled_body` >>
  qabbrev_tac `xs = FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions` >>
  `EVERY (from_block bb.bb_instructions) scheduled_body` by fs[dft_block_rel_def] >>
  `EVERY (\i. ~is_pseudo i.inst_opcode) scheduled_body` by
    (fs[EVERY_MEM, from_block_def] >> metis_tac[flip_operands_is_pseudo]) >>
  `EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
   EVERY (\i. is_pseudo i.inst_opcode) pre` by
    simp[Abbr `xs`, Abbr `pre`, EVERY_MEM, MEM_FILTER] >>
  `EVERY (\i. MEM i bb.bb_instructions) norm` by
    (qpat_x_assum `PERM _ norm` (mp_tac o MATCH_MP PERM_MEM_EQ) >>
     simp[EVERY_MEM, MEM_FILTER] >> metis_tac[]) >>
  `!t. ev_suffix orc p d fuel C norm t = ev_suffix orc p d fuel C scheduled_body t` by
    (gen_tac >> irule ev_normalized_suffix_eq >>
     conj_tac >- (qexists_tac `bb.bb_instructions` >> simp[]) >>
     irule LIST_REL_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (DROP (phi_prefix_length pre) pre)` by
    (irule EVERY_DROP >> fs[Abbr `pre`, EVERY_MEM, MEM_FILTER] >>
     rpt strip_tac >> Cases_on `i.inst_opcode` >> gvs[is_pseudo_def, is_terminator_def]) >>
  `!b rest. b.bb_instructions = pre ++ rest /\
    EVERY (\i. ~is_pseudo i.inst_opcode) rest ==>
    (case eval_phis s b.bb_instructions of
       OK u => ev_block orc p d fuel C b
         (u with vs_inst_idx := phi_prefix_length b.bb_instructions)
     | Error e => Error e) =
    (case eval_phis s pre of
       OK u => FOLDR (dft_exec_cons fuel C) (ev_suffix orc p d fuel C rest)
         (DROP (phi_prefix_length pre) pre)
         (u with vs_inst_idx := phi_prefix_length pre)
     | Error e => Error e)` by
    (rpt strip_tac >> irule ev_block_prefix >> simp[]) >>
  qpat_assum `!b rest. _` (qspecl_then [`bb`, `xs`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_then SUBST1_TAC >>
  qpat_assum `!b rest. _` (qspecl_then [`bb'`, `scheduled_body`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_then SUBST1_TAC >>
  qspecl_then [`s`, `pre`] strip_assume_tac eval_phis_ok_or_error_defs >> simp[] >>
  irule dft_exec_prefix_rel >> simp[] >> rpt strip_tac >>
  `~t.vs_call_ctx.cc_static` by
    (drule_all dft_prefix_call_ctx >> drule dft_eval_phis_call_ctx >> simp[]) >>
  `dft_remaining_inv fn bb xs t` by
    (simp[Abbr `xs`] >> irule dft_remaining_inv_initialized >>
     conj_tac >- simp[] >> conj_tac >- simp[] >>
     qexistsl_tac [`C`, `fuel`, `s`, `s'`] >>
     fs[Abbr `pre`] >> metis_tac[]) >>
  metis_tac[ev_head_bubbles]
QED
