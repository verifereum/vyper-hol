Theory dftGasSimSchedule
Ancestors
  dftGasSimSwap dftGasSimInvariant dftGasSimBoundary dftGasSimLocalBoundary
  dftRunRel dftScheduleOrder dftStructural dftCorrectness dftDefs
  dftGasOracleDefs venomExecSemantics
  venomState venomInst venomEffects venomWf list finite_map

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
