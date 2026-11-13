Theory dftGasInvExtraction
Ancestors
  dftGasInvInversion dftGasInvFlexibleTrace dftGasInvResidualTrace
  dftGasInvSSAProbe dftGasInvOracleFrame dftGasOracleDefs
  dftRunRel dftScheduleOrder dftCorrectness dftAvailability dftBlockSim dftStructural
  venomExecSemantics venomInst venomState list rich_list pred_set sorting
  dftSsaPreserve dftPermSim venomWf dftWf

Theorem inv_ftrace_original_representatives:
  !scheduled s t.
  EVERY (from_block bi) scheduled /\ inv_ev_ftrace orc p d ctx scheduled s t ==>
  ?originals. MAP (\i. i.inst_id) originals = MAP (\i. i.inst_id) scheduled /\
    EVERY (\i. MEM i bi /\ ~is_pseudo i.inst_opcode) originals /\
    inv_ev_ftrace orc p d ctx originals s t
Proof
  Induct
  >- simp[inv_ev_ftrace_def] >>
  simp[inv_ev_ftrace_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `from_block _ _` mp_tac >> simp[from_block_def] >> strip_tac >>
  qexists_tac `j::originals` >> simp[] >>
  gvs[flip_operands_inst_id] >>
  simp[inv_ev_ftrace_def] >>
  metis_tac[inv_ev_flip_step, inv_ev_flip_nonterminator]
QED

Theorem inv_ftrace_remaining:
  !xs remaining s t.
  wf_function fn /\ EVERY inst_wf bb.bb_instructions /\
  dft_remaining_inv fn bb remaining s /\
  ALL_DISTINCT xs /\ EVERY (\i. MEM i remaining) xs /\
  inv_ev_ftrace orc p d ctx xs s t ==>
  dft_remaining_inv fn bb
    (FILTER (\i. ~MEM i xs) remaining) t
Proof
  Induct >> simp[inv_ev_ftrace_def] >> rpt strip_tac >>
  `?pre post. remaining = pre ++ h::post` by metis_tac[MEM_SPLIT] >>
  `ALL_DISTINCT remaining` by metis_tac[dft_remaining_inv_def] >>
  `FILTER (\i. i <> h) remaining = pre ++ post` by
    (gvs[ALL_DISTINCT_APPEND] >>
     `FILTER (\i. i <> h) pre = pre /\ FILTER (\i. i <> h) post = post` by
       (simp[FILTER_EQ_ID, EVERY_MEM] >> metis_tac[]) >>
     simp[FILTER_APPEND_DISTRIB]) >>
  `dft_remaining_inv fn bb (pre ++ post)
      (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule inv_remaining_ev_step >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `EVERY (\i. MEM i (pre ++ post)) xs` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  first_x_assum drule_all >>
  `FILTER (\i. i <> h /\ ~MEM i xs) remaining =
   FILTER (\i. ~MEM i xs) (FILTER (\i. i <> h) remaining)` by
    simp[FILTER_FILTER, CONJ_COMM] >>
  asm_rewrite_tac[]
QED

Theorem inv_ftrace_pull:
  !pre s t.
  EVERY (\z. dft_gas_swap_pair x z /\ inst_wf x /\ inst_wf z) pre /\
  inv_ev_ftrace orc p d ctx (pre ++ x::post) s t ==>
  inv_ev_ftrace orc p d ctx (x::pre ++ post) s t
Proof
  Induct >> simp[] >> rpt strip_tac >>
  qpat_x_assum `inv_ev_ftrace _ _ _ _ _ _ _` mp_tac >>
  simp[Once inv_ev_ftrace_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  irule inv_ev_ftrace_exchange >> simp[] >>
  simp[Once inv_ev_ftrace_def] >> gvs[APPEND] >> metis_tac[]
QED

Theorem inv_ftrace_source_sort:
  !ordered executed s t.
  ALL_DISTINCT ordered /\ PERM executed ordered /\
  (!x z. id_before ordered x z /\ id_before executed z x ==>
     dft_gas_swap_pair x z /\ inst_wf x /\ inst_wf z) /\
  inv_ev_ftrace orc p d ctx executed s t ==>
  inv_ev_ftrace orc p d ctx ordered s t
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `MEM h executed` by metis_tac[PERM_MEM_EQ, MEM] >>
  `?pre post. executed = pre ++ h::post` by metis_tac[MEM_SPLIT] >>
  `PERM (pre ++ post) ordered` by
    (irule perm_cons_delete >> qexists_tac `h` >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> metis_tac[]) >>
  `EVERY (\z. dft_gas_swap_pair h z /\ inst_wf h /\ inst_wf z) pre` by
    (simp[EVERY_MEM] >> gen_tac >> disch_tac >> first_x_assum irule >>
     simp[dftSsaPreserveTheory.id_before_cons,
          dftSsaPreserveTheory.id_before_append] >>
     metis_tac[PERM_MEM_EQ, MEM_APPEND]) >>
  `inv_ev_ftrace orc p d ctx (h::pre ++ post) s t` by
    (irule inv_ftrace_pull >> goal_assum (drule_at Any) >> metis_tac[]) >>
  gvs[Once inv_ev_ftrace_def] >> simp[Once inv_ev_ftrace_def] >>
  goal_assum (drule_at Any) >> simp[] >> first_x_assum irule >>
  goal_assum (drule_at Any) >> simp[] >>
  ntac 2 gen_tac >> strip_tac >> first_x_assum irule >>
  gvs[dftSsaPreserveTheory.id_before_cons,
      dftSsaPreserveTheory.id_before_append] >> metis_tac[]
QED

Theorem inv_completed_prefix_perm:
  ALL_DISTINCT (srcpre ++ srcpost) /\ ALL_DISTINCT consumed /\
  EVERY (\i. MEM i (srcpre ++ srcpost)) consumed ==>
  PERM (consumed ++ FILTER (\i. ~MEM i consumed) srcpre)
       (srcpre ++ FILTER (\i. MEM i consumed) srcpost)
Proof
  strip_tac >> irule PERM_ALL_DISTINCT >>
  conj_tac
  >- (gvs[EVERY_MEM, MEM_FILTER] >> metis_tac[]) >>
  gvs[ALL_DISTINCT_APPEND] >>
  simp[ALL_DISTINCT_APPEND, FILTER_ALL_DISTINCT, MEM_FILTER] >> metis_tac[]
QED

Theorem inv_ftrace_call_ctx:
  !xs s t. inv_ev_ftrace orc p d ctx xs s t ==>
  t.vs_call_ctx = s.vs_call_ctx
Proof
  Induct >> simp[inv_ev_ftrace_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >> metis_tac[inv_ev_step_call_ctx]
QED

Theorem inv_id_before_filter_reflect:
  !xs. id_before (FILTER pred xs) x z ==> id_before xs x z
Proof
  Induct >- simp[id_before_def] >>
  gen_tac >> Cases_on `pred h` >>
  simp[dftSsaPreserveTheory.id_before_cons, MEM_FILTER] >> metis_tac[]
QED

Theorem inv_completion_inversion:
  ALL_DISTINCT (srcpre ++ obs::srcpost) /\
  PERM (consumed ++ obs::later) (srcpre ++ obs::srcpost) /\
  id_before (srcpre ++ obs::srcpost) x z /\
  id_before (consumed ++ FILTER (\i. ~MEM i consumed) srcpre) z x ==>
  id_before (consumed ++ obs::later) z x
Proof
  strip_tac >>
  qpat_x_assum `id_before (consumed ++ _) _ _` mp_tac >>
  simp[dftSsaPreserveTheory.id_before_append] >> strip_tac
  >- simp[dftSsaPreserveTheory.id_before_append]
  >- (`id_before (srcpre ++ obs::srcpost) z x` by
        metis_tac[inv_id_before_filter_reflect,
                  dftSsaPreserveTheory.id_before_append] >>
      metis_tac[id_before_asym]) >>
  `MEM x srcpre /\ ~MEM x consumed` by gvs[MEM_FILTER] >>
  `x <> obs` by (gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `MEM x later` by
    (drule PERM_MEM_EQ >> disch_then (qspec_then `x` mp_tac) >> simp[]) >>
  simp[dftSsaPreserveTheory.id_before_append]
QED

Theorem inv_completed_order_source:
  id_before (srcpre ++ FILTER pred srcpost) x z ==>
  id_before (srcpre ++ obs::srcpost) x z
Proof
  simp[dftSsaPreserveTheory.id_before_append,
       dftSsaPreserveTheory.id_before_cons, MEM_FILTER] >>
  metis_tac[inv_id_before_filter_reflect]
QED

Theorem inv_lookup_completed_sort:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  bb.bb_instructions = pseudos ++ (srcpre ++ obs::srcpost) /\
  EVERY (\i. ~is_pseudo i.inst_opcode) (srcpre ++ obs::srcpost) /\
  MAP (\i. i.inst_id) bb'.bb_instructions =
    MAP (\i. i.inst_id) pseudos ++
    MAP (\i. i.inst_id) (consumed ++ obs::later) /\
  ALL_DISTINCT (srcpre ++ obs::srcpost) /\
  PERM (consumed ++ obs::later) (srcpre ++ obs::srcpost) /\
  inv_ev_ftrace orc p d ctx
    (consumed ++ FILTER (\i. ~MEM i consumed) srcpre) s t ==>
  inv_ev_ftrace orc p d ctx
    (srcpre ++ FILTER (\i. MEM i consumed) srcpost) s t
Proof
  strip_tac >>
  `ALL_DISTINCT (consumed ++ obs::later)` by metis_tac[ALL_DISTINCT_PERM] >>
  `EVERY (\i. MEM i (srcpre ++ srcpost)) consumed` by
    (gvs[ALL_DISTINCT_APPEND, EVERY_MEM] >> rpt strip_tac >>
     drule PERM_MEM_EQ >> disch_then (qspec_then `i` mp_tac) >>
     simp[] >> metis_tac[]) >>
  `ALL_DISTINCT (srcpre ++ srcpost)` by gvs[ALL_DISTINCT_APPEND] >>
  `PERM (consumed ++ FILTER (\i. ~MEM i consumed) srcpre)
        (srcpre ++ FILTER (\i. MEM i consumed) srcpost)` by
    (irule inv_completed_prefix_perm >> gvs[ALL_DISTINCT_APPEND]) >>
  irule inv_ftrace_source_sort >> conj_tac
  >- (gvs[ALL_DISTINCT_APPEND] >>
      simp[ALL_DISTINCT_APPEND, FILTER_ALL_DISTINCT, MEM_FILTER] >> metis_tac[]) >>
  qexists_tac `consumed ++ FILTER (\i. ~MEM i consumed) srcpre` >>
  simp[] >> ntac 2 gen_tac >> strip_tac >>
  `id_before (srcpre ++ obs::srcpost) x z` by
    metis_tac[inv_completed_order_source] >>
  `id_before (consumed ++ obs::later) z x` by
    metis_tac[inv_completion_inversion] >>
  `MEM x (srcpre ++ obs::srcpost) /\ MEM z (srcpre ++ obs::srcpost)` by
    metis_tac[id_before_def, EL_MEM, arithmeticTheory.LESS_TRANS] >>
  `id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id z.inst_id /\
   id_before (MAP (\i. i.inst_id) bb'.bb_instructions) z.inst_id x.inst_id` by
    (`id_before (MAP (\i. i.inst_id) (srcpre ++ obs::srcpost))
        x.inst_id z.inst_id /\
      id_before (MAP (\i. i.inst_id) (consumed ++ obs::later))
        z.inst_id x.inst_id` by
       metis_tac[dftSsaPreserveTheory.id_before_map] >>
     asm_rewrite_tac[MAP_APPEND] >>
     metis_tac[id_before_append_right, MAP_APPEND]) >>
  `MEM x bb.bb_instructions /\ MEM z bb.bb_instructions /\
   ~is_pseudo x.inst_opcode /\ ~is_pseudo z.inst_opcode` by
    (asm_rewrite_tac[MEM_APPEND] >> fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all inv_lookup_inversion_swap >> simp[]
QED

Theorem inv_lookup_missing_predecessors:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  bb.bb_instructions = pseudos ++ (srcpre ++ obs::srcpost) /\
  EVERY inst_shape_ok bb.bb_instructions /\
  EVERY (\i. ~is_pseudo i.inst_opcode) (srcpre ++ obs::srcpost) /\
  MAP (\i. i.inst_id) bb'.bb_instructions =
    MAP (\i. i.inst_id) pseudos ++
    MAP (\i. i.inst_id) (consumed ++ obs::later) /\
  ALL_DISTINCT (srcpre ++ obs::srcpost) /\
  PERM (consumed ++ obs::later) (srcpre ++ obs::srcpost) ==>
  EVERY (\x. inst_shape_ok x /\ ~is_terminator x.inst_opcode /\
    ~dft_must_order x obs) (FILTER (\i. ~MEM i consumed) srcpre)
Proof
  strip_tac >> simp[EVERY_MEM, MEM_FILTER] >> gen_tac >> strip_tac >>
  `MEM x bb.bb_instructions /\ MEM obs bb.bb_instructions /\
   ~is_pseudo x.inst_opcode /\ ~is_pseudo obs.inst_opcode /\ inst_shape_ok x` by
    (fs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
  `x <> obs` by (gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `MEM x later` by
    (drule PERM_MEM_EQ >> disch_then (qspec_then `x` mp_tac) >> simp[]) >>
  `id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id obs.inst_id /\
   id_before (MAP (\i. i.inst_id) bb'.bb_instructions) obs.inst_id x.inst_id` by
    (asm_rewrite_tac[MAP_APPEND] >>
     simp[dftSsaPreserveTheory.id_before_append,
          dftSsaPreserveTheory.id_before_cons, MEM_MAP] >> metis_tac[]) >>
  drule_all inv_lookup_block_contract >> strip_tac >>
  drule_all dft_fn_rel_lookup_order >> strip_tac >>
  `~dft_must_order x obs` by metis_tac[dft_inversion_not_must_order] >>
  drule_all inv_lookup_inversion_swap >> simp[dft_gas_swap_pair_def]
QED

Theorem inv_ev_ftrace_initial_fmp:
  !xs s t. inv_ev_ftrace orc p d ctx xs s t ==>
  t.vs_initial_fmp = s.vs_initial_fmp
Proof
  Induct >> simp[inv_ev_ftrace_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >> metis_tac[inv_ev_step_initial_fmp]
QED

Theorem inv_lookup_normalized_observation:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  bb.bb_instructions = pseudos ++ (srcpre ++ obs::srcpost) /\
  EVERY inst_shape_ok bb.bb_instructions /\
  EVERY (\i. ~is_pseudo i.inst_opcode) (srcpre ++ obs::srcpost) /\
  MAP (\i. i.inst_id) bb'.bb_instructions =
    MAP (\i. i.inst_id) pseudos ++
    MAP (\i. i.inst_id) (consumed ++ obs::later) /\
  ALL_DISTINCT (srcpre ++ obs::srcpost) /\
  PERM (consumed ++ obs::later) (srcpre ++ obs::srcpost) /\
  dft_remaining_inv fn bb (srcpre ++ obs::srcpost) s0 /\
  s0.vs_inst_idx = LENGTH pseudos /\ ~s0.vs_call_ctx.cc_static /\
  inv_ev_ftrace orc p d ctx consumed s0 sT /\
  inv_memory_observation obs.inst_opcode ==>
  ?sS. inv_ev_prefix orc p d ctx bb (LENGTH srcpre) s0 sS /\
    sS.vs_inst_idx = LENGTH pseudos + LENGTH srcpre /\
    (!op. MEM op obs.inst_operands ==> eval_operand op sS = eval_operand op sT) /\
    sS.vs_initial_fmp = sT.vs_initial_fmp
Proof
  strip_tac >>
  `ALL_DISTINCT (consumed ++ obs::later)` by metis_tac[ALL_DISTINCT_PERM] >>
  `ALL_DISTINCT consumed /\ ~MEM obs consumed` by
    (fs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `EVERY (\i. MEM i (srcpre ++ obs::srcpost)) consumed` by
    (simp[EVERY_MEM] >> gen_tac >> strip_tac >>
     drule PERM_MEM_EQ >> disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  `wf_function fn /\ wf_ssa fn` by metis_tac[dft_fn_rel_def] >>
  drule_all inv_lookup_block_contract >> strip_tac >>
  drule_all inv_lookup_missing_predecessors >> strip_tac >>
  `~sT.vs_call_ctx.cc_static` by metis_tac[inv_ftrace_call_ctx] >>
  `dft_remaining_inv fn bb
      (FILTER (\i. ~MEM i consumed) srcpre ++
       obs::FILTER (\i. ~MEM i consumed) srcpost) sT` by
    (drule_all inv_ftrace_remaining >> simp[FILTER_APPEND_DISTRIB]) >>
  `?u. inv_ev_trace orc p d 0 ctx (FILTER (\i. ~MEM i consumed) srcpre) sT u /\
       (!op. MEM op obs.inst_operands ==> eval_operand op u = eval_operand op sT)` by
    (drule_all inv_remaining_trace_extension >> metis_tac[]) >>
  `inv_ev_ftrace orc p d ctx
     (consumed ++ FILTER (\i. ~MEM i consumed) srcpre) s0 u` by
    metis_tac[inv_ev_trace_ftrace, inv_ev_ftrace_append] >>
  drule_all inv_lookup_completed_sort >>
  simp[inv_ev_ftrace_append] >> strip_tac >>
  rename1 `inv_ev_ftrace orc p d ctx srcpre s0 sS` >>
  `EVERY (\z. MEM z bb.bb_instructions /\ ~is_pseudo z.inst_opcode /\
     id_before (MAP (\i. i.inst_id) bb.bb_instructions) obs.inst_id z.inst_id /\
     id_before (MAP (\i. i.inst_id) bb'.bb_instructions) z.inst_id obs.inst_id)
     (FILTER (\i. MEM i consumed) srcpost)` by
    (simp[EVERY_MEM, MEM_FILTER] >> gen_tac >> strip_tac >>
     `MEM z bb.bb_instructions /\ ~is_pseudo z.inst_opcode` by
       (fs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
     asm_rewrite_tac[MAP_APPEND] >>
     simp[dftSsaPreserveTheory.id_before_append,
          dftSsaPreserveTheory.id_before_cons, MEM_MAP] >> metis_tac[]) >>
  `MEM obs bb.bb_instructions /\ ~is_pseudo obs.inst_opcode` by
    (fs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
  drule_all inv_lookup_trailing_trace_frame >> strip_tac >>
  qexists_tac `sS` >>
  `inv_ev_prefix orc p d ctx bb (LENGTH srcpre) s0 sS` by
    (qspecl_then [`srcpre`, `pseudos`, `s0`, `sS`] mp_tac (Q.INST [`b` |-> `obs::srcpost`] inv_ev_ftrace_slice) >>
     simp[APPEND_ASSOC]) >>
  qpat_assum `inv_ev_ftrace _ _ _ _ srcpre s0 sS`
    (mp_tac o MATCH_MP inv_ev_ftrace_idx) >> simp[] >>
  metis_tac[inv_ev_ftrace_initial_fmp, inv_ev_trace_ftrace]
QED

Theorem inv_from_block_representatives:
  !xs. EVERY (from_block bi) xs ==>
  ?ys. MAP (\i. i.inst_id) ys = MAP (\i. i.inst_id) xs /\
    EVERY (\i. MEM i bi /\ ~is_pseudo i.inst_opcode) ys
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qpat_x_assum `from_block _ _` mp_tac >> simp[from_block_def] >> strip_tac >>
  qexists_tac `j::ys` >> gvs[flip_operands_inst_id]
QED

Theorem inv_original_ids_perm:
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
  EVERY (\i. MEM i bi) xs /\ EVERY (\i. MEM i bi) ys /\
  PERM (MAP (\i. i.inst_id) xs) (MAP (\i. i.inst_id) ys) ==>
  PERM xs ys
Proof
  strip_tac >>
  drule (Q.ISPEC `\id. @i. MEM i bi /\ i.inst_id = id` PERM_MAP) >>
  `!zs. EVERY (\i. MEM i bi) zs ==>
    MAP (\id. @i. MEM i bi /\ i.inst_id = id) (MAP (\i. i.inst_id) zs) = zs` by
    (Induct >> simp[] >> rpt strip_tac >>
     first_x_assum drule >> simp[] >> strip_tac >>
     SELECT_ELIM_TAC >> metis_tac[all_distinct_map_mem_inj]) >>
  disch_then (qspec_then `bi` mp_tac) >> simp[]
QED

Theorem inv_lookup_scheduled_observation:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  bb.bb_instructions = pseudos ++ (srcpre ++ obs::srcpost) /\
  EVERY (\i. is_pseudo i.inst_opcode) pseudos /\
  EVERY (\i. ~is_pseudo i.inst_opcode) (srcpre ++ obs::srcpost) /\
  EVERY inst_shape_ok bb.bb_instructions /\
  bb'.bb_instructions = pseudos ++ (scheduled ++ targetobs::targetpost) /\
  targetobs.inst_id = obs.inst_id /\
  dft_remaining_inv fn bb (srcpre ++ obs::srcpost) s0 /\
  s0.vs_inst_idx = LENGTH pseudos /\ ~s0.vs_call_ctx.cc_static /\
  inv_ev_ftrace orc p d ctx scheduled s0 sT /\
  inv_memory_observation obs.inst_opcode ==>
  ?sS. inv_ev_prefix orc p d ctx bb (LENGTH srcpre) s0 sS /\
    sS.vs_inst_idx = LENGTH pseudos + LENGTH srcpre /\
    (!op. MEM op obs.inst_operands ==> eval_operand op sS = eval_operand op sT) /\
    sS.vs_initial_fmp = sT.vs_initial_fmp
Proof
  strip_tac >>
  `FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions = pseudos /\
   FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions = srcpre ++ obs::srcpost` by
    (`FILTER (\i. is_pseudo i.inst_opcode) pseudos = pseudos /\
      FILTER (\i. ~is_pseudo i.inst_opcode) pseudos = [] /\
      FILTER (\i. is_pseudo i.inst_opcode) (srcpre ++ obs::srcpost) = [] /\
      FILTER (\i. ~is_pseudo i.inst_opcode) (srcpre ++ obs::srcpost) = srcpre ++ obs::srcpost` by
       (simp[FILTER_EQ_ID, FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
     asm_rewrite_tac[FILTER_APPEND_DISTRIB, APPEND_NIL, APPEND]) >>
  drule_all dft_fn_rel_lookup_order >> strip_tac >>
  qpat_x_assum `dft_block_rel _ _` mp_tac >>
  simp[dft_block_rel_def] >> strip_tac >> gvs[] >>
  `EVERY (from_block bb.bb_instructions) scheduled /\
   EVERY (from_block bb.bb_instructions) targetpost` by metis_tac[APPEND_ASSOC, APPEND] >>
  drule_all inv_ftrace_original_representatives >> strip_tac >>
  rename1 `inv_ev_ftrace orc p d ctx originals s0 sT` >>
  qpat_assum `EVERY (from_block _) targetpost`
    (mp_tac o MATCH_MP inv_from_block_representatives) >> strip_tac >>
  rename1 `MAP (\i. i.inst_id) later = MAP (\i. i.inst_id) targetpost` >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[dft_fn_rel_def, wf_fn_block_inst_ids_distinct] >>
  `PERM (originals ++ obs::later) (srcpre ++ obs::srcpost)` by
    (irule inv_original_ids_perm >> conj_tac
     >- (qexists_tac `bb.bb_instructions` >>
         fs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
     asm_rewrite_tac[MAP_APPEND, MAP] >>
     metis_tac[APPEND_ASSOC, APPEND]) >>
  `ALL_DISTINCT (srcpre ++ obs::srcpost)` by
    metis_tac[dft_remaining_inv_def] >>
  `MAP (\i. i.inst_id) bb'.bb_instructions =
    MAP (\i. i.inst_id) pseudos ++ MAP (\i. i.inst_id) (originals ++ obs::later)` by
    (asm_rewrite_tac[MAP_APPEND, MAP] >> metis_tac[APPEND_ASSOC, APPEND]) >>
  qpat_x_assum `!x y. _` kall_tac >>
  qpat_x_assum `!x y. _` kall_tac >>
  irule inv_lookup_normalized_observation >>
  simp[] >> qexists_tac `bb'` >> qexists_tac `originals` >>
  goal_assum (drule_at Any) >> simp[MAP_APPEND] >>
  metis_tac[]
QED
