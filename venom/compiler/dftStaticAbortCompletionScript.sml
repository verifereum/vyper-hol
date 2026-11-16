Theory dftStaticAbortCompletion
Ancestors
  dftGasInvExtraction dftGasInvPairedHistory dftGasInvPairedPrefix
  dftGasInvInversion dftSsaPreserve sorting
  dftStaticReachAvailability dftGasInvSSAProbe dftGasInvPrefixReach
  dftGasInvMemoryObservation staticShadowEventReachable dftGasToListReachBoundary
  dftGasInvTerminalReach
  dftGasInvFlexibleTrace dftGasInvResidualTrace dftGasInvOracleFrame
  dftGasOracleDefs dftRunRel dftScheduleOrder dftStructural dftDefs dftWf
  o1PassContract unitShapeDefs venomExecSemantics venomInst venomState
  venomWf venomExecProofs contextCodegenRel list rich_list option

Theorem inv_reached_static_write_fails:
  s.vs_call_ctx.cc_static /\ MEM x.inst_opcode [SSTORE; TSTORE; LOG] /\
  IS_SOME (eval_operands x.inst_operands s) ==>
  ev_step orc p d fuel ctx x s =
    Abort ExHalt_abort (halt_state (set_returndata [] s))
Proof
  strip_tac >> gvs[] >>
  simp[Once ev_step_def, Once step_inst_def, Once step_inst_base_def]
QED

Theorem inv_static_observation_normalized_setup:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C initial.vs_labels /\ o1_initial_state_ok initial /\
  initial.vs_fmp = initial.vs_initial_fmp /\ code_layout_valid initial /\
  initial.vs_call_ctx.cc_static /\
  ev_reachable orc initial C' p d fn' inst t /\
  inv_memory_observation inst.inst_opcode ==>
  ?fn s0 startinst bb bb' pseudos srcpre srcpost consumed later.
    MEM fn C.ctx_functions /\ fn' = dft_fn fn /\ dft_fn_rel fn fn' /\
    ev_reachable orc initial C p d fn startinst s0 /\
    lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block s0.vs_current_bb fn'.fn_blocks = SOME bb' /\
    s0.vs_current_bb = t.vs_current_bb /\ s0.vs_inst_idx = LENGTH pseudos /\
    s0.vs_call_ctx.cc_static /\ MEM bb fn.fn_blocks /\
    bb.bb_instructions = pseudos ++ (srcpre ++ inst::srcpost) /\
    EVERY inst_shape_ok bb.bb_instructions /\
    EVERY (\i. is_pseudo i.inst_opcode) pseudos /\
    EVERY (\i. ~is_pseudo i.inst_opcode) (srcpre ++ inst::srcpost) /\
    MAP (\i. i.inst_id) bb'.bb_instructions =
      MAP (\i. i.inst_id) pseudos ++ MAP (\i. i.inst_id) (consumed ++ inst::later) /\
    ALL_DISTINCT (srcpre ++ inst::srcpost) /\
    PERM (consumed ++ inst::later) (srcpre ++ inst::srcpost) /\
    dft_remaining_inv fn bb (srcpre ++ inst::srcpost) s0 /\
    inv_ev_ftrace orc p d C consumed s0 t /\
    t.vs_inst_idx = LENGTH pseudos + LENGTH consumed
Proof
  strip_tac >> drule inv_paired_history_static >> disch_then (qspec_then `C` mp_tac) >>
  simp[] >> strip_tac >>
  drule_all inv_paired_prefix_cut >> strip_tac
  >- metis_tac[inv_memory_observation_nonpseudo] >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions = pseudos /\
   FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions = sourcebody` by
    (`FILTER (\i. is_pseudo i.inst_opcode) pseudos = pseudos /\
      FILTER (\i. ~is_pseudo i.inst_opcode) pseudos = [] /\
      FILTER (\i. is_pseudo i.inst_opcode) sourcebody = [] /\
      FILTER (\i. ~is_pseudo i.inst_opcode) sourcebody = sourcebody` by
       (simp[FILTER_EQ_ID, FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
     asm_rewrite_tac[FILTER_APPEND_DISTRIB, APPEND_NIL, APPEND]) >>
  `from_block bb.bb_instructions inst` by
    (drule_all dft_fn_rel_lookup_order >> simp[dft_block_rel_def] >>
     strip_tac >> gvs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
  `MEM inst bb.bb_instructions` by metis_tac[inv_memory_observation_original] >>
  `MEM inst sourcebody` by
    (gvs[EVERY_MEM] >> metis_tac[MEM_APPEND, inv_memory_observation_nonpseudo]) >>
  `?srcpre srcpost. sourcebody = srcpre ++ inst::srcpost` by metis_tac[MEM_SPLIT] >>
  `EVERY inst_shape_ok bb.bb_instructions` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >>
     first_x_assum (drule_then assume_tac) >>
     fs[o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM, fn_insts_def] >>
     rpt strip_tac >> first_x_assum irule >>
     simp[fn_insts_blocks_MEM] >> qexists_tac `bb` >> simp[]) >>
  `s0.vs_call_ctx.cc_static` by metis_tac[static_shadow_ev_reachable] >>
  `dft_remaining_inv fn bb sourcebody s0` by
    (`s0.vs_inst_idx = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions)` by simp[] >>
     drule_all inv_ev_reachable_source_initialized_static >> simp[]) >>
  suspend "normalize"
QED

Resume inv_static_observation_normalized_setup[normalize]:
  drule_all dft_fn_rel_lookup_order >> strip_tac >>
  `EVERY (from_block bb.bb_instructions) scheduled /\
   EVERY (from_block bb.bb_instructions) targetpost` by
    (qpat_x_assum `dft_block_rel _ _` mp_tac >>
     simp[dft_block_rel_def] >> strip_tac >> gvs[] >>
     metis_tac[APPEND_ASSOC, APPEND]) >>
  drule_all inv_ftrace_original_representatives >> strip_tac >>
  rename1 `inv_ev_ftrace orc p d C originals s0 t` >>
  qpat_assum `EVERY (from_block _) targetpost`
    (mp_tac o MATCH_MP inv_from_block_representatives) >> strip_tac >>
  rename1 `MAP (\i. i.inst_id) later = MAP (\i. i.inst_id) targetpost` >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[dft_fn_rel_def, wf_fn_block_inst_ids_distinct] >>
  `PERM (originals ++ inst::later) (srcpre ++ inst::srcpost)` by
    (irule inv_original_ids_perm >> conj_tac
     >- (qexists_tac `bb.bb_instructions` >>
         fs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
     qpat_x_assum `dft_block_rel _ _` mp_tac >>
     simp[dft_block_rel_def] >> strip_tac >> gvs[] >>
     asm_rewrite_tac[MAP_APPEND, MAP] >> metis_tac[APPEND_ASSOC, APPEND]) >>
  `ALL_DISTINCT (srcpre ++ inst::srcpost)` by
    metis_tac[dft_remaining_inv_def] >>
  `MAP (\i. i.inst_id) bb'.bb_instructions =
    MAP (\i. i.inst_id) pseudos ++ MAP (\i. i.inst_id) (originals ++ inst::later)` by
    (asm_rewrite_tac[MAP_APPEND, MAP] >> metis_tac[APPEND_ASSOC, APPEND]) >>
  `s0.vs_current_bb = t.vs_current_bb` by metis_tac[lookup_block_label] >>
  `t.vs_inst_idx = LENGTH pseudos + LENGTH originals` by
    (drule inv_ev_ftrace_idx >> simp[]) >>
  qexistsl [`fn`, `s0`, `startinst`, `bb`, `bb'`, `pseudos`,
            `srcpre`, `srcpost`, `originals`, `later`] >> gvs[] >>
  metis_tac[APPEND_ASSOC, APPEND]
QED

Finalise inv_static_observation_normalized_setup

Theorem inv_static_normalized_source_completion:
  (!pre s fn bb rest y post orc p d fuel ctx.
    wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
    EVERY inst_wf bb.bb_instructions /\
    dft_remaining_inv fn bb (pre ++ rest ++ y::post) s /\
    EVERY (\x. ~MEM x.inst_opcode [SSTORE; TSTORE; LOG]) pre /\
    inv_memory_observation y.inst_opcode /\
    EVERY (\x. inst_shape_ok x /\ ~is_terminator x.inst_opcode /\
      ~dft_must_order x y) pre ==>
    ?t. inv_ev_trace orc p d fuel ctx pre s t /\
      dft_remaining_inv fn bb (rest ++ y::post) t /\
      (!op. MEM op y.inst_operands ==> eval_operand op t = eval_operand op s)) /\
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  bb.bb_instructions = pseudos ++ (srcpre ++ obs::srcpost) /\
  EVERY inst_shape_ok bb.bb_instructions /\
  EVERY (\i. ~is_pseudo i.inst_opcode) (srcpre ++ obs::srcpost) /\
  MAP (\i. i.inst_id) bb'.bb_instructions =
    MAP (\i. i.inst_id) pseudos ++ MAP (\i. i.inst_id) (consumed ++ obs::later) /\
  ALL_DISTINCT (srcpre ++ obs::srcpost) /\
  PERM (consumed ++ obs::later) (srcpre ++ obs::srcpost) /\
  fn' = dft_fn fn /\ EVERY (\i. is_pseudo i.inst_opcode) pseudos /\
  EVERY (\x. ~MEM x.inst_opcode [SSTORE; TSTORE; LOG]) consumed /\
  inv_memory_observation obs.inst_opcode /\
  s0.vs_inst_idx = LENGTH pseudos /\ s0.vs_call_ctx.cc_static /\
  dft_remaining_inv fn bb (srcpre ++ obs::srcpost) s0 /\
  inv_ev_ftrace orc p d ctx consumed s0 t ==>
  (?sS. inv_ev_prefix orc p d ctx bb (LENGTH srcpre) s0 sS /\
    sS.vs_inst_idx = LENGTH pseudos + LENGTH srcpre /\
    (!op. MEM op obs.inst_operands ==> eval_operand op sS = eval_operand op t) /\
    sS.vs_initial_fmp = t.vs_initial_fmp) \/
  (?a x0 b sX. srcpre = a ++ x0::b /\ ~MEM x0 consumed /\
    MEM x0.inst_opcode [SSTORE; TSTORE; LOG] /\
    inv_ev_prefix orc p d ctx bb (LENGTH a) s0 sX /\
    sX.vs_inst_idx = LENGTH pseudos + LENGTH a /\ sX.vs_call_ctx.cc_static /\
    dft_remaining_inv fn bb (x0::b ++ obs::srcpost) sX /\
    IS_SOME (eval_operands x0.inst_operands sX))
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
  `dft_remaining_inv fn bb
      (FILTER (\i. ~MEM i consumed) srcpre ++
       obs::FILTER (\i. ~MEM i consumed) srcpost) t` by
    (drule_all inv_ftrace_remaining >> simp[FILTER_APPEND_DISTRIB]) >>
  Cases_on `EVERY (\x. ~MEM x.inst_opcode [SSTORE; TSTORE; LOG]) srcpre`
  >- suspend "observation" >>
  suspend "write"
QED

Resume inv_static_normalized_source_completion[observation]:
  disj1_tac >>
  `?u. inv_ev_trace orc p d 0 ctx (FILTER (\i. ~MEM i consumed) srcpre) t u /\
       (!op. MEM op obs.inst_operands ==> eval_operand op u = eval_operand op t)` by
    (`EVERY (\x. ~MEM x.inst_opcode [SSTORE; TSTORE; LOG])
       (FILTER (\i. ~MEM i consumed) srcpre)` by
       (gvs[EVERY_MEM, MEM_FILTER] >> metis_tac[]) >>
     qpat_x_assum `!pre s fn bb rest y post orc p d fuel ctx. _`
       (qspecl_then [`FILTER (\i. ~MEM i consumed) srcpre`, `t`, `fn`, `bb`, `[]`] mp_tac) >>
     simp[] >> disch_then drule_all >> metis_tac[]) >>
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
    (irule (iffLR inv_ev_ftrace_slice) >> conj_tac
     >- (qexistsl [`pseudos`, `obs::srcpost`] >> simp[APPEND_ASSOC]) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `inv_ev_ftrace _ _ _ _ srcpre s0 sS`
    (mp_tac o MATCH_MP inv_ev_ftrace_idx) >> simp[] >>
  metis_tac[inv_ev_ftrace_initial_fmp, inv_ev_trace_ftrace]
QED

Resume inv_static_normalized_source_completion[write]:
  Cases_on `SPLITP (\x. MEM x.inst_opcode [SSTORE; TSTORE; LOG]) srcpre` >>
  rename1 `SPLITP _ srcpre = (a,r)` >>
  `srcpre = a ++ r` by metis_tac[SPLITP_JOIN] >>
  `EVERY (\x. ~MEM x.inst_opcode [SSTORE; TSTORE; LOG]) a /\
   (~NULL r ==> MEM (HD r).inst_opcode [SSTORE; TSTORE; LOG])` by
    (drule SPLITP_IMP >> simp[combinTheory.o_DEF]) >>
  Cases_on `r` >- gvs[EVERY_MEM, EXISTS_MEM, combinTheory.o_DEF] >>
  rename1 `srcpre = a ++ x0::b` >>
  `MEM x0.inst_opcode [SSTORE; TSTORE; LOG] /\ ~MEM x0 consumed` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\x. ~MEM x.inst_opcode [SSTORE; TSTORE; LOG])
     (FILTER (\i. ~MEM i consumed) a)` by
    (fs[EVERY_MEM, MEM_FILTER] >> metis_tac[]) >>
  `EVERY (\x. inst_shape_ok x /\ ~is_terminator x.inst_opcode /\
      ~dft_must_order x obs) (FILTER (\i. ~MEM i consumed) a)` by
    (fs[EVERY_MEM, MEM_FILTER] >> metis_tac[MEM_APPEND, MEM]) >>
  `dft_remaining_inv fn bb
     (FILTER (\i. ~MEM i consumed) a ++
      (x0::FILTER (\i. ~MEM i consumed) b) ++
      obs::FILTER (\i. ~MEM i consumed) srcpost) t` by
    (qpat_x_assum `dft_remaining_inv _ _ (FILTER _ srcpre ++ _) t` mp_tac >>
     simp[FILTER_APPEND_DISTRIB, APPEND_ASSOC]) >>
  `?u. inv_ev_trace orc p d 0 ctx (FILTER (\i. ~MEM i consumed) a) t u` by
    (qpat_x_assum `!pre s fn bb rest y post orc p d fuel ctx. _`
       (qspecl_then [`FILTER (\i. ~MEM i consumed) a`, `t`, `fn`, `bb`,
         `x0::FILTER (\i. ~MEM i consumed) b`] mp_tac) >>
     disch_then drule_all >>
     gvs[FILTER_APPEND_DISTRIB] >> metis_tac[]) >>
  `inv_ev_ftrace orc p d ctx
     (consumed ++ FILTER (\i. ~MEM i consumed) a) s0 u` by
    metis_tac[inv_ev_trace_ftrace, inv_ev_ftrace_append] >>
  `PERM (consumed ++ FILTER (\i. ~MEM i consumed) a)
     (a ++ FILTER (\i. MEM i consumed) (x0::b ++ obs::srcpost))` by
    (irule inv_completed_prefix_perm >>
     fs[APPEND_ASSOC, ALL_DISTINCT_APPEND, EVERY_MEM] >> metis_tac[]) >>
  `inv_ev_ftrace orc p d ctx
     (a ++ FILTER (\i. MEM i consumed) (x0::b ++ obs::srcpost)) s0 u` by
    (irule inv_ftrace_source_sort >> conj_tac
     >- (fs[ALL_DISTINCT_APPEND] >>
         simp[ALL_DISTINCT_APPEND, FILTER_ALL_DISTINCT, MEM_FILTER] >> metis_tac[]) >>
     qexists_tac `consumed ++ FILTER (\i. ~MEM i consumed) a` >> simp[] >>
     ntac 2 gen_tac >> strip_tac >> suspend "write_inversion") >>
  suspend "write_endpoint"
QED

Resume inv_static_normalized_source_completion[write_inversion]:
  `id_before (srcpre ++ obs::srcpost) x z` by
    (qpat_x_assum `id_before (a ++ _) x z` mp_tac >>
     simp[dftSsaPreserveTheory.id_before_append,
          dftSsaPreserveTheory.id_before_cons, MEM_FILTER] >>
     rpt (pop_assum kall_tac) >>
     strip_tac >- simp[]
     >- (drule inv_id_before_filter_reflect >>
         simp[dftSsaPreserveTheory.id_before_append,
              dftSsaPreserveTheory.id_before_cons] >> metis_tac[]) >>
     metis_tac[]) >>
  `id_before (consumed ++ FILTER (\i. ~MEM i consumed) srcpre) z x` by
    (qpat_x_assum `id_before (consumed ++ _) z x` mp_tac >>
     simp[FILTER_APPEND_DISTRIB,
          dftSsaPreserveTheory.id_before_append, MEM_FILTER] >>
     metis_tac[dftSsaPreserveTheory.id_before_append, MEM_APPEND]) >>
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
    (qpat_x_assum `EVERY (\i. ~is_pseudo i.inst_opcode) _` mp_tac >>
     qpat_x_assum `bb.bb_instructions = _` mp_tac >>
     qpat_x_assum `MEM x (srcpre ++ _)` mp_tac >>
     qpat_x_assum `MEM z (srcpre ++ _)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[EVERY_MEM, MEM_APPEND] >> metis_tac[]) >>
  drule_all inv_lookup_inversion_swap >> simp[]
QED

Resume inv_static_normalized_source_completion[write_endpoint]:
  qpat_x_assum `inv_ev_ftrace _ _ _ _ (a ++ _) s0 u` mp_tac >>
  simp[inv_ev_ftrace_append] >> strip_tac >>
  rename1 `inv_ev_ftrace orc p d ctx a s0 sX` >>
  `ALL_DISTINCT a /\ EVERY (\i. MEM i (srcpre ++ obs::srcpost)) a` by
    (fs[ALL_DISTINCT_APPEND, EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
  `FILTER (\i. ~MEM i a) (srcpre ++ obs::srcpost) = x0::b ++ obs::srcpost` by
    (qpat_x_assum `ALL_DISTINCT (srcpre ++ _)` mp_tac >>
     qpat_x_assum `srcpre = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     pure_asm_rewrite_tac[GSYM APPEND_ASSOC] >>
     qabbrev_tac `tail = x0::b ++ obs::srcpost` >>
     `ALL_DISTINCT (a ++ tail) ==>
       FILTER (\i. ~MEM i a) (a ++ tail) = tail` suffices_by
       simp[Abbr `tail`] >>
     simp[ALL_DISTINCT_APPEND] >> strip_tac >>
     `FILTER (\i. ~MEM i a) a = []` by simp[FILTER_EQ_NIL, EVERY_MEM] >>
     `FILTER (\i. ~MEM i a) tail = tail` by
       (simp[FILTER_EQ_ID, EVERY_MEM] >> metis_tac[]) >>
     simp[FILTER_APPEND_DISTRIB]) >>
  `dft_remaining_inv fn bb (x0::b ++ obs::srcpost) sX` by
    (drule_all inv_ftrace_remaining >> simp[]) >>
  `~is_terminator x0.inst_opcode /\ x0.inst_opcode <> INVOKE /\
   x0.inst_opcode <> CODECOPY` by
    (qpat_x_assum `MEM x0.inst_opcode _` mp_tac >>
     simp[is_terminator_def] >> strip_tac >> simp[is_terminator_def]) >>
  `IS_SOME (eval_operands x0.inst_operands sX)` by
    (simp[eval_operands_IS_SOME_EVERY, EVERY_MEM] >>
     qpat_x_assum `dft_remaining_inv fn bb (x0::b ++ _) sX`
       (assume_tac o REWRITE_RULE [APPEND]) >>
     (metisTools.METIS_TAC [dftGasInvSSAProbeTheory.inv_remaining_head_operands])) >>
  `inv_ev_prefix orc p d ctx bb (LENGTH a) s0 sX` by
    (irule (iffLR inv_ev_ftrace_slice) >> conj_tac
     >- (qexistsl [`pseudos`, `x0::b ++ obs::srcpost`] >> simp[APPEND_ASSOC]) >>
     first_assum ACCEPT_TAC) >>
  `sX.vs_inst_idx = LENGTH pseudos + LENGTH a` by
    metis_tac[inv_ev_ftrace_idx] >>
  `sX.vs_call_ctx.cc_static` by metis_tac[inv_ftrace_call_ctx] >>
  disj2_tac >> qexistsl [`a`, `x0`, `b`, `sX`] >>
  simp[] >> conj_tac
  >- (qpat_x_assum `MEM x0.inst_opcode _` mp_tac >> simp[]) >>
  qpat_x_assum `dft_remaining_inv fn bb (x0::b ++ _) sX` mp_tac >>
  simp[APPEND]
QED

Finalise inv_static_normalized_source_completion

Theorem inv_static_observation_source_completion:
  (!pre s fn bb rest y post orc p d fuel ctx.
    wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
    EVERY inst_wf bb.bb_instructions /\
    dft_remaining_inv fn bb (pre ++ rest ++ y::post) s /\
    EVERY (\x. ~MEM x.inst_opcode [SSTORE; TSTORE; LOG]) pre /\
    inv_memory_observation y.inst_opcode /\
    EVERY (\x. inst_shape_ok x /\ ~is_terminator x.inst_opcode /\
      ~dft_must_order x y) pre ==>
    ?t. inv_ev_trace orc p d fuel ctx pre s t /\
      dft_remaining_inv fn bb (rest ++ y::post) t /\
      (!op. MEM op y.inst_operands ==> eval_operand op t = eval_operand op s)) /\
  (!xs s t orc p d ctx. s.vs_call_ctx.cc_static /\
    inv_ev_ftrace orc p d ctx xs s t ==>
    EVERY (\x. ~MEM x.inst_opcode [SSTORE; TSTORE; LOG]) xs) /\
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C initial.vs_labels /\ o1_initial_state_ok initial /\
  initial.vs_fmp = initial.vs_initial_fmp /\ code_layout_valid initial /\
  initial.vs_call_ctx.cc_static /\
  ev_reachable orc initial C' p d fn' inst t /\
  inv_memory_observation inst.inst_opcode /\ inst.inst_opcode <> DRET ==>
  ?fn s0 startinst bb bb' pseudos srcpre srcpost consumed later.
    MEM fn C.ctx_functions /\ fn' = dft_fn fn /\ dft_fn_rel fn fn' /\
    ev_reachable orc initial C p d fn startinst s0 /\
    lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block s0.vs_current_bb fn'.fn_blocks = SOME bb' /\
    s0.vs_current_bb = t.vs_current_bb /\ s0.vs_inst_idx = LENGTH pseudos /\
    s0.vs_call_ctx.cc_static /\ MEM bb fn.fn_blocks /\
    bb.bb_instructions = pseudos ++ (srcpre ++ inst::srcpost) /\
    EVERY inst_shape_ok bb.bb_instructions /\
    EVERY (\i. is_pseudo i.inst_opcode) pseudos /\
    EVERY (\i. ~is_pseudo i.inst_opcode) (srcpre ++ inst::srcpost) /\
    MAP (\i. i.inst_id) bb'.bb_instructions =
      MAP (\i. i.inst_id) pseudos ++ MAP (\i. i.inst_id) (consumed ++ inst::later) /\
    ALL_DISTINCT (srcpre ++ inst::srcpost) /\
    PERM (consumed ++ inst::later) (srcpre ++ inst::srcpost) /\
    EVERY (\x. ~MEM x.inst_opcode [SSTORE; TSTORE; LOG]) consumed /\
    dft_remaining_inv fn bb (srcpre ++ inst::srcpost) s0 /\
    inv_ev_ftrace orc p d C consumed s0 t /\
    t.vs_inst_idx = LENGTH pseudos + LENGTH consumed /\
    ((?sS. inv_ev_prefix orc p d C bb (LENGTH srcpre) s0 sS /\
      sS.vs_inst_idx = LENGTH pseudos + LENGTH srcpre /\
      (!op. MEM op inst.inst_operands ==> eval_operand op sS = eval_operand op t) /\
      sS.vs_initial_fmp = t.vs_initial_fmp /\
      ev_reachable orc initial C p d fn inst sS /\ active_inst fn inst sS) \/
     (?a x0 b sX. srcpre = a ++ x0::b /\ ~MEM x0 consumed /\
      MEM x0.inst_opcode [SSTORE; TSTORE; LOG] /\
      inv_ev_prefix orc p d C bb (LENGTH a) s0 sX /\
      sX.vs_inst_idx = LENGTH pseudos + LENGTH a /\ sX.vs_call_ctx.cc_static /\
      dft_remaining_inv fn bb (x0::b ++ inst::srcpost) sX /\
      IS_SOME (eval_operands x0.inst_operands sX) /\
      ev_reachable orc initial C p d fn x0 sX /\ active_inst fn x0 sX /\
      (!fuel. ev_step orc p d fuel C x0 sX =
        Abort ExHalt_abort (halt_state (set_returndata [] sX)))))
Proof
  strip_tac >> drule_all inv_static_observation_normalized_setup >> strip_tac >>
  `EVERY (\x. ~MEM x.inst_opcode [SSTORE; TSTORE; LOG]) consumed` by
    (first_x_assum irule >> goal_assum (drule_at Any) >> simp[]) >>
  qexistsl [`fn`, `s0`, `startinst`, `bb`, `bb'`, `pseudos`,
            `srcpre`, `srcpost`, `consumed`, `later`] >>
  asm_rewrite_tac[] >>
  `active_inst fn startinst s0` by
    (qpat_x_assum `ev_reachable _ _ C _ _ fn startinst s0` mp_tac >>
     simp[Once ev_reachable_cases] >> metis_tac[]) >>
  `ALL_DISTINCT (fn_labels fn)` by
    metis_tac[dft_fn_rel_def, wf_function_def] >>
  `get_instruction bb s0.vs_inst_idx = SOME startinst` by
    (drule_all active_inst_lookup_distinct >> strip_tac >> gvs[]) >>
  `bb.bb_label = s0.vs_current_bb` by metis_tac[lookup_block_label] >>
  drule_all inv_static_normalized_source_completion >> strip_tac
  >- suspend "observation_reach" >>
  suspend "write_reach"
QED

Resume inv_static_observation_source_completion[observation_reach]:
  `inv_ev_ftrace orc p d C srcpre s0 sS` by
    (irule (iffRL inv_ev_ftrace_slice) >>
     qexistsl [`pseudos`, `inst::srcpost`, `bb`] >> simp[APPEND_ASSOC]) >>
  `sS.vs_current_bb = s0.vs_current_bb` by
    metis_tac[inv_ev_ftrace_current_bb] >>
  `get_instruction bb sS.vs_inst_idx = SOME inst` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `active_inst fn inst sS` by
    (simp[active_inst_def] >> qexists_tac `bb` >> simp[EL_APPEND_EQN]) >>
  `ev_reachable orc initial C p d fn inst sS` by
    metis_tac[inv_ev_prefix_reachable] >>
  disj1_tac >> qexists_tac `sS` >> simp[]
QED

Resume inv_static_observation_source_completion[write_reach]:
  `inv_ev_ftrace orc p d C a s0 sX` by
    (irule (iffRL inv_ev_ftrace_slice) >>
     qexistsl [`pseudos`, `x0::b ++ inst::srcpost`, `bb`] >>
     simp[APPEND_ASSOC, APPEND]) >>
  `sX.vs_current_bb = s0.vs_current_bb` by
    metis_tac[inv_ev_ftrace_current_bb] >>
  `get_instruction bb sX.vs_inst_idx = SOME x0` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `active_inst fn x0 sX` by
    (simp[active_inst_def] >> qexists_tac `bb` >> simp[EL_APPEND_EQN]) >>
  `ev_reachable orc initial C p d fn x0 sX` by
    metis_tac[inv_ev_prefix_reachable] >>
  `!fuel. ev_step orc p d fuel C x0 sX =
     Abort ExHalt_abort (halt_state (set_returndata [] sX))` by
    (gen_tac >> irule inv_reached_static_write_fails >> simp[]) >>
  disj2_tac >> qexistsl [`a`, `x0`, `b`, `sX`] >>
  asm_rewrite_tac[]
QED

Finalise inv_static_observation_source_completion
