Theory dftGasInvTerminalPrefix
Ancestors
  dftGasInvMemoryObservation dftGasInvExtraction dftGasInvFlexibleTrace
  dftGasInvPrefixRun dftGasInvCrossingProbe dftRunRel dftScheduleOrder
  dftStructural dftCorrectness dftSsaPreserve dftWf venomWf venomInst
  venomExecSemantics venomState list rich_list sorting

Theorem inv_terminal_suffix_empty:
  bb_well_formed bb /\ bb.bb_instructions = pre ++ inst::post /\
  is_terminator inst.inst_opcode ==> post = []
Proof
  strip_tac >>
  `LENGTH pre = PRE (LENGTH bb.bb_instructions)` by
    (qpat_x_assum `bb_well_formed bb` mp_tac >>
     pure_rewrite_tac[bb_well_formed_def] >> strip_tac >>
     qpat_x_assum `!i. _ /\ _ ==> _` (qspec_then `LENGTH pre` mp_tac) >>
     simp[EL_APPEND_EQN]) >>
  Cases_on `post` >> gvs[]
QED

Theorem inv_lookup_dret_prefix:
  dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks /\
  lookup_block name fn.fn_blocks = SOME bb /\
  lookup_block name fn'.fn_blocks = SOME bb' /\
  bb.bb_instructions = pseudos ++ sourcebody /\
  EVERY (\i. is_pseudo i.inst_opcode) pseudos /\
  EVERY (\i. ~is_pseudo i.inst_opcode) sourcebody /\
  EVERY inst_shape_ok bb.bb_instructions /\
  bb'.bb_instructions = pseudos ++ (scheduled ++ inst::targetpost) /\
  inst.inst_opcode = DRET /\ s0.vs_inst_idx = LENGTH pseudos /\
  inv_ev_ftrace orc p d ctx scheduled s0 t ==>
  ?srcpre. sourcebody = srcpre ++ [inst] /\
    inv_ev_prefix orc p d ctx bb (LENGTH srcpre) s0 t /\
    t.vs_inst_idx = LENGTH pseudos + LENGTH srcpre
Proof
  strip_tac >>
  `FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions = pseudos /\
   FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions = sourcebody` by
    (`FILTER (\i. is_pseudo i.inst_opcode) pseudos = pseudos /\
      FILTER (\i. ~is_pseudo i.inst_opcode) pseudos = [] /\
      FILTER (\i. is_pseudo i.inst_opcode) sourcebody = [] /\
      FILTER (\i. ~is_pseudo i.inst_opcode) sourcebody = sourcebody` by
       (simp[FILTER_EQ_ID, FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
     asm_rewrite_tac[FILTER_APPEND_DISTRIB, APPEND_NIL, APPEND]) >>
  drule_all dft_fn_rel_lookup_order >> strip_tac >>
  qpat_x_assum `dft_block_rel _ _` mp_tac >>
  simp[dft_block_rel_def] >> strip_tac >> gvs[] >>
  `EVERY (from_block bb.bb_instructions) scheduled /\
   EVERY (from_block bb.bb_instructions) targetpost /\
   from_block bb.bb_instructions inst` by metis_tac[APPEND_ASSOC, APPEND] >>
  `MEM inst bb.bb_instructions` by
    (irule inv_memory_observation_original >> simp[inv_memory_observation_def]) >>
  `MEM inst sourcebody` by
    (fs[EVERY_MEM] >> metis_tac[MEM_APPEND, is_pseudo_def]) >>
  `?srcpre srcpost. sourcebody = srcpre ++ inst::srcpost` by metis_tac[MEM_SPLIT] >>
  `bb_well_formed bb` by fs[dft_fn_rel_def, wf_function_def, EVERY_MEM] >>
  `srcpost = []` by
    (irule inv_terminal_suffix_empty >> qexistsl_tac [`bb`, `inst`, `pseudos ++ srcpre`] >>
     simp[is_terminator_def, APPEND_ASSOC]) >>
  gvs[] >>
  drule_all inv_ftrace_original_representatives >> strip_tac >>
  rename1 `inv_ev_ftrace orc p d ctx originals s0 t` >>
  qpat_assum `EVERY (from_block _) targetpost`
    (mp_tac o MATCH_MP inv_from_block_representatives) >> strip_tac >>
  rename1 `MAP (\i. i.inst_id) later = MAP (\i. i.inst_id) targetpost` >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[dft_fn_rel_def, wf_fn_block_inst_ids_distinct] >>
  `PERM (originals ++ inst::later) (srcpre ++ [inst])` by
    (irule inv_original_ids_perm >> conj_tac
     >- (qexists_tac `bb.bb_instructions` >>
         fs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
     asm_rewrite_tac[MAP_APPEND, MAP] >>
     metis_tac[APPEND_ASSOC, APPEND]) >>
  `ALL_DISTINCT bb.bb_instructions` by
    (qpat_assum `ALL_DISTINCT (MAP _ _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[ALL_DISTINCT_MAP]) >>
  `ALL_DISTINCT (srcpre ++ [inst])` by
    (qpat_x_assum `ALL_DISTINCT bb.bb_instructions` mp_tac >>
     simp[ALL_DISTINCT_APPEND]) >>
  `MAP (\i. i.inst_id) bb'.bb_instructions =
    MAP (\i. i.inst_id) pseudos ++ MAP (\i. i.inst_id) (originals ++ inst::later)` by
    (asm_rewrite_tac[MAP_APPEND, MAP] >> metis_tac[APPEND_ASSOC, APPEND]) >>
  qpat_x_assum `!x y. _` kall_tac >>
  qpat_x_assum `!x y. _` kall_tac >>
  `EVERY (\x. inst_shape_ok x /\ ~is_terminator x.inst_opcode /\
      ~dft_must_order x inst) (FILTER (\i. ~MEM i originals) srcpre)` by
    (irule inv_lookup_missing_predecessors >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`bb`, `fn`, `fn'`, `name`, `[]`] >>
     simp[APPEND_ASSOC]) >>
  `FILTER (\i. ~MEM i originals) srcpre = []` by
    (qpat_x_assum `EVERY _ (FILTER _ srcpre)` mp_tac >>
     Cases_on `FILTER (\i. ~MEM i originals) srcpre` >>
     simp[dft_must_order_def, is_terminator_def]) >>
  `inv_ev_ftrace orc p d ctx srcpre s0 t` by
    (irule (SRULE [] (Q.INST [`srcpost` |-> `[]`] inv_lookup_completed_sort)) >>
     simp[] >> goal_assum (drule_at (Pat `PERM _ _`)) >>
     goal_assum (drule_at (Pat `dft_fn_rel _ _`)) >>
     goal_assum (drule_at (Pat `lookup_block _ fn.fn_blocks = _`)) >>
     goal_assum (drule_at (Pat `lookup_block _ fn'.fn_blocks = _`)) >>
     qexists_tac `pseudos` >> simp[APPEND_ASSOC]) >>
  conj_tac
  >- (`inv_ev_ftrace orc p d ctx srcpre s0 t <=>
        inv_ev_prefix orc p d ctx bb (LENGTH srcpre) s0 t` by
        (irule inv_ev_ftrace_slice >> qexistsl_tac [`pseudos`, `[inst]`] >> simp[]) >>
      metis_tac[]) >>
  metis_tac[inv_ev_ftrace_idx]
QED
