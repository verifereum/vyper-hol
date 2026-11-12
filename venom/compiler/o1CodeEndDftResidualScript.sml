Theory o1CodeEndDftResidual
Ancestors
  o1CodeEndDftCallFrame dftGasInvExtraction dftGasInvInversion
  dftGasInvFlexibleTrace dftGasInvResidualTrace dftGasInvSSAProbe
  dftRunRel dftScheduleOrder dftStructural dftSsaPreserve
  venomInst venomState list rich_list sorting

Theorem code_end_dft_replay_fprefix_operands:
  !pre s t.
    EVERY (\x. inst_wf x /\ ~is_pseudo x.inst_opcode /\
      ~is_terminator x.inst_opcode /\ ~dft_must_order x obs) pre /\
    inv_ev_ftrace orc p d ctx pre s t ==>
    !op. MEM op obs.inst_operands ==> eval_operand op t = eval_operand op s
Proof
  Induct >> simp[inv_ev_ftrace_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all code_end_dft_crossing_operand_frame >> metis_tac[]
QED

(* The completion premise asserts success, not totality of skipped instructions.
   In particular each crossed INVOKE may use its own successful fuel. *)
Theorem code_end_lookup_normalized_observation:
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
  (?u. inv_ev_ftrace orc p d ctx
    (FILTER (\i. ~MEM i consumed) srcpre) sT u) ==>
  ?sS. inv_ev_prefix orc p d ctx bb (LENGTH srcpre) s0 sS /\
    sS.vs_inst_idx = LENGTH pseudos + LENGTH srcpre /\
    (!op. MEM op obs.inst_operands ==> eval_operand op sS = eval_operand op sT) /\
    sS.vs_initial_fmp = sT.vs_initial_fmp
Proof
  strip_tac >>
  drule_all inv_lookup_block_contract >> strip_tac >>
  drule_all inv_lookup_missing_predecessors >> strip_tac >>
  `EVERY (\x. inst_wf x /\ ~is_pseudo x.inst_opcode /\
     ~is_terminator x.inst_opcode /\ ~dft_must_order x obs)
     (FILTER (\i. ~MEM i consumed) srcpre)` by
    (fs[EVERY_MEM, MEM_FILTER] >> metis_tac[MEM_APPEND, MEM]) >>
  `!op. MEM op obs.inst_operands ==>
      eval_operand op u = eval_operand op sT` by
    metis_tac[code_end_dft_replay_fprefix_operands] >>
  `inv_ev_ftrace orc p d ctx
     (consumed ++ FILTER (\i. ~MEM i consumed) srcpre) s0 u` by
    metis_tac[inv_ev_ftrace_append] >>
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
    (qspecl_then [`srcpre`, `pseudos`, `s0`, `sS`] mp_tac
       (Q.INST [`b` |-> `obs::srcpost`] inv_ev_ftrace_slice) >>
     simp[APPEND_ASSOC]) >>
  qpat_assum `inv_ev_ftrace _ _ _ _ srcpre s0 sS`
    (mp_tac o MATCH_MP inv_ev_ftrace_idx) >>
  simp[] >> metis_tac[inv_ev_ftrace_initial_fmp]
QED
