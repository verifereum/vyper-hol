Theory dftPacketFreshSingletonObservation
Ancestors
  dftPacketRowAlignment dftPacketFreshCut dftPacketFreshRow
  dftPacketFillingBoundary dftPacketObservationSuccess dftPacketSuccessorObservation
  dftGasFromListReplayBoundary dftGasFromListTraceDefs dftRunRel dftWf
  venomExecSemantics venomInst venomState list rich_list alist arithmetic

Theorem fresh_observation_keys_distinct[local]:
  !xs b e. ALL_DISTINCT (MAP (\i. i.inst_id) xs) ==>
    ALL_DISTINCT (FLAT (MAP (\i.
      if i.inst_opcode = GAS then [(b,e,i.inst_id)] else []) xs))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = GAS` >> simp[] >>
  gvs[MEM_FLAT,MEM_MAP] >> gen_tac >> CCONTR_TAC >> gvs[] >>
  Cases_on `i.inst_opcode = GAS` >> gvs[]
QED

Theorem dft_packet_fresh_singleton_observation:
  !F. row_eval = (\F C owner (bb,e,z) s.
    case eval_phis s bb.bb_instructions of
      OK sp =>
       (gas_events_block (F-e) C owner
         (bb with bb_instructions :=
           TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
        FOLDR (dft_exec_cons (F-e) C) OK z
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    | other => ([],other)) /\
  plan_eval = (\F C owner plan entry.
    FOLDL (\(es,r) row.
      case r of
        OK s => (es ++ FST (row_eval F C owner row s), SND (row_eval F C owner row s))
      | other => (es,other)) ([],OK entry) plan) /\
  LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  ctf = dft_fn csf /\ dft_fn_rel csf ctf /\
  cb.bb_instructions = cps ++ cxs /\
  cbt.bb_instructions = cps ++ cys /\
  EVERY (\i. is_pseudo i.inst_opcode) cps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) cxs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) cys /\
  MEM cb csf.fn_blocks /\
  lookup_block child_entry.vs_current_bb csf.fn_blocks = SOME cb /\
  lookup_block child_entry.vs_current_bb ctf.fn_blocks = SOME cbt /\
  EVERY inst_shape_ok cb.bb_instructions /\
  eval_phis child_entry (cps ++ cys) = OK csp /\
  FOLDR (dft_exec_cons g C8) OK
    (DROP (phi_prefix_length (cps ++ cys)) cps)
    (csp with vs_inst_idx := phi_prefix_length (cps ++ cys)) = OK be /\
  be.vs_inst_idx = LENGTH cps /\ dft_remaining_inv csf cb cxs be /\
  q < LENGTH cxs /\ cys <> [] /\ ci = HD cys /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) (TAKE q cxs) /\
  z = DROP (phi_prefix_length cb.bb_instructions) cps ++ TAKE q cxs /\
  cm = GENLIST (\r. if (EL r cxs).inst_opcode = GAS then [NONE] else []) (LENGTH cxs) /\
  ce = GENLIST (\r. if (EL r cxs).inst_opcode = GAS then [(csf.fn_name,(EL r cxs).inst_id)] else []) (LENGTH cxs) /\
  ck = GENLIST (\r. if (EL r cxs).inst_opcode = GAS then [((b:(num # num) list),SUC d,(EL r cxs).inst_id)] else []) (LENGTH cxs) /\
  Mc = FLAT (TAKE q cm) /\ SUC d <= F /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mc gs_child /\
  plan_eval F C7 csf.fn_name [(cb,SUC d,z)]
    (child_entry with vs_gas_readings := gs_child ++ tail) = (events,OK u) /\
  inv_memory_observation ci.inst_opcode /\ EL q cxs = ci ==>
  (!op. MEM op ci.inst_operands ==> eval_operand op u = eval_operand op be) /\
  u.vs_initial_fmp = be.vs_initial_fmp
Proof
  qx_gen_tac `fuel` >> strip_tac >>
  `FOLDR (dft_exec_cons (fuel-SUC d) C7) OK (TAKE q cxs)
     (be with vs_gas_readings := gs_child ++ tail) = OK u` by
    suspend "source_success" >>
  `trace_gas (trace_block b (SUC d) (fuel-SUC d) C7 csf
     (cb with bb_instructions := TAKE (LENGTH cps + q) cb.bb_instructions)
     (be with vs_gas_readings := gs_child ++ tail)) =
       ZIP (FLAT (TAKE q ck),gs_child)` by suspend "source_zip" >>
  suspend "observation"
QED

Resume dft_packet_fresh_singleton_observation[source_success]:
  qpat_x_assum `plan_eval _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `plan_eval = _` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `row_eval = _` (fn th => rewrite_tac[th]) >>
  simp[] >> strip_tac >>
  irule dft_packet_row_body_success >> simp[] >>
  goal_assum (drule_at (Pat `FOLDR _ _ _ _ = OK be`)) >>
  goal_assum (drule_at (Pat `eval_phis _ _ = OK csp`)) >>
  simp[] >>
  qpat_x_assum `_ = (events,OK u)` mp_tac >>
  qpat_assum `cb.bb_instructions = _` (fn th => rewrite_tac[th]) >>
  Cases_on `eval_phis (child_entry with vs_gas_readings := gs_child ++ tail) (cps ++ cxs)` >>
  gvs[]
QED

Resume dft_packet_fresh_singleton_observation[source_zip]:
  `?kgss. gs_child = FLAT kgss /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q cm) kgss` by
    metis_tac[dft_packet_flat_filling_split] >>
  `q <= LENGTH cxs` by decide_tac >>
  drule_all dft_packet_fresh_row_replay >>
  (gvs[])
QED

Resume dft_packet_fresh_singleton_observation[observation]:
  `ALL_DISTINCT (MAP (\i. i.inst_id) (TAKE q cxs))` by
    (fs[dft_fn_rel_def] >> drule_all wf_fn_block_inst_ids_distinct >>
     simp[MAP_APPEND,ALL_DISTINCT_APPEND] >>
     metis_tac[MAP_TAKE,ALL_DISTINCT_TAKE]) >>
  `ALL_DISTINCT (FLAT (TAKE q ck))` by
    (simp[GENLIST_EL_MAP,GSYM MAP_TAKE] >>
     irule fresh_observation_keys_distinct >> simp[]) >>
  `LENGTH (FLAT (TAKE q ck)) = LENGTH gs_child` by
    (imp_res_tac LIST_REL_LENGTH >>
     gvs[GENLIST_EL_MAP,GSYM MAP_TAKE,LENGTH_FLAT,MAP_MAP_o,combinTheory.o_DEF,COND_RAND]) >>
  `trace_block b (SUC d) 0 C8 ctf
     (cbt with bb_instructions := TAKE (LENGTH cps) cbt.bb_instructions) be = []` by
    simp[Once trace_defs,get_instruction_def,LENGTH_TAKE] >>
  drule_at (Pat `trace_gas _ = _`) trace_agrees_lookup_fill >>
  disch_then (qspec_then `[]` mp_tac) >>
  FAIL_TAC "oracle"
QED

Finalise dft_packet_fresh_singleton_observation
