Theory dftPacketFreshSingletonNormalize
Ancestors
  dftPacketFreshChildOccurrence dftPacketNativeSlice dftGasToListReplay dftIndexedExec
  dftGasFromListTraceDefs gasEvents venomExecSemantics venomInst venomState
  stateEquiv list rich_list arithmetic

Theorem dft_packet_fresh_singleton_source_prefix:
  row_eval = (\F C owner (bb,e,z) s.
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
  bb.bb_instructions = ps ++ xs /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  eval_phis entry (ps ++ ys) = OK sp /\
  m = phi_prefix_length bb.bb_instructions /\
  k <= LENGTH (DROP m bb.bb_instructions) /\
  z = TAKE k (DROP m bb.bb_instructions) ==>
  !F C owner e readings.
    ?sp'. eval_phis (entry with vs_gas_readings := readings) bb.bb_instructions = OK sp' /\
      plan_eval F C owner [(bb,e,z)] (entry with vs_gas_readings := readings) =
        (gas_events_block (F-e) C owner
           (bb with bb_instructions := TAKE (m+k) bb.bb_instructions)
           (sp' with vs_inst_idx := m),
         FOLDR (dft_exec_cons (F-e) C) OK
           (TAKE k (DROP m bb.bb_instructions)) (sp' with vs_inst_idx := m))
Proof
  strip_tac >> rpt gen_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) xs /\
   EVERY (\i. i.inst_opcode <> PHI) ys` by
    (gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
     Cases_on `i.inst_opcode` >> gvs[is_pseudo_def]) >>
  gvs[dft_eval_phis_append] >>
  qspecl_then [`ps`,`entry`,`readings`] mp_tac replay_phis >>
  simp[residual_result_def] >>
  Cases_on `eval_phis (entry with vs_gas_readings := readings) ps` >>
  simp[lift_result_def] >> strip_tac >> gvs[] >>
  simp[GSYM TAKE_SUM]
QED

Theorem dft_packet_fresh_body_trace_prefix:
  bb.bb_instructions = ps ++ xs /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  m <= LENGTH ps /\ q <= LENGTH xs /\ s.vs_inst_idx = m /\
  FOLDR (dft_exec_cons f C) OK (DROP m ps) s = OK be ==>
  trace_gas (trace_block b e f C sf
    (bb with bb_instructions := TAKE (LENGTH ps+q) bb.bb_instructions) s) =
  trace_gas (trace_block b e f C sf
    (bb with bb_instructions := TAKE (LENGTH ps+q) bb.bb_instructions) be)
Proof
  strip_tac >> irule dft_packet_pseudo_prefix_trace_gas >>
  qexistsl [`DROP m ps`,`TAKE q xs`] >>
  simp[EVERY_DROP,TAKE_APPEND2,DROP_APPEND1]
QED

Theorem dft_packet_fresh_pseudo_trace_prefix:
  bb.bb_instructions = ps ++ xs /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  m <= l /\ l <= LENGTH ps /\ s.vs_inst_idx = m /\
  FOLDR (dft_exec_cons f C) OK (DROP m (TAKE l ps)) s = OK t ==>
  trace_gas (trace_block b e f C sf
    (bb with bb_instructions := TAKE l bb.bb_instructions) s) = []
Proof
  strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) ps` by
    (gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
     Cases_on `i.inst_opcode` >> gvs[is_pseudo_def,is_terminator_def]) >>
  `t.vs_inst_idx = l` by
    (qspecl_then [`l-m`,`s`,`t`] mp_tac
      (Q.INST [`bb` |-> `bb with bb_instructions := TAKE l ps`,
               `fuel` |-> `f`, `C` |-> `C`]
        (cj 1 native_trace_block_prefix_split)) >>
     gvs[DROP_TAKE,EVERY_DROP,EVERY_TAKE,TAKE_TAKE]) >>
  `trace_gas (trace_block b e f C sf
      (bb with bb_instructions := TAKE l bb.bb_instructions) s) =
   trace_gas (trace_block b e f C sf
      (bb with bb_instructions := TAKE l bb.bb_instructions) t)` by
    (irule dft_packet_pseudo_prefix_trace_gas >>
     qexistsl [`DROP m (TAKE l ps)`,`[]`] >>
     simp[TAKE_APPEND1,EVERY_DROP,EVERY_TAKE]) >>
  simp[Once trace_defs,get_instruction_def,LENGTH_TAKE,trace_gas_def]
QED
