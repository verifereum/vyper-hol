Theory dftPacketCutExtension
Ancestors
  dftPacketNativeContinuation dftGasFromListReadings dftGasFromListTraceDefs
  rich_list

Theorem dft_packet_native_child_insert:
  !F C root_fn root_entry T b j a e sf c u nm ops csf args cs
    child_before visit child_after.
    T = trace_blocks [] 0 F C root_fn root_entry /\
    b = (e,c.inst_id)::a /\
    j < LENGTH T /\ EL j T = ((a,e,c.inst_id),sf,c,u) /\
    c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME csf /\
    eval_operands ops u = SOME args /\ setup_callee csf args u = SOME cs /\
    trace_blocks b e (F-e) C csf cs =
      child_before ++ [visit] ++ child_after ==>
    (?after. T = TAKE j T ++ [((a,e,c.inst_id),sf,c,u)] ++
      child_before ++ [visit] ++ after) /\
    trace_gas (TAKE j T ++ [((a,e,c.inst_id),sf,c,u)] ++ child_before) =
      trace_gas (TAKE j T) ++ trace_gas child_before /\
    (!K0 gs0 K1 gs1.
      trace_gas (TAKE j T) = ZIP (K0,gs0) /\
      trace_gas child_before = ZIP (K1,gs1) /\
      LENGTH K0 = LENGTH gs0 /\ LENGTH K1 = LENGTH gs1 ==>
      trace_gas (TAKE j T ++ [((a,e,c.inst_id),sf,c,u)] ++ child_before) =
        ZIP (K0 ++ K1,gs0 ++ gs1))
Proof
  rpt gen_tac >> strip_tac >>
  reverse conj_tac
  >- (simp[visit_gas_def] >> rpt strip_tac >> simp[GSYM ZIP_APPEND]) >>
  gvs[] >> drule_all native_trace_blocks_continuation >> strip_tac >>
  drule_then assume_tac trace_block_visit >>
  drule_all trace_step_invoke >> strip_tac >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `child_before ++ [visit] ++ child_after ++ caller_tail ++ rest` >>
  qexists_tac `child_after ++ caller_tail ++ rest` >>
  qpat_x_assum `DROP j _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `TAKE j rt` >>
  strip_tac >>
  qspecl_then [`j`,`rt`] mp_tac listTheory.TAKE_DROP >>
  pure_asm_rewrite_tac [GSYM APPEND_ASSOC,listTheory.APPEND] >>
  metis_tac[]
QED
