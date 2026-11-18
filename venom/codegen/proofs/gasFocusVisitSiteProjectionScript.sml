(* Ordered GAS sites of the native list trace at the ordinary collector's root. *)
Theory gasFocusVisitSiteProjection
Ancestors
  dftGasFromListTraceDefs dftGasFromListTracePrefix gasEvents gasEventsFuel
  venomExecSemantics venomInst list arithmetic

Theorem focus_visit_site_projection:
  (!p d fuel C fn i s.
     MAP (\(e,fn,i,s). (fn.fn_name,i.inst_id))
       (FILTER (\(e,fn,i,s). i.inst_opcode = GAS)
          (((p,d,i.inst_id),fn,i,s)::trace_step p d fuel C fn i s)) =
     gas_events_step fuel C fn.fn_name i s) /\
  (!p d fuel C fn bb s.
     MAP (\(e,fn,i,s). (fn.fn_name,i.inst_id))
       (FILTER (\(e,fn,i,s). i.inst_opcode = GAS)
          (trace_block p d fuel C fn bb s)) =
     gas_events_block fuel C fn.fn_name bb s) /\
  (!p d fuel C fn s.
     MAP (\(e,fn,i,s). (fn.fn_name,i.inst_id))
       (FILTER (\(e,fn,i,s). i.inst_opcode = GAS)
          (trace_blocks p d fuel C fn s)) =
     gas_events_blocks fuel C fn s)
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume focus_visit_site_projection[step]:
  rpt gen_tac >> strip_tac >>
  rename1 `trace_step p d fuel ctx fn inst s` >>
  simp[cj 1 trace_defs, gas_events_step_def] >>
  Cases_on `inst.inst_opcode = GAS` >> simp[] >>
  Cases_on `inst.inst_opcode = INVOKE` >> simp[] >>
  Cases_on `decode_invoke inst` >> simp[] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 ctx.ctx_functions` >> simp[] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands pair1 s` >> simp[] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >> simp[] >>
  metis_tac[]
QED

Resume focus_visit_site_projection[block]:
  rpt gen_tac >> strip_tac >>
  rename1 `trace_block p d fuel ctx fn bb s` >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[Once (cj 2 trace_defs), Once gas_events_block_def] >>
  rename1 `get_instruction _ _ = SOME inst` >>
  once_rewrite_tac[cj 2 trace_defs, gas_events_block_def] >> simp[] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[FILTER_APPEND_DISTRIB, MAP_APPEND] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[FILTER_APPEND_DISTRIB, MAP_APPEND] >>
  Cases_on `inst.inst_opcode = GAS` >> gvs[FILTER_APPEND_DISTRIB, MAP_APPEND]
QED

Resume focus_visit_site_projection[blocks]:
  rpt gen_tac >> strip_tac >>
  rename1 `trace_blocks p d fuel ctx fn s` >>
  Cases_on `fuel` >- simp[Once gas_events_blocks_def] >>
  rename1 `SUC k` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[Once (cj 3 trace_defs), Once gas_events_blocks_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  simp[Once (cj 3 trace_defs), Once gas_events_blocks_def] >>
  rename1 `eval_phis _ _ = OK sp` >>
  Cases_on `exec_block k ctx bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  simp[FILTER_APPEND_DISTRIB, MAP_APPEND] >>
  rename1 `exec_block _ _ _ _ = OK sn` >>
  Cases_on `sn.vs_halted` >> gvs[FILTER_APPEND_DISTRIB, MAP_APPEND]
QED

Finalise focus_visit_site_projection

(* The two fuels are extended independently to a common fuel. The suffix can
   be discarded from the site list only if the split trace is non-Error. *)
Theorem focus_rooted_visit_site_comparison:
  !p d low fuel high C fn s pre post.
    trace_blocks p d low C fn s = pre ++ post /\ low <= high /\ fuel <= high ==>
    ?later extra.
      trace_blocks p d high C fn s = pre ++ post ++ later /\
      gas_events_blocks high C fn s =
        MAP (\(e,fn,i,s). (fn.fn_name,i.inst_id))
          (FILTER (\(e,fn,i,s). i.inst_opcode = GAS) pre) ++
        MAP (\(e,fn,i,s). (fn.fn_name,i.inst_id))
          (FILTER (\(e,fn,i,s). i.inst_opcode = GAS) post) ++
        MAP (\(e,fn,i,s). (fn.fn_name,i.inst_id))
          (FILTER (\(e,fn,i,s). i.inst_opcode = GAS) later) /\
      gas_events_blocks high C fn s = gas_events_blocks fuel C fn s ++ extra /\
      ((!err. run_blocks low C fn s <> Error err) ==>
       gas_events_blocks high C fn s =
         MAP (\(e,fn,i,s). (fn.fn_name,i.inst_id))
           (FILTER (\(e,fn,i,s). i.inst_opcode = GAS) pre) ++
         MAP (\(e,fn,i,s). (fn.fn_name,i.inst_id))
           (FILTER (\(e,fn,i,s). i.inst_opcode = GAS) post))
Proof
  rpt strip_tac >>
  `?later. trace_blocks p d high C fn s = pre ++ post ++ later` by
    metis_tac[cj 3 trace_prefix, APPEND_ASSOC] >>
  `?extra. gas_events_blocks high C fn s = gas_events_blocks fuel C fn s ++ extra` by
    metis_tac[cj 3 gas_events_fuel_extension] >>
  qexistsl [`later`, `extra`] >> simp[] >> conj_tac
  >- metis_tac[cj 3 focus_visit_site_projection, FILTER_APPEND_DISTRIB, MAP_APPEND] >>
  strip_tac >>
  `gas_events_blocks high C fn s = gas_events_blocks low C fn s` by
    metis_tac[cj 3 gas_events_fuel_extension] >>
  metis_tac[cj 3 focus_visit_site_projection, FILTER_APPEND_DISTRIB, MAP_APPEND]
QED
