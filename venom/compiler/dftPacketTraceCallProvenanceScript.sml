Theory dftPacketTraceCallProvenance
Ancestors
  dftGasFromListTraceNames dftGasFromListTraceDefs venomExecSemantics
  venomInst list rich_list arithmetic

Theorem frame_below_cons_cases[local]:
  !P a site call.
    frame_below (call::P) (site::a) ==>
    (a = P /\ site = call) \/ frame_below (call::P) a
Proof
  simp[frame_below_def] >> rpt strip_tac >>
  Cases_on `extra` >> gvs[] >> metis_tac[]
QED

Theorem native_trace_call_provenance:
  (!P D fuel C f head s. !a e cid d id fn i t.
    MEM (((e,cid)::a,d,id),fn,i,t) (trace_step P D fuel C f head s) /\
    frame_below ((D,head.inst_id)::P) a ==>
    ?parent c b0.
      MEM ((a,e,cid),parent,c,b0) (trace_step P D fuel C f head s) /\
      c.inst_id = cid /\ c.inst_opcode = INVOKE /\ e <= D + fuel /\
      MEM (((e,cid)::a,d,id),fn,i,t)
        (trace_step a e (D + fuel - e) C parent c b0)) /\
  (!P D fuel C f bb s. !a e cid d id fn i t.
    MEM (((e,cid)::a,d,id),fn,i,t) (trace_block P D fuel C f bb s) /\
    frame_below P a ==>
    ?parent c b0.
      MEM ((a,e,cid),parent,c,b0) (trace_block P D fuel C f bb s) /\
      c.inst_id = cid /\ c.inst_opcode = INVOKE /\ e <= D + fuel /\
      MEM (((e,cid)::a,d,id),fn,i,t)
        (trace_step a e (D + fuel - e) C parent c b0)) /\
  (!P D fuel C f s. !a e cid d id fn i t.
    MEM (((e,cid)::a,d,id),fn,i,t) (trace_blocks P D fuel C f s) /\
    frame_below P a ==>
    ?parent c b0.
      MEM ((a,e,cid),parent,c,b0) (trace_blocks P D fuel C f s) /\
      c.inst_id = cid /\ c.inst_opcode = INVOKE /\ e <= D + fuel /\
      MEM (((e,cid)::a,d,id),fn,i,t)
        (trace_step a e (D + fuel - e) C parent c b0))
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume native_trace_call_provenance[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `head.inst_opcode = INVOKE` >> gvs[cj 1 trace_defs] >>
  Cases_on `decode_invoke head` >> gvs[] >>
  rename1 `decode_invoke head = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 C.ctx_functions` >> gvs[] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands pair1 s` >> gvs[] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >> gvs[] >>
  first_x_assum irule >> metis_tac[]
QED

Resume native_trace_call_provenance[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `MEM _ _` mp_tac >> simp[Once (cj 2 trace_defs)]) >>
  rename1 `get_instruction _ _ = SOME head` >>
  drule_then assume_tac trace_block_visit >>
  `P <> (e,cid)::a` by
    (gvs[frame_below_def] >> strip_tac >>
     `LENGTH P = LENGTH ((e,cid)::(extra ++ P))` by metis_tac[] >> gvs[]) >>
  Cases_on `MEM (((e,cid)::a,d,id),fn,i,t) (trace_step P D fuel C f head s)`
  >- (mp_tac (cj 1 trace_regions) >> simp[EVERY_MEM] >>
      disch_then drule >> simp[] >> strip_tac >>
      drule frame_below_cons_cases >> strip_tac
      >- (gvs[] >> qexistsl_tac [`f`, `head`, `s`] >> simp[] >>
          Cases_on `head.inst_opcode = INVOKE` >> simp[] >>
          gvs[trace_step_noninvoke]) >>
      qpat_x_assum `!head'. _` (qspec_then `head` mp_tac) >>
      simp[] >> disch_then drule_all >>
      strip_tac >> qexistsl_tac [`parent`, `c`, `b0`] >> simp[]) >>
  Cases_on `step_inst fuel C head s` >> gvs[] >>
  rename1 `step_inst _ _ _ _ = OK post` >>
  Cases_on `is_terminator head.inst_opcode` >> gvs[] >>
  qpat_x_assum `!inst s''. _` drule_all >>
  strip_tac >> qexistsl_tac [`parent`, `c`, `b0`] >> simp[]
QED

Resume native_trace_call_provenance[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  FAIL_TAC "blocks"
QED

Finalise native_trace_call_provenance
