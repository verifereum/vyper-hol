Theory dftGasFromListTraceLift
Ancestors
  dftGasFromListOpenTrace dftGasFromListTraceDefs dftGasFromListTracePrefix dftGasFromListTraceNames
  venomExecProofs venomInstProofs venomExecSemantics venomInst venomState list arithmetic

Theorem trace_cofinal_factor:
  (!p d n ctx fn inst s. !q h g i t.
    MEM ((q,h,i.inst_id),g,i,t) (trace_step p d n ctx fn inst s) ==>
    ?bb. lookup_block t.vs_current_bb g.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME i /\
      (!k b. ?m k' pre post. b <= m /\ k <= k' /\
        trace_step p d m ctx fn inst s =
          pre ++ open_trace q h k' ctx g bb t ++ post /\
        (q = (d,inst.inst_id)::p ==> post = []))) /\
  (!p d n ctx fn outer s. !q h g i t.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME outer /\
    MEM ((q,h,i.inst_id),g,i,t) (trace_block p d n ctx fn outer s) ==>
    ?bb. lookup_block t.vs_current_bb g.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME i /\
      (!k b. ?m k' pre post. b <= m /\ k <= k' /\
        open_trace p d m ctx fn outer s =
          pre ++ open_trace q h k' ctx g bb t ++ post /\
        (q = p ==> post = []))) /\
  (!p d n ctx fn s. !q h g i t.
    MEM ((q,h,i.inst_id),g,i,t) (trace_blocks p d n ctx fn s) ==>
    ?bb. lookup_block t.vs_current_bb g.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME i /\
      (!k b. ?m k' pre post. b <= m /\ k <= k' /\
        trace_blocks p d m ctx fn s =
          pre ++ open_trace q h k' ctx g bb t ++ post /\
        (q = p ==> post = [])))
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume trace_cofinal_factor[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (Cases_on `decode_invoke inst`
      >- simp[Once trace_defs] >>
      rename1 `decode_invoke inst = SOME decoded` >> PairCases_on `decoded` >>
      Cases_on `lookup_function decoded0 ctx.ctx_functions`
      >- simp[Once trace_defs] >>
      rename1 `lookup_function _ _ = SOME callee` >>
      Cases_on `eval_operands decoded1 s`
      >- simp[Once trace_defs] >>
      rename1 `eval_operands _ _ = SOME args` >>
      Cases_on `setup_callee callee args s`
      >- simp[Once trace_defs] >>
      rename1 `setup_callee _ _ _ = SOME cs` >>
      simp[Once trace_defs] >> strip_tac >>
      qpat_x_assum `!v nm ops fn args cs. _`
        (mp_tac o SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO]) >>
      disch_then drule >> disch_then drule >>
      disch_then drule >> disch_then drule >>
      disch_then (qspecl_then [`q`,`h`,`g`,`i`,`t`] mp_tac) >>
      simp[] >> strip_tac >> qexists_tac `bb` >> simp[] >>
      rpt gen_tac >> first_x_assum (qspecl_then [`k`,`b`]
        (qx_choosel_then [`m`,`remain`,`pre`,`post`] strip_assume_tac)) >>
      qexistsl_tac [`m`,`remain`,`pre`,`post`] >> simp[Once trace_defs]) >>
  simp[trace_step_noninvoke]
QED

Resume trace_cofinal_factor[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction outer s.vs_inst_idx`
  >- (qpat_x_assum `MEM _ _` mp_tac >> simp[Once trace_defs]) >>
  rename1 `get_instruction outer s.vs_inst_idx = SOME inst` >>
  qpat_x_assum `MEM _ (trace_block _ _ _ _ _ _ _)` mp_tac >>
  simp[Once trace_defs, MEM_APPEND] >> strip_tac
  >- (gvs[] >> rpt gen_tac >>
      qexistsl_tac [`MAX k b`,`MAX k b`,`[]`] >> simp[])
  >- (qpat_x_assum `!inst'. SOME inst = SOME inst' ==> _`
        (mp_tac o SRULE []) >>
      disch_then (qspecl_then [`q`,`h`,`g`,`i`,`t`] mp_tac) >>
      simp[] >> strip_tac >> qexists_tac `bb` >> simp[] >>
      `q <> p` by
        (qspecl_then [`p`,`d`,`n`,`ctx`,`fn`,`inst`,`s`] mp_tac (cj 1 trace_regions) >>
         simp[EVERY_MEM] >>
         disch_then (qspec_then `((q,h,i.inst_id),g,i,t)` mp_tac) >>
         simp[] >> metis_tac[frame_not_below_self]) >>
      rpt gen_tac >> first_x_assum (qspecl_then [`k`,`b`]
        (qx_choosel_then [`m`,`remain`,`pre`,`post`] strip_assume_tac)) >>
      qexistsl_tac [`m`,`remain`,
        `((p,d,inst.inst_id),fn,inst,s)::pre`,
        `post ++
          (case step_inst m ctx inst s of
             OK out => if is_terminator inst.inst_opcode then []
               else trace_block p d m ctx fn outer
                 (out with vs_inst_idx := SUC s.vs_inst_idx)
           | _ => []) ++
          (case exec_block m ctx outer s of
             OK out => if out.vs_halted then [] else trace_blocks p d m ctx fn out
           | _ => [])`] >>
      simp[open_trace_def, Once trace_defs, APPEND_ASSOC]) >>
  Cases_on `step_inst n ctx inst s` >> gvs[] >>
  rename1 `step_inst n ctx inst s = OK out` >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  `out.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  qpat_x_assum `!q' h' g' i' t'. lookup_block _ _ = SOME outer /\ _ ==> _`
    (qspecl_then [`q`,`h`,`g`,`i`,`t`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `bb` >> simp[] >>
  rpt gen_tac >> first_x_assum (qspecl_then [`k`,`MAX n b`]
    (qx_choosel_then [`m`,`remain`,`pre`,`post`] strip_assume_tac)) >>
  `n <= m /\ b <= m` by (gvs[MAX_DEF] >> decide_tac) >>
  `step_inst m ctx inst s = OK out` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `n` >> simp[]) >>
  qexistsl_tac [`m`,`remain`,
    `((p,d,inst.inst_id),fn,inst,s)::(trace_step p d m ctx fn inst s ++ pre)`,
    `post`] >> simp[] >>
  drule_all open_trace_next >>
  disch_then (qspecl_then [`p`,`fn`,`d`] SUBST1_TAC) >> simp[APPEND_ASSOC]
QED

Resume trace_cofinal_factor[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `n` >- simp[Once trace_defs] >>
  rename1 `trace_blocks p d (SUC n) ctx fn s` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[Once trace_defs] >>
  rename1 `lookup_block _ _ = SOME outer` >>
  Cases_on `eval_phis s outer.bb_instructions` >>
  simp[Once trace_defs, MEM_APPEND] >> gvs[] >>
  rename1 `eval_phis s outer.bb_instructions = OK sp` >>
  `sp.vs_current_bb = s.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  strip_tac
  >- (qpat_x_assum `!outer' sp'. _`
        (mp_tac o SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO]) >>
      disch_then (qspecl_then [`q`,`h`,`g`,`i`,`t`] mp_tac) >>
      simp[] >> strip_tac >> qexists_tac `bb` >> simp[] >>
      rpt gen_tac >> first_x_assum (qspecl_then [`k`,`b`]
        (qx_choosel_then [`m`,`remain`,`pre`,`post`] strip_assume_tac)) >>
      qexistsl_tac [`SUC m`,`remain`,`pre`,`post`] >> simp[] >>
      drule_all trace_blocks_open >>
      disch_then (qspecl_then [`p`,`m`,`d`,`ctx`] SUBST1_TAC) >> simp[]) >>
  Cases_on `exec_block n ctx outer
    (sp with vs_inst_idx := phi_prefix_length outer.bb_instructions)` >> gvs[] >>
  rename1 `exec_block _ _ _ _ = OK out` >>
  Cases_on `out.vs_halted` >> gvs[] >>
  qpat_x_assum `!q' h' g' i' t'. MEM _ (trace_blocks _ _ _ _ _ _) ==> _`
    (qspecl_then [`q`,`h`,`g`,`i`,`t`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `bb` >> simp[] >>
  rpt gen_tac >> first_x_assum (qspecl_then [`k`,`MAX n b`]
    (qx_choosel_then [`m`,`remain`,`pre`,`post`] strip_assume_tac)) >>
  `n <= m /\ b <= m` by (gvs[MAX_DEF] >> decide_tac) >>
  `exec_block m ctx outer
    (sp with vs_inst_idx := phi_prefix_length outer.bb_instructions) = OK out` by
    (irule (cj 2 fuel_mono) >> simp[] >> qexists_tac `n` >> simp[]) >>
  qexistsl_tac [`SUC m`,`remain`,
    `trace_block p (SUC d) m ctx fn outer
      (sp with vs_inst_idx := phi_prefix_length outer.bb_instructions) ++ pre`,
    `post`] >> simp[] >> simp[Once trace_defs, APPEND_ASSOC]
QED

Finalise trace_cofinal_factor

Theorem trace_blocks_actual_return_suffix:
  MEM ((p,h,i.inst_id),fn,i,t) (trace_blocks p d n ctx fn entry) /\
  i.inst_opcode = RET /\ step_inst ret_fuel ctx i t = IntRet ret send ==>
  !b. ?m pre. b <= m /\
    trace_blocks p d m ctx fn entry = pre ++ [((p,h,i.inst_id),fn,i,t)]
Proof
  strip_tac >> drule (cj 3 trace_cofinal_factor) >> strip_tac >> gen_tac >>
  first_x_assum (qspecl_then [`ret_fuel`,`b`]
    (qx_choosel_then [`m`,`remain`,`pre`,`post`] strip_assume_tac)) >> gvs[] >>
  `step_inst remain ctx i t = IntRet ret send` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `ret_fuel` >> simp[]) >>
  `open_trace p h remain ctx fn bb t = [((p,h,i.inst_id),fn,i,t)]` by
    simp[open_trace_def, Once (cj 2 trace_defs), Once exec_block_def,
         trace_step_noninvoke] >>
  qexistsl_tac [`m`,`pre`] >> simp[]
QED

Theorem trace_context_cofinal_factor:
  MEM ((q,h,i.inst_id),g,i,t) (trace_context n ctx s) ==>
  ?bb. lookup_block t.vs_current_bb g.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME i /\
    (!k b. ?m k' pre post. b <= m /\ k <= k' /\
      trace_context m ctx s =
        pre ++ open_trace q h k' ctx g bb t ++ post /\
      (q = [] ==> post = []))
Proof
  Cases_on `ctx.ctx_entry` >- simp[trace_context_def] >>
  rename1 `ctx.ctx_entry = SOME nm` >>
  Cases_on `lookup_function nm ctx.ctx_functions`
  >- simp[trace_context_def] >>
  rename1 `lookup_function _ _ = SOME fn` >>
  Cases_on `fn_entry_label fn` >- simp[trace_context_def, trace_function_def] >>
  simp[trace_context_def, trace_function_def] >>
  strip_tac >> drule (cj 3 trace_cofinal_factor) >>
  strip_tac >> qexists_tac `bb` >> simp[]
QED

Theorem trace_cofinal:
  (!p d n ctx fn inst s. !q h g i t.
    MEM ((q,h,i.inst_id),g,i,t) (trace_step p d n ctx fn inst s) ==>
    ?bb. lookup_block t.vs_current_bb g.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME i /\
      (!k b. ?m. b <= m /\
        !v. MEM v (open_trace q h k ctx g bb t) ==>
            MEM v (trace_step p d m ctx fn inst s))) /\
  (!p d n ctx fn outer s. !q h g i t.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME outer /\
    MEM ((q,h,i.inst_id),g,i,t) (trace_block p d n ctx fn outer s) ==>
    ?bb. lookup_block t.vs_current_bb g.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME i /\
      (!k b. ?m. b <= m /\
        !v. MEM v (open_trace q h k ctx g bb t) ==>
            MEM v (open_trace p d m ctx fn outer s))) /\
  (!p d n ctx fn s. !q h g i t.
    MEM ((q,h,i.inst_id),g,i,t) (trace_blocks p d n ctx fn s) ==>
    ?bb. lookup_block t.vs_current_bb g.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME i /\
      (!k b. ?m. b <= m /\
        !v. MEM v (open_trace q h k ctx g bb t) ==>
            MEM v (trace_blocks p d m ctx fn s)))
Proof
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (drule (cj 1 trace_cofinal_factor) >> strip_tac >>
      qexists_tac `bb` >> simp[] >> rpt gen_tac >>
      first_x_assum (qspecl_then [`k`,`b`]
        (qx_choosel_then [`m`,`remain`,`pre`,`post`] strip_assume_tac)) >>
      qexists_tac `m` >> simp[] >> rpt strip_tac >>
      `MEM v (open_trace q h remain ctx g bb t)` by metis_tac[open_trace_mono] >>
      metis_tac[MEM_APPEND])
  >- (drule_all (cj 2 trace_cofinal_factor) >> strip_tac >>
      qexists_tac `bb` >> simp[] >> rpt gen_tac >>
      first_x_assum (qspecl_then [`k`,`b`]
        (qx_choosel_then [`m`,`remain`,`pre`,`post`] strip_assume_tac)) >>
      qexists_tac `m` >> simp[] >> rpt strip_tac >>
      `MEM v (open_trace q h remain ctx g bb t)` by metis_tac[open_trace_mono] >>
      metis_tac[MEM_APPEND]) >>
  drule (cj 3 trace_cofinal_factor) >> strip_tac >>
  qexists_tac `bb` >> simp[] >> rpt gen_tac >>
  first_x_assum (qspecl_then [`k`,`b`]
    (qx_choosel_then [`m`,`remain`,`pre`,`post`] strip_assume_tac)) >>
  qexists_tac `m` >> simp[] >> rpt strip_tac >>
  `MEM v (open_trace q h remain ctx g bb t)` by metis_tac[open_trace_mono] >>
  metis_tac[MEM_APPEND]
QED

Theorem trace_context_cofinal:
  MEM ((q,h,i.inst_id),g,i,t) (trace_context n ctx s) ==>
  ?bb. lookup_block t.vs_current_bb g.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME i /\
    (!k b. ?m. b <= m /\
      !v. MEM v (open_trace q h k ctx g bb t) ==>
          MEM v (trace_context m ctx s))
Proof
  strip_tac >> drule trace_context_cofinal_factor >> strip_tac >>
  qexists_tac `bb` >> simp[] >> rpt gen_tac >>
  first_x_assum (qspecl_then [`k`,`b`]
    (qx_choosel_then [`m`,`remain`,`pre`,`post`] strip_assume_tac)) >>
  qexists_tac `m` >> simp[] >> rpt strip_tac >>
  `MEM v (open_trace q h remain ctx g bb t)` by metis_tac[open_trace_mono] >>
  metis_tac[MEM_APPEND]
QED
