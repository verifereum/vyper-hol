Theory dftGasSimTransport
Ancestors
  dftGasSimSchedule dftGasSimInvariant dftGasSimBoundary dftGasOracleDefs
  dftRunRel passSimulationDefs venomExecSemantics venomInst venomState list option

Theorem ev_step_context_rel:
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  (!name fn fn' t path depth.
    lookup_function name C.ctx_functions = SOME fn /\
    lookup_function name C'.ctx_functions = SOME fn' /\
    fn_entry_label fn = SOME t.vs_current_bb /\
    strict_dom_vars_defined fn t /\ ctx_labels_bound C t.vs_labels /\
    ~t.vs_call_ctx.cc_static /\
    terminates (ev_blocks orc path depth fuel C fn t) ==>
    dft_res_rel (ev_blocks orc path depth fuel C fn t)
                (ev_blocks orc path depth fuel C' fn' t)) /\
  ctx_labels_bound C s.vs_labels /\ ~s.vs_call_ctx.cc_static /\
  terminates (ev_step orc p d fuel C i s) ==>
  dft_res_rel (ev_step orc p d fuel C i s) (ev_step orc p d fuel C' i s)
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE`
  >- (simp[Ntimes ev_step_def 2] >>
      Cases_on `decode_invoke i` >- simp[dft_res_rel_def] >> simp[] >>
      rename1 `decode_invoke i = SOME pair` >> PairCases_on `pair` >> simp[] >>
      drule dft_fn_rel_lookup_function >> disch_then (qspec_then `pair0` mp_tac) >>
      Cases_on `lookup_function pair0 C.ctx_functions` >>
      Cases_on `lookup_function pair0 C'.ctx_functions` >>
      simp[OPTREL_def] >> strip_tac >> rename1 `dft_fn_rel callee callee'` >>
      `!args. setup_callee callee' args s = setup_callee callee args s` by
        metis_tac[dft_fn_rel_setup_callee] >>
      simp[] >> Cases_on `eval_operands pair1 s` >- simp[dft_res_rel_def] >>
      simp[] >> rename1 `eval_operands pair1 s = SOME args` >>
      Cases_on `setup_callee callee args s` >- simp[dft_res_rel_def] >>
      simp[] >> rename1 `setup_callee callee args s = SOME t` >>
      `fn_entry_label callee = SOME t.vs_current_bb /\
       strict_dom_vars_defined callee t /\ ctx_labels_bound C t.vs_labels /\
       ~t.vs_call_ctx.cc_static` by
        metis_tac[dft_setup_callee_entry, ev_setup_callee_dominators,
          ev_setup_callee_labels_bound, ev_setup_callee_nonstatic] >>
      `terminates (ev_blocks orc ((d,i.inst_id)::p) d fuel C callee t)` by
        (qpat_x_assum `terminates (ev_step _ _ _ _ _ _ _)` mp_tac >>
         simp[ev_step_def] >>
         Cases_on `ev_blocks orc ((d,i.inst_id)::p) d fuel C callee t` >>
         simp[terminates_def]) >>
      qpat_x_assum `!name fn fn' t path depth. _` (drule_all_then mp_tac) >>
      Cases_on `ev_blocks orc ((d,i.inst_id)::p) d fuel C callee t` >>
      Cases_on `ev_blocks orc ((d,i.inst_id)::p) d fuel C' callee' t` >>
      simp[dft_res_rel_def] >> rpt strip_tac >> gvs[] >>
      Cases_on `bind_outputs i.inst_outputs i'.iret_values
        (adopt_return_fmp i' (merge_callee_state s v))` >> simp[]) >>
  simp[ev_step_def]
QED

Theorem ev_suffix_context_rel:
  (!i t. ctx_labels_bound C t.vs_labels /\ ~t.vs_call_ctx.cc_static /\
    terminates (ev_step orc p d fuel C i t) ==>
    dft_res_rel (ev_step orc p d fuel C i t) (ev_step orc p d fuel C' i t)) ==>
  !xs s. ctx_labels_bound C s.vs_labels /\ ~s.vs_call_ctx.cc_static /\
    terminates (ev_suffix orc p d fuel C xs s) ==>
  dft_res_rel (ev_suffix orc p d fuel C xs s)
              (ev_suffix orc p d fuel C' xs s)
Proof
  strip_tac >> Induct >- simp[ev_suffix_def] >> rpt gen_tac >> strip_tac >>
  `terminates (ev_step orc p d fuel C h s)` by
    (qpat_x_assum `terminates (ev_suffix _ _ _ _ _ _ _)` mp_tac >>
     simp[Once ev_suffix_def] >>
     Cases_on `ev_step orc p d fuel C h s` >> simp[terminates_def]) >>
  `dft_res_rel (ev_step orc p d fuel C h s) (ev_step orc p d fuel C' h s)` by
    simp[] >>
  Cases_on `ev_step orc p d fuel C h s` >>
  Cases_on `ev_step orc p d fuel C' h s` >>
  gvs[dft_res_rel_def] >> simp[ev_suffix_def, dft_res_rel_def] >>
  Cases_on `is_terminator h.inst_opcode`
  >- (Cases_on `v.vs_halted` >> simp[]) >>
  simp[] >> first_x_assum irule >>
  simp[] >> drule ev_step_labels >> drule ev_step_call_ctx >>
  gvs[Once ev_suffix_def]
QED

Theorem ev_block_context_rel:
  (!i t. ctx_labels_bound C t.vs_labels /\ ~t.vs_call_ctx.cc_static /\
    terminates (ev_step orc p d fuel C i t) ==>
    dft_res_rel (ev_step orc p d fuel C i t) (ev_step orc p d fuel C' i t)) /\
  ctx_labels_bound C s.vs_labels /\ ~s.vs_call_ctx.cc_static /\
  terminates (ev_block orc p d fuel C bb s) ==>
  dft_res_rel (ev_block orc p d fuel C bb s) (ev_block orc p d fuel C' bb s)
Proof
  strip_tac >>
  `!D. ev_block orc p d fuel D bb s =
    ev_suffix orc p d fuel D (DROP s.vs_inst_idx bb.bb_instructions) s` by
    (gen_tac >> sym_tac >> irule ev_suffix_block >> simp[]) >>
  gvs[] >> irule ev_suffix_context_rel >> simp[]
QED
