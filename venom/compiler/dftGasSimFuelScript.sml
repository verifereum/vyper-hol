Theory dftGasSimFuel
Ancestors
  dftGasSimTransport dftGasSimFrameBoundary dftGasSimSchedule
  dftRunRel dftWf dftScheduleOrder o1PassContract passSimulationProofs
  venomWf venomExecSemantics venomInst venomState list
  unitLabelMapIdentity simplifyCfgDefs dftGasOracleDefs passSimulationDefs option
  o1PassLift dftCorrectness dftDefs relation venomExecProofs venomExecProps
  venomWfProps

Theorem ev_frame_schedule:
  dft_fn_rel fn fn' /\ MEM fn C.ctx_functions /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block s.vs_current_bb fn'.fn_blocks = SOME bb' /\
  strict_dom_vars_defined fn s /\ ctx_labels_bound C s.vs_labels /\
  ~s.vs_call_ctx.cc_static ==>
  dft_res_rel
    (case eval_phis s bb.bb_instructions of
       OK u => ev_block orc p d fuel D bb
         (u with vs_inst_idx := phi_prefix_length bb.bb_instructions)
     | Error e => Error e)
    (case eval_phis s bb'.bb_instructions of
       OK u => ev_block orc p d fuel D bb'
         (u with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
     | Error e => Error e)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_member_label] >>
  drule_all dft_fn_rel_lookup_order >> strip_tac >>
  irule ev_block_schedule >>
  gvs[dft_fn_rel_def, fn_inst_wf_def, fn_pseudos_prefix_def] >>
  rpt conj_tac
  >- (rpt strip_tac >> gvs[ctx_labels_bound_def] >>
      first_x_assum irule >> simp[fn_insts_MEM] >> metis_tac[])
  >- metis_tac[wf_fn_block_inst_ids_distinct]
  >- (gvs[EVERY_MEM, fn_insts_MEM] >> metis_tac[])
  >- (gvs[EVERY_MEM, fn_insts_MEM] >> rpt strip_tac >>
      Cases_on `i.inst_opcode` >> gvs[is_alloca_op_def] >> metis_tac[]) >>
  qexists_tac `fn` >> simp[]
QED

Theorem ev_blocks_frame_sim:
  !fuel p d C C' fn fn' s.
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\ fn' = dft_fn fn /\
  dft_fn_rel fn fn' /\ strict_dom_vars_defined fn s /\
  fn_reachable fn s.vs_current_bb /\ ctx_labels_bound C s.vs_labels /\
  ~s.vs_call_ctx.cc_static /\ terminates (ev_blocks orc p d fuel C fn s) ==>
  dft_res_rel (ev_blocks orc p d fuel C fn s)
              (ev_blocks orc p d fuel C' fn' s)
Proof
  Induct >- simp[Once ev_blocks_def, terminates_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >-
    (qpat_x_assum `terminates _` mp_tac >>
     simp[Once ev_blocks_def, terminates_def]) >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  `OPTREL dft_block_rel (SOME bb)
      (lookup_block s.vs_current_bb fn'.fn_blocks)` by
    (gvs[dft_fn_rel_def] >> metis_tac[dft_block_rel_lookup_block]) >>
  Cases_on `lookup_block s.vs_current_bb fn'.fn_blocks` >> gvs[OPTREL_def] >>
  rename1 `dft_block_rel bb bb'` >>
  `!name callee callee' t path depth.
    lookup_function name C.ctx_functions = SOME callee /\
    lookup_function name C'.ctx_functions = SOME callee' /\
    fn_entry_label callee = SOME t.vs_current_bb /\
    strict_dom_vars_defined callee t /\ ctx_labels_bound C t.vs_labels /\
    ~t.vs_call_ctx.cc_static /\
    terminates (ev_blocks orc path depth fuel C callee t) ==>
    dft_res_rel (ev_blocks orc path depth fuel C callee t)
                (ev_blocks orc path depth fuel C' callee' t)` by
    (rpt strip_tac >>
     `callee' = dft_fn callee` by
       (qpat_assum `LIST_REL (\fn fn'. fn' = dft_fn fn) _ _`
          (mp_tac o MATCH_MP (SRULE[GSYM AND_IMP_INTRO] list_rel_lookup_function)) >>
        (impl_tac >- (simp[] >> gen_tac >> simp[dft_fn_def] >>
                      pairarg_tac >> simp[])) >>
        disch_then (qspec_then `name` mp_tac) >> simp[OPTREL_def]) >>
     `dft_fn_rel callee callee'` by
       (drule dft_fn_rel_lookup_function >>
        disch_then (qspec_then `name` mp_tac) >> simp[OPTREL_def]) >>
     gvs[] >> first_x_assum irule >> simp[fn_reachable_def] >>
     metis_tac[lookup_function_MEM]) >>
  `!i t. ctx_labels_bound C t.vs_labels /\ ~t.vs_call_ctx.cc_static /\
    terminates (ev_step orc p (SUC d) fuel C i t) ==>
    dft_res_rel (ev_step orc p (SUC d) fuel C i t)
                (ev_step orc p (SUC d) fuel C' i t)` by
    (rpt strip_tac >> irule ev_step_context_rel >> simp[] >> metis_tac[]) >>
  suspend "block_entry"
QED

Resume ev_blocks_frame_sim[block_entry]:
  `dft_res_rel
    (case eval_phis s bb.bb_instructions of
       OK u => ev_block orc p (SUC d) fuel C' bb
         (u with vs_inst_idx := phi_prefix_length bb.bb_instructions)
     | Error e => Error e)
    (case eval_phis s bb'.bb_instructions of
       OK u => ev_block orc p (SUC d) fuel C' bb'
         (u with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
     | Error e => Error e)` by
    (irule ev_frame_schedule >> metis_tac[]) >>
  qpat_x_assum `!name callee callee' t path depth. _` kall_tac >>
  reverse (qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs)
  >- (qpat_x_assum `terminates _` mp_tac >>
      simp[Once ev_blocks_def, terminates_def]) >>
  rename1 `eval_phis s bb.bb_instructions = OK u` >>
  `terminates (ev_block orc p (SUC d) fuel C bb
    (u with vs_inst_idx := phi_prefix_length bb.bb_instructions))` by
    (qpat_x_assum `terminates _` mp_tac >>
     simp[Once ev_blocks_def] >>
     Cases_on `ev_block orc p (SUC d) fuel C bb
       (u with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
     simp[terminates_def]) >>
  `ctx_labels_bound C u.vs_labels /\ ~u.vs_call_ctx.cc_static` by
    metis_tac[eval_phis_preserves_labels, dft_eval_phis_call_ctx] >>
  `dft_res_rel
     (ev_block orc p (SUC d) fuel C bb
       (u with vs_inst_idx := phi_prefix_length bb.bb_instructions))
     (ev_block orc p (SUC d) fuel C' bb
       (u with vs_inst_idx := phi_prefix_length bb.bb_instructions))` by
    (irule ev_block_context_rel >> simp[]) >>
  `dft_res_rel
     (ev_block orc p (SUC d) fuel C bb
       (u with vs_inst_idx := phi_prefix_length bb.bb_instructions))
     (case eval_phis s bb'.bb_instructions of
       OK v => ev_block orc p (SUC d) fuel C' bb'
         (v with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
       | Error e => Error e)` by
    (irule dft_res_rel_trans >> goal_assum (drule_at Any) >> gvs[]) >>
  suspend "continuation"
QED

Resume ev_blocks_frame_sim[continuation]:
  qpat_x_assum `!i t. _` kall_tac >>
  gvs[] >>
  qpat_x_assum `dft_res_rel (ev_block _ _ _ _ C' _ _) _` kall_tac >>
  qpat_x_assum `dft_res_rel _ (ev_block _ _ _ _ _ _ _)` kall_tac >>
  qmatch_asmsub_abbrev_tac `dft_res_rel _ scheduled` >>
  `ev_blocks orc p d (SUC fuel) C' (dft_fn fn) s =
    case scheduled of
      OK t => if t.vs_halted then Halt t
              else ev_blocks orc p (SUC d) fuel C' (dft_fn fn) t
    | other => other` by
    (simp[Once ev_blocks_def, Abbr `scheduled`] >>
     qspecl_then [`s`, `bb'.bb_instructions`] strip_assume_tac
       eval_phis_ok_or_error_defs >> simp[]) >>
  pop_assum SUBST1_TAC >>
  simp[Once ev_blocks_def] >>
  Cases_on `ev_block orc p (SUC d) fuel C bb
    (u with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  Cases_on `scheduled` >> gvs[dft_res_rel_def, terminates_def] >>
  rename1 `ev_block _ _ _ _ C bb _ = OK t` >>
  Cases_on `t.vs_halted` >- simp[] >> simp[] >>
  pure_rewrite_tac[GSYM dft_res_rel_def] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_member_label] >>
  `wf_function fn /\ EVERY inst_wf bb.bb_instructions` by
    (gvs[dft_fn_rel_def, fn_inst_wf_def, EVERY_MEM, fn_insts_MEM] >>
     metis_tac[]) >>
  `strict_dom_vars_defined fn t /\ fn_reachable fn t.vs_current_bb /\
   ctx_labels_bound C t.vs_labels /\ ~t.vs_call_ctx.cc_static` by
    (irule ev_block_entry_frame_inv >> metis_tac[]) >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM dft_res_rel_def, GSYM terminates_def]) >>
  first_x_assum irule >> simp[] >>
  qpat_x_assum `terminates (ev_blocks _ _ _ (SUC _) _ _ _)` mp_tac >>
  simp[Once ev_blocks_def]
QED

Finalise ev_blocks_frame_sim

Theorem ev_function_frame_sim:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\ fn' = dft_fn fn /\
  dft_fn_rel fn fn' /\ ctx_labels_bound C s.vs_labels /\
  ~s.vs_call_ctx.cc_static /\ terminates (ev_function orc fuel C fn s) ==>
  dft_res_rel (ev_function orc fuel C fn s) (ev_function orc fuel C' fn' s)
Proof
  strip_tac >>
  `fn_entry_label fn' = fn_entry_label fn` by metis_tac[dft_fn_rel_entry_label] >>
  Cases_on `fn_entry_label fn` >-
    (qpat_x_assum `terminates _` mp_tac >> simp[ev_function_def, terminates_def]) >>
  rename1 `fn_entry_label fn = SOME lbl` >>
  simp[ev_function_def] >> irule ev_blocks_frame_sim >>
  simp[fn_reachable_def] >>
  qpat_x_assum `terminates _` mp_tac >> simp[ev_function_def] >>
  strip_tac >> conj_tac >- metis_tac[] >>
  irule strict_dom_vars_defined_entry >> simp[]
QED

(* Conditional recursive observation: the two local interfaces are discharged
   by the context-transport and scheduling publications. *)
Theorem ev_blocks_frame_sim_revert_empty_conditional:
  (!fuel p d C C' i s.
    LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
    (!name fn fn' t path depth.
      lookup_function name C.ctx_functions = SOME fn /\
      lookup_function name C'.ctx_functions = SOME fn' /\
      fn_entry_label fn = SOME t.vs_current_bb /\
      strict_dom_vars_defined fn t /\ ctx_labels_bound C t.vs_labels /\
      ~t.vs_call_ctx.cc_static /\
      terminates (ev_blocks orc path depth fuel C fn t) ==>
      dft_res_rel (ev_blocks orc path depth fuel C fn t)
                  (ev_blocks orc path depth fuel C' fn' t) /\
      (!a. ev_blocks orc path depth fuel C fn t = Abort Revert_abort a /\
           a.vs_returndata = [] ==>
           ?b. ev_blocks orc path depth fuel C' fn' t = Abort Revert_abort b /\
               b.vs_returndata = [])) /\
    ctx_labels_bound C s.vs_labels /\ ~s.vs_call_ctx.cc_static /\
    terminates (ev_step orc p d fuel C i s) ==>
    dft_res_rel (ev_step orc p d fuel C i s) (ev_step orc p d fuel C' i s) /\
    (!a. ev_step orc p d fuel C i s = Abort Revert_abort a /\
         a.vs_returndata = [] ==>
         ?b. ev_step orc p d fuel C' i s = Abort Revert_abort b /\
             b.vs_returndata = [])) /\
  (!fn fn' C s bb bb' p d fuel D a.
    dft_fn_rel fn fn' /\ MEM fn C.ctx_functions /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block s.vs_current_bb fn'.fn_blocks = SOME bb' /\
    strict_dom_vars_defined fn s /\ ctx_labels_bound C s.vs_labels /\
    ~s.vs_call_ctx.cc_static /\
    (case eval_phis s bb.bb_instructions of
       OK u => ev_block orc p d fuel D bb
         (u with vs_inst_idx := phi_prefix_length bb.bb_instructions)
     | Error e => Error e) = Abort Revert_abort a /\ a.vs_returndata = [] ==>
    ?b. (case eval_phis s bb'.bb_instructions of
       OK u => ev_block orc p d fuel D bb'
         (u with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
     | Error e => Error e) = Abort Revert_abort b /\ b.vs_returndata = []) ==>
  !fuel p d C C' fn fn' s.
    LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
    LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
    o1_ctx_shape C /\ MEM fn C.ctx_functions /\ fn' = dft_fn fn /\
    dft_fn_rel fn fn' /\ strict_dom_vars_defined fn s /\
    fn_reachable fn s.vs_current_bb /\ ctx_labels_bound C s.vs_labels /\
    ~s.vs_call_ctx.cc_static /\ terminates (ev_blocks orc p d fuel C fn s) ==>
    dft_res_rel (ev_blocks orc p d fuel C fn s)
                (ev_blocks orc p d fuel C' fn' s) /\
    (!a. ev_blocks orc p d fuel C fn s = Abort Revert_abort a /\
         a.vs_returndata = [] ==>
         ?b. ev_blocks orc p d fuel C' fn' s = Abort Revert_abort b /\
             b.vs_returndata = [])
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "transport") (mk_asm "schedule")) >>
  Induct >- simp[Once ev_blocks_def, terminates_def] >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule ev_blocks_frame_sim >> simp[]) >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >-
    (qpat_x_assum `terminates _` mp_tac >>
     simp[Once ev_blocks_def, terminates_def]) >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  `OPTREL dft_block_rel (SOME bb)
      (lookup_block s.vs_current_bb fn'.fn_blocks)` by
    (gvs[dft_fn_rel_def] >> metis_tac[dft_block_rel_lookup_block]) >>
  Cases_on `lookup_block s.vs_current_bb fn'.fn_blocks` >> gvs[OPTREL_def] >>
  rename1 `dft_block_rel bb bb'` >>
  suspend "callee"
QED

Resume ev_blocks_frame_sim_revert_empty_conditional[callee]:
  `!name callee callee' t path depth.
    lookup_function name C.ctx_functions = SOME callee /\
    lookup_function name C'.ctx_functions = SOME callee' /\
    fn_entry_label callee = SOME t.vs_current_bb /\
    strict_dom_vars_defined callee t /\ ctx_labels_bound C t.vs_labels /\
    ~t.vs_call_ctx.cc_static /\
    terminates (ev_blocks orc path depth fuel C callee t) ==>
    dft_res_rel (ev_blocks orc path depth fuel C callee t)
                (ev_blocks orc path depth fuel C' callee' t) /\
    (!a. ev_blocks orc path depth fuel C callee t = Abort Revert_abort a /\
         a.vs_returndata = [] ==>
         ?b. ev_blocks orc path depth fuel C' callee' t = Abort Revert_abort b /\
             b.vs_returndata = [])` by
    (rpt gen_tac >> strip_tac >>
     `callee' = dft_fn callee` by
       (qpat_assum `LIST_REL (\fn fn'. fn' = dft_fn fn) _ _`
          (mp_tac o MATCH_MP (SRULE[GSYM AND_IMP_INTRO] list_rel_lookup_function)) >>
        (impl_tac >- (simp[] >> gen_tac >> simp[dft_fn_def] >>
                      pairarg_tac >> simp[])) >>
        disch_then (qspec_then `name` mp_tac) >> simp[OPTREL_def]) >>
     `dft_fn_rel callee callee'` by
       (drule dft_fn_rel_lookup_function >>
        disch_then (qspec_then `name` mp_tac) >> simp[OPTREL_def]) >>
     gvs[] >> first_x_assum irule >> simp[fn_reachable_def] >>
     metis_tac[lookup_function_MEM]) >>
  `!i t. ctx_labels_bound C t.vs_labels /\ ~t.vs_call_ctx.cc_static /\
    terminates (ev_step orc p (SUC d) fuel C i t) ==>
    dft_res_rel (ev_step orc p (SUC d) fuel C i t)
                (ev_step orc p (SUC d) fuel C' i t) /\
    (!a. ev_step orc p (SUC d) fuel C i t = Abort Revert_abort a /\
         a.vs_returndata = [] ==>
         ?b. ev_step orc p (SUC d) fuel C' i t = Abort Revert_abort b /\
             b.vs_returndata = [])` by
    (rpt gen_tac >> strip_tac >>
     asm_x "transport" irule >> simp[] >>
     metis_tac[]) >>
  suspend "entry"
QED

Resume ev_blocks_frame_sim_revert_empty_conditional[entry]:
  reverse (qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs)
  >- (qpat_x_assum `terminates _` mp_tac >>
      simp[Once ev_blocks_def, terminates_def]) >>
  rename1 `eval_phis s bb.bb_instructions = OK u` >>
  `terminates (ev_block orc p (SUC d) fuel C bb
    (u with vs_inst_idx := phi_prefix_length bb.bb_instructions))` by
    (qpat_x_assum `terminates _` mp_tac >>
     simp[Once ev_blocks_def] >>
     Cases_on `ev_block orc p (SUC d) fuel C bb
       (u with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
     simp[terminates_def]) >>
  `ctx_labels_bound C u.vs_labels /\ ~u.vs_call_ctx.cc_static` by
    metis_tac[eval_phis_preserves_labels, dft_eval_phis_call_ctx] >>
  `dft_res_rel
     (ev_block orc p (SUC d) fuel C bb
       (u with vs_inst_idx := phi_prefix_length bb.bb_instructions))
     (ev_block orc p (SUC d) fuel C' bb
       (u with vs_inst_idx := phi_prefix_length bb.bb_instructions)) /\
   (!a. ev_block orc p (SUC d) fuel C bb
       (u with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
         Abort Revert_abort a /\ a.vs_returndata = [] ==>
     ?b. ev_block orc p (SUC d) fuel C' bb
       (u with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
         Abort Revert_abort b /\ b.vs_returndata = [])` by
    (irule ev_block_context_rel_revert_empty_conditional >> simp[] >> gvs[]) >>
  suspend "continuation"
QED

Resume ev_blocks_frame_sim_revert_empty_conditional[continuation]:
  `dft_res_rel
    (case eval_phis s bb.bb_instructions of
       OK v => ev_block orc p (SUC d) fuel C' bb
         (v with vs_inst_idx := phi_prefix_length bb.bb_instructions)
     | Error e => Error e)
    (case eval_phis s bb'.bb_instructions of
       OK v => ev_block orc p (SUC d) fuel C' bb'
         (v with vs_inst_idx := phi_prefix_length bb'.bb_instructions)
     | Error e => Error e)` by
    (irule ev_frame_schedule >> metis_tac[]) >>
  asm_x "transport" kall_tac >>
  qpat_x_assum `!name callee callee' t path depth. _` kall_tac >>
  qpat_x_assum `!i t. _` kall_tac >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `dft_res_rel _ scheduled` >>
  `!a. ev_block orc p (SUC d) fuel C' bb
       (u with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
       Abort Revert_abort a /\ a.vs_returndata = [] ==>
       ?b. scheduled = Abort Revert_abort b /\ b.vs_returndata = []` by
    (rpt strip_tac >> simp[Abbr `scheduled`] >>
     asm_x "schedule" irule >> simp[] >>
     qexistsl_tac [`C`, `a`, `bb`, `fn`, `dft_fn fn`] >> simp[]) >>
  asm_x "schedule" kall_tac >>
  `ev_blocks orc p d (SUC fuel) C' (dft_fn fn) s =
    case scheduled of
      OK t => if t.vs_halted then Halt t
              else ev_blocks orc p (SUC d) fuel C' (dft_fn fn) t
    | other => other` by
    (simp[Once ev_blocks_def, Abbr `scheduled`] >>
     qspecl_then [`s`, `bb'.bb_instructions`] strip_assume_tac
       eval_phis_ok_or_error_defs >> simp[]) >>
  pop_assum SUBST1_TAC >>
  simp[Once ev_blocks_def] >>
  Cases_on `ev_block orc p (SUC d) fuel C bb
    (u with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  Cases_on `ev_block orc p (SUC d) fuel C' bb
    (u with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  Cases_on `scheduled` >> gvs[dft_res_rel_def, terminates_def] >>
  rename1 `ev_block _ _ _ _ C bb _ = OK t` >>
  Cases_on `t.vs_halted` >- simp[] >> simp[] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_member_label] >>
  `wf_function fn /\ EVERY inst_wf bb.bb_instructions` by
    (gvs[dft_fn_rel_def, fn_inst_wf_def, EVERY_MEM, fn_insts_MEM] >>
     metis_tac[]) >>
  `strict_dom_vars_defined fn t /\ fn_reachable fn t.vs_current_bb /\
   ctx_labels_bound C t.vs_labels /\ ~t.vs_call_ctx.cc_static` by
    (irule ev_block_entry_frame_inv >> metis_tac[]) >>
  suspend "recursive_tail"
QED

Resume ev_blocks_frame_sim_revert_empty_conditional[recursive_tail]:
  rule_assum_tac (PURE_REWRITE_RULE [GSYM terminates_def]) >>
  `terminates (ev_blocks orc p (SUC d) fuel C fn t)` by
    (qpat_x_assum `terminates (ev_blocks _ _ _ (SUC _) _ _ _)` mp_tac >>
     simp[Once ev_blocks_def]) >>
  first_x_assum (drule_all_then strip_assume_tac) >> simp[]
QED

Finalise ev_blocks_frame_sim_revert_empty_conditional

Theorem ev_function_frame_sim_revert_empty:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\ fn' = dft_fn fn /\
  dft_fn_rel fn fn' /\ ctx_labels_bound C s.vs_labels /\
  ~s.vs_call_ctx.cc_static /\ terminates (ev_function orc fuel C fn s) ==>
  dft_res_rel (ev_function orc fuel C fn s) (ev_function orc fuel C' fn' s) /\
  (!a. ev_function orc fuel C fn s = Abort Revert_abort a /\
       a.vs_returndata = [] ==>
       ?b. ev_function orc fuel C' fn' s = Abort Revert_abort b /\
           b.vs_returndata = [])
Proof
  strip_tac >>
  `fn_entry_label fn' = fn_entry_label fn` by metis_tac[dft_fn_rel_entry_label] >>
  Cases_on `fn_entry_label fn` >-
    (qpat_x_assum `terminates _` mp_tac >> simp[ev_function_def, terminates_def]) >>
  rename1 `fn_entry_label fn = SOME lbl` >>
  simp[ev_function_def] >>
  mp_tac ev_blocks_frame_sim_revert_empty_conditional >>
  (impl_tac >-
    (conj_tac
     >- (rpt gen_tac >> strip_tac >>
         irule ev_step_context_rel_revert_empty >> simp[] >> metis_tac[]) >>
     rpt gen_tac >> strip_tac >>
     rename1 `lookup_block st.vs_current_bb f.fn_blocks = SOME bb` >>
     `MEM bb f.fn_blocks /\ bb.bb_label = st.vs_current_bb` by
       metis_tac[lookup_block_member_label] >>
     drule_all dft_fn_rel_lookup_order >> strip_tac >>
     irule ev_block_schedule_revert_empty >>
     conj_tac >- simp[] >>
     qexistsl_tac [`bb`, `f`, `a`] >>
     gvs[dft_fn_rel_def, fn_inst_wf_def, fn_pseudos_prefix_def] >>
     rpt conj_tac
     >- (rpt strip_tac >> gvs[ctx_labels_bound_def] >>
         first_x_assum irule >> simp[fn_insts_MEM] >> metis_tac[])
     >- metis_tac[wf_fn_block_inst_ids_distinct]
     >- (gvs[EVERY_MEM, fn_insts_MEM] >> metis_tac[])
     >- (gvs[EVERY_MEM, fn_insts_MEM] >> rpt strip_tac >>
         Cases_on `i.inst_opcode` >> gvs[is_alloca_op_def] >> metis_tac[]))) >>
  disch_then irule >> simp[fn_reachable_def] >>
  qpat_x_assum `terminates _` mp_tac >> simp[ev_function_def] >>
  strip_tac >> conj_tac >- metis_tac[] >>
  irule strict_dom_vars_defined_entry >> simp[]
QED
