Theory dftPacketCallNative
Ancestors
  dftGasFromListTraceDefs dftGasFromListTracePrefix dftGasToListReachBoundary frameCfgBoundary
  contextCodegenRel venomExecSemantics
  venomExecProofs rich_list arithmetic

Theorem native_call_next:
  (!rp rd n C root i0 s0.
    !j p d fn i s nm ops child args cs s1 ci.
    j < LENGTH (trace_step rp rd n C root i0 s0) /\
    EL j (trace_step rp rd n C root i0 s0) = ((p,d,i.inst_id),fn,i,s) /\
    i.inst_opcode = INVOKE /\ decode_invoke i = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME child /\
    eval_operands ops s = SOME args /\ setup_callee child args s = SOME cs /\
    enters_block child cs s1 /\ ALL_DISTINCT (fn_labels child) /\ active_inst child ci s1 ==>
    SUC j < LENGTH (trace_step rp rd (SUC n) C root i0 s0) /\
    EL (SUC j) (trace_step rp rd (SUC n) C root i0 s0) =
      (((d,i.inst_id)::p,SUC d,ci.inst_id),child,ci,s1)) /\
  (!rp rd n C root bb s0.
    !j p d fn i s nm ops child args cs s1 ci.
    j < LENGTH (trace_block rp rd n C root bb s0) /\
    EL j (trace_block rp rd n C root bb s0) = ((p,d,i.inst_id),fn,i,s) /\
    i.inst_opcode = INVOKE /\ decode_invoke i = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME child /\
    eval_operands ops s = SOME args /\ setup_callee child args s = SOME cs /\
    enters_block child cs s1 /\ ALL_DISTINCT (fn_labels child) /\ active_inst child ci s1 ==>
    SUC j < LENGTH (trace_block rp rd (SUC n) C root bb s0) /\
    EL (SUC j) (trace_block rp rd (SUC n) C root bb s0) =
      (((d,i.inst_id)::p,SUC d,ci.inst_id),child,ci,s1)) /\
  (!rp rd n C root s0.
    !j p d fn i s nm ops child args cs s1 ci.
    j < LENGTH (trace_blocks rp rd n C root s0) /\
    EL j (trace_blocks rp rd n C root s0) = ((p,d,i.inst_id),fn,i,s) /\
    i.inst_opcode = INVOKE /\ decode_invoke i = SOME (nm,ops) /\
    lookup_function nm C.ctx_functions = SOME child /\
    eval_operands ops s = SOME args /\ setup_callee child args s = SOME cs /\
    enters_block child cs s1 /\ ALL_DISTINCT (fn_labels child) /\ active_inst child ci s1 ==>
    SUC j < LENGTH (trace_blocks rp rd (SUC n) C root s0) /\
    EL (SUC j) (trace_blocks rp rd (SUC n) C root s0) =
      (((d,i.inst_id)::p,SUC d,ci.inst_id),child,ci,s1))
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume native_call_next[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `i0.inst_opcode = INVOKE` >> gvs[cj 1 trace_defs] >>
  Cases_on `decode_invoke i0` >> gvs[] >>
  rename1 `decode_invoke i0 = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 C.ctx_functions` >> gvs[] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands pair1 s0` >> gvs[] >>
  rename1 `eval_operands _ _ = SOME argv` >>
  Cases_on `setup_callee callee argv s0` >> gvs[] >>
  first_x_assum (qspec_then `j` mp_tac) >>
  simp[] >> disch_then drule >> simp[] >> metis_tac[]
QED

Resume native_call_next[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s0.vs_inst_idx`
  >- (qpat_x_assum `j < _` mp_tac >> simp[Once (cj 2 trace_defs)]) >>
  rename1 `get_instruction bb s0.vs_inst_idx = SOME head` >>
  drule_then assume_tac trace_block_visit >> gvs[] >>
  Cases_on `j`
  >- (gvs[] >>
      drule_all active_inst_lookup_distinct >> strip_tac >>
      `s1.vs_current_bb = cs.vs_current_bb` by
        metis_tac[enters_block_control_labels] >>
      gvs[enters_block_def] >>
      simp[cj 1 trace_defs] >>
      once_rewrite_tac[cj 3 trace_defs] >> simp[] >>
      once_rewrite_tac[cj 2 trace_defs] >> simp[])
  >> rename1 `SUC k` >>
  gvs[] >>
  Cases_on `k < LENGTH (trace_step rp rd n C root head s0)`
  >- (gvs[EL_APPEND] >>
      `SUC k < LENGTH (trace_step rp rd (SUC n) C root head s0) /\
       EL (SUC k) (trace_step rp rd (SUC n) C root head s0) =
         (((d,i.inst_id)::p,SUC d,ci.inst_id),child,ci,s1)` by metis_tac[] >>
      simp[EL_APPEND]) >>
  Cases_on `step_inst n C head s0` >> gvs[] >>
  Cases_on `is_terminator head.inst_opcode` >> gvs[] >>
  rename1 `step_inst n C head s0 = OK post` >>
  `step_inst (SUC n) C head s0 = OK post` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `n` >> simp[]) >>
  `trace_step rp rd (SUC n) C root head s0 =
   trace_step rp rd n C root head s0` by
    (irule (cj 1 trace_stable) >> simp[]) >>
  gvs[EL_APPEND] >>
  `k - LENGTH (trace_step rp rd n C root head s0) <
   LENGTH (trace_block rp rd n C root bb (post with vs_inst_idx := SUC s0.vs_inst_idx))`
    by decide_tac >>
  `SUC k - LENGTH (trace_step rp rd n C root head s0) =
   SUC (k - LENGTH (trace_step rp rd n C root head s0))` by decide_tac >>
  simp[] >>
  qpat_x_assum `!j p d fn i s nm ops child args cs s1 ci.
    j < LENGTH (trace_block _ _ _ _ _ _ _) /\ _ ==> _`
    (qspec_then `k - LENGTH (trace_step rp rd n C root head s0)` mp_tac) >>
  simp[] >> disch_then drule >> simp[] >>
  disch_then (qspec_then `ci` mp_tac) >> simp[] >> strip_tac >>
  simp[] >> decide_tac
QED

Resume native_call_next[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `n` >> gvs[] >>
  qmatch_asmsub_rename_tac `j < LENGTH (trace_blocks rp rd (SUC k) C root s0)` >>
  Cases_on `lookup_block s0.vs_current_bb root.fn_blocks`
  >- (qpat_x_assum `j < _` mp_tac >> simp[Once (cj 3 trace_defs)]) >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s0 bb.bb_instructions` >>
  gvs[]
  >- (rename1 `eval_phis _ _ = OK sp` >>
      drule_all trace_blocks_enter >> strip_tac >> gvs[] >>
      qmatch_asmsub_abbrev_tac `exec_block k C bb start` >>
      Cases_on `j < LENGTH (trace_block rp (SUC rd) k C root bb start)`
      >- (gvs[EL_APPEND] >>
          `SUC j < LENGTH (trace_block rp (SUC rd) (SUC k) C root bb start) /\
           EL (SUC j) (trace_block rp (SUC rd) (SUC k) C root bb start) =
             (((d,i.inst_id)::p,SUC d,ci.inst_id),child,ci,s1)` by metis_tac[] >>
          simp[EL_APPEND]) >>
      Cases_on `exec_block k C bb start` >> gvs[] >>
      rename1 `exec_block k C bb start = OK post` >>
      Cases_on `post.vs_halted` >> gvs[] >>
      `exec_block (SUC k) C bb start = OK post` by
        (irule (cj 2 fuel_mono) >> simp[] >> qexists_tac `k` >> simp[]) >>
      `trace_block rp (SUC rd) (SUC k) C root bb start =
       trace_block rp (SUC rd) k C root bb start` by
        (irule (cj 2 trace_stable) >> simp[]) >>
      gvs[EL_APPEND] >>
      `j - LENGTH (trace_block rp (SUC rd) k C root bb start) <
       LENGTH (trace_blocks rp (SUC rd) k C root post)` by decide_tac >>
      `SUC j - LENGTH (trace_block rp (SUC rd) k C root bb start) =
       SUC (j - LENGTH (trace_block rp (SUC rd) k C root bb start))` by decide_tac >>
      simp[] >>
      qpat_x_assum `!j p d fn i s nm ops child args cs s1 ci.
        j < LENGTH (trace_blocks _ _ _ _ _ _) /\ _ ==> _`
        (qspec_then `j - LENGTH (trace_block rp (SUC rd) k C root bb start)` mp_tac) >>
      simp[] >> disch_then drule >> simp[] >>
      disch_then (qspec_then `ci` mp_tac) >> simp[] >> strip_tac >>
      simp[] >> decide_tac) >>
  (qpat_x_assum `j < _` mp_tac >> simp[Once (cj 3 trace_defs)])
QED

Finalise native_call_next

Theorem dft_packet_native_call_entry:
  j < LENGTH (trace_blocks rp rd n C root entry) /\
  EL j (trace_blocks rp rd n C root entry) = ((p,d,i.inst_id),fn,i,s) /\
  i.inst_opcode = INVOKE /\ decode_invoke i = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME child /\
  eval_operands ops s = SOME args /\ setup_callee child args s = SOME cs /\
  enters_block child cs s1 /\ ALL_DISTINCT (fn_labels child) /\
  active_inst child ci s1 ==>
  ?m suffix.
    n <= m /\
    trace_blocks rp rd m C root entry = trace_blocks rp rd n C root entry ++ suffix /\
    SUC j < LENGTH (trace_blocks rp rd m C root entry) /\
    EL (SUC j) (trace_blocks rp rd m C root entry) =
      (((d,i.inst_id)::p,SUC d,ci.inst_id),child,ci,s1) /\
    TAKE (SUC j) (trace_blocks rp rd m C root entry) =
      TAKE (SUC j) (trace_blocks rp rd n C root entry)
Proof
  strip_tac >>
  drule_all (cj 3 native_call_next) >> strip_tac >>
  `?suffix. trace_blocks rp rd (SUC n) C root entry =
     trace_blocks rp rd n C root entry ++ suffix` by
    (irule (cj 3 trace_prefix) >> simp[]) >>
  qexistsl_tac [`SUC n`, `suffix`] >>
  simp[] >> irule TAKE_APPEND1 >> simp[]
QED
