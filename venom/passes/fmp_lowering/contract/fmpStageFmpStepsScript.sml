(*
 * FmpLowering's stage simulation, the FMP-specific steps: a point's
 * reclaim restore, DALLOCA's 4-instruction expansion, RETPC_PARAM with the
 * root, the context entry's frame, and INVOKE's call and return.  Each
 * keeps fmpStageRel's joint relation, with the site map sm and the runner
 * lo moved as the step frees or makes sites.
 *
 * TOP-LEVEL:
 *   fmp_stage_restore        - the restores at a source point (F -> T)
 *   fmp_stage_dalloca_step   - DALLOCA against its expansion
 *   fmp_stage_retpc_step     - RETPC_PARAM, with the root before it
 *   fmp_stage_entry          - the context entry's first related point
 *   fmp_stage_invoke_call    - INVOKE, into the callee's first point
 *   fmp_stage_invoke_return  - RET, back to the caller past its INVOKE
 *)
Theory fmpStageFmpSteps
Ancestors
  fmpStageOpBase fmpStageControl fmpStageReclaimSound fmpStageRel
  fmpStageCallArity fmpStageRetStep
  fmpStageFmpStepsCallMatch fmpStageFmpStepsCallAssemble
  fmpStageFmpStepsEntryLayout fmpStageFmpStepsEntryInitialization
  ptrStaticDiscipline o1PassContract
  ptrDiscipline venomExecSemantics venomState venomInst finite_map words
  list

Theorem fmp_stage_restore:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts ==>
  ?n t1 lo'.
    (!k. fmp_target_run k C' fn.fn_name t n t1) /\ lo' <= lo /\
    n <= 1 /\
    (n = 1 ==>
     ?fn' bb'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
       lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
       (EL t.vs_inst_idx bb'.bb_instructions).inst_opcode = ASSIGN) /\
    fmp_stage_rel D C'
      (DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < lo'})
      fmp0 raw0 eom T stk PG G tn fn s lo' t1 ts
Proof
  cheat
QED

Theorem fmp_stage_dalloca_step:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ inst.inst_opcode = DALLOCA /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  step_inst k C inst s = r /\ terminates r ==>
  ?s1 t1.
    r = OK s1 /\ (!k'. fmp_target_run k' C' fn.fn_name t 4 t1) /\
    fmp_stage_rel D C'
      (if w2n s1.vs_fmp = w2n s.vs_fmp then sm
       else sm |+ ((w2n s.vs_fmp, w2n s1.vs_fmp - w2n s.vs_fmp),
                  (lo, inst.inst_id)))
      fmp0 raw0 eom F stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (lo + (w2n s1.vs_fmp - w2n s.vs_fmp)) t1 ts
Proof
  cheat
QED

Theorem fmp_stage_retpc_step:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ inst.inst_opcode = RETPC_PARAM /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  step_inst k C inst s = r /\ terminates r ==>
  ?s1 n t1.
    r = OK s1 /\ 1 <= n /\ n <= 2 /\
    (!k'. fmp_target_run k' C' fn.fn_name t n t1) /\
    fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG
      (step_prov PG G inst s1) (step_taint inst s s1 tn) fn
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) lo t1 ts
Proof
  cheat
QED

Theorem fmp_stage_entry:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  C.ctx_entry = SOME name /\
  lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  enters_block fn
    (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                vs_inst_idx := 0 |>) s1 /\
  active_inst fn inst s1 ==>
  ?n t1.
    (!k. fmp_target_run k C' name
           (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                        vs_inst_idx := 0 |>) n t1) /\
    fmp_stage_rel D C' FEMPTY (w2n vs'.vs_initial_fmp) (w2n fmp) eom F
      [] [] FEMPTY entry_taint fn s1 (w2n vs'.vs_initial_fmp) t1 []
Proof
  strip_tac >>
  drule_all fmp_entry_source_shape >> strip_tac >> gvs[] >>
  `wf_function fn` by
    (gvs[fmp_stage_ctx_def, o1_ctx_shape_def, EVERY_MEM] >>
     metis_tac[o1_fn_shape_def, lookup_function_MEM]) >>
  `fn.fn_fmp_signature = NONE` by
    (gvs[fmp_stage_ctx_def, o1_inv_def, o1_static_inv_def,
         fmp_free_ctx_def, EVERY_MEM] >>
     metis_tac[lookup_function_MEM]) >>
  drule_all fmp_entry_actual_lowering >> strip_tac >>
  `fn_is_context_entry ctx fn` by simp[fmpWfDefsTheory.fn_is_context_entry_def] >>
  drule_all fmp_entry_root_position >> strip_tac >>
  drule_all fmp_entry_target_block >> strip_tac >>
  irule fmp_stage_entry_from_layout >>
  simp[] >>
  (reverse conj_tac >- metis_tac[]) >>
  qexistsl_tac [`ctx`, `infos`, `runner`] >>
  simp[] >> strip_tac >>
  drule_all fmp_entry_initial_prefix >> strip_tac >> gvs[] >>
  qexists_tac `id` >> simp[]
QED

Theorem fmp_stage_invoke_call:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn ivk s /\ active_inst fn ivk s /\
  ~s.vs_halted /\ ivk.inst_opcode = INVOKE /\
  decode_invoke ivk = SOME (nm,ops) /\ C.ctx_entry <> SOME nm /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  active_inst fn' ivk' t ==>
  ?ops' callee' args' cs' t1.
    ivk'.inst_opcode = INVOKE /\ decode_invoke ivk' = SOME (nm,ops') /\
    lookup_function nm C'.ctx_functions = SOME callee' /\
    eval_operands ops' t = SOME args' /\
    setup_callee callee' args' t = SOME cs' /\
    enters_block callee' cs' t1 /\
    fmp_stage_rel D C' sm fmp0 raw0 eom F
      (<| cf_fn := fn; cf_inst := ivk; cf_state := s; cf_params := PG;
          cf_prov := G; cf_tvar := tn.t_var |> :: stk)
      (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee s1
      lo t1 ((t,lo)::ts)
Proof
  strip_tac >>
  drule_all fmp_call_match >> strip_tac >>
  mp_tac fmp_stage_invoke_call_from_match >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  simp[] >> metis_tac[]
QED

Theorem fmp_stage_invoke_return:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C (f::stk) PG G tn fn rinst s /\
  active_inst fn rinst s /\ ~s.vs_halted /\
  fmp_stage_rel D C' sm fmp0 raw0 eom T (f::stk) PG G tn fn s lo t
    ((tc,lc)::ts) /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  active_inst fn' rinst' t /\
  step_inst k C rinst s = IntRet ret s_end /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) =
    SOME s' /\
  active_inst f.cf_fn inst'
    (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  ?ret' t_end fc' ivk' t'.
    (!k'. step_inst k' C' rinst' t = IntRet ret' t_end) /\
    ret'.iret_values = ret.iret_values /\
    lookup_function f.cf_fn.fn_name C'.ctx_functions = SOME fc' /\
    active_inst fc' ivk' tc /\
    bind_outputs ivk'.inst_outputs ret'.iret_values
      (adopt_return_fmp ret' (merge_callee_state tc t_end)) = SOME t' /\
    fmp_stage_rel D C'
      (DRESTRICT sm {key | FST key < w2n f.cf_state.vs_fmp})
      fmp0 raw0 eom F stk f.cf_params
      (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
      (tn with t_var :=
         DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      f.cf_fn (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) lc
      (t' with vs_inst_idx := SUC tc.vs_inst_idx) ts
Proof
  cheat
QED
