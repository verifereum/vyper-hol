Theory o1ContractCfgNormJointCursors
Ancestors
  o1ContractCfgNormCursors o1ContractCfgNormCursorBlocks
  o1ContractCfgNormCursorCalls o1ContractCfgNormCursorReturns
  o1ContractCfgNormCursorProjection o1ContractCfgNorm o1PassContract o1PassLift
  cfgNormSupplySim cfgNormDefs frameJointTransition frameOriginHistory
  venomExecSemantics venomExecProofs venomStepProps venomInst venomState
  venomWf venomWfProps unitShapeDefs unitTransformDefs stateFrame
  ptrDiscipline contextCodegenRel ctxLookupAgreeHelpers
  list rich_list finite_map arithmetic pair option

(* Fixed schedule data is selected before runtime entries. Saved cells
   belong to the actual paired call frames; histories remain independent.
   Head equality alone cannot classify a stutter: a real self-loop can
   also leave the head fixed. Administrative cases require their opcode
   classification from the cursor construction. *)

Definition cfg_norm_joint_cursors_def:
  cfg_norm_joint_cursors C8 C9 (schedules,(rounds,cells),saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) <=>
  C9.ctx_entry = C8.ctx_entry /\
  ALL_DISTINCT (MAP (\fn. fn.fn_name) C8.ctx_functions) /\
  MAP FST schedules = C8.ctx_functions /\
  MAP (FST o SND) schedules = C9.ctx_functions /\
  EVERY (\(sf,tf,rs).
    ?s t meta.
      supply_norm_inv s sf /\ EVERY label_positions_ok (fn_insts sf) /\
      cfg_norm_function_supply s sf = (tf,t) /\
      sf.fn_name = tf.fn_name /\ fn_entry_label sf = fn_entry_label tf /\
      rs <> [] /\ HD rs = (s,sf,meta) /\ LAST rs = (t,tf,NONE) /\
      LENGTH rs <= SUC (2 * LENGTH sf.fn_blocks) /\
      !C cs v inst.
        fn_entry_state sf cs /\ enters_block tf cs v /\ active_inst tf inst v ==>
        ?cur first a.
          cfg_norm_cursors C rs cur /\
          LAST cur = ((inst,v),NONE) /\ HD cur = ((first,a),NONE) /\
          enters_block sf cs a) schedules /\
  MEM (fn8,fn9,rounds) schedules /\
  cfg_norm_cursors C8 rounds cells /\
  (?pending. HD cells = ((inst8,s8),pending)) /\
  LAST cells = ((inst9,s9),NONE) /\
  LENGTH stk8 = LENGTH stk9 /\
  LENGTH oms8 = LENGTH stk8 /\ LENGTH hs8 = LENGTH stk8 /\
  LENGTH oms9 = LENGTH stk9 /\ LENGTH hs9 = LENGTH stk9 /\
  LIST_REL (\(rs,cur) (f8,f9).
    MEM (f8.cf_fn,f9.cf_fn,rs) schedules /\
    cfg_norm_cursors C8 rs cur /\
    (?pending. HD cur = ((f8.cf_inst,f8.cf_state),pending)) /\
    LAST cur = ((f9.cf_inst,f9.cf_state),NONE) /\
    f8.cf_inst.inst_opcode = INVOKE /\ f9.cf_inst.inst_opcode = INVOKE)
    saved (ZIP (stk8,stk9))
End

Theorem cfg_norm_schedule_list[local]:
  !fs gs.
  LIST_REL (\sf tf. ?s t.
    supply_norm_inv s sf /\ EVERY label_positions_ok (fn_insts sf) /\
    cfg_norm_function_supply s sf = (tf,t)) fs gs ==>
  ?schedules.
    MAP FST schedules = fs /\ MAP (FST o SND) schedules = gs /\
    EVERY (\(sf,tf,rs). ?s t meta.
      supply_norm_inv s sf /\ EVERY label_positions_ok (fn_insts sf) /\
      cfg_norm_function_supply s sf = (tf,t) /\
      sf.fn_name = tf.fn_name /\ fn_entry_label sf = fn_entry_label tf /\
      rs <> [] /\ HD rs = (s,sf,meta) /\ LAST rs = (t,tf,NONE) /\
      LENGTH rs <= SUC (2 * LENGTH sf.fn_blocks) /\
      !C cs v inst.
        fn_entry_state sf cs /\ enters_block tf cs v /\ active_inst tf inst v ==>
        ?cur first a. cfg_norm_cursors C rs cur /\
          LAST cur = ((inst,v),NONE) /\ HD cur = ((first,a),NONE) /\
          enters_block sf cs a) schedules
Proof
  Induct >> Cases_on `gs` >> simp[] >> rpt strip_tac >>
  rename1 `cfg_norm_function_supply s sf = (tf,t')` >>
  first_x_assum drule >> strip_tac >>
  drule_all cfg_norm_function_supply_cursors >> strip_tac >>
  drule cfg_norm_function_supply_identity >> strip_tac >>
  qexists_tac `(sf,tf,rounds)::schedules` >> simp[] >>
  metis_tac[]
QED

(* Initialization must prove the static certificate in the wrapper, rather
   than take it as a callback premise. The state fields are actual entry
   requirements: joint_initial alone allows arbitrary variables/halted. *)
Theorem cfg_norm_joint_cursors_initial:
  ctx_pass_stage rp (CFP_Simple VP_CFGNormalization) view C8 C9 /\
  o1_ctx_shape C8 /\ EVERY wf_ssa C8.ctx_functions ==>
  ?schedules.
    !vs0 q8 q9.
      vs0.vs_vars = FEMPTY /\ ~vs0.vs_halted /\
      joint_initial vs0 C8 q8 /\ joint_initial vs0 C9 q9 ==>
      ?current. cfg_norm_joint_cursors C8 C9 (schedules,current,[]) q8 q9
Proof
  rpt strip_tac >> drule cfg_norm_stage_functions >> strip_tac >>
  `LIST_REL (\sf tf. ?s t.
     supply_norm_inv s sf /\ EVERY label_positions_ok (fn_insts sf) /\
     cfg_norm_function_supply s sf = (tf,t))
     C8.ctx_functions C9.ctx_functions` by
    (irule LIST_REL_MEM_MONO >> goal_assum (drule_at Any) >>
     simp[] >> rpt strip_tac >> PairCases_on `x` >> gvs[] >>
     `MEM x0 C8.ctx_functions` by
       (drule LIST_REL_LENGTH >> strip_tac >>
        gvs[MEM_ZIP] >> metis_tac[MEM_EL]) >>
     drule_all cfg_norm_stage_fn_ok >> strip_tac >>
     simp[supply_norm_inv_def] >> metis_tac[]) >>
  drule cfg_norm_schedule_list >> strip_tac >>
  qexists_tac `schedules` >> rpt strip_tac >>
  gvs[joint_initial_cases] >>
  `LIST_REL (\sf tf. ?rs. MEM (sf,tf,rs) schedules)
    C8.ctx_functions C9.ctx_functions` by
    (qpat_x_assum `MAP FST schedules = _` (SUBST1_TAC o SYM) >>
     qpat_x_assum `MAP (FST o SND) schedules = _` (SUBST1_TAC o SYM) >>
     simp[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >>
     qexists_tac `SND (SND (EL n schedules))` >>
     simp[] >> metis_tac[MEM_EL]) >>
  qpat_assum `LIST_REL (\sf tf. ?rs. MEM (sf,tf,rs) schedules) _ _`
    (mp_then Any mp_tac list_rel_lookup_function) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    qpat_assum `EVERY _ schedules` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
    disch_then drule >> simp[] >> metis_tac[])) >>
  disch_then (qspec_then `name` mp_tac) >> simp[] >> strip_tac >>
  qpat_assum `EVERY _ schedules` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then drule >> simp[] >> strip_tac >>
  gvs[] >>
  `fn_entry_state fn
    (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)`
    by simp[fn_entry_state_def] >>
  first_x_assum (qspec_then `C8` mp_tac) >>
  disch_then drule >> disch_then drule >> disch_then drule >> strip_tac >>
  `a = s1` by (gvs[enters_block_def]) >> gvs[] >>
  `active_inst fn first a` by
    (drule cfg_norm_cursors_lengths >> strip_tac >>
     Cases_on `rs` >> Cases_on `cur` >> gvs[] >>
     drule cfg_norm_cursors_head >> simp[]) >>
  `first = inst` by
    (gvs[active_inst_def, supply_norm_inv_def, wf_function_def, fn_labels_def] >>
     imp_res_tac MEM_lookup_block >> gvs[]) >>
  qexists_tac `(rs,cur)` >> simp[cfg_norm_joint_cursors_def] >>
  gvs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def]
QED

Theorem cfg_norm_joint_cursors_ordinary:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  joint_transition C9
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9)
    (SOME (OriginOrdinary fuel post)) q9' ==>
  ?current' q8'.
    ((q8' = JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8 /\
      MEM inst9.inst_opcode [ASSIGN; JMP; JNZ] /\
      inst9.inst_opcode <> GAS /\ inst9.inst_opcode <> INVOKE /\
      inst_mem_ranges inst9 s9 = []) \/
     ?ev8. joint_transition C8
       (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8) ev8 q8') /\
    cfg_norm_joint_cursors C8 C9 (schedules,current',saved) q8' q9'
Proof
  strip_tac >> Cases_on `current` >>
  gvs[cfg_norm_joint_cursors_def, joint_transition_ordinary] >>
  qpat_assum `EVERY _ schedules` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then drule >> simp[] >> strip_tac >>
  drule_all cfg_norm_cursors_next_classified >> strip_tac
  >- (`inst_mem_ranges inst9 s9 = []` by
        (irule supply_inst_mem_ranges_empty >> gvs[]) >>
      Cases_on `HD cursors'` >> gvs[] >>
      qexistsl [`(q,cursors')`,
        `JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8`] >>
      simp[cfg_norm_joint_cursors_def] >> gvs[]) >>
  `r <> [] /\ cursors' <> []` by metis_tac[cfg_norm_cursors_lengths] >>
  Cases_on `HD cursors'` >> gvs[] >>
  `active_inst fn8 first a /\
   active_inst fn8 after (u with vs_inst_idx := SUC a.vs_inst_idx)` by
    (Cases_on `q` >> Cases_on `r` >> Cases_on `cursors'` >> gvs[] >>
     metis_tac[cfg_norm_cursors_head]) >>
  qexists_tac `(q,cursors')` >>
  qexists_tac `JointConfig stk8 PG8 (step_prov PG8 G8 first u)
    (step_taint first a u tn8) fn8 after
    (u with vs_inst_idx := SUC a.vs_inst_idx) oms8 (origin_step PG8 om8 first u) hs8
    (h8 ++ [OriginOrdinary fuel u; OriginObserve
      (OriginSnapshot fn8 PG8 (step_prov PG8 G8 first u)
        (origin_step PG8 om8 first u) after (u with vs_inst_idx := SUC a.vs_inst_idx))])` >>
  conj_tac >- (disj2_tac >> qexists_tac `SOME (OriginOrdinary fuel u)` >>
    simp[joint_transition_ordinary]) >>
  simp[cfg_norm_joint_cursors_def] >> gvs[]
QED

Theorem cfg_norm_joint_cursors_block:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  joint_transition C9
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9)
    (SOME (OriginBlock fuel post)) q9' ==>
  ?current' q8'.
    ((q8' = JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8 /\
      MEM inst9.inst_opcode [ASSIGN; JMP; JNZ] /\
      inst9.inst_opcode <> GAS /\ inst9.inst_opcode <> INVOKE /\
      inst_mem_ranges inst9 s9 = []) \/
     ?ev8. joint_transition C8
       (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8) ev8 q8') /\
    cfg_norm_joint_cursors C8 C9 (schedules,current',saved) q8' q9'
Proof
  strip_tac >> Cases_on `current` >>
  gvs[cfg_norm_joint_cursors_def, joint_transition_block_iff] >>
  qpat_assum `EVERY _ schedules` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then drule >> simp[] >> strip_tac >>
  drule_all cfg_norm_cursors_block_classified >> strip_tac
  >- (`inst_mem_ranges inst9 s9 = []` by
        (irule supply_inst_mem_ranges_empty >> gvs[]) >>
      Cases_on `HD cursors'` >> gvs[] >>
      qexistsl [`(q,cursors')`,
        `JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8`] >>
      simp[cfg_norm_joint_cursors_def] >> gvs[]) >>
  `r <> [] /\ cursors' <> []` by metis_tac[cfg_norm_cursors_lengths] >>
  Cases_on `HD cursors'` >> gvs[] >>
  `active_inst fn8 first a /\ active_inst fn8 after b` by
    (Cases_on `q` >> Cases_on `r` >> Cases_on `cursors'` >> gvs[] >>
     metis_tac[cfg_norm_cursors_head]) >>
  qexists_tac `(q,cursors')` >>
  qexists_tac `JointConfig stk8 PG8 (entry_prov fn8 u G8)
    (entry_taint_vars fn8 u tn8) fn8 after b oms8 (origin_entry fn8 u om8) hs8
    (h8 ++ [OriginBlock k u; OriginObserve
      (OriginSnapshot fn8 PG8 (entry_prov fn8 u G8)
        (origin_entry fn8 u om8) after b)])` >>
  conj_tac >- (disj2_tac >> qexists_tac `SOME (OriginBlock k u)` >>
    simp[joint_transition_block_iff]) >>
  simp[cfg_norm_joint_cursors_def] >> gvs[]
QED

Theorem cfg_norm_joint_cursors_call:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  joint_transition C9
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) NONE q9' ==>
  ?current' q8'.
    joint_transition C8
      (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8) NONE q8' /\
    cfg_norm_joint_cursors C8 C9 (schedules,current',current::saved) q8' q9'
Proof
  strip_tac >> Cases_on `current` >>
  gvs[cfg_norm_joint_cursors_def, joint_transition_call_iff] >>
  `LIST_REL (\sf tf. ?rs. MEM (sf,tf,rs) schedules)
    C8.ctx_functions C9.ctx_functions` by
    (qpat_x_assum `MAP FST schedules = _` (SUBST1_TAC o SYM) >>
     qpat_x_assum `MAP (FST o SND) schedules = _` (SUBST1_TAC o SYM) >>
     simp[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >>
     qexists_tac `SND (SND (EL n schedules))` >>
     simp[] >> metis_tac[MEM_EL]) >>
  qpat_assum `LIST_REL (\sf tf. ?rs. MEM (sf,tf,rs) schedules) _ _`
    (mp_then Any mp_tac list_rel_lookup_function) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    qpat_assum `EVERY _ schedules` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
    disch_then drule >> simp[] >> metis_tac[])) >>
  disch_then (qspec_then `nm` mp_tac) >> simp[] >>
  Cases_on `lookup_function nm C8.ctx_functions` >> simp[] >> strip_tac >>
  qpat_assum `EVERY _ schedules` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then drule >> simp[] >> strip_tac >>
  drule_all cfg_norm_cursors_call >> strip_tac >> gvs[] >>
  first_x_assum (qspec_then `C8` mp_tac) >>
  disch_then drule >> disch_then drule >> disch_then drule >> strip_tac >>
  `active_inst fn8 inst8 s8` by
    (qpat_assum `EVERY _ schedules` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `(fn8,fn9,q)` mp_tac) >> simp[] >> strip_tac >>
     `q <> [] /\ r <> []` by metis_tac[cfg_norm_cursors_lengths] >>
     Cases_on `q` >> Cases_on `r` >> gvs[] >>
     metis_tac[cfg_norm_cursors_head]) >>
  `active_inst x first a` by
    (`cur <> []` by metis_tac[cfg_norm_cursors_lengths] >>
     Cases_on `rs` >> Cases_on `cur` >> gvs[] >>
     metis_tac[cfg_norm_cursors_head]) >>
  qexistsl [`(rs,cur)`,
    `JointConfig
      (<|cf_fn := fn8; cf_inst := inst8; cf_state := s8; cf_params := PG8;
         cf_prov := G8; cf_tvar := tn8.t_var |> :: stk8)
      (MAP (op_prov G8) ops) FEMPTY (tn8 with t_var := FEMPTY) x first a
      (om8::oms8) FEMPTY (h8::hs8)
      [OriginCallee cs; OriginObserve
        (OriginSnapshot x (MAP (op_prov G8) ops) FEMPTY FEMPTY first a)]`] >>
  simp[cfg_norm_joint_cursors_def]
QED

Theorem cfg_norm_joint_cursors_return:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  joint_transition C9
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9)
    (SOME (OriginResume fuel fn9 inst9 s9 ret send post)) q9' ==>
  ?current' saved' q8' ev8.
    joint_transition C8
      (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8) ev8 q8' /\
    cfg_norm_joint_cursors C8 C9 (schedules,current',saved') q8' q9'
Proof
  strip_tac >> Cases_on `current` >>
  gvs[cfg_norm_joint_cursors_def, joint_transition_return] >>
  Cases_on `stk8` >> gvs[] >>
  Cases_on `oms8` >> gvs[] >> Cases_on `hs8` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  qpat_assum `EVERY _ schedules` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  disch_then (qspec_then `(h.cf_fn,f.cf_fn,x0)` mp_tac) >> simp[] >> strip_tac >>
  drule_all cfg_norm_cursors_ret >> strip_tac >>
  `active_inst fn8 inst8 s8` by
    (qpat_assum `EVERY _ schedules` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `(fn8,fn9,q)` mp_tac) >> simp[] >> strip_tac >>
     `q <> [] /\ r <> []` by metis_tac[cfg_norm_cursors_lengths] >>
     Cases_on `q` >> Cases_on `r` >> gvs[] >>
     metis_tac[cfg_norm_cursors_head]) >>
  `active_inst h.cf_fn next8 (w8 with vs_inst_idx := SUC h.cf_state.vs_inst_idx)` by
    (`saved' <> []` by metis_tac[cfg_norm_cursors_lengths] >>
     Cases_on `x0` >> Cases_on `saved'` >> gvs[] >>
     metis_tac[cfg_norm_cursors_head]) >>
  qexistsl [`(x0,saved')`, `xs`,
    `JointConfig t h.cf_params
      (DRESTRICT h.cf_prov (COMPL (set h.cf_inst.inst_outputs)))
      (tn8 with t_var := DRESTRICT h.cf_tvar (COMPL (set h.cf_inst.inst_outputs)))
      h.cf_fn next8 (w8 with vs_inst_idx := SUC h.cf_state.vs_inst_idx) t'
      (DRESTRICT h' (COMPL (set h.cf_inst.inst_outputs))) t''
      (h'' ++ [OriginResume fuel fn8 inst8 s8 ret e8 w8; OriginObserve
        (OriginSnapshot h.cf_fn h.cf_params
          (DRESTRICT h.cf_prov (COMPL (set h.cf_inst.inst_outputs)))
          (DRESTRICT h' (COMPL (set h.cf_inst.inst_outputs)))
          next8 (w8 with vs_inst_idx := SUC h.cf_state.vs_inst_idx))])`,
    `SOME (OriginResume fuel fn8 inst8 s8 ret e8 w8)`] >>
  simp[joint_transition_return, cfg_norm_joint_cursors_def]
QED

(* Stronger than the generic ML goal only in explicitly retaining the
   SAME schedules. Current/saved cells evolve through actual transitions. *)
Theorem cfg_norm_joint_cursors_step:
  !C8 C9 schedules current saved
    stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8
    stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9 ev q9'.
    cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
      (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
      (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
    joint_transition C9
      (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) ev q9' ==>
    mem_corr inst8 s8 inst9 s9 /\ call_corr inst8 s8 inst9 s9 /\
    (inst_mem_ranges inst9 s9 <> [] /\ ~in_revert_forward fn9 s9 ==>
      ~in_revert_forward fn8 s8) /\
    ?current' saved' q8'.
      ((q8' = JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8 /\
        MEM inst9.inst_opcode [ASSIGN; JMP; JNZ] /\
        inst9.inst_opcode <> GAS /\ inst9.inst_opcode <> INVOKE /\
        inst_mem_ranges inst9 s9 = []) \/
       ?ev8. joint_transition C8
         (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8) ev8 q8') /\
      cfg_norm_joint_cursors C8 C9 (schedules,current',saved') q8' q9'
Proof
  rpt gen_tac >> strip_tac >>
  `mem_corr inst8 s8 inst9 s9 /\ call_corr inst8 s8 inst9 s9 /\
   (inst_mem_ranges inst9 s9 <> [] /\ ~in_revert_forward fn9 s9 ==>
     ~in_revert_forward fn8 s8)` by
    (Cases_on `current` >> gvs[cfg_norm_joint_cursors_def] >>
     qpat_assum `EVERY _ schedules` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then drule >> simp[] >> strip_tac >>
     metis_tac[cfg_norm_cursors_projection]) >>
  simp[] >> drule joint_transition_label_cases >> strip_tac >> gvs[]
  >- (drule_all cfg_norm_joint_cursors_call >> metis_tac[])
  >- (drule_all cfg_norm_joint_cursors_ordinary >> simp[] >> metis_tac[])
  >- (drule_all cfg_norm_joint_cursors_block >> simp[] >> metis_tac[]) >>
  `fn = fn9 /\ inst = inst9 /\ s = s9` by
    gvs[joint_transition_return] >> gvs[] >>
  drule_all cfg_norm_joint_cursors_return >> metis_tac[]
QED
