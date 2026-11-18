(* The normal LowerDload call at the actual target entry, with both ghosts. *)
Theory gasFocusLowerDloadFrameCallEntry
Ancestors
  gasFocusLowerDloadInvokeSetup gasFocusLowerDloadCutGuards
  lowerDloadPtrNormalPush lowerDloadPtrPhase lowerDloadPtrRel lowerDloadPtrJointScalar
  lowerDloadSafetyBoundary lowerDloadSafetyRelation lowerDloadSafetyAmbient
  lowerDloadSafetyKernel lowerDloadPtrInvoke lowerDloadPtrStatic o1LowerDloadJointScalar
  lowerDloadReturnInvokePush lowerDloadReturnInvokeStack lowerDloadReturnAlignment
  lowerDloadLiveAllocation lowerDloadOracleCallAssembly
  o1ContractLowerDload o1PassContract o1SafeUpto calleeTransport ptrDiscipline
  unitShapeDefs venomWf venomExecSemantics venomInst venomState
  finite_map list pair pred_set
Libs
  lowerDloadReturnPackageLib

Theorem ld_frame_invoke_singleton[local]:
  dload_control_match q fn gn s t inst X h /\ ti = EL h X /\
  ti.inst_opcode = INVOKE ==> inst = ti /\ X = [ti] /\ h = 0
Proof
  strip_tac >> drule_then strip_assume_tac dload_control_match_expansion >>
  `MEM ti X` by metis_tac[EL_MEM] >>
  `ti = inst` by
    (irule lower_dload_inst_supply_control >> conj_tac
     >- (qexistsl [`is`, `after`, `X`] >> metis_tac[]) >> simp[]) >>
  `lower_dload_inst_supply is inst = ([inst],is)` by
    (irule lower_dload_inst_supply_special >> gvs[]) >>
  `X = [inst]` by metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `ti = EL h X` kall_tac >> gvs[]
QED

Theorem ld_frame_control_envelope[local]:
  dload_control_match q fn gn s t inst X 0 ==>
  ld_envelope q fn s s.vs_inst_idx X t.vs_inst_idx
Proof
  rw[dload_control_match_def, ld_envelope_def] >> metis_tac[FST, SND]
QED

Theorem ld_frame_call_taint[local]:
  ptr_discipline_upto lo n C vs /\
  ld_sync lo P C vs stk PG G tn fn inst s t A frames N /\
  s.vs_gas_readings = t.vs_gas_readings /\
  setup_callee gcallee ys t = SOME v /\ enters_block gcallee v t1 /\
  gas_cut n vs t1 ==> taint_ok fn tn inst s
Proof
  strip_tac >> drule_all_then assume_tac ld_callee_entry_cut_back >>
  drule_then strip_assume_tac ld_sync_source >>
  `gas_cut n vs s` by gvs[gas_cut_def] >>
  fs[ptr_discipline_upto_def] >> metis_tac[]
QED

Theorem ld_frame_call_operational_push[local]:
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  lookup_function nm C.ctx_functions = SOME callee /\
  setup_callee callee argsS s = SOME cs /\
  setup_callee gcallee argsT t = SOME ct /\
  cs.vs_current_bb = ct.vs_current_bb /\ cs.vs_prev_bb = ct.vs_prev_bb /\
  fc = <|lf_serial := N; lf_supply := q; lf_fn := callee;
    lf_src := cs; lf_tgt := ct; lf_H := FEMPTY;
    lf_Q := MAP (op_prov f.lf_H) ops; lf_E := {}; lf_tv := FEMPTY|> /\
  saved = <|cf_fn := fn; cf_inst := inst; cf_state := s;
    cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> /\
  frame_reachable vs C (saved::stk) (MAP (op_prov G) ops) FEMPTY
    (tn with t_var := FEMPTY) callee i cs /\
  ld_memory lo A (tn with t_var := FEMPTY) cs ct /\
  ld_nonghost (tn with t_var := FEMPTY) cs ct /\
  ld_vars P A fc /\ active_inst callee i cs /\
  ld_envelope q callee cs cs.vs_inst_idx X ct.vs_inst_idx ==>
  ld_sync lo P C vs (saved::stk) (MAP (op_prov G) ops) FEMPTY
    (tn with t_var := FEMPTY) callee i cs ct A (fc::f::fs) (SUC N)
Proof
  strip_tac >> drule_then strip_assume_tac ld_sync_active >>
  `MEM callee C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `cs.vs_allocas = FEMPTY /\ cs.vs_alloca_next = s.vs_alloca_next /\
   ct.vs_allocas = FEMPTY /\ ct.vs_alloca_next = t.vs_alloca_next` by
    metis_tac[ld_setup_empty_shape] >>
  `ld_dyn_agree (dyn_floor C vs) tn.t_mem cs.vs_memory ct.vs_memory` by
    (drule_then strip_assume_tac ld_sync_dyn_agree >>
     qpat_assum `setup_callee callee _ s = SOME cs`
       (mp_then Any strip_assume_tac setup_callee_shared_fields) >>
     qpat_assum `setup_callee gcallee _ t = SOME ct`
       (mp_then Any strip_assume_tac setup_callee_shared_fields) >> fs[]) >>
  `ld_params_ok (dyn_floor C vs) A (MAP (op_prov f.lf_H) ops)
    (MAP (op_prov G) ops)` by
    (drule_then strip_assume_tac ld_sync_ghosts >>
     rw[ld_params_ok_def, EL_MAP] >>
     Cases_on `EL k ops` >> simp[op_prov_def] >>
     rename1 `FLOOKUP f.lf_H v` >> Cases_on `FLOOKUP f.lf_H v` >>
     fs[ld_ghost_ok_def] >> metis_tac[]) >>
  `ld_sync lo P C vs (saved::stk) (MAP (op_prov G) ops)
    (ld_erase A o_f fc.lf_H) (tn with t_var := FEMPTY) fc.lf_fn i
    fc.lf_src fc.lf_tgt A (fc::f::fs) (SUC N)` suffices_by gvs[] >>
  irule ld_sync_call_push >> goal_assum (drule_at Any) >>
  gvs[ld_maps_def, ld_intervals_def] >> metis_tac[]
QED

Theorem ld_frame_call_stable[local]:
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  callee_first names C.ctx_functions /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  fc.lf_fn.fn_name = nm /\ fc.lf_supply = Sigma nm /\
  fc.lf_src.vs_allocas = FEMPTY /\ fc.lf_tgt.vs_allocas = FEMPTY /\
  fc.lf_src.vs_alloca_next = s.vs_alloca_next /\
  fc.lf_tgt.vs_alloca_next = t.vs_alloca_next /\ fc.lf_H = FEMPTY /\
  (!a. MEM (SOME a) fc.lf_Q ==> a IN FDOM A) /\
  (!j a. j < LENGTH fc.lf_Q /\ EL j fc.lf_Q = SOME a ==> j IN P nm) ==>
  ^ld_probe_stable lo P Sigma names (f::fs) fc A A (fc::f::fs)
Proof
  qabbrev_tac `Stable = ^ld_probe_stable` >> strip_tac >>
  drule_then strip_assume_tac ld_sync_source >>
  drule_then (strip_assume_tac o SRULE []) ld_sync_active >>
  `MEM fn C.ctx_functions` by gvs[ld_sync_def] >>
  `MEM nm (fn_invoke_targets fn)` by
    (irule active_invoke_target >> goal_assum (drule_at Any) >> simp[]) >>
  `list_precedes nm fn.fn_name names` by
    (gvs[callee_first_def] >> metis_tac[]) >>
  `!g. MEM g (f::fs) ==> list_precedes nm g.lf_fn.fn_name names` by
    (gen_tac >> simp[] >> strip_tac >- simp[] >>
     `?j. j < LENGTH fs /\ g = EL j fs` by metis_tac[MEM_EL] >>
     `list_precedes f.lf_fn.fn_name g.lf_fn.fn_name names` by
       (qpat_assum `Stable lo P Sigma names fs0 f0 A0 A (f::fs)` mp_tac >>
        simp[NoAsms, Abbr `Stable`] >> strip_tac >>
        qpat_x_assum `!j k. _ ==> list_precedes _ _ names`
          (qspecl_then [`0`,`SUC j`] mp_tac) >> simp[]) >>
     metis_tac[list_precedes_transitive]) >>
  qunabbrev_tac `Stable` >> irule ld_call_stable_push >>
  drule_then strip_assume_tac ld_sync_slots >> simp[] >>
  qexistsl [`A0`,`f0`] >> gvs[]
  >> (metis_tac[])
QED

Theorem ld_focus_frame_call_entry:
  o1_ctx_shape C /\ callee_first names C.ctx_functions /\
  (!g. MEM g C.ctx_functions ==>
    ir_supply_covers_fn (Sigma g.fn_name) g /\ fn_ptr_ok P g /\
    lookup_function g.fn_name C'.ctx_functions =
      SOME (FST (lower_dload_function_supply (Sigma g.fn_name) g))) /\
  ptr_discipline_upto lo n C vs /\
  ld_sync lo P C vs stk PG G tn fn inst s t0 A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  ld_prefix C' gn X p h t0 t /\ call = EL h X /\
  dload_control_match f.lf_supply fn gn s t inst X h /\
  dload_prefix_match pfuel C' PH X h t0 H0 un0 t H un /\
  dload_boundary_core (dyn_floor C vs) lo rs
    (set (fn_ir_vars fn) DIFF {a | retpc_var fn a})
    (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {a | retpc_var c.cf_fn a}) stk)
    PG PH G H0 tn un0 s t0 stk ds /\
  (!a. a IN set (fn_ir_vars fn) ==>
    (lookup_var a s = NONE <=> lookup_var a t0 = NONE)) /\
  LENGTH rs = SUC (LENGTH stk) /\ LENGTH stk = LENGTH ds /\
  (!k. k < LENGTH ds ==>
    (EL k ds).cf_fn = ld_image (EL (SUC k) (f::fs)) /\
    (EL k ds).cf_state = (EL (SUC k) (f::fs)).lf_tgt) /\
  (!k. k < LENGTH rs ==>
    (EL k rs).dr_scratch =
      FDOM (EL k (t0::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
      {id | ?i. MEM i (fn_insts (EL k (fn::MAP (\c. c.cf_fn) stk))) /\
                i.inst_id = id}) /\
  (!k. k < LENGTH stk ==>
    dload_live_layout lo (EL k stk).cf_state.vs_alloca_next
      (EL k ds).cf_state.vs_alloca_next (DROP (SUC k) rs) /\
    dload_equal_environment (EL k stk).cf_state (EL k ds).cf_state /\
    (EL k stk).cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
    (EL k stk).cf_inst = (EL k ds).cf_inst /\
    (!a. a IN set (fn_ir_vars (EL k stk).cf_fn) ==>
      (lookup_var a (EL k stk).cf_state = NONE <=>
       lookup_var a (EL k ds).cf_state = NONE)) /\
    (?q. ir_supply_covers_fn q (EL k stk).cf_fn /\
      (?q'. lower_dload_function_supply q (EL k stk).cf_fn = ((EL k ds).cf_fn,q')) /\
      dload_control_match q (EL k stk).cf_fn (EL k ds).cf_fn
        (EL k stk).cf_state (EL k ds).cf_state (EL k stk).cf_inst
        [(EL k stk).cf_inst] 0)) /\
  s.vs_gas_readings = t0.vs_gas_readings /\
  EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
    LENGTH s.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) (f::fs) /\
  call.inst_opcode = INVOKE /\ decode_invoke call = SOME (nm,ops) /\
  lookup_function nm C'.ctx_functions = SOME gcallee /\
  eval_operands ops t = SOME argsT /\ setup_callee gcallee argsT t = SOME ct /\
  enters_block gcallee ct tp /\ active_inst gcallee ti tp /\ gas_cut n vs tp ==>
  ?callee cs i emitted fc.
    let saved = <|cf_fn := fn; cf_inst := call; cf_state := s;
                   cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|>;
        savedT = <|cf_fn := gn; cf_inst := call; cf_state := t;
                    cf_params := PH; cf_prov := H; cf_tvar := un.t_var|>;
        rs' = (<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|>)::rs
    in
    tp = ct /\ fc.lf_supply = Sigma callee.fn_name /\
    gcallee = ld_image fc /\
    ld_sync lo P C vs (saved::stk) (MAP (op_prov G) ops) FEMPTY
      (tn with t_var := FEMPTY) callee i cs tp A (fc::f::fs) (SUC N) /\
    ^ld_probe_stable lo P Sigma names (f::fs) fc A A (fc::f::fs) /\
    ld_envelope fc.lf_supply callee cs cs.vs_inst_idx emitted tp.vs_inst_idx /\
    ld_prefix C' gcallee emitted tp.vs_inst_idx 0 tp tp /\ ti = EL 0 emitted /\
    dload_boundary_core (dyn_floor C vs) lo rs'
      (set (fn_ir_vars callee) DIFF {a | retpc_var callee a})
      (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {a | retpc_var c.cf_fn a}) (saved::stk))
      (MAP (op_prov G) ops) (MAP (op_prov H) ops) FEMPTY FEMPTY
      (tn with t_var := FEMPTY) (un with t_var := FEMPTY) cs tp (saved::stk) (savedT::ds) /\
    dload_control_match fc.lf_supply callee gcallee cs tp i emitted 0 /\
    dload_prefix_match pfuel C' (MAP (op_prov H) ops) emitted 0
      tp FEMPTY (un with t_var := FEMPTY) tp FEMPTY (un with t_var := FEMPTY) /\
    (!a. a IN set (fn_ir_vars callee) ==>
      (lookup_var a cs = NONE <=> lookup_var a tp = NONE)) /\
    (!k. k < LENGTH (savedT::ds) ==>
      (EL k (savedT::ds)).cf_fn = ld_image (EL (SUC k) (fc::f::fs)) /\
      (EL k (savedT::ds)).cf_state = (EL (SUC k) (fc::f::fs)).lf_tgt) /\
    LENGTH rs' = SUC (LENGTH (saved::stk)) /\ LENGTH (saved::stk) = LENGTH (savedT::ds) /\
    (!k. k < LENGTH rs' ==>
      (EL k rs').dr_scratch =
        FDOM (EL k (tp::MAP (\d. d.cf_state) (savedT::ds))).vs_allocas DIFF
        {id | ?j. MEM j (fn_insts (EL k (callee::MAP (\c. c.cf_fn) (saved::stk)))) /\
                  j.inst_id = id}) /\
    (!k. k < LENGTH (saved::stk) ==>
      dload_live_layout lo (EL k (saved::stk)).cf_state.vs_alloca_next
        (EL k (savedT::ds)).cf_state.vs_alloca_next (DROP (SUC k) rs') /\
      dload_equal_environment (EL k (saved::stk)).cf_state (EL k (savedT::ds)).cf_state /\
      (EL k (saved::stk)).cf_state.vs_call_ctx.cc_address = cs.vs_call_ctx.cc_address /\
      (EL k (saved::stk)).cf_inst = (EL k (savedT::ds)).cf_inst /\
      (!a. a IN set (fn_ir_vars (EL k (saved::stk)).cf_fn) ==>
        (lookup_var a (EL k (saved::stk)).cf_state = NONE <=>
         lookup_var a (EL k (savedT::ds)).cf_state = NONE)) /\
      (?q. ir_supply_covers_fn q (EL k (saved::stk)).cf_fn /\
        (?q'. lower_dload_function_supply q (EL k (saved::stk)).cf_fn =
                ((EL k (savedT::ds)).cf_fn,q')) /\
        dload_control_match q (EL k (saved::stk)).cf_fn (EL k (savedT::ds)).cf_fn
          (EL k (saved::stk)).cf_state (EL k (savedT::ds)).cf_state
          (EL k (saved::stk)).cf_inst [(EL k (saved::stk)).cf_inst] 0)) /\
    cs.vs_gas_readings = tp.vs_gas_readings /\
    EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
      LENGTH cs.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) (fc::f::fs)
Proof
  qabbrev_tac `Stable = ^ld_probe_stable` >> strip_tac >>
  drule_all_then strip_assume_tac ld_frame_invoke_singleton >>
  qpat_x_assum `h = 0` SUBST_ALL_TAC >>
  qpat_x_assum `X = [call]` SUBST_ALL_TAC >>
  qpat_x_assum `inst = call` SUBST_ALL_TAC >>
  qpat_x_assum `ld_prefix _ _ _ _ _ _ _`
    (strip_assume_tac o SRULE[ld_prefix_zero]) >>
  qpat_x_assum `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SRULE[dload_prefix_match_def]) >>
  qpat_x_assum `t = t0` SUBST_ALL_TAC >>
  qpat_x_assum `H = H0` SUBST_ALL_TAC >>
  qpat_x_assum `un = un0` SUBST_ALL_TAC >>
  drule_all_then assume_tac ld_frame_call_taint >>
  `ld_global lo A (f::fs)` by fs[Abbr `Stable`] >>
  `!g. MEM g C.ctx_functions ==> lookup_function g.fn_name C'.ctx_functions =
    SOME (FST (lower_dload_function_supply (Sigma g.fn_name) g))` by metis_tac[] >>
  drule_all_then strip_assume_tac ld_focus_invoke_correlated_setup >>
  drule_then strip_assume_tac ld_sync_source >>
  drule_then (strip_assume_tac o SRULE []) ld_sync_active >>
  `MEM fn C.ctx_functions` by gvs[ld_sync_def] >>
  `MEM callee C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `o1_fn_shape C fn /\ o1_fn_shape C callee` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `opaque_use_ok fn /\ first_block_no_phi callee /\ ~NULL callee.fn_blocks` by
    (fs[o1_fn_shape_def, fn_shape_ok_def, fn_entry_label_def, entry_block_def] >>
     Cases_on `callee.fn_blocks` >> gvs[]) >>
  `!a. MEM (Var a) ops ==> a IN (set (fn_ir_vars fn) DIFF {a | retpc_var fn a})` by
    (`!v. ~retpc_use_ok call v` by simp[retpc_use_ok_def] >>
     `!a. MEM (Var a) ops ==> MEM (Var a) call.inst_operands` by
       gvs[decode_invoke_def, AllCaseEqs()] >>
     simp[] >> metis_tac[fn_ir_vars_operand, ld_active_inst_member,
                          ld_active_operand_non_retpc]) >>
  `?qc'. lower_dload_function_supply f.lf_supply fn = (gn,qc')` by
    fs[dload_control_match_def] >>
  `lower_dload_function_supply (Sigma nm) callee =
    (gcallee,SND (lower_dload_function_supply (Sigma nm) callee))` by
    metis_tac[pairTheory.PAIR] >>
  `gn = ld_image f` by simp[ld_image_def] >>
  `f.lf_supply = Sigma fn.fn_name` by fs[Abbr `Stable`] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) gcallee.fn_blocks)` by
    metis_tac[o1_fn_shape_components, lower_dload_function_supply_labels, fn_labels_def] >>
  `ir_supply_covers_fn f.lf_supply fn /\ ir_supply_covers_fn (Sigma nm) callee /\
   (!g. MEM g C.ctx_functions ==> fn_ptr_ok P g)` by metis_tac[] >>
  drule_all_then strip_assume_tac dload_normal_invoke_call >>
  `xs = argsS` by fs[] >>
  qpat_x_assum `xs = argsS` SUBST_ALL_TAC >>
  `u = cs` by fs[] >>
  qpat_x_assum `u = cs` SUBST_ALL_TAC >>
  `first_block_no_phi gcallee` by
    (irule lower_dload_function_supply_first_no_phi >>
     goal_assum (drule_at Any) >> fs[NULL_EQ]) >>
  `tp = ct` by metis_tac[dload_setup_no_phi_entry] >>
  qpat_x_assum `tp = ct` SUBST_ALL_TAC >>
  qpat_assum `dload_control_match _ callee gcallee cs ct i emitted 0`
    (mp_then Any strip_assume_tac dload_control_match_boundary) >>
  `ld_envelope (Sigma nm) callee cs cs.vs_inst_idx emitted ct.vs_inst_idx` by
    (irule ld_frame_control_envelope >> goal_assum (drule_at Any)) >>
  qabbrev_tac `fc = <|lf_serial := N; lf_supply := Sigma nm; lf_fn := callee;
    lf_src := cs; lf_tgt := ct; lf_H := FEMPTY;
    lf_Q := MAP (op_prov f.lf_H) ops; lf_E := {}; lf_tv := FEMPTY|>` >>
  qabbrev_tac `saved = <|cf_fn := fn; cf_inst := call; cf_state := s;
    cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|>` >>
  `ld_sync lo P C vs (saved::stk) (MAP (op_prov G) ops) FEMPTY
    (tn with t_var := FEMPTY) callee i cs ct A (fc::f::fs) (SUC N)` by
    (irule ld_frame_call_operational_push >> goal_assum (drule_at Any) >>
     simp[Abbr `fc`, Abbr `saved`] >> metis_tac[]) >>
  qpat_assum `setup_callee callee _ s = SOME cs`
    (mp_then Any strip_assume_tac ld_setup_empty_shape) >>
  qpat_assum `setup_callee gcallee _ t0 = SOME ct`
    (mp_then Any strip_assume_tac ld_setup_empty_shape) >>
  `Stable lo P Sigma names (f::fs) fc A A (fc::f::fs)` by
    (qunabbrev_tac `Stable` >>
     qpat_assum `ld_sync lo P C vs stk PG G tn fn call s t0 A (f::fs) N`
       (mp_then Any irule ld_frame_call_stable) >>
     simp[Abbr `fc`] >>
     qexistsl [`A0`, `f0`] >>
     qpat_assum `^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs)`
       (strip_assume_tac o SRULE[]) >>
     gvs[] >>
     qpat_assum `!g. MEM g fs ==> FRANGE g.lf_H SUBSET ld_slots A fs /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `fc.lf_supply = Sigma nm /\ gcallee = ld_image fc /\
   fc.lf_src = cs /\ fc.lf_tgt = ct` by simp[Abbr `fc`, ld_image_def] >>
  `0 < LENGTH emitted` by metis_tac[dload_control_match_expansion] >>
  qexistsl [`callee`,`cs`,`i`,`emitted`,`fc`] >>
  rewrite_tac[LET_THM] >> BETA_TAC >>
  qpat_assum `callee.fn_name = nm` (rewrite_tac o single) >>
  qpat_assum `fc.lf_supply = Sigma nm` (rewrite_tac o single) >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (rewrite_tac[ld_prefix_zero, EL] >> conj_tac >> first_assum ACCEPT_TAC)
  >- simp[]
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- rewrite_tac[dload_prefix_match_def]
  >- simp[]
  >- (Cases >> simp[] >> strip_tac >>
      qpat_assum `!k. k < LENGTH ds ==> _` drule >> simp[])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC >>
  simp[Abbr `fc`] >>
  qpat_assum `EVERY _ (f::fs)` mp_tac >>
  rewrite_tac[EVERY_DEF] >>
  qpat_assum `s.vs_gas_readings = t0.vs_gas_readings` (rewrite_tac o single) >>
  disch_then (ACCEPT_TAC o CONJUNCT2)
QED
