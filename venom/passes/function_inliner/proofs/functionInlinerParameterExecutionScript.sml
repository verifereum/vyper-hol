(* Produced execution of the selected entry parameter interval. *)
Theory functionInlinerParameterExecution
Ancestors
  functionInlinerParameterReady functionInlinerParameterLifecycle
  functionInlinerParameterSequential functionInlinerParameterLocations
  functionInlinerActivation functionInlinerOperationalCuts
  venomExecSemantics venomInstProps venomState venomInst list pred_set

Theorem inline_parameter_finite_sequence[local]:
  !N P R t0.
    P 0 t0 /\
    (!k t. k < N /\ P k t ==> ?t'. R k t t' /\ P (SUC k) t') ==>
    ?T. T 0 = t0 /\
      (!k. k <= N ==> P k (T k)) /\
      (!k. k < N ==> R k (T k) (T (SUC k)))
Proof
  Induct >- (rpt strip_tac >> qexists `K t0` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `?T. T 0 = t0 /\ (!k. k <= N ==> P k (T k)) /\
       (!k. k < N ==> R k (T k) (T (SUC k)))` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> decide_tac) >>
  rename1 `seq 0 = t0` >>
  `?t'. R N (seq N) t' /\ P (SUC N) t'` by
    (first_x_assum irule >> simp[]) >>
  qexists `\k. if k = SUC N then t' else seq k` >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> IF_CASES_TAC >> simp[] >>
      first_x_assum irule >> decide_tac) >>
  rpt strip_tac >> Cases_on `k = N` >> simp[] >>
  `k < N /\ k <> SUC N /\ SUC k <> SUC N` by decide_tac >> simp[]
QED

Theorem inline_parameter_prefix_execute[local]:
  inliner_input_ok C /\ inline_annotated_origin C n root cert /\
  inline_call_incidence cert root p fn l j orig (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q sigma child /\ ca.ia_function = child /\
  child.fn_blocks = entry::rest /\ entry.bb_instructions = params ++ tail /\
  param_insts_from 0 params /\
  inline_parameter_boundary_path (InlineEnter e::zipper)
    e.ise_callee entry.bb_label 0 root ml mj /\
  inline_original_child C cfuel pa.ia_id occurrence orig saved r ca cr /\
  pa.ia_function = fn /\
  inline_owner_storage cert
    ((q,ca,route,snap)::(p,pa,proute,psnap)::entries) frame /\
  inline_parameter_saved_reads
    ((q,ca,route,snap)::(p,pa,proute,psnap)::entries) /\
  inline_parameter_ancestry C cert root
    (inline_parameter_owners ((q,ca,route,snap)::(p,pa,proute,psnap)::entries)) /\
  snap.ils_state = ca.ia_entry /\ snap.ils_defined = {} /\
  ss 0 = ca.ia_entry /\ (ss 0).vs_inst_idx = 0 /\
  frame.ipf_state.vs_current_bb = ml /\ frame.ipf_state.vs_inst_idx = mj /\
  (!k. k < LENGTH params ==> ?s'.
    step_inst fuel C (EL k params) (ss k) = OK s' /\
    ss (SUC k) = s' with vs_inst_idx := SUC (ss k).vs_inst_idx) ==>
  ?ts.
    ts 0 = frame.ipf_state /\
    (!k. k <= LENGTH params ==>
      (ss k).vs_inst_idx = k /\
      (ss k).vs_params = ca.ia_entry.vs_params /\
      (ss k).vs_return_pc_token = ca.ia_entry.vs_return_pc_token /\
      (ts k).vs_current_bb = ml /\ (ts k).vs_inst_idx = mj+k /\
      inline_owner_storage cert
        ((q,ca,route,snap with <|ils_state := ss k;
          ils_defined := set (FLAT (MAP (\i. i.inst_outputs) (TAKE k params)))|>)::
         (p,pa,proute,psnap)::entries) (frame with ipf_state := ts k) /\
      inline_parameter_saved_reads
        ((q,ca,route,snap with <|ils_state := ss k;
          ils_defined := set (FLAT (MAP (\i. i.inst_outputs) (TAKE k params)))|>)::
         (p,pa,proute,psnap)::entries) /\
      inline_parameter_ancestry C cert root
        (inline_parameter_owners
          ((q,ca,route,snap with <|ils_state := ss k;
            ils_defined := set (FLAT (MAP (\i. i.inst_outputs) (TAKE k params)))|>)::
           (p,pa,proute,psnap)::entries))) /\
    (!k. k < LENGTH params ==> ?bb inst t.
      lookup_block ml root.fn_blocks = SOME bb /\
      get_instruction bb (ts k).vs_inst_idx = SOME inst /\
      ~is_terminator inst.inst_opcode /\
      step_inst tfuel Tctx inst (ts k) = OK t /\
      ts (SUC k) = t with vs_inst_idx := SUC (ts k).vs_inst_idx)
Proof
  strip_tac >> ho_match_mp_tac inline_parameter_finite_sequence >>
  conj_tac
  >- (`snap with <|ils_state := ca.ia_entry; ils_defined := {}|> = snap` by
        simp[inline_logical_snapshot_component_equality] >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!k. k < LENGTH params ==> ?s'. _`
    (qspec_then `k` mp_tac) >> simp[] >> strip_tac >>
  drule_at (Pat `inline_call_incidence cert root p fn l j orig outcome`)
    inline_selected_parameter_ready_step >>
  disch_then (drule_at (Pat `param_insts_from 0 params`)) >>
  disch_then (drule_at (Pat `inline_owner_storage cert entries frame`)) >>
  fs[] >> disch_then (drule_at (Pat `step_inst fuel C src s = OK s'`)) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`tfuel`,`Tctx`] strip_assume_tac) >>
  `t'.vs_current_bb = t.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `set (FLAT (MAP (\i. i.inst_outputs) (TAKE (SUC k) params))) =
   x INSERT set (FLAT (MAP (\i. i.inst_outputs) (TAKE k params)))` by
    simp[rich_listTheory.TAKE_SUC_BY_TAKE, rich_listTheory.SNOC_APPEND,
         MAP_APPEND, FLAT_APPEND, INSERT_UNION_EQ, UNION_COMM] >>
  qexists `t' with vs_inst_idx := mj+SUC k` >>
  fs[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD_COMM] >> metis_tac[]
QED

(* Entry positioning is explicit.  This boundary does not pretend to execute
   the caller's jump, and is the unchanged incoming state when already there. *)
Theorem inline_selected_parameters_execute:
  inliner_input_ok C /\ inline_annotated_origin C n root cert /\
  inline_owner_storage cert ((p,pa,proute,psnap)::entries) frame /\
  inline_original_child C cfuel pa.ia_id occurrence orig psnap.ils_state r ca cr /\
  inline_call_incidence cert root p pa.ia_function l j orig
    (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q route.ir_rename ca.ia_function /\
  inline_parameter_saved_reads ((p,pa,proute,psnap)::entries) /\
  inline_parameter_ancestry C cert root
    (inline_parameter_owners ((p,pa,proute,psnap)::entries)) /\
  ca.ia_function.fn_blocks = entry::rest /\
  entry.bb_instructions = params ++ tail /\ param_insts_from 0 params /\
  ss 0 = ca.ia_entry /\
  (!k. k < LENGTH params ==> ?s'.
    step_inst fuel C (EL k params) (ss k) = OK s' /\
    ss (SUC k) = s' with vs_inst_idx := SUC (ss k).vs_inst_idx) ==>
  ?ml mj bb snap ts.
    lookup_block ml root.fn_blocks = SOME bb /\
    mj + LENGTH params <= LENGTH bb.bb_instructions /\
    inline_parameter_boundary_path (InlineEnter e::zipper)
      e.ise_callee entry.bb_label 0 root ml mj /\
    inline_parameter_boundary_path (InlineEnter e::zipper)
      e.ise_callee entry.bb_label (LENGTH params) root ml (mj+LENGTH params) /\
    snap.ils_state = ca.ia_entry /\ snap.ils_defined = {} /\
    snap.ils_saved = psnap.ils_state /\
    snap.ils_protected = (psnap.ils_defined DIFF psnap.ils_opaque) DIFF set orig.inst_outputs /\
    snap.ils_parent_rename = proute.ir_rename /\
    ts 0 = frame.ipf_state with <|vs_current_bb := ml; vs_inst_idx := mj|> /\
    (frame.ipf_state.vs_current_bb = ml /\ frame.ipf_state.vs_inst_idx = mj ==>
      ts 0 = frame.ipf_state) /\
    (!k. k < LENGTH params ==> ?inst t.
      get_instruction bb (ts k).vs_inst_idx = SOME inst /\
      ~is_terminator inst.inst_opcode /\
      step_inst tfuel Tctx inst (ts k) = OK t /\
      ts (SUC k) = t with vs_inst_idx := SUC (ts k).vs_inst_idx) /\
    exec_block tfuel Tctx bb (ts 0) = exec_block tfuel Tctx bb (ts (LENGTH params)) /\
    (ss (LENGTH params)).vs_inst_idx = LENGTH params /\
    (ts (LENGTH params)).vs_current_bb = ml /\
    (ts (LENGTH params)).vs_inst_idx = mj+LENGTH params /\
    inline_owner_storage cert
      ((q,ca,route,snap with <|ils_state := ss (LENGTH params);
        ils_defined := set (FLAT (MAP (\i. i.inst_outputs) params))|>)::
       (p,pa,proute,psnap)::entries)
      (frame with ipf_state := ts (LENGTH params)) /\
    inline_parameter_saved_reads
      ((q,ca,route,snap with <|ils_state := ss (LENGTH params);
        ils_defined := set (FLAT (MAP (\i. i.inst_outputs) params))|>)::
       (p,pa,proute,psnap)::entries) /\
    inline_parameter_ancestry C cert root
      (inline_parameter_owners
        ((q,ca,route,snap with <|ils_state := ss (LENGTH params);
          ils_defined := set (FLAT (MAP (\i. i.inst_outputs) params))|>)::
         (p,pa,proute,psnap)::entries))
Proof
  strip_tac >>
  drule_all inline_selected_parameter_interval >> strip_tac >>
  drule_all inline_parameter_lifecycle_selected_push >> strip_tac >>
  rename1 `snap.ils_defined = {}` >>
  `(ss 0).vs_inst_idx = 0` by
    (fs[inline_original_child_def] >>
     qpat_x_assum `setup_callee _ _ _ = SOME _` mp_tac >>
     simp[setup_callee_def] >> strip_tac >>
     qpat_x_assum `_ = ca.ia_entry` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  `inline_owner_storage cert
    ((q,ca,route,snap)::(p,pa,proute,psnap)::entries)
    (frame with ipf_state := frame.ipf_state with <|
      vs_current_bb := ml; vs_inst_idx := mj|>)` by
    (qpat_assum `inline_owner_storage cert ((q,ca,route,snap)::_) frame`
       (mp_then Any mp_tac inline_owner_storage_projections) >> simp[] >>
     disch_then (qspecl_then [
       `frame.ipf_state with <|vs_current_bb := ml; vs_inst_idx := mj|>`,
       `snap.ils_state`] mp_tac) >>
     `snap with ils_state := ca.ia_entry = snap` by
       simp[inline_logical_snapshot_component_equality] >> simp[]) >>
  drule_at (Pat `inline_call_incidence cert root p fn l j orig outcome`)
    inline_parameter_prefix_execute >>
  disch_then (drule_at (Pat `param_insts_from 0 params`)) >>
  disch_then (drule_at (Pat `inline_owner_storage cert entries frame`)) >>
  fs[] >> disch_then drule_all >>
  disch_then (qspecl_then [`tfuel`,`Tctx`] strip_assume_tac) >>
  qpat_assum `!k. k <= LENGTH params ==> _`
    (qspec_then `LENGTH params` (strip_assume_tac o SRULE [])) >>
  `?bb. lookup_block ml root.fn_blocks = SOME bb /\
        mj+LENGTH params <= LENGTH bb.bb_instructions` by
    fs[inline_parameter_interval_def] >>
  `!k. k < LENGTH params ==> ?inst t.
    get_instruction bb (ts k).vs_inst_idx = SOME inst /\
    ~is_terminator inst.inst_opcode /\ step_inst tfuel Tctx inst (ts k) = OK t /\
    ts (SUC k) = t with vs_inst_idx := SUC (ts k).vs_inst_idx` by
    (rpt strip_tac >>
     qpat_x_assum `!k. k < LENGTH params ==> ?bb inst t. _`
       (qspec_then `k` mp_tac) >> simp[] >> metis_tac[]) >>
  `exec_block tfuel Tctx bb (ts 0) = exec_block tfuel Tctx bb (ts (LENGTH params))` by
    (qabbrev_tac `es = GENLIST (\k. THE (get_instruction bb (ts k).vs_inst_idx)) (LENGTH params)` >>
     qspecl_then [`es`,`ts`,`mj`]
       (mp_tac o Q.INST [`fuel` |-> `tfuel`, `C` |-> `Tctx`])
       inline_parameter_sequential_exec >>
     simp[Abbr `es`] >> impl_tac
     >- (qx_gen_tac `k` >> strip_tac >>
         qpat_x_assum `!k. k < LENGTH params ==> ?inst t.
           get_instruction bb _ = SOME inst /\ _`
           (qspec_then `k` mp_tac) >>
         (impl_tac >- simp[]) >> strip_tac >> gvs[]) >>
     simp[]) >>
  qexistsl [`mj`,`bb`,`snap`,`ts`] >>
  simp[] >> rpt strip_tac >> simp[venom_state_component_equality]
QED
