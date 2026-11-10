(* Addressed owner-local data storage, separate from operational reachability. *)
Theory functionInlinerOperationalCuts
Ancestors
  functionInlinerReachableCuts functionInlinerStackSupports functionInlinerCuts
  functionInlinerOccurrences
  functionInlinerActivation functionInlinerEnvelopes venomState cfgTransform list pred_set
  venomExecSemantics

Definition inline_owner_storage_def:
  inline_owner_storage cert entries frame <=>
    inline_address_stack cert entries /\
    inline_addresses_ordered (MAP FST entries) /\
    inline_suspended_observations (inline_erase_addresses entries) frame
End

Theorem inline_owner_storage_static:
  inline_owner_storage cert entries frame ==>
  inline_address_stack cert entries /\ inline_addresses_ordered (MAP FST entries)
Proof simp[inline_owner_storage_def]
QED

Theorem inline_owner_storage_head:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame ==>
  inline_tracked_snapshot a.ia_function a route snap frame /\
  inline_suspended_observations (inline_erase_addresses rest) frame
Proof
  simp[inline_owner_storage_def, inline_erase_addresses_def,
       inline_suspended_observations_def]
QED

Theorem inline_owner_storage_root:
  a.ia_entry.vs_labels = FEMPTY /\
  inline_namespace_leaf_at cert p I a.ia_function ==>
  ?snap frame.
    inline_owner_storage cert [(p,a,inline_route_identity a.ia_id,snap)] frame /\
    snap.ils_state = a.ia_entry /\ frame.ipf_state = a.ia_entry
Proof
  strip_tac >>
  drule (inline_tracked_snapshot_identity |> Q.INST [`fn` |-> `a.ia_function`]) >>
  strip_tac >>
  simp[inline_owner_storage_def, inline_erase_addresses_def,
       inline_suspended_observations_def, inline_address_stack_def,
       inline_address_entry_def, inline_address_links_def,
       inline_route_identity_def] >>
  gvs[inline_route_identity_def] >>
  goal_assum (drule_at Any) >> simp[SUBSET_DEF]
QED

Theorem inline_owner_storage_writes:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  INJ route.ir_rename (set (MAP FST writes) UNION snap.ils_defined) UNIV /\
  EVERY (\(x,w). MEM x (cfgTransform$fn_all_vars a.ia_function) /\
                  ~retpc_var a.ia_function x) writes ==>
  inline_owner_storage cert
    ((p,a,route,snap with <|ils_state :=
       FOLDL (\s (x,w). update_var x w s) snap.ils_state writes;
       ils_defined := set (MAP FST writes) UNION snap.ils_defined|>)::rest)
    (frame with ipf_state :=
       FOLDL (\s (x,w). update_var (route.ir_rename x) w s) frame.ipf_state writes)
Proof
  strip_tac >>
  drule inline_owner_storage_static >> strip_tac >>
  drule inline_owner_storage_head >> strip_tac >>
  `EVERY (\(x,w). MEM x (cfgTransform$fn_all_vars a.ia_function) /\
      ~retpc_var a.ia_function x /\
      (!v. v IN snap.ils_protected ==> snap.ils_parent_rename v <> route.ir_rename x)) writes` by
    (gvs[EVERY_MEM, pairTheory.FORALL_PROD] >>
     metis_tac[inline_address_stack_body_protected]) >>
  drule_all inline_tracked_resume_writes >> strip_tac >>
  `EVERY (\(d,w). inline_suspended_avoids (inline_erase_addresses rest) d)
    (MAP (\(x,w). (route.ir_rename x,w)) writes)` by
    (simp[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD] >> rpt strip_tac >>
     drule inline_address_stack_body_avoids >> disch_then drule >>
     disch_then irule >> gvs[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  drule_all inline_suspended_writes >> strip_tac >>
  gvs[inline_owner_storage_def, inline_erase_addresses_def,
      inline_suspended_observations_def, rich_listTheory.FOLDL_MAP,
      combinTheory.o_DEF, pairTheory.LAMBDA_PROD] >>
  Cases_on `rest`
  >- (gvs[inline_address_stack_def, inline_address_entry_def, inline_address_links_def,
          SUBSET_DEF, EVERY_MEM, MEM_MAP, pairTheory.FORALL_PROD,
          pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  PairCases_on `h` >>
  gvs[inline_address_stack_def, inline_address_entry_def, inline_address_links_def,
      SUBSET_DEF, EVERY_MEM, MEM_MAP, pairTheory.FORALL_PROD,
      pairTheory.EXISTS_PROD] >> metis_tac[]
QED

Theorem inline_owner_storage_opaque_write:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  MEM x (cfgTransform$fn_all_vars a.ia_function) /\
  retpc_var a.ia_function x /\
  INJ route.ir_rename (x INSERT snap.ils_defined) UNIV ==>
  inline_owner_storage cert
    ((p,a,route,snap with <|ils_state := update_var x w snap.ils_state;
       ils_defined := x INSERT snap.ils_defined|>)::rest)
    (frame with ipf_state := update_var (route.ir_rename x) u frame.ipf_state)
Proof
  strip_tac >>
  drule inline_owner_storage_static >> strip_tac >>
  drule inline_owner_storage_head >> strip_tac >>
  `!v. v IN snap.ils_protected ==> snap.ils_parent_rename v <> route.ir_rename x` by
    metis_tac[inline_address_stack_body_protected] >>
  drule_all inline_tracked_resume_opaque_write >> strip_tac >>
  `inline_suspended_avoids (inline_erase_addresses rest) (route.ir_rename x)` by
    metis_tac[inline_address_stack_body_avoids] >>
  drule_all inline_suspended_write >> strip_tac >>
  gvs[inline_owner_storage_def, inline_erase_addresses_def,
      inline_suspended_observations_def] >>
  Cases_on `rest`
  >- (gvs[inline_address_stack_def, inline_address_entry_def,
          inline_address_links_def, SUBSET_DEF] >> metis_tac[]) >>
  PairCases_on `h` >>
  gvs[inline_address_stack_def, inline_address_entry_def,
      inline_address_links_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem inline_owner_storage_selected_child:
  inline_owner_storage cert ((p,pa,proute,psnap)::rest) frame /\
  inline_original_child C fuel pa.ia_id occurrence call psnap.ils_state r child cr /\
  inline_call_incidence cert root p pa.ia_function l j call
    (InlineSelected uaddr q e zipper) /\
  inline_namespace_leaf_at cert q route.ir_rename child.ia_function ==>
  ?csnap.
    csnap.ils_state = child.ia_entry /\ csnap.ils_defined = {} /\
    csnap.ils_saved = psnap.ils_state /\
    csnap.ils_protected = (psnap.ils_defined DIFF psnap.ils_opaque) DIFF set call.inst_outputs /\
    csnap.ils_parent_rename = proute.ir_rename /\
    inline_owner_storage cert
      ((q,child,route,csnap)::(p,pa,proute,psnap)::rest) frame
Proof
  strip_tac >>
  drule inline_owner_storage_static >> strip_tac >>
  drule inline_owner_storage_head >> strip_tac >>
  drule_all inline_suspended_push_child >>
  disch_then (qspec_then `route` strip_assume_tac) >>
  `csnap.ils_protected SUBSET set (cfgTransform$fn_all_vars pa.ia_function)` by
    (gvs[inline_address_stack_def, inline_address_entry_def, SUBSET_DEF] >>
     metis_tac[]) >>
  `csnap.ils_defined SUBSET set (cfgTransform$fn_all_vars child.ia_function)` by simp[] >>
  drule_all inline_address_stack_selected_push >> strip_tac >>
  qexists `csnap` >>
  gvs[inline_owner_storage_def, inline_erase_addresses_def,
      inline_suspended_observations_def]
QED

Theorem inline_owner_storage_selected_child_writes:
  inline_owner_storage cert ((p,pa,proute,psnap)::rest) frame /\
  inline_original_child C fuel pa.ia_id occurrence call psnap.ils_state r child cr /\
  inline_call_incidence cert root p pa.ia_function l j call
    (InlineSelected uaddr q e zipper) /\
  inline_namespace_leaf_at cert q route.ir_rename child.ia_function /\
  inline_annotated_origin C n root cert ==>
  ?csnap.
    csnap.ils_state = child.ia_entry /\ csnap.ils_defined = {} /\
    csnap.ils_saved = psnap.ils_state /\
    inline_owner_storage cert
      ((q,child,route,csnap)::(p,pa,proute,psnap)::rest) frame /\
    !writes.
      INJ route.ir_rename (set (MAP FST writes)) UNIV /\
      EVERY (\(x,w). MEM x (cfgTransform$fn_all_vars child.ia_function) /\
                       ~retpc_var child.ia_function x) writes ==>
      inline_owner_storage cert
        ((q,child,route,csnap with <|ils_state :=
           FOLDL (\s (x,w). update_var x w s) csnap.ils_state writes;
           ils_defined := set (MAP FST writes) UNION csnap.ils_defined|>)::
         (p,pa,proute,psnap)::rest)
        (frame with ipf_state :=
           FOLDL (\s (x,w). update_var (route.ir_rename x) w s) frame.ipf_state writes)
Proof
  strip_tac >> drule_all inline_owner_storage_selected_child >> strip_tac >>
  qexists `csnap` >> simp[] >> rpt strip_tac >>
  `INJ route.ir_rename (set (MAP FST writes) UNION csnap.ils_defined) UNIV` by simp[] >>
  drule_all inline_owner_storage_writes >> simp[]
QED

Theorem inline_owner_storage_assign_step:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  src.inst_opcode = ASSIGN /\ src.inst_operands = [op] /\ src.inst_outputs = [x] /\
  step_inst fuel C src snap.ils_state = OK s' /\
  MEM x (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function x /\
  INJ route.ir_rename (x INSERT snap.ils_defined) UNIV /\
  (!v. op = Var v ==> MEM v (cfgTransform$fn_all_vars a.ia_function) /\
                         ~retpc_var a.ia_function v) /\
  dst.inst_opcode = ASSIGN /\
  dst.inst_operands = [inline_rename_operand route.ir_rename lab op] /\
  dst.inst_outputs = [route.ir_rename x] ==>
  ?t. step_inst tfuel Tctx dst frame.ipf_state = OK t /\
      inline_owner_storage cert
        ((p,a,route,snap with <|ils_state := s';
           ils_defined := x INSERT snap.ils_defined|>)::rest)
        (frame with ipf_state := t)
Proof
  strip_tac >>
  `?w. eval_operand op snap.ils_state = SOME w /\ s' = update_var x w snap.ils_state` by
    (gvs[Once step_inst_def, step_inst_base_def, AllCaseEqs()]) >>
  drule inline_owner_storage_head >> strip_tac >>
  `eval_operand (inline_rename_operand route.ir_rename lab op) frame.ipf_state = SOME w` by
    (irule EQ_TRANS >> qexists `eval_operand op snap.ils_state` >>
     reverse conj_tac >- simp[] >>
     irule inline_snapshot_eval_operand >>
     gvs[inline_tracked_snapshot_def] >>
     `frame.ipf_state.vs_labels = FEMPTY` by
       metis_tac[inline_snapshot_anchor_empty_labels] >>
     conj_tac
     >- (rpt strip_tac >> gvs[eval_operand_def, pred_setTheory.IN_APP]) >>
     simp[] >> metis_tac[]) >>
  qexists `update_var (route.ir_rename x) w frame.ipf_state` >>
  conj_tac
  >- simp[Once step_inst_def, step_inst_base_def] >>
  `INJ route.ir_rename (set (MAP FST [(x,w)]) UNION snap.ils_defined) UNIV` by
    simp[INSERT_UNION_EQ] >>
  `EVERY (\(y,v). MEM y (cfgTransform$fn_all_vars a.ia_function) /\
                     ~retpc_var a.ia_function y) [(x,w)]` by simp[] >>
  drule_all inline_owner_storage_writes >> simp[INSERT_UNION_EQ]
QED

Theorem inline_owner_storage_assign_cell:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  src.inst_opcode = ASSIGN /\ src.inst_operands = [op] /\ src.inst_outputs = [x] /\
  step_inst fuel C src snap.ils_state = OK s' /\
  MEM x (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function x /\
  INJ route.ir_rename (x INSERT snap.ils_defined) UNIV /\
  (!v. op = Var v ==> MEM v (cfgTransform$fn_all_vars a.ia_function) /\
                         ~retpc_var a.ia_function v) /\
  inline_cell_at d /\
  d.ic_fields = (ASSIGN,[inline_rename_operand route.ir_rename lab op],[route.ir_rename x]) ==>
  ?bb dst t.
    lookup_block d.ic_block d.ic_function.fn_blocks = SOME bb /\
    get_instruction bb d.ic_index = SOME dst /\
    step_inst tfuel Tctx dst frame.ipf_state = OK t /\
    inline_owner_storage cert
      ((p,a,route,snap with <|ils_state := s';
         ils_defined := x INSERT snap.ils_defined|>)::rest)
      (frame with ipf_state := t)
Proof
  strip_tac >>
  gvs[inline_cell_at_def, functionInlinerSiteLayoutTheory.inline_fetched_fields_def,
      functionInlinerSiteLayoutTheory.inline_inst_fields_def] >>
  drule_all inline_owner_storage_assign_step >> strip_tac >>
  simp[]
QED

Theorem inline_owner_storage_assign_zipper:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  src.inst_opcode = ASSIGN /\ src.inst_operands = [op] /\ src.inst_outputs = [x] /\
  step_inst fuel C src snap.ils_state = OK s' /\
  MEM x (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function x /\
  INJ route.ir_rename (x INSERT snap.ils_defined) UNIV /\
  (!v. op = Var v ==> MEM v (cfgTransform$fn_all_vars a.ia_function) /\
                         ~retpc_var a.ia_function v) /\
  inline_cell_at c /\ inline_cell_zipper c frames d /\
  d.ic_fields = (ASSIGN,[inline_rename_operand route.ir_rename lab op],[route.ir_rename x]) ==>
  ?bb dst t.
    lookup_block d.ic_block d.ic_function.fn_blocks = SOME bb /\
    get_instruction bb d.ic_index = SOME dst /\
    step_inst tfuel Tctx dst frame.ipf_state = OK t /\
    inline_owner_storage cert
      ((p,a,route,snap with <|ils_state := s';
         ils_defined := x INSERT snap.ils_defined|>)::rest)
      (frame with ipf_state := t)
Proof
  strip_tac >> drule_all inline_cell_zipper_sound >> strip_tac >>
  irule inline_owner_storage_assign_cell >> metis_tac[]
QED

(* Memory effects do not alter addressed local observations or bookkeeping. *)
Theorem inline_tracked_snapshot_memory[simp]:
  inline_tracked_snapshot fn a route
    (snap with ils_state := snap.ils_state with vs_memory := m)
    (frame with ipf_state := frame.ipf_state with vs_memory := n) <=>
  inline_tracked_snapshot fn a route snap frame
Proof
  simp[inline_tracked_snapshot_def, inline_snapshot_data_def,
       functionInlinerSimulationTheory.inline_caller_bookkeeping_def,
       lookup_var_def]
QED

Theorem inline_suspended_memory[simp]:
  inline_suspended_observations obs
    (frame with ipf_state := frame.ipf_state with vs_memory := m) <=>
  inline_suspended_observations obs frame
Proof
  simp[inline_suspended_observations_def, EVERY_MEM, pairTheory.FORALL_PROD,
       inline_tracked_snapshot_def, inline_snapshot_data_def,
       functionInlinerSimulationTheory.inline_caller_bookkeeping_def,
       lookup_var_def]
QED

Theorem inline_owner_storage_memory:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame ==>
  inline_owner_storage cert
    ((p,a,route,snap with ils_state := snap.ils_state with vs_memory := m)::rest)
    (frame with ipf_state := frame.ipf_state with vs_memory := n)
Proof
  Cases_on `rest`
  >- simp[inline_owner_storage_def, inline_address_stack_def,
          inline_address_entry_def, inline_address_links_def,
          inline_erase_addresses_def, inline_suspended_observations_def,
          inline_tracked_snapshot_def, inline_snapshot_data_def,
          functionInlinerSimulationTheory.inline_caller_bookkeeping_def, lookup_var_def] >>
  PairCases_on `h` >>
  simp[inline_owner_storage_def, inline_address_stack_def,
       inline_address_entry_def, inline_address_links_def,
       inline_erase_addresses_def, inline_suspended_observations_def] >>
  strip_tac >>
  gvs[inline_tracked_snapshot_def, inline_snapshot_data_def,
       functionInlinerSimulationTheory.inline_caller_bookkeeping_def, lookup_var_def]
QED

Theorem inline_tracked_operands_success:
  inline_tracked_snapshot fn a route snap frame /\
  eval_operands ops snap.ils_state = SOME args /\
  EVERY (\op. !v. op = Var v ==>
    MEM v (cfgTransform$fn_all_vars fn) /\ ~retpc_var fn v) ops ==>
  eval_operands (MAP (inline_rename_operand route.ir_rename lab) ops)
    frame.ipf_state = SOME args
Proof
  strip_tac >>
  `EVERY (\op. IS_SOME (eval_operand op snap.ils_state)) ops` by
    (simp[GSYM venomExecProofsTheory.eval_operands_IS_SOME_EVERY] >> simp[]) >>
  irule EQ_TRANS >> qexists `eval_operands ops snap.ils_state` >>
  reverse conj_tac >- simp[] >>
  irule inline_snapshot_eval_operands >>
  gvs[inline_tracked_snapshot_def] >>
  `frame.ipf_state.vs_labels = FEMPTY` by
    metis_tac[inline_snapshot_anchor_empty_labels] >>
  simp[] >> reverse conj_tac >- metis_tac[] >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  `IS_SOME (lookup_var v snap.ils_state)` by
    (qpat_x_assum `!op. MEM op ops ==> IS_SOME (eval_operand op snap.ils_state)`
       (qspec_then `Var v` mp_tac) >> gvs[eval_operand_def]) >>
  gvs[pred_setTheory.IN_APP] >> metis_tac[]
QED

Theorem inline_owner_storage_mstore_step:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
  inline_shared_frame snap.ils_state = inline_shared_frame frame.ipf_state /\
  src.inst_opcode = MSTORE /\ src.inst_operands = [op1;op2] /\
  step_inst fuel C src snap.ils_state = OK s' /\
  EVERY (\op. !v. op = Var v ==>
    MEM v (cfgTransform$fn_all_vars a.ia_function) /\
    ~retpc_var a.ia_function v) [op1;op2] /\
  dst.inst_opcode = MSTORE /\
  dst.inst_operands = MAP (inline_rename_operand route.ir_rename lab) [op1;op2] ==>
  ?t. step_inst tfuel Tctx dst frame.ipf_state = OK t /\
      inline_owner_storage cert
        ((p,a,route,snap with ils_state := s')::rest)
        (frame with ipf_state := t) /\
      inline_shared_frame s' = inline_shared_frame t /\
      s'.vs_memory = t.vs_memory /\
      s'.vs_current_bb = snap.ils_state.vs_current_bb /\
      s'.vs_inst_idx = snap.ils_state.vs_inst_idx /\
      t.vs_current_bb = frame.ipf_state.vs_current_bb /\
      t.vs_inst_idx = frame.ipf_state.vs_inst_idx
Proof
  strip_tac >>
  `?addr w. eval_operand op1 snap.ils_state = SOME addr /\
      eval_operand op2 snap.ils_state = SOME w /\
      s' = mstore (w2n addr) w snap.ils_state` by
    gvs[Once step_inst_def, step_inst_base_def, exec_write2_def, AllCaseEqs()] >>
  drule inline_owner_storage_head >> strip_tac >>
  `eval_operands [op1;op2] snap.ils_state = SOME [addr;w]` by
    simp[eval_operands_def] >>
  drule_all inline_tracked_operands_success >>
  disch_then (qspec_then `lab` assume_tac) >>
  qexists `mstore (w2n addr) w frame.ipf_state` >>
  conj_tac
  >- gvs[step_inst_non_invoke, step_inst_base_def, exec_write2_def,
         eval_operands_def, AllCaseEqs()] >>
  conj_tac
  >- (gvs[mstore_def] >> irule inline_owner_storage_memory >> simp[]) >>
  simp[functionInlinerOperationalTheory.inline_shared_frame_mstore] >>
  `snap.ils_state.vs_memory = frame.ipf_state.vs_memory` by
    (qpat_x_assum `inline_shared_frame _ = inline_shared_frame _`
       (mp_tac o Q.AP_TERM `\s. s.vs_memory`) >>
     simp[functionInlinerFrameTheory.inline_shared_frame_def,
          stateFrameTheory.execution_frame_def]) >>
  gvs[mstore_def]
QED

(* Base control cut before any compiler edits: the initial logical and
   physical owner both start at the actual first block, before its PHI batch. *)
Theorem inline_owner_root_control:
  a.ia_entry.vs_labels = FEMPTY /\
  inline_namespace_leaf_at cert p I a.ia_function /\
  a.ia_function.fn_blocks <> [] /\
  a.ia_entry.vs_current_bb = (HD a.ia_function.fn_blocks).bb_label /\
  a.ia_entry.vs_inst_idx = 0 ==>
  ?snap frame.
    inline_owner_storage cert [(p,a,inline_route_identity a.ia_id,snap)] frame /\
    snap.ils_state = a.ia_entry /\ frame.ipf_state = a.ia_entry /\
    lookup_block snap.ils_state.vs_current_bb a.ia_function.fn_blocks =
      SOME (HD a.ia_function.fn_blocks) /\
    lookup_block frame.ipf_state.vs_current_bb a.ia_function.fn_blocks =
      SOME (HD a.ia_function.fn_blocks) /\
    snap.ils_state.vs_inst_idx = 0 /\ frame.ipf_state.vs_inst_idx = 0 /\
    inline_shared_frame snap.ils_state = inline_shared_frame frame.ipf_state /\
    inline_path_location (inline_route_identity a.ia_id).ir_path
      (SOME (inline_before_phi_location snap.ils_state.vs_current_bb 0)) =
      SOME (inline_before_phi_location frame.ipf_state.vs_current_bb 0)
Proof
  strip_tac >> drule_all inline_owner_storage_root >> strip_tac >>
  qexistsl [`snap`, `frame`] >> gvs[inline_route_identity_def] >>
  Cases_on `a.ia_function.fn_blocks` >>
  gvs[venomInstTheory.lookup_block_def, FIND_thm]
QED

(* The nonempty compiled path is a control witness, separate from the identity
   data-storage route. No equality of source and transformed instructions. *)
Theorem inline_owner_transformed_root_control:
  inline_annotated_origin ctx n root cert /\
  a.ia_function = inline_entry_function cert /\
  a.ia_function.fn_blocks <> [] /\ a.ia_entry.vs_labels = FEMPTY /\
  a.ia_entry.vs_current_bb = (HD a.ia_function.fn_blocks).bb_label /\
  a.ia_entry.vs_inst_idx = 0 ==>
  ?path snap frame.
    inline_routed_leaf cert root (inline_entry_address cert) a.ia_function path /\
    inline_path_rename path = I /\ EVERY (\c. ?e. c = InlineKeep e) path /\
    inline_owner_storage cert
      [(inline_entry_address cert,a,inline_route_identity a.ia_id,snap)] frame /\
    snap.ils_state = a.ia_entry /\ frame.ipf_state = a.ia_entry /\
    root.fn_blocks <> [] /\
    lookup_block snap.ils_state.vs_current_bb a.ia_function.fn_blocks =
      SOME (HD a.ia_function.fn_blocks) /\
    lookup_block frame.ipf_state.vs_current_bb root.fn_blocks =
      SOME (HD root.fn_blocks) /\
    snap.ils_state.vs_inst_idx = 0 /\ frame.ipf_state.vs_inst_idx = 0 /\
    inline_shared_frame snap.ils_state = inline_shared_frame frame.ipf_state /\
    inline_path_location path
      (SOME (inline_before_phi_location snap.ils_state.vs_current_bb 0)) =
      SOME (inline_before_phi_location frame.ipf_state.vs_current_bb 0)
Proof
  strip_tac >>
  `inline_namespace_leaf_at cert (inline_entry_address cert) I a.ia_function` by
    metis_tac[inline_entry_leaf] >>
  drule_all inline_owner_root_control >> strip_tac >>
  drule inline_annotated_entry_route >> strip_tac >>
  drule inline_annotated_entry_first_label >> simp[] >> strip_tac >>
  qexistsl [`path`, `snap`, `frame`] >>
  simp[inline_before_phi_keep_path] >>
  Cases_on `root.fn_blocks` >> gvs[venomInstTheory.lookup_block_def, FIND_thm]
QED
