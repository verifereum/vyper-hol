(* Addressed owner-local data storage, separate from operational reachability. *)
Theory functionInlinerOperationalCuts
Ancestors
  functionInlinerReachableCuts functionInlinerStackSupports functionInlinerCuts
  functionInlinerOccurrences
  functionInlinerActivation functionInlinerEnvelopes venomState cfgTransform list pred_set
  venomExecSemantics functionInlinerOperational functionInlinerFrame

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

(* Storage observes only these local and activation-bookkeeping projections.
   Shared effects and execution control may change independently. *)
Theorem inline_tracked_snapshot_projections:
  s.vs_vars = snap.ils_state.vs_vars /\
  s.vs_params = snap.ils_state.vs_params /\
  s.vs_return_pc_token = snap.ils_state.vs_return_pc_token /\
  s.vs_labels = snap.ils_state.vs_labels /\
  t.vs_vars = frame.ipf_state.vs_vars /\
  t.vs_params = frame.ipf_state.vs_params /\
  t.vs_call_entry_fmp = frame.ipf_state.vs_call_entry_fmp /\
  t.vs_return_pc_token = frame.ipf_state.vs_return_pc_token /\
  t.vs_labels = frame.ipf_state.vs_labels ==>
  (inline_tracked_snapshot fn a route (snap with ils_state := s)
    (frame with ipf_state := t) <=> inline_tracked_snapshot fn a route snap frame)
Proof
  simp[inline_tracked_snapshot_def, inline_snapshot_data_def,
       functionInlinerSimulationTheory.inline_caller_bookkeeping_def, lookup_var_def]
QED

Theorem inline_tracked_physical_projections:
  t.vs_vars = frame.ipf_state.vs_vars /\
  t.vs_params = frame.ipf_state.vs_params /\
  t.vs_call_entry_fmp = frame.ipf_state.vs_call_entry_fmp /\
  t.vs_return_pc_token = frame.ipf_state.vs_return_pc_token /\
  t.vs_labels = frame.ipf_state.vs_labels ==>
  (inline_tracked_snapshot fn a route snap (frame with ipf_state := t) <=>
   inline_tracked_snapshot fn a route snap frame)
Proof
  simp[inline_tracked_snapshot_def, inline_snapshot_data_def,
       functionInlinerSimulationTheory.inline_caller_bookkeeping_def, lookup_var_def]
QED

Theorem inline_suspended_projections:
  t.vs_vars = frame.ipf_state.vs_vars /\
  t.vs_params = frame.ipf_state.vs_params /\
  t.vs_call_entry_fmp = frame.ipf_state.vs_call_entry_fmp /\
  t.vs_return_pc_token = frame.ipf_state.vs_return_pc_token /\
  t.vs_labels = frame.ipf_state.vs_labels ==>
  (inline_suspended_observations obs (frame with ipf_state := t) <=>
   inline_suspended_observations obs frame)
Proof
  simp[inline_suspended_observations_def, EVERY_MEM, pairTheory.FORALL_PROD,
       inline_tracked_snapshot_def, inline_snapshot_data_def,
       functionInlinerSimulationTheory.inline_caller_bookkeeping_def, lookup_var_def]
QED

Theorem inline_owner_storage_projections:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
  s.vs_vars = snap.ils_state.vs_vars /\
  s.vs_params = snap.ils_state.vs_params /\
  s.vs_return_pc_token = snap.ils_state.vs_return_pc_token /\
  s.vs_labels = snap.ils_state.vs_labels /\
  t.vs_vars = frame.ipf_state.vs_vars /\
  t.vs_params = frame.ipf_state.vs_params /\
  t.vs_call_entry_fmp = frame.ipf_state.vs_call_entry_fmp /\
  t.vs_return_pc_token = frame.ipf_state.vs_return_pc_token /\
  t.vs_labels = frame.ipf_state.vs_labels ==>
  inline_owner_storage cert ((p,a,route,snap with ils_state := s)::rest)
    (frame with ipf_state := t)
Proof
  Cases_on `rest`
  >- simp[inline_owner_storage_def, inline_address_stack_def,
          inline_address_entry_def, inline_address_links_def,
          inline_erase_addresses_def, inline_suspended_observations_def,
          inline_tracked_snapshot_projections] >>
  PairCases_on `h` >>
  simp[inline_owner_storage_def, inline_address_stack_def,
       inline_address_entry_def, inline_address_links_def,
       inline_erase_addresses_def, inline_suspended_observations_def] >>
  rpt strip_tac >>
  simp[inline_tracked_snapshot_projections, inline_tracked_physical_projections,
       GSYM inline_suspended_observations_def, inline_suspended_projections] >>
  simp[inline_suspended_observations_def]
QED

(* Locality plus bookkeeping is enough to preserve any suspended view whose
   observed names avoid the declared writes. *)
Theorem inline_suspended_success_footprint:
  inline_suspended_observations obs frame /\
  inline_success_footprint outs frame.ipf_state t /\
  EVERY (inline_suspended_avoids obs) outs ==>
  inline_suspended_observations obs (frame with ipf_state := t)
Proof
  simp[inline_suspended_observations_def, inline_suspended_avoids_def,
       EVERY_MEM, pairTheory.FORALL_PROD,
       inline_success_footprint_def, inline_tracked_snapshot_def,
       inline_snapshot_data_def,
       functionInlinerSimulationTheory.inline_caller_bookkeeping_def] >>
  rpt strip_tac >> simp[] >> metis_tac[]
QED

Theorem inline_tracked_success_footprint:
  inline_tracked_snapshot fn a route snap frame /\
  inline_success_footprint outs snap.ils_state s /\
  inline_success_footprint (MAP route.ir_rename outs) frame.ipf_state t /\
  set outs SUBSET set (cfgTransform$fn_all_vars fn) /\
  (!x. x IN snap.ils_protected ==>
    ~MEM (snap.ils_parent_rename x) (MAP route.ir_rename outs)) /\
  inline_opaque_frame_rel route.ir_rename
    (set outs UNION snap.ils_defined) snap.ils_opaque FEMPTY {} s t ==>
  inline_tracked_snapshot fn a route
    (snap with <|ils_state := s;
      ils_defined := set outs UNION snap.ils_defined|>)
    (frame with ipf_state := t)
Proof
  simp[inline_tracked_snapshot_def, inline_snapshot_data_def,
       inline_success_footprint_def,
       functionInlinerSimulationTheory.inline_caller_bookkeeping_def,
       inline_opaque_frame_rel_def, inline_frame_rel_def,
       SUBSET_DEF] >>
  rpt strip_tac >> simp[] >> metis_tac[]
QED

Theorem inline_owner_storage_success_footprint:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  EVERY (\x. MEM x (cfgTransform$fn_all_vars a.ia_function) /\
    ~retpc_var a.ia_function x) outs /\
  inline_success_footprint outs snap.ils_state s /\
  inline_success_footprint (MAP route.ir_rename outs) frame.ipf_state t /\
  inline_opaque_frame_rel route.ir_rename
    (set outs UNION snap.ils_defined) snap.ils_opaque FEMPTY {} s t ==>
  inline_owner_storage cert
    ((p,a,route,snap with <|ils_state := s;
      ils_defined := set outs UNION snap.ils_defined|>)::rest)
    (frame with ipf_state := t) /\
  inline_shared_frame s = inline_shared_frame t
Proof
  strip_tac >>
  drule inline_owner_storage_static >> strip_tac >>
  drule inline_owner_storage_head >> strip_tac >>
  `!x. x IN snap.ils_protected ==>
    ~MEM (snap.ils_parent_rename x) (MAP route.ir_rename outs)` by
    (simp[MEM_MAP] >> rpt strip_tac >>
     gvs[EVERY_MEM] >> metis_tac[inline_address_stack_body_protected]) >>
  `EVERY (inline_suspended_avoids (inline_erase_addresses rest))
    (MAP route.ir_rename outs)` by
    (simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     drule inline_address_stack_body_avoids >> disch_then drule >>
     disch_then irule >> gvs[EVERY_MEM] >> metis_tac[]) >>
  `inline_suspended_observations (inline_erase_addresses rest)
    (frame with ipf_state := t)` by
    (irule inline_suspended_success_footprint >> metis_tac[]) >>
  `inline_tracked_snapshot a.ia_function a route
    (snap with <|ils_state := s;
      ils_defined := set outs UNION snap.ils_defined|>)
    (frame with ipf_state := t)` by
    (irule inline_tracked_success_footprint >> simp[] >>
     gvs[EVERY_MEM, SUBSET_DEF]) >>
  reverse conj_tac
  >- gvs[inline_opaque_frame_rel_def, inline_frame_rel_def] >>
  gvs[inline_owner_storage_def, inline_erase_addresses_def,
      inline_suspended_observations_def] >>
  Cases_on `rest`
  >- (gvs[inline_address_stack_def, inline_address_entry_def,
          inline_address_links_def, EVERY_MEM, SUBSET_DEF] >> metis_tac[]) >>
  PairCases_on `h` >>
  gvs[inline_address_stack_def, inline_address_entry_def,
      inline_address_links_def, EVERY_MEM, SUBSET_DEF] >> metis_tac[]
QED

(* Logical and physical control locations need not be equal. Storage ignores
   both, and shared-frame agreement is maintained separately. *)
Theorem inline_owner_storage_control:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame ==>
  inline_owner_storage cert
    ((p,a,route,snap with ils_state := snap.ils_state with <|
      vs_current_bb := sb; vs_prev_bb := sp; vs_inst_idx := si |> )::rest)
    (frame with ipf_state := frame.ipf_state with <|
      vs_current_bb := tb; vs_prev_bb := tp; vs_inst_idx := ti |>)
Proof
  strip_tac >> irule inline_owner_storage_projections >> simp[]
QED

Theorem inline_owner_storage_index:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame ==>
  inline_owner_storage cert
    ((p,a,route,snap with ils_state := snap.ils_state with vs_inst_idx := si)::rest)
    (frame with ipf_state := frame.ipf_state with vs_inst_idx := ti)
Proof
  strip_tac >> irule inline_owner_storage_projections >> simp[]
QED

Theorem inline_owner_storage_jump:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame ==>
  inline_owner_storage cert
    ((p,a,route,snap with ils_state := jump_to sb snap.ils_state)::rest)
    (frame with ipf_state := jump_to tb frame.ipf_state)
Proof
  strip_tac >> irule inline_owner_storage_projections >> simp[jump_to_def]
QED

Theorem inline_owner_storage_shared_memory:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
  inline_shared_frame snap.ils_state = inline_shared_frame frame.ipf_state ==>
  inline_owner_storage cert
    ((p,a,route,snap with ils_state := snap.ils_state with vs_memory := m)::rest)
    (frame with ipf_state := frame.ipf_state with vs_memory := m) /\
  inline_shared_frame (snap.ils_state with vs_memory := m) =
    inline_shared_frame (frame.ipf_state with vs_memory := m)
Proof
  strip_tac >> conj_tac
  >- (irule inline_owner_storage_projections >> simp[]) >>
  gvs[functionInlinerFrameTheory.inline_shared_frame_def,
      stateFrameTheory.execution_frame_def]
QED

(* Common post-evaluation cut for single-output classes. *)
Theorem inline_owner_storage_write_cut:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  inline_shared_frame snap.ils_state = inline_shared_frame frame.ipf_state /\
  MEM x (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function x /\
  INJ route.ir_rename (x INSERT snap.ils_defined) UNIV ==>
  inline_owner_storage cert
    ((p,a,route,snap with <|ils_state := update_var x w snap.ils_state;
      ils_defined := x INSERT snap.ils_defined|>)::rest)
    (frame with ipf_state := update_var (route.ir_rename x) w frame.ipf_state) /\
  inline_shared_frame (update_var x w snap.ils_state) =
    inline_shared_frame (update_var (route.ir_rename x) w frame.ipf_state) /\
  (update_var x w snap.ils_state).vs_current_bb = snap.ils_state.vs_current_bb /\
  (update_var x w snap.ils_state).vs_inst_idx = snap.ils_state.vs_inst_idx /\
  (update_var (route.ir_rename x) w frame.ipf_state).vs_current_bb = frame.ipf_state.vs_current_bb /\
  (update_var (route.ir_rename x) w frame.ipf_state).vs_inst_idx = frame.ipf_state.vs_inst_idx
Proof
  strip_tac >> reverse conj_tac >- simp[update_var_def] >>
  `INJ route.ir_rename (set (MAP FST [(x,w)]) UNION snap.ils_defined) UNIV`
    by simp[INSERT_UNION_EQ] >>
  `EVERY (\(y,v). MEM y (cfgTransform$fn_all_vars a.ia_function) /\
       ~retpc_var a.ia_function y) [(x,w)]` by simp[] >>
  drule_all inline_owner_storage_writes >> simp[INSERT_UNION_EQ]
QED

(* Class boundary: evaluate the two operands once, then establish the one
   declared output through the addressed write interface. *)
Theorem inline_owner_storage_pure2:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  inline_shared_frame snap.ils_state = inline_shared_frame frame.ipf_state /\
  src.inst_outputs = [x] /\ exec_pure2 f src snap.ils_state = OK s' /\
  MEM x (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function x /\
  INJ route.ir_rename (x INSERT snap.ils_defined) UNIV /\
  EVERY (\op. !v. op = Var v ==>
    MEM v (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function v)
    src.inst_operands /\
  dst.inst_operands = MAP (inline_rename_operand route.ir_rename lab) src.inst_operands /\
  dst.inst_outputs = [route.ir_rename x] ==>
  ?t. exec_pure2 f dst frame.ipf_state = OK t /\
      inline_owner_storage cert
        ((p,a,route,snap with <|ils_state := s';
          ils_defined := x INSERT snap.ils_defined|>)::rest)
        (frame with ipf_state := t) /\
      inline_shared_frame s' = inline_shared_frame t /\
      s'.vs_current_bb = snap.ils_state.vs_current_bb /\
      s'.vs_inst_idx = snap.ils_state.vs_inst_idx /\
      t.vs_current_bb = frame.ipf_state.vs_current_bb /\
      t.vs_inst_idx = frame.ipf_state.vs_inst_idx
Proof
  strip_tac >>
  `?v1 v2. eval_operands src.inst_operands snap.ils_state = SOME [v1;v2] /\
      s' = update_var x (f v1 v2) snap.ils_state` by
    (gvs[exec_pure2_def, AllCaseEqs()] >>
     simp[eval_operands_def]) >>
  drule inline_owner_storage_head >> strip_tac >>
  drule_all inline_tracked_operands_success >>
  disch_then (qspec_then `lab` assume_tac) >>
  qexists `update_var (route.ir_rename x) (f v1 v2) frame.ipf_state` >>
  conj_tac
  >- (gvs[exec_pure2_def, AllCaseEqs()] >>
      gvs[eval_operands_def, AllCaseEqs()]) >>
  gvs[] >> metis_tac[inline_owner_storage_write_cut]
QED

Theorem inline_owner_pure2_dispatch[local]:
  inline_pure2_opcode src.inst_opcode /\ dst.inst_opcode = src.inst_opcode ==>
  ?f. (!fuel C s. step_inst fuel C src s = exec_pure2 f src s) /\
      (!tfuel Tctx t. step_inst tfuel Tctx dst t = exec_pure2 f dst t)
Proof
  Cases_on `src.inst_opcode` >>
  simp[functionInlinerOperationalTheory.inline_pure2_opcode_def] >>
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  metis_tac[]
QED

Theorem inline_owner_storage_pure2_step:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  inline_shared_frame snap.ils_state = inline_shared_frame frame.ipf_state /\
  inline_pure2_opcode src.inst_opcode /\ src.inst_outputs = [x] /\
  step_inst fuel C src snap.ils_state = OK s' /\
  MEM x (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function x /\
  INJ route.ir_rename (x INSERT snap.ils_defined) UNIV /\
  EVERY (\op. !v. op = Var v ==>
    MEM v (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function v)
    src.inst_operands /\
  dst.inst_opcode = src.inst_opcode /\
  dst.inst_operands = MAP (inline_rename_operand route.ir_rename lab) src.inst_operands /\
  dst.inst_outputs = [route.ir_rename x] ==>
  ?t. step_inst tfuel Tctx dst frame.ipf_state = OK t /\
      inline_owner_storage cert
        ((p,a,route,snap with <|ils_state := s';
          ils_defined := x INSERT snap.ils_defined|>)::rest)
        (frame with ipf_state := t) /\
      inline_shared_frame s' = inline_shared_frame t /\
      s'.vs_current_bb = snap.ils_state.vs_current_bb /\
      s'.vs_inst_idx = snap.ils_state.vs_inst_idx /\
      t.vs_current_bb = frame.ipf_state.vs_current_bb /\
      t.vs_inst_idx = frame.ipf_state.vs_inst_idx
Proof
  strip_tac >> drule_all inline_owner_pure2_dispatch >> strip_tac >>
  gvs[] >> irule inline_owner_storage_pure2 >> metis_tac[]
QED


(* Side-effect class: f may change shared effects, but not frame bookkeeping,
   locals or pre-advancement control. These are exactly the storage projections. *)
Theorem inline_owner_storage_write2:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
  inline_shared_frame snap.ils_state = inline_shared_frame frame.ipf_state /\
  exec_write2 f src snap.ils_state = OK s' /\
  EVERY (\op. !v. op = Var v ==>
    MEM v (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function v)
    src.inst_operands /\
  dst.inst_operands = MAP (inline_rename_operand route.ir_rename lab) src.inst_operands /\
  (!u v s. ((f u v s).vs_vars, (f u v s).vs_params,
       (f u v s).vs_call_entry_fmp, (f u v s).vs_return_pc_token,
       (f u v s).vs_labels, (f u v s).vs_current_bb, (f u v s).vs_inst_idx) =
      (s.vs_vars, s.vs_params, s.vs_call_entry_fmp, s.vs_return_pc_token,
       s.vs_labels, s.vs_current_bb, s.vs_inst_idx)) /\
  (!u v s t. inline_shared_frame s = inline_shared_frame t ==>
    inline_shared_frame (f u v s) = inline_shared_frame (f u v t)) ==>
  ?t. exec_write2 f dst frame.ipf_state = OK t /\
    inline_owner_storage cert
      ((p,a,route,snap with ils_state := s')::rest) (frame with ipf_state := t) /\
    inline_shared_frame s' = inline_shared_frame t /\
    s'.vs_current_bb = snap.ils_state.vs_current_bb /\
    s'.vs_inst_idx = snap.ils_state.vs_inst_idx /\
    t.vs_current_bb = frame.ipf_state.vs_current_bb /\
    t.vs_inst_idx = frame.ipf_state.vs_inst_idx
Proof
  strip_tac >>
  `?v1 v2. eval_operands src.inst_operands snap.ils_state = SOME [v1;v2] /\
      s' = f v1 v2 snap.ils_state` by
    (gvs[exec_write2_def, AllCaseEqs()] >> simp[eval_operands_def]) >>
  drule inline_owner_storage_head >> strip_tac >>
  drule_all inline_tracked_operands_success >>
  disch_then (qspec_then `lab` assume_tac) >>
  qexists `f v1 v2 frame.ipf_state` >> conj_tac
  >- (gvs[exec_write2_def, AllCaseEqs()] >>
      gvs[eval_operands_def, AllCaseEqs()]) >>
  conj_tac
  >- (irule inline_owner_storage_projections >> gvs[] >> metis_tac[pairTheory.PAIR_EQ]) >>
  gvs[] >> metis_tac[pairTheory.PAIR_EQ]
QED

Theorem inline_owner_storage_pure1:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  inline_shared_frame snap.ils_state = inline_shared_frame frame.ipf_state /\
  src.inst_outputs = [x] /\ exec_pure1 f src snap.ils_state = OK s' /\
  MEM x (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function x /\
  INJ route.ir_rename (x INSERT snap.ils_defined) UNIV /\
  EVERY (\op. !v. op = Var v ==>
    MEM v (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function v)
    src.inst_operands /\
  dst.inst_operands = MAP (inline_rename_operand route.ir_rename lab) src.inst_operands /\
  dst.inst_outputs = [route.ir_rename x] ==>
  ?t. exec_pure1 f dst frame.ipf_state = OK t /\
      inline_owner_storage cert
        ((p,a,route,snap with <|ils_state := s';
          ils_defined := x INSERT snap.ils_defined|>)::rest)
        (frame with ipf_state := t) /\
      inline_shared_frame s' = inline_shared_frame t /\
      s'.vs_current_bb = snap.ils_state.vs_current_bb /\
      s'.vs_inst_idx = snap.ils_state.vs_inst_idx /\
      t.vs_current_bb = frame.ipf_state.vs_current_bb /\
      t.vs_inst_idx = frame.ipf_state.vs_inst_idx
Proof
  strip_tac >>
  `?v. eval_operands src.inst_operands snap.ils_state = SOME [v] /\
      s' = update_var x (f v) snap.ils_state` by
    (gvs[exec_pure1_def, AllCaseEqs()] >> simp[eval_operands_def]) >>
  drule inline_owner_storage_head >> strip_tac >>
  drule_all inline_tracked_operands_success >>
  disch_then (qspec_then `lab` assume_tac) >>
  qexists `update_var (route.ir_rename x) (f v) frame.ipf_state` >>
  conj_tac
  >- (gvs[exec_pure1_def, AllCaseEqs()] >> gvs[eval_operands_def, AllCaseEqs()]) >>
  gvs[] >> metis_tac[inline_owner_storage_write_cut]
QED

Theorem inline_owner_storage_pure3:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  inline_shared_frame snap.ils_state = inline_shared_frame frame.ipf_state /\
  src.inst_outputs = [x] /\ exec_pure3 f src snap.ils_state = OK s' /\
  MEM x (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function x /\
  INJ route.ir_rename (x INSERT snap.ils_defined) UNIV /\
  EVERY (\op. !v. op = Var v ==>
    MEM v (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function v)
    src.inst_operands /\
  dst.inst_operands = MAP (inline_rename_operand route.ir_rename lab) src.inst_operands /\
  dst.inst_outputs = [route.ir_rename x] ==>
  ?t. exec_pure3 f dst frame.ipf_state = OK t /\
      inline_owner_storage cert
        ((p,a,route,snap with <|ils_state := s';
          ils_defined := x INSERT snap.ils_defined|>)::rest)
        (frame with ipf_state := t) /\
      inline_shared_frame s' = inline_shared_frame t /\
      s'.vs_current_bb = snap.ils_state.vs_current_bb /\
      s'.vs_inst_idx = snap.ils_state.vs_inst_idx /\
      t.vs_current_bb = frame.ipf_state.vs_current_bb /\
      t.vs_inst_idx = frame.ipf_state.vs_inst_idx
Proof
  strip_tac >>
  `?v1 v2 v3. eval_operands src.inst_operands snap.ils_state = SOME [v1;v2;v3] /\
      s' = update_var x (f v1 v2 v3) snap.ils_state` by
    (gvs[exec_pure3_def, AllCaseEqs()] >> simp[eval_operands_def]) >>
  drule inline_owner_storage_head >> strip_tac >>
  drule_all inline_tracked_operands_success >>
  disch_then (qspec_then `lab` assume_tac) >>
  qexists `update_var (route.ir_rename x) (f v1 v2 v3) frame.ipf_state` >>
  conj_tac
  >- (gvs[exec_pure3_def, AllCaseEqs()] >> gvs[eval_operands_def, AllCaseEqs()]) >>
  gvs[] >> metis_tac[inline_owner_storage_write_cut]
QED

Theorem inline_owner_storage_read0:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  inline_shared_frame snap.ils_state = inline_shared_frame frame.ipf_state /\
  src.inst_outputs = [x] /\ exec_read0 f src snap.ils_state = OK s' /\
  MEM x (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function x /\
  INJ route.ir_rename (x INSERT snap.ils_defined) UNIV /\
  (!s t. inline_shared_frame s = inline_shared_frame t ==> f s = f t) /\
  dst.inst_outputs = [route.ir_rename x] ==>
  ?t. exec_read0 f dst frame.ipf_state = OK t /\
      inline_owner_storage cert
        ((p,a,route,snap with <|ils_state := s';
          ils_defined := x INSERT snap.ils_defined|>)::rest)
        (frame with ipf_state := t) /\
      inline_shared_frame s' = inline_shared_frame t /\
      s'.vs_current_bb = snap.ils_state.vs_current_bb /\
      s'.vs_inst_idx = snap.ils_state.vs_inst_idx /\
      t.vs_current_bb = frame.ipf_state.vs_current_bb /\
      t.vs_inst_idx = frame.ipf_state.vs_inst_idx
Proof
  strip_tac >>
  `f snap.ils_state = f frame.ipf_state` by metis_tac[] >>
  qexists `update_var (route.ir_rename x) (f snap.ils_state) frame.ipf_state` >>
  conj_tac >- simp[exec_read0_def] >>
  gvs[exec_read0_def] >> metis_tac[inline_owner_storage_write_cut]
QED

Theorem inline_owner_storage_read1:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  inline_shared_frame snap.ils_state = inline_shared_frame frame.ipf_state /\
  src.inst_outputs = [x] /\ exec_read1 f src snap.ils_state = OK s' /\
  MEM x (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function x /\
  INJ route.ir_rename (x INSERT snap.ils_defined) UNIV /\
  EVERY (\op. !v. op = Var v ==>
    MEM v (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function v)
    src.inst_operands /\
  (!v s t. inline_shared_frame s = inline_shared_frame t ==> f v s = f v t) /\
  dst.inst_operands = MAP (inline_rename_operand route.ir_rename lab) src.inst_operands /\
  dst.inst_outputs = [route.ir_rename x] ==>
  ?t. exec_read1 f dst frame.ipf_state = OK t /\
      inline_owner_storage cert
        ((p,a,route,snap with <|ils_state := s';
          ils_defined := x INSERT snap.ils_defined|>)::rest)
        (frame with ipf_state := t) /\
      inline_shared_frame s' = inline_shared_frame t /\
      s'.vs_current_bb = snap.ils_state.vs_current_bb /\
      s'.vs_inst_idx = snap.ils_state.vs_inst_idx /\
      t.vs_current_bb = frame.ipf_state.vs_current_bb /\
      t.vs_inst_idx = frame.ipf_state.vs_inst_idx
Proof
  strip_tac >>
  `?v. eval_operands src.inst_operands snap.ils_state = SOME [v] /\
      s' = update_var x (f v snap.ils_state) snap.ils_state` by
    (gvs[exec_read1_def, AllCaseEqs()] >> simp[eval_operands_def]) >>
  drule inline_owner_storage_head >> strip_tac >>
  drule_all inline_tracked_operands_success >>
  disch_then (qspec_then `lab` assume_tac) >>
  `f v snap.ils_state = f v frame.ipf_state` by metis_tac[] >>
  qexists `update_var (route.ir_rename x) (f v snap.ils_state) frame.ipf_state` >>
  conj_tac
  >- (gvs[exec_read1_def, AllCaseEqs()] >>
      gvs[eval_operands_def, AllCaseEqs()] >> metis_tac[]) >>
  gvs[] >> metis_tac[inline_owner_storage_write_cut]
QED

Theorem inline_owner_pure1_dispatch[local]:
  inline_pure1_opcode src.inst_opcode /\ dst.inst_opcode = src.inst_opcode ==>
  ?f. (!fuel C s. step_inst fuel C src s = exec_pure1 f src s) /\
      (!tfuel Tctx t. step_inst tfuel Tctx dst t = exec_pure1 f dst t)
Proof
  Cases_on `src.inst_opcode` >>
  simp[functionInlinerOperationalTheory.inline_pure1_opcode_def] >>
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >> metis_tac[]
QED

Theorem inline_owner_pure3_dispatch[local]:
  inline_pure3_opcode src.inst_opcode /\ dst.inst_opcode = src.inst_opcode ==>
  ?f. (!fuel C s. step_inst fuel C src s = exec_pure3 f src s) /\
      (!tfuel Tctx t. step_inst tfuel Tctx dst t = exec_pure3 f dst t)
Proof
  Cases_on `src.inst_opcode` >>
  simp[functionInlinerOperationalTheory.inline_pure3_opcode_def] >>
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >> metis_tac[]
QED

Theorem inline_owner_read0_dispatch[local]:
  inline_read0_opcode src.inst_opcode /\ dst.inst_opcode = src.inst_opcode ==>
  ?f. (!fuel C s. step_inst fuel C src s = exec_read0 f src s) /\
      (!tfuel Tctx t. step_inst tfuel Tctx dst t = exec_read0 f dst t) /\
      (!s. f (inline_shared_frame s) = f s)
Proof
  Cases_on `src.inst_opcode` >>
  simp[functionInlinerOperationalTheory.inline_read0_opcode_def] >> strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  qmatch_goalsub_abbrev_tac `exec_read0 reader src` >> qexists `reader` >>
  simp[Abbr `reader`, functionInlinerFrameTheory.inline_shared_frame_def,
       stateFrameTheory.execution_frame_def]
QED

Theorem inline_owner_read1_dispatch[local]:
  inline_read1_opcode src.inst_opcode /\ dst.inst_opcode = src.inst_opcode ==>
  ?f. (!fuel C s. step_inst fuel C src s = exec_read1 f src s) /\
      (!tfuel Tctx t. step_inst tfuel Tctx dst t = exec_read1 f dst t) /\
      (!v s. f v (inline_shared_frame s) = f v s)
Proof
  Cases_on `src.inst_opcode` >>
  simp[functionInlinerOperationalTheory.inline_read1_opcode_def] >> strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  qmatch_goalsub_abbrev_tac `exec_read1 reader src` >> qexists `reader` >>
  simp[Abbr `reader`, functionInlinerFrameTheory.inline_shared_frame_def,
       stateFrameTheory.execution_frame_def,
       mload_def, sload_def, tload_def, contract_storage_def, contract_transient_def]
QED

Theorem inline_owner_storage_value_step:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  inline_shared_frame snap.ils_state = inline_shared_frame frame.ipf_state /\
  (inline_pure1_opcode src.inst_opcode \/ inline_pure2_opcode src.inst_opcode \/
   inline_pure3_opcode src.inst_opcode \/ inline_read0_opcode src.inst_opcode \/
   inline_read1_opcode src.inst_opcode) /\
  src.inst_outputs = [x] /\ step_inst fuel C src snap.ils_state = OK s' /\
  MEM x (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function x /\
  INJ route.ir_rename (x INSERT snap.ils_defined) UNIV /\
  EVERY (\op. !v. op = Var v ==>
    MEM v (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function v)
    src.inst_operands /\
  dst.inst_opcode = src.inst_opcode /\
  dst.inst_operands = MAP (inline_rename_operand route.ir_rename lab) src.inst_operands /\
  dst.inst_outputs = [route.ir_rename x] ==>
  ?t. step_inst tfuel Tctx dst frame.ipf_state = OK t /\
      inline_owner_storage cert
        ((p,a,route,snap with <|ils_state := s';
          ils_defined := x INSERT snap.ils_defined|>)::rest)
        (frame with ipf_state := t) /\
      inline_shared_frame s' = inline_shared_frame t /\
      s'.vs_current_bb = snap.ils_state.vs_current_bb /\
      s'.vs_inst_idx = snap.ils_state.vs_inst_idx /\
      t.vs_current_bb = frame.ipf_state.vs_current_bb /\
      t.vs_inst_idx = frame.ipf_state.vs_inst_idx
Proof
  strip_tac
  >- (drule_all inline_owner_pure1_dispatch >> strip_tac >> gvs[] >>
      irule inline_owner_storage_pure1 >> metis_tac[]) 
  >- (irule inline_owner_storage_pure2_step >> metis_tac[]) 
  >- (drule_all inline_owner_pure3_dispatch >> strip_tac >> gvs[] >>
      irule inline_owner_storage_pure3 >> metis_tac[]) 
  >- (drule_all inline_owner_read0_dispatch >> strip_tac >> gvs[] >>
      irule inline_owner_storage_read0 >> simp[] >> metis_tac[]) >>
  drule_all inline_owner_read1_dispatch >> strip_tac >> gvs[] >>
  irule inline_owner_storage_read1 >> simp[] >> metis_tac[]
QED

Theorem inline_owner_storage_value_zipper:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  inline_shared_frame snap.ils_state = inline_shared_frame frame.ipf_state /\
  (inline_pure1_opcode src.inst_opcode \/ inline_pure2_opcode src.inst_opcode \/
   inline_pure3_opcode src.inst_opcode \/ inline_read0_opcode src.inst_opcode \/
   inline_read1_opcode src.inst_opcode) /\
  src.inst_outputs = [x] /\ step_inst fuel C src snap.ils_state = OK s' /\
  MEM x (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function x /\
  INJ route.ir_rename (x INSERT snap.ils_defined) UNIV /\
  EVERY (\op. !v. op = Var v ==>
    MEM v (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function v)
    src.inst_operands /\
  inline_cell_at c /\ inline_cell_zipper c frames d /\
  d.ic_fields = (src.inst_opcode,
    MAP (inline_rename_operand route.ir_rename lab) src.inst_operands,
    [route.ir_rename x]) ==>
  ?bb dst t.
    lookup_block d.ic_block d.ic_function.fn_blocks = SOME bb /\
    get_instruction bb d.ic_index = SOME dst /\
    step_inst tfuel Tctx dst frame.ipf_state = OK t /\
    inline_owner_storage cert
      ((p,a,route,snap with <|ils_state := s';
        ils_defined := x INSERT snap.ils_defined|>)::rest)
      (frame with ipf_state := t) /\
    inline_shared_frame s' = inline_shared_frame t /\
    s'.vs_current_bb = snap.ils_state.vs_current_bb /\
    s'.vs_inst_idx = snap.ils_state.vs_inst_idx /\
    t.vs_current_bb = frame.ipf_state.vs_current_bb /\
    t.vs_inst_idx = frame.ipf_state.vs_inst_idx
Proof
  strip_tac >> drule_all inline_cell_zipper_sound >> strip_tac >>
  gvs[inline_cell_at_def, functionInlinerSiteLayoutTheory.inline_fetched_fields_def,
      functionInlinerSiteLayoutTheory.inline_inst_fields_def] >>
  irule inline_owner_storage_value_step >> simp[] >> metis_tac[]
QED
