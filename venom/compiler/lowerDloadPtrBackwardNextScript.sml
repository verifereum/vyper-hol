Theory lowerDloadPtrBackwardNext
Ancestors
  lowerDloadPtrExpansionNext lowerDloadPtrBackward lowerDloadPtrBytesTransport
  lowerDloadPtrJointNext lowerDloadPtrPhase lowerDloadPtrRel
  ptrDiscipline lowerDloadDefs venomInst venomExecSemantics venomState
  instIdxIndep list words finite_map pred_set arithmetic

Theorem dloadbytes_supply_definedness_control:
  lower_dload_inst_supply supply i = (xs,next) /\
  fresh_ir_var supply = (cv,supply1) /\
  i.inst_opcode = DLOADBYTES /\ i.inst_operands = [dst;off;sz] /\ i.inst_outputs = [] /\
  cv NOTIN U /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  step_inst fuel C i s = OK s1 /\
  dload_prefix_match fuel Ct PH xs 2 t H un t2 H2 un2 ==>
  s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
  s1.vs_inst_idx = s.vs_inst_idx /\
  t2.vs_current_bb = t.vs_current_bb /\ t2.vs_prev_bb = t.vs_prev_bb /\
  t2.vs_inst_idx = t.vs_inst_idx + LENGTH xs /\
  (!v. v IN U ==>
    (lookup_var v (s1 with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
     lookup_var v t2 = NONE))
Proof
  strip_tac >>
  qpat_x_assum `lower_dload_inst_supply _ _ = _` mp_tac >>
  simp[lower_dload_inst_supply_def] >>
  Cases_on `fresh_inst_id supply1` >> simp[] >>
  rename1 `fresh_inst_id supply1 = (add_id,supply2)` >>
  Cases_on `fresh_inst_id supply2` >> simp[] >> strip_tac >> gvs[] >>
  drule_at (Pat `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _`)
    dloadbytes_two_step_lookup >> simp[] >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = _`)) >> simp[] >> strip_tac >>
  suspend "control"
QED

Resume dloadbytes_supply_definedness_control[control]:
  qpat_x_assum `step_inst _ _ i _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  `2 = SUC (SUC 0)` by decide_tac >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  simp[dload_prefix_match_def] >> rpt strip_tac >> gvs[] >>
  simp[write_memory_with_expansion_def] >>
  qpat_x_assum `step_inst _ _ _ (_ with vs_inst_idx := _) = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  fs[write_memory_with_expansion_def, lookup_var_def] >>
  qpat_x_assum `step_inst _ _ _ t = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def] >>
  simp[exec_pure2_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  simp[write_memory_with_expansion_def, update_var_def] >>
  rpt strip_tac >> rename1 `w IN U` >>
  `w <> cv` by metis_tac[] >> simp[FLOOKUP_UPDATE]
QED

Finalise dloadbytes_supply_definedness_control

(* General implementations; the historical interfaces below are compatibility
   corollaries. V tracks relational values, U tracks lookup definedness. *)
Theorem dload_tracked_backward_next_fresh:
  dload_boundary_core lo (r::rs) V Ws PG PH G H tn un s t cs ds /\
  r.dr_scratch = FDOM t.vs_allocas DIFF orig /\
  FDOM s.vs_allocas SUBSET orig /\ (EL 0 xs).inst_id NOTIN orig /\
  (FLOOKUP t.vs_allocas (EL 0 xs).inst_id = NONE ==> t.vs_alloca_next + 32 < dimword (:256)) /\
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\ i.inst_outputs = [out] /\
  lower_dload_inst_supply supply i = (xs,next) /\
  (EL 0 xs).inst_outputs = [av] /\ (EL 1 xs).inst_outputs = [cv] /\
  av <> cv /\ av NOTIN V /\ cv NOTIN V /\
  off <> Var av /\ code_layout_valid s /\ dload_offset_ok C f i s /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  taint_ok f tn i s /\ (!v. off = Var v ==> v IN V) /\
  dload_prefix_match fuel Ct PH xs 4 t H un t4 H4 un4 /\
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i xs 0 /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  av NOTIN U /\ cv NOTIN U /\ active_inst g j t4 ==>
  ?s1 r1 i' emitted'.
    step_inst fuel C i s = OK s1 /\
    r1.dr_source = r.dr_source /\
    r1.dr_scratch = (EL 0 xs).inst_id INSERT r.dr_scratch /\
    dload_boundary_core lo (r1::rs) V Ws PG PH
      (step_prov PG G i s1) H4 (step_taint i s s1 tn) un4
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) t4 cs ds /\
    frame_reachable vs C cs PG (step_prov PG G i s1) (step_taint i s s1 tn)
      f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    dload_control_match q f g (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      t4 i' emitted' 0 /\ j = HD emitted' /\
    (!v. v IN U ==>
      (lookup_var v (s1 with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
       lookup_var v t4 = NONE))
Proof
  strip_tac >> drule_all dload_supply_backward_boundary_fresh >> strip_tac >>
  drule_all dload_supply_definedness_control >> strip_tac >>
  drule_all dload_control_emission_next_fields >> strip_tac >>
  qexistsl [`s1`,`r1`,`i'`,`emitted'`] >> simp[] >>
  irule frame_reachable_next >> simp[is_terminator_def] >>
  `active_inst f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ i' _ _` mp_tac >>
     simp[dload_control_match_def] >> metis_tac[]) >>
  simp[] >> conj_tac >- metis_tac[] >>
  qpat_x_assum `dload_control_match _ _ _ s t _ _ _` mp_tac >>
  simp[dload_control_match_def] >> metis_tac[]
QED

Theorem dload_tracked_backward_next:
  dload_boundary_core lo (r::rs) V Ws PG PH G H tn un s t cs ds /\
  r.dr_scratch = FDOM t.vs_allocas DIFF orig /\
  FDOM s.vs_allocas SUBSET orig /\ (EL 0 xs).inst_id NOTIN orig /\
  t.vs_alloca_next + 32 < dimword (:256) /\
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\ i.inst_outputs = [out] /\
  lower_dload_inst_supply supply i = (xs,next) /\
  (EL 0 xs).inst_outputs = [av] /\ (EL 1 xs).inst_outputs = [cv] /\
  av <> cv /\ av NOTIN V /\ cv NOTIN V /\
  off <> Var av /\ code_layout_valid s /\ dload_offset_ok C f i s /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  taint_ok f tn i s /\ (!v. off = Var v ==> v IN V) /\
  dload_prefix_match fuel Ct PH xs 4 t H un t4 H4 un4 /\
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i xs 0 /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  av NOTIN U /\ cv NOTIN U /\ active_inst g j t4 ==>
  ?s1 r1 i' emitted'.
    step_inst fuel C i s = OK s1 /\
    r1.dr_source = r.dr_source /\
    r1.dr_scratch = (EL 0 xs).inst_id INSERT r.dr_scratch /\
    dload_boundary_core lo (r1::rs) V Ws PG PH
      (step_prov PG G i s1) H4 (step_taint i s s1 tn) un4
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) t4 cs ds /\
    frame_reachable vs C cs PG (step_prov PG G i s1) (step_taint i s s1 tn)
      f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    dload_control_match q f g (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      t4 i' emitted' 0 /\ j = HD emitted' /\
    (!v. v IN U ==>
      (lookup_var v (s1 with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
       lookup_var v t4 = NONE))
Proof
  strip_tac >> irule dload_tracked_backward_next_fresh >> metis_tac[]
QED

Theorem dloadbytes_tracked_next:
  lower_dload_inst_supply supply i = (xs,next) /\
  fresh_ir_var supply = (cv,supply1) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  i.inst_opcode = DLOADBYTES /\ i.inst_operands = [dst;off;sz] /\ i.inst_outputs = [] /\
  cv NOTIN V /\ dst <> Var cv /\ sz <> Var cv /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  taint_ok f tn i s /\ access_ok lo G f i s /\ ~in_revert_forward f s /\
  code_layout_valid s /\ dload_offset_ok C f i s /\
  dload_prefix_match fuel Ct PH xs 2 t H un t2 H2 un2 /\
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i xs 0 /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  cv NOTIN U /\ active_inst g j t2 ==>
  ?s1 i' emitted'.
    step_inst fuel C i s = OK s1 /\
    frame_reachable vs C cs PG (step_prov PG G i s1) (step_taint i s s1 tn)
      f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    dload_control_match q f g (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      t2 i' emitted' 0 /\ j = HD emitted' /\
    dload_boundary_core lo fs V Ws PG PH
      (step_prov PG G i s1) H2 (step_taint i s s1 tn) un2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) t2 cs ds /\
    (!v. lookup_var v s1 = lookup_var v s) /\
    (!v. v <> cv ==> lookup_var v t2 = lookup_var v t) /\
    (!v. v IN U ==>
      (lookup_var v (s1 with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
       lookup_var v t2 = NONE))
Proof
  strip_tac >> drule_all dloadbytes_supply_boundary >> strip_tac >>
  drule_all dloadbytes_supply_definedness_control >> strip_tac >>
  drule_all dload_control_emission_next_fields >> strip_tac >>
  qexistsl [`s1`,`i'`,`emitted'`] >> simp[] >>
  irule frame_reachable_next >> simp[is_terminator_def] >>
  `active_inst f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ i' _ _` mp_tac >>
     simp[dload_control_match_def] >> metis_tac[]) >>
  simp[] >> conj_tac >- metis_tac[] >>
  qpat_x_assum `dload_control_match _ _ _ s t _ _ _` mp_tac >>
  simp[dload_control_match_def] >> metis_tac[]
QED

Theorem dload_actual_backward_dload_next:
  dload_boundary_core lo (r::rs) {v | ~retpc_var f v} Ws PG PH G H tn un s t cs ds /\
  r.dr_scratch = FDOM t.vs_allocas DIFF orig /\
  FDOM s.vs_allocas SUBSET orig /\ (EL 0 xs).inst_id NOTIN orig /\
  t.vs_alloca_next + 32 < dimword (:256) /\
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\ i.inst_outputs = [out] /\
  lower_dload_inst_supply supply i = (xs,next) /\
  (EL 0 xs).inst_outputs = [av] /\ (EL 1 xs).inst_outputs = [cv] /\
  av <> cv /\ av NOTIN {v | ~retpc_var f v} /\ cv NOTIN {v | ~retpc_var f v} /\
  off <> Var av /\ code_layout_valid s /\ dload_offset_ok C f i s /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  taint_ok f tn i s /\ (!v. off = Var v ==> v IN {v | ~retpc_var f v}) /\
  dload_prefix_match fuel Ct PH xs 4 t H un t4 H4 un4 /\
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i xs 0 /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  (!v. v IN set (fn_ir_vars f) ==>
    (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  av NOTIN set (fn_ir_vars f) /\ cv NOTIN set (fn_ir_vars f) /\
  active_inst g j t4 ==>
  ?s1 r1 i' emitted'.
    step_inst fuel C i s = OK s1 /\
    r1.dr_source = r.dr_source /\
    r1.dr_scratch = (EL 0 xs).inst_id INSERT r.dr_scratch /\
    dload_boundary_core lo (r1::rs) {v | ~retpc_var f v} Ws PG PH
      (step_prov PG G i s1) H4 (step_taint i s s1 tn) un4
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) t4 cs ds /\
    frame_reachable vs C cs PG (step_prov PG G i s1) (step_taint i s s1 tn)
      f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    dload_control_match q f g (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      t4 i' emitted' 0 /\ j = HD emitted' /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v (s1 with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
       lookup_var v t4 = NONE))
Proof
  strip_tac >> drule_all dload_tracked_backward_next >> simp[]
QED

Theorem dload_actual_dloadbytes_next:
  lower_dload_inst_supply supply i = (xs,next) /\
  fresh_ir_var supply = (cv,supply1) /\
  dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH G H tn un s t cs ds /\
  i.inst_opcode = DLOADBYTES /\ i.inst_operands = [dst;off;sz] /\ i.inst_outputs = [] /\
  cv NOTIN {v | ~retpc_var f v} /\ dst <> Var cv /\ sz <> Var cv /\
  (!v. MEM (Var v) i.inst_operands ==> v IN {v | ~retpc_var f v}) /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  taint_ok f tn i s /\ access_ok lo G f i s /\ ~in_revert_forward f s /\
  code_layout_valid s /\ dload_offset_ok C f i s /\
  dload_prefix_match fuel Ct PH xs 2 t H un t2 H2 un2 /\
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i xs 0 /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  (!v. v IN set (fn_ir_vars f) ==>
    (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  cv NOTIN set (fn_ir_vars f) /\ active_inst g j t2 ==>
  ?s1 i' emitted'.
    step_inst fuel C i s = OK s1 /\
    frame_reachable vs C cs PG (step_prov PG G i s1) (step_taint i s s1 tn)
      f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    dload_control_match q f g (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      t2 i' emitted' 0 /\ j = HD emitted' /\
    dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH
      (step_prov PG G i s1) H2 (step_taint i s s1 tn) un2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx) t2 cs ds /\
    (!v. lookup_var v s1 = lookup_var v s) /\
    (!v. v <> cv ==> lookup_var v t2 = lookup_var v t) /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v (s1 with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
       lookup_var v t2 = NONE))
Proof
  strip_tac >> drule_all dloadbytes_tracked_next >> simp[]
QED

