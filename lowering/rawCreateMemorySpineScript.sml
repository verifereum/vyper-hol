(* A primitive snapshot instruction has a concrete raw successor.  The
   origin path supplies its checked first edge, not its final cursor. *)
Theory rawCreateMemorySpine
Ancestors
  rawCreateAdminSpine fragGasOrigin fragGasOriginPtr fragExec bodyPtrMakeArrayEmission
  bodyPtrMakeArrayPrimitiveInstall entryDecodeStructure abiEncoderProps
  venomExecSemantics venomInst venomState arithmetic

Theorem admin_ok_spine_primitive:
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_id IN frag_ids a b /\ s.vs_inst_idx < LENGTH b.cs_current_insts /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  step_inst_base i s = OK r /\
  t = (r with vs_inst_idx := SUC s.vs_inst_idx) /\
  gas_origin_ptr_path (D,lo,E,C,f,PG) (s,G,tn) [] (OK t,G1,tn1) ==>
  admin_ok_spine a b E C f s t
Proof
  strip_tac >> drule gas_origin_ptr_path_projections >> strip_tac >>
  qpat_x_assum `gas_origin_path T E C f s [] (OK t)`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [Once gas_origin_path_cases,exit_result_def])
  >- fs[] >>
  rename1 `gas_origin_edge T E C f s [] (OK mid)` >>
  `mid = t` by
    (qpat_assum `gas_origin_edge T E C f s [] (OK mid)` mp_tac >>
     rewrite_tac[gas_origin_edge_def] >> strip_tac >>
     gvs[step_inst_non_invoke,exit_result_def]) >>
  irule admin_ok_spine_single >> fs[] >> metis_tac[]
QED

Theorem admin_ok_spine_emit:
  emit_op opc args x = (Var p,y) /\ fn_has_code x y f /\
  s.vs_current_bb = x.cs_current_bb /\ s.vs_inst_idx = LENGTH x.cs_current_insts /\
  a.cs_next_id <= x.cs_next_id /\ y.cs_next_id <= b.cs_next_id /\
  LENGTH y.cs_current_insts <= LENGTH b.cs_current_insts /\
  opc <> INVOKE /\ ~is_terminator opc /\
  step_inst_base (mk_inst x.cs_next_id opc args [p]) s = OK r /\
  t = (r with vs_inst_idx := LENGTH y.cs_current_insts) /\
  gas_origin_ptr_path (D,lo,E,C,f,PG) (s,G,tn) [] (OK t,G1,tn1) ==>
  admin_ok_spine a b E C f s t
Proof
  strip_tac >> drule_all emit_op_fetch_boundary >> strip_tac >>
  drule emit_op_next_id >> strip_tac >>
  irule admin_ok_spine_primitive >>
  qpat_assum `step_inst_base _ _ = OK _` (irule_at Any) >>
  qpat_assum `gas_origin_ptr_path _ _ [] _` (irule_at Any) >>
  qexists_tac `bb` >>
  gvs[frag_ids_def,mk_inst_def] >> decide_tac
QED

Theorem admin_ok_spine_emit_void:
  emit_void opc args x = ((),y) /\ fn_has_code x y f /\
  s.vs_current_bb = x.cs_current_bb /\ s.vs_inst_idx = LENGTH x.cs_current_insts /\
  a.cs_next_id <= x.cs_next_id /\ y.cs_next_id <= b.cs_next_id /\
  LENGTH y.cs_current_insts <= LENGTH b.cs_current_insts /\
  opc <> INVOKE /\ ~is_terminator opc /\
  step_inst_base (mk_inst x.cs_next_id opc args []) s = OK r /\
  t = (r with vs_inst_idx := LENGTH y.cs_current_insts) /\
  gas_origin_ptr_path (D,lo,E,C,f,PG) (s,G,tn) [] (OK t,G1,tn1) ==>
  admin_ok_spine a b E C f s t
Proof
  strip_tac >> drule_all emit_void_fetch_boundary >> strip_tac >>
  drule emit_void_next_id >> strip_tac >>
  irule admin_ok_spine_primitive >>
  qpat_assum `step_inst_base _ _ = OK _` (irule_at Any) >>
  qpat_assum `gas_origin_ptr_path _ _ [] _` (irule_at Any) >>
  qexists_tac `bb` >>
  gvs[frag_ids_def,mk_inst_def] >> decide_tac
QED
