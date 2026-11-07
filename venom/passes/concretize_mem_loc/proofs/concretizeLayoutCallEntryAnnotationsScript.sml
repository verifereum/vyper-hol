Theory concretizeLayoutCallEntryAnnotations
Ancestors frameResolvedCoherent frameResolvedTrace frameResolvedOrigins
  frameActivationLifetime frameJointTrace frameJointTransition frameOriginUpdates
  ptrDiscipline ptrDisciplineEmptyTaint venomExecSemantics venomState
  finite_map list arithmetic

(* The edge is from the fixed ambient annotation sequence. *)
Theorem layout_call_annotation_edge:
  resolved_annotation_edge C n
    (JointConfig stk PG G tn fn inst s oms om hs h) NONE qc
    ids ((rp,rv)::anns) ids' anns' /\
  decode_invoke inst = SOME (name,ops) ==>
  ids' = SUC n::ids /\
  anns' = (MAP (resolved_op rv) ops,FEMPTY)::(rp,rv)::anns
Proof
  simp[resolved_annotation_edge_def, lifetime_step_def] >> strip_tac >>
  qpat_x_assum `resolved_annotation_update _ _ _ _ _` mp_tac >>
  simp[Once resolved_annotation_update_cases] >> rpt strip_tac >> gvs[]
QED

Theorem layout_resolved_argument_fresh:
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  lifetime_ok n (birth::ids)
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  MEM (SOME ((token,aid),site)) (MAP (resolved_op rv) ops) ==>
  token <> SUC n
Proof
  strip_tac >> drule resolved_config_current >> simp[] >> strip_tac >>
  fs[resolved_frame_ok_def] >> drule_all resolved_arguments_live >>
  simp[resolved_live_def, lifetime_ok_def] >> rpt strip_tac >>
  `MEM token (birth::ids)` by (pure_rewrite_tac[MEM_EL] >> qexists `k` >> simp[]) >>
  gvs[lifetime_ok_def, EVERY_MEM] >>
  first_x_assum drule >> simp[]
QED

Theorem layout_resolved_phis_no_predecessor:
  !insts. resolved_phis NONE FEMPTY insts = FEMPTY
Proof
  Induct >> simp[resolved_phis_def, resolved_phi_def, origin_set_def] >>
  gen_tac >> Cases_on `h.inst_outputs` >> simp[]
QED

Theorem layout_phis_taint_no_predecessor:
  !insts tn. var_taint_empty tn.t_var ==>
    var_taint_empty (phis_taint NONE tn insts)
Proof
  Induct >> simp[phis_taint_def, phi_taint_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  irule set_var_taint_empty >> simp[]
QED

val _ = export_theory();
