Theory makeSsaCurrentRetainedJoint
Ancestors makeSsaCurrentRetainedRead makeSsaCurrentPhiOrigins
  makeSsaCurrentJointRuntime venomWf venomExecSemantics venomExecProps list alist

Theorem current_joint_selected_phi_success:
  current_joint_rel V M N rs D st st' /\ MEM v D /\
  st.vs_prev_bb = SOME p /\ inst.inst_opcode = PHI /\ inst_wf inst /\
  resolve_phi p inst.inst_operands = SOME (Var v) /\
  eval_one_phi st inst = SOME (dst,value) /\
  target.inst_outputs = [name] /\
  resolve_phi p target.inst_operands = SOME (Var (latest_current_name rs v)) ==>
  ?origin. ALOOKUP M v = SOME origin /\ V origin = SOME value /\
    current_phi_origin_read M p inst (dst,origin) /\
    current_phi_origin_read N p target (name,origin) /\
    eval_one_phi st' target = SOME (name,value)
Proof
  strip_tac >>
  `current_origin_realizes V M st /\ current_origin_realizes V N st' /\
   st'.vs_prev_bb = SOME p /\
   ALOOKUP M v = ALOOKUP N (latest_current_name rs v)` by
    (fs[current_joint_rel_def] >> metis_tac[]) >>
  drule_all current_phi_origin_extract >> strip_tac >>
  `ALOOKUP M v = SOME origin` by
    (gvs[current_phi_origin_read_def] >> metis_tac[]) >>
  `current_phi_origin_read N p target (name,origin)` by
    (simp[current_phi_origin_read_def] >> metis_tac[]) >>
  qexists `origin` >> simp[] >>
  drule_all current_phi_origin_read_eval >> simp[]
QED

Theorem current_certificate_retained_joint:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\ fn_phis_non_degenerate fn /\
  lookup_block h fn.fn_blocks = SOME old /\ i < LENGTH old.bb_instructions /\
  (EL i old.bb_instructions).inst_opcode = PHI /\
  (EL i old.bb_instructions).inst_outputs = [dst] /\
  MEM ev events /\ current_event_label ev = p /\ fn_cfg_edge fn p h /\
  resolve_phi p (EL i old.bb_instructions).inst_operands = SOME (Var v) /\
  current_joint_rel V M N (current_event_exit_rs ev) D st st' /\ MEM v D /\
  st.vs_prev_bb = SOME p /\
  eval_one_phi st (EL i old.bb_instructions) = SOME (dst,value) ==>
  ?out r name origin. lookup_block h fn'.fn_blocks = SOME out /\
    r < LENGTH out.bb_instructions /\ (EL r out.bb_instructions).inst_opcode = PHI /\
    (EL r out.bb_instructions).inst_outputs = [name] /\
    current_token_name H (CurrentOriginal h i 0) = SOME name /\
    ALOOKUP M v = SOME origin /\ V origin = SOME value /\
    current_phi_origin_read M p (EL i old.bb_instructions) (dst,origin) /\
    current_phi_origin_read N p (EL r out.bb_instructions) (name,origin) /\
    eval_one_phi st' (EL r out.bb_instructions) = SOME (name,value)
Proof
  strip_tac >> drule_all current_certificate_retained_read >> strip_tac >>
  `inst_wf (EL i old.bb_instructions)` by
    (fs[fn_inst_wf_def] >> first_x_assum irule >> qexists `old` >>
     conj_tac >- metis_tac[lookup_block_MEM] >> metis_tac[EL_MEM]) >>
  drule_all current_joint_selected_phi_success >> strip_tac >>
  qexistsl_tac [`out`, `r`, `name`, `origin`] >> simp[]
QED

Theorem current_phi_origin_read_functional:
  current_phi_origin_read N p inst b /\ current_phi_origin_read N p inst c ==> b = c
Proof
  Cases_on `b` >> Cases_on `c` >>
  simp[current_phi_origin_read_def] >> rpt strip_tac >> gvs[]
QED

Theorem current_phi_origin_binding_member:
  !prefix bindings. LIST_REL (current_phi_origin_read N p) prefix bindings /\
    MEM inst prefix /\ current_phi_origin_read N p inst (name,origin) ==>
    MEM (name,origin) bindings
Proof
  Induct >> Cases_on `bindings` >> simp[] >> rpt strip_tac >> gvs[]
  >- metis_tac[current_phi_origin_read_functional] >>
  metis_tac[]
QED

Theorem current_phi_origin_binding_outputs:
  !prefix bindings. LIST_REL (current_phi_origin_read N p) prefix bindings ==>
    MAP FST bindings = FLAT (MAP (\i. i.inst_outputs) prefix)
Proof
  Induct >> Cases_on `bindings` >> simp[] >> rpt strip_tac >>
  fs[current_phi_origin_read_def] >> simp[]
QED

Theorem current_phi_origin_batch_projection:
  LIST_REL (current_phi_origin_read N p) prefix bindings /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) prefix)) /\
  MEM inst prefix /\ current_phi_origin_read N p inst (name,origin) ==>
  ALOOKUP (bindings ++ N) name = SOME origin
Proof
  strip_tac >> drule_all current_phi_origin_binding_member >> strip_tac >>
  drule current_phi_origin_binding_outputs >> strip_tac >>
  `ALL_DISTINCT (MAP FST bindings)` by metis_tac[] >>
  simp[ALOOKUP_APPEND] >>
  `ALOOKUP bindings name = SOME origin` by metis_tac[ALOOKUP_ALL_DISTINCT_MEM] >> simp[]
QED

Theorem current_eval_phis_retained_origin:
  EVERY (\i. i.inst_opcode = PHI /\ inst_wf i) prefix /\
  (suffix = [] \/ (HD suffix).inst_opcode <> PHI) /\
  st.vs_prev_bb = SOME p /\ current_origin_realizes V N st /\
  eval_phis st (prefix ++ suffix) = OK post /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) prefix)) /\
  MEM inst prefix /\ current_phi_origin_read N p inst (name,origin) ==>
  ?bindings. LIST_REL (current_phi_origin_read N p) prefix bindings /\
    current_origin_realizes V (bindings ++ N) post /\
    ALOOKUP (bindings ++ N) name = SOME origin
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_eval_phis_origin_batch >> strip_tac >>
  qexists `bindings` >> simp[] >>
  irule current_phi_origin_batch_projection >> metis_tac[]
QED
