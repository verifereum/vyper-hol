(* Simulation of GAS-event prefixes along a selected path.  The entry
   certificates fix the target's next step, block entry or callee entry from
   the path up to the next config only; their tails, quantified over the rest
   of the run, give back the existing next and run_next certificates.
   Completed steps and blocks go through selected_simulation_induction. *)
Theory frameSelectedPrefix
Ancestors frameSelectedSimulation frameDecoratedPrefix frameFinitePrefix
  frameGasEvents frameSelectedDecoration frameFiniteJointDecoration
  frameFiniteExecution gasEvents venomExecSemantics venomState venomInst
  list arithmetic

(* The target either stays put on a source step that leaves no event, or
   takes its own successful non-terminator step j. *)
Definition block_advance_def:
  block_advance bb' (i:instruction) (j:instruction) (t:venom_state) rs' tb <=>
    (tb = t /\ i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE) \/
    (?tp. get_instruction bb' t.vs_inst_idx = SOME j /\
      ~is_terminator j.inst_opcode /\ rs' = OK tp /\
      tb = tp with vs_inst_idx := SUC t.vs_inst_idx)
End

Definition target_block_entry_def:
  target_block_entry fn' (t:venom_state) bb' tb <=>
    ?phi'. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
      eval_phis t bb'.bb_instructions = OK phi' /\
      tb = phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions
End

Definition selected_next_entry_certificate_def:
  selected_next_entry_certificate C C' q0 path ES EB OS OB <=>
    !bb s i post fn q n ws qm ds ev qn bb' t.
      decoration_at fn i s q /\ get_instruction bb s.vs_inst_idx = SOME i /\
      decorated_step C i s (OK post) q n ws qm ds /\
      ~is_terminator i.inst_opcode /\ decoration_consumes C i q post qm ev qn /\
      decoration_entry fn (post with vs_inst_idx := SUC s.vs_inst_idx) qn /\
      selected_segment C q0 path n q (ws++[(ev,qn)]) qn /\
      EB q n bb s bb' t ==>
      ?j. ES q n i s j t /\
        (!rs'. finite_step C' j t rs' /\
          OS q n qm (n+LENGTH ws) i s j t (OK post) rs' ==>
          ?tb. EB qn (n+LENGTH ws+1) bb
            (post with vs_inst_idx := SUC s.vs_inst_idx) bb' tb /\
            block_advance bb' i j t rs' tb /\
            !r wb qe db rb'.
              decorated_block C bb (post with vs_inst_idx := SUC s.vs_inst_idx)
                r qn (n+LENGTH ws+1) wb qe db /\
              selected_segment C q0 path n q (ws++[(ev,qn)]++wb) qe /\
              finite_block C' bb' tb rb' /\
              OB qn (n+LENGTH ws+1) qe (n+LENGTH ws+1+LENGTH wb) bb
                (post with vs_inst_idx := SUC s.vs_inst_idx) bb' tb r rb' ==>
              selected_block_match C' OB q n (ws++[(ev,qn)]++wb) qe bb s bb' t r)
End

Definition selected_run_next_entry_certificate_def:
  selected_run_next_entry_certificate C C' q0 path EB ER OB OutR <=>
    !fn s bb phi post q n wb qm db fuel qn fn' t.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      eval_phis s bb.bb_instructions = OK phi /\
      decoration_entry fn (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) q /\
      decorated_block C bb (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
        (OK post) q n wb qm db /\ ~post.vs_halted /\ local_pending C qm (OK post) /\
      (?stk PG G tn i si oms om hs h.
        qm = JointConfig stk PG G tn fn i si oms om hs h /\
        active_inst fn i si /\ is_terminator i.inst_opcode) /\
      joint_transition C qm (SOME (OriginBlock fuel post)) qn /\
      selected_segment C q0 path n q (wb++[(SOME (OriginBlock fuel post),qn)]) qn /\
      ER q n fn s fn' t ==>
      ?bb' tb. EB q n bb (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) bb' tb /\
        target_block_entry fn' t bb' tb /\
        !rb'. finite_block C' bb' tb rb' /\
          OB q n qm (n+LENGTH wb) bb
            (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) bb' tb (OK post) rb' ==>
          ?tr. rb' = OK tr /\ ~tr.vs_halted /\
            ER qn (n+LENGTH wb+1) fn post fn' tr /\
            !r wr qe dr rr'.
              decorated_run C fn post r qn (n+LENGTH wb+1) wr qe dr /\
              selected_segment C q0 path n q
                (wb++[(SOME (OriginBlock fuel post),qn)]++wr) qe /\
              finite_run C' fn' tr rr' /\
              OutR qn (n+LENGTH wb+1) qe (n+LENGTH wb+1+LENGTH wr) fn post fn' tr r rr' ==>
              selected_run_match C' OutR q n
                (wb++[(SOME (OriginBlock fuel post),qn)]++wr) qe fn s fn' t r
End

Definition selected_run_entry_certificate_def:
  selected_run_entry_certificate C C' q0 path EB ER <=>
    !fn s bb phi q n fn' t.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      eval_phis s bb.bb_instructions = OK phi /\
      decoration_entry fn (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) q /\
      selected_segment C q0 path n q [] q /\ ER q n fn s fn' t ==>
      fn'.fn_name = fn.fn_name /\
      ?bb' tb. EB q n bb (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) bb' tb /\
        target_block_entry fn' t bb' tb
End

Definition selected_call_entry_certificate_def:
  selected_call_entry_certificate C C' q0 path ES ER <=>
    !i s name ops fn args cs caller q n qc j t.
      decoration_at caller i s q /\ i.inst_opcode = INVOKE /\
      decode_invoke i = SOME (name,ops) /\
      lookup_function name C.ctx_functions = SOME fn /\
      eval_operands ops s = SOME args /\ setup_callee fn args s = SOME cs /\
      joint_transition C q NONE qc /\
      selected_segment C q0 path n q [(NONE,qc)] qc /\ ES q n i s j t ==>
      ?name' ops' fn' args' ct. j.inst_opcode = INVOKE /\
        decode_invoke j = SOME (name',ops') /\
        lookup_function name' C'.ctx_functions = SOME fn' /\
        eval_operands ops' t = SOME args' /\ setup_callee fn' args' t = SOME ct /\
        ER qc (n+1) fn cs fn' ct
End

Definition selected_prefix_end_certificate_def:
  selected_prefix_end_certificate C C' q0 path ES EB <=>
    !bb s i fn q n bb' t.
      decoration_at fn i s q /\ get_instruction bb s.vs_inst_idx = SOME i /\
      (i.inst_opcode = GAS \/ i.inst_opcode = INVOKE) /\
      selected_segment C q0 path n q [] q /\ EB q n bb s bb' t ==>
      ?j. get_instruction bb' t.vs_inst_idx = SOME j /\
        (i.inst_opcode = GAS ==> j.inst_opcode = GAS /\ j.inst_id = i.inst_id) /\
        (i.inst_opcode = INVOKE ==> ES q n i s j t)
End

Definition selected_prefix_certificates_def:
  selected_prefix_certificates C C' q0 path ES EB ER OS OB OutR <=>
    selected_next_entry_certificate C C' q0 path ES EB OS OB /\
    selected_run_next_entry_certificate C C' q0 path EB ER OB OutR /\
    selected_run_entry_certificate C C' q0 path EB ER /\
    selected_call_entry_certificate C C' q0 path ES ER /\
    selected_prefix_end_certificate C C' q0 path ES EB
End

(* ===== The entry certificates give back the existing ones ===== *)

Theorem selected_next_entry_certificate_next:
  selected_next_entry_certificate C C' q0 path ES EB OS OB ==>
  selected_next_certificate C C' q0 path ES EB OS OB
Proof
  rewrite_tac[selected_next_entry_certificate_def,
    selected_next_certificate_def] >>
  rpt strip_tac >>
  `joint_segment C q ws qm` by metis_tac[cj 1 decorated_execution_segment] >>
  `joint_segment C qn wb qe` by metis_tac[cj 2 decorated_execution_segment] >>
  `joint_segment C q (ws++[(ev,qn)]) qn` by
    (irule joint_segment_append >> fs[decoration_consumes_def] >>
     simp[joint_segment_def] >> metis_tac[]) >>
  `selected_segment C q0 path n q (ws++[(ev,qn)]) qn` by
    (drule_all selected_segment_parts >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  qexists `j` >> simp[] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists `tb` >> fs[] >> rpt strip_tac >>
  first_x_assum irule >> fs[] >> metis_tac[]
QED

Theorem selected_run_next_entry_certificate_run_next:
  selected_run_next_entry_certificate C C' q0 path EB ER OB OutR ==>
  selected_run_next_certificate C C' q0 path EB ER OB OutR
Proof
  rewrite_tac[selected_run_next_entry_certificate_def,
    selected_run_next_certificate_def] >>
  strip_tac >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `joint_segment C q wb qm` by metis_tac[cj 2 decorated_execution_segment] >>
  `joint_segment C qn wr qe` by metis_tac[cj 3 decorated_execution_segment] >>
  `joint_segment C q (wb++[(SOME (OriginBlock fuel post),qn)]) qn` by
    (irule joint_segment_append >> simp[joint_segment_def] >> metis_tac[]) >>
  `selected_segment C q0 path n q
     (wb++[(SOME (OriginBlock fuel post),qn)]) qn` by
    (drule_all selected_segment_parts >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl [`bb'`, `tb`] >> simp[] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists `tr` >> fs[] >> rpt strip_tac >>
  first_x_assum irule >> fs[] >> metis_tac[]
QED

(* ===== The prefix driver ===== *)

Theorem selected_prefix_simulation_induction:
  (!C owner bb s q n w qe es. decorated_block_prefix C owner bb s q n w qe es ==>
    !C' q0 path ES EB ER OS OB OutR bb' t.
      selected_simulation_contract C C' q0 path ES EB ER
        (events_OS C C' OS) (events_OB C C' OB) (events_OutR C C' OutR) /\
      selected_prefix_certificates C C' q0 path ES EB ER
        (events_OS C C' OS) (events_OB C C' OB) (events_OutR C C' OutR) /\
      selected_segment C q0 path n q w qe /\ EB q n bb s bb' t ==>
      finite_block_prefix C' owner bb' t es) /\
  (!C fn s q n w qe es. decorated_run_prefix C fn s q n w qe es ==>
    !C' q0 path ES EB ER OS OB OutR fn' t.
      selected_simulation_contract C C' q0 path ES EB ER
        (events_OS C C' OS) (events_OB C C' OB) (events_OutR C C' OutR) /\
      selected_prefix_certificates C C' q0 path ES EB ER
        (events_OS C C' OS) (events_OB C C' OB) (events_OutR C C' OutR) /\
      selected_segment C q0 path n q w qe /\ ER q n fn s fn' t ==>
      finite_run_prefix C' fn' t es)
Proof
  ho_match_mp_tac decorated_prefix_strongind >> rpt conj_tac
  >- suspend "gas"
  >- suspend "invoke"
  >- suspend "next"
  >- suspend "run_here"
  >> suspend "run_next"
QED

Resume selected_prefix_simulation_induction[gas]:
  rpt strip_tac >> fs[selected_prefix_certificates_def] >>
  qpat_x_assum `selected_prefix_end_certificate _ _ _ _ _ _` mp_tac >>
  rewrite_tac[selected_prefix_end_certificate_def] >>
  disch_then (qspecl_then [`bb`, `s`, `i`, `fn`, `q`, `n`, `bb'`, `t`] mp_tac) >>
  simp[] >> strip_tac >>
  `[(owner,i.inst_id)] = [(owner,j.inst_id)]` by simp[] >>
  pop_assum SUBST1_TAC >> irule finite_prefix_gas >> simp[]
QED

Resume selected_prefix_simulation_induction[invoke]:
  rpt strip_tac >>
  qmatch_asmsub_rename_tac `decorated_run_prefix C fn cs qc (n + 1) wc qe es` >>
  qpat_assum `selected_prefix_certificates _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[selected_prefix_certificates_def] >> strip_tac >>
  `joint_segment C qc wc qe` by metis_tac[cj 2 decorated_prefix_segment] >>
  `selected_segment C q0 path n q [(NONE,qc)] qc /\
   selected_segment C q0 path
     (n + LENGTH ([(NONE,qc)]:(origin_event option # joint_config) list)) qc wc qe` by
    (irule selected_segment_parts >> gvs[joint_segment_def]) >>
  `selected_segment C q0 path n q [] q` by metis_tac[selected_segment_start] >>
  qpat_x_assum `selected_prefix_end_certificate _ _ _ _ _ _` mp_tac >>
  rewrite_tac[selected_prefix_end_certificate_def] >>
  disch_then (qspecl_then [`bb`, `s`, `i`, `caller`, `q`, `n`, `bb'`, `t`] mp_tac) >>
  impl_tac >- fs[] >> strip_tac >>
  `ES q n i s j t` by metis_tac[] >>
  qpat_x_assum `selected_call_entry_certificate _ _ _ _ _ _` mp_tac >>
  rewrite_tac[selected_call_entry_certificate_def] >>
  disch_then drule_all >> strip_tac >>
  first_x_assum (qspecl_then [`C'`, `q0`, `path`, `ES`, `EB`, `ER`, `OS`,
    `OB`, `OutR`, `fn'`, `ct`] mp_tac) >>
  impl_tac >- fs[selected_prefix_certificates_def] >> strip_tac >>
  irule finite_prefix_invoke >> metis_tac[]
QED

Resume selected_prefix_simulation_induction[next]:
  rpt strip_tac >>
  qmatch_asmsub_rename_tac `decoration_consumes C i q post qm ev qn` >>
  qmatch_asmsub_rename_tac `decorated_block_prefix C owner bb _ qn _ wb qe es` >>
  qpat_assum `selected_prefix_certificates _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[selected_prefix_certificates_def] >> strip_tac >>
  `joint_segment C q ws qm` by metis_tac[cj 1 decorated_execution_segment] >>
  `joint_segment C qn wb qe` by metis_tac[cj 1 decorated_prefix_segment] >>
  `joint_transition C qm ev qn` by fs[decoration_consumes_def] >>
  `joint_segment C q (ws++[(ev,qn)]) qn` by
    (irule joint_segment_append >> simp[joint_segment_def] >> metis_tac[]) >>
  `selected_segment C q0 path n q (ws++[(ev,qn)]) qn /\
   selected_segment C q0 path (n + LENGTH (ws++[(ev,qn)])) qn wb qe` by
    (irule selected_segment_parts >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `selected_segment C q0 path n q ws qm /\
   selected_segment C q0 path (n + LENGTH ws) qm [(ev,qn)] qn` by
    (irule selected_segment_parts >> simp[joint_segment_def]) >>
  qpat_x_assum `selected_next_entry_certificate _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[selected_next_entry_certificate_def] >>
  disch_then drule_all >> strip_tac >>
  drule (cj 1 selected_simulation_induction) >>
  disch_then drule_all >> rewrite_tac[selected_step_match_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum (qspecl_then [`C'`, `q0`, `path`, `ES`, `EB`, `ER`, `OS`,
    `OB`, `OutR`, `bb'`, `tb`] mp_tac) >>
  impl_tac >- fs[selected_prefix_certificates_def] >> strip_tac >>
  qpat_x_assum `block_advance _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [block_advance_def])
  >- gvs[gas_events_step_def] >>
  gvs[events_OS_def, step_events_agree_def] >>
  `?k'. step_inst k' C' j t = OK tp` by metis_tac[finite_step_iff] >>
  first_x_assum (qspecl_then [`owner`, `k`, `k'`] mp_tac) >>
  simp[] >> disch_then (SUBST1_TAC o SYM) >>
  irule finite_prefix_next >> simp[]
QED

Resume selected_prefix_simulation_induction[run_here]:
  rpt strip_tac >>
  qpat_assum `selected_prefix_certificates _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[selected_prefix_certificates_def] >> strip_tac >>
  drule selected_segment_start >> strip_tac >>
  qpat_x_assum `selected_run_entry_certificate _ _ _ _ _ _` mp_tac >>
  rewrite_tac[selected_run_entry_certificate_def] >>
  disch_then drule_all >> strip_tac >>
  first_x_assum (qspecl_then [`C'`, `q0`, `path`, `ES`, `EB`, `ER`, `OS`,
    `OB`, `OutR`, `bb'`, `tb`] mp_tac) >>
  impl_tac >- fs[selected_prefix_certificates_def] >> strip_tac >>
  qpat_x_assum `fn'.fn_name = fn.fn_name` (assume_tac o SYM) >>
  qpat_x_assum `target_block_entry _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [target_block_entry_def]) >>
  gvs[] >> irule finite_prefix_run_here >> simp[]
QED

Resume selected_prefix_simulation_induction[run_next]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_rename_tac `joint_transition C _ (SOME (OriginBlock fuel post)) qn` >>
  qmatch_asmsub_rename_tac `decorated_run_prefix C fn post qn _ wr qe es` >>
  qpat_assum `selected_prefix_certificates _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[selected_prefix_certificates_def] >> strip_tac >>
  `joint_segment C q wb qm` by metis_tac[cj 2 decorated_execution_segment] >>
  `joint_segment C qn wr qe` by metis_tac[cj 2 decorated_prefix_segment] >>
  `joint_segment C q (wb++[(SOME (OriginBlock fuel post),qn)]) qn` by
    (irule joint_segment_append >> simp[joint_segment_def] >> metis_tac[]) >>
  `selected_segment C q0 path n q (wb++[(SOME (OriginBlock fuel post),qn)]) qn /\
   selected_segment C q0 path
     (n + LENGTH (wb++[(SOME (OriginBlock fuel post),qn)])) qn wr qe` by
    (irule selected_segment_parts >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `selected_segment C q0 path n q wb qm /\
   selected_segment C q0 path (n + LENGTH wb) qm
     [(SOME (OriginBlock fuel post),qn)] qn` by
    (irule selected_segment_parts >> simp[joint_segment_def]) >>
  `selected_segment C q0 path n q [] q` by metis_tac[selected_segment_start] >>
  qpat_x_assum `selected_run_entry_certificate _ _ _ _ _ _` mp_tac >>
  rewrite_tac[selected_run_entry_certificate_def] >>
  disch_then drule_all >> disch_then (assume_tac o CONJUNCT1) >>
  qpat_x_assum `selected_run_next_entry_certificate _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[selected_run_next_entry_certificate_def] >>
  disch_then drule_all >> strip_tac >>
  drule (cj 2 selected_simulation_induction) >>
  disch_then drule_all >> rewrite_tac[selected_block_match_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  first_x_assum (qspecl_then [`C'`, `q0`, `path`, `ES`, `EB`, `ER`, `OS`,
    `OB`, `OutR`, `fn'`, `tr`] mp_tac) >>
  impl_tac >- fs[selected_prefix_certificates_def] >> strip_tac >>
  `?k'. exec_block k' C' bb' tb = OK tr` by metis_tac[finite_block_iff] >>
  qpat_x_assum `fn'.fn_name = fn.fn_name` (assume_tac o SYM) >>
  qpat_x_assum `target_block_entry _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [target_block_entry_def]) >>
  gvs[events_OB_def, block_events_agree_def] >>
  first_x_assum (qspecl_then [`fn'.fn_name`, `k`, `k'`] mp_tac) >>
  simp[] >> disch_then (SUBST1_TAC o SYM) >>
  irule finite_prefix_run_next >> simp[]
QED

Finalise selected_prefix_simulation_induction

Theorem selected_prefix_simulation:
  decorated_run_prefix C fn s q n w qe es /\
  selected_simulation_contract C C' q0 path ES EB ER
    (events_OS C C' OS) (events_OB C C' OB) (events_OutR C C' OutR) /\
  selected_prefix_certificates C C' q0 path ES EB ER
    (events_OS C C' OS) (events_OB C C' OB) (events_OutR C C' OutR) /\
  selected_segment C q0 path n q w qe /\ ER q n fn s fn' t ==>
  finite_run_prefix C' fn' t es
Proof
  metis_tac[cj 2 selected_prefix_simulation_induction]
QED
