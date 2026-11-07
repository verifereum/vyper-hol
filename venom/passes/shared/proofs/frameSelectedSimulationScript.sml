Theory frameSelectedSimulation
Ancestors frameSelectedDecoration frameFiniteJointDecoration list arithmetic

(* Outcomes retain the exact source endpoints and absolute cursors. *)
Definition selected_step_match_def:
  selected_step_match C' OS q n (w:(origin_event option # joint_config) list) qe i s j t r <=>
    ?r'. finite_step C' j t r' /\
      OS q n qe (n+LENGTH w) i s j t r r'
End
Definition selected_block_match_def:
  selected_block_match C' OB q n (w:(origin_event option # joint_config) list) qe bb s bb' t r <=>
    ?r'. finite_block C' bb' t r' /\
      OB q n qe (n+LENGTH w) bb s bb' t r r'
End
Definition selected_run_match_def:
  selected_run_match C' OutR q n (w:(origin_event option # joint_config) list) qe fn s fn' t r <=>
    ?r'. finite_run C' fn' t r' /\
      OutR q n qe (n+LENGTH w) fn s fn' t r r'
End

Definition selected_base_certificate_def:
  selected_base_certificate C C' q0 path ES OS <=>
    !i s r fn q n j t.
      decoration_at fn i s q /\ i.inst_opcode <> INVOKE /\
      step_inst_base i s = r /\ (!e. r <> Error e) /\
      selected_segment C q0 path n q [] q /\ ES q n i s j t ==>
      selected_step_match C' OS q n [] q i s j t r
End

Definition selected_call_return_certificate_def:
  selected_call_return_certificate C C' q0 path ES ER OS OutR <=>
    !i s name ops fn args cs ret send post caller q n qc wc qe dc j t.
      decoration_at caller i s q /\ i.inst_opcode = INVOKE /\
      decode_invoke i = SOME (name,ops) /\
      lookup_function name C.ctx_functions = SOME fn /\
      eval_operands ops s = SOME args /\ setup_callee fn args s = SOME cs /\
      joint_transition C q NONE qc /\
      decorated_run C fn cs (IntRet ret send) qc (n+1) wc qe dc /\
      bind_outputs i.inst_outputs ret.iret_values
        (adopt_return_fmp ret (merge_callee_state s send)) = SOME post /\
      selected_segment C q0 path n q ((NONE,qc)::wc) qe /\ ES q n i s j t ==>
      ?fn' ct. ER qc (n+1) fn cs fn' ct /\
        (!rc'. finite_run C' fn' ct rc' /\
          OutR qc (n+1) qe (n+1+LENGTH wc) fn cs fn' ct (IntRet ret send) rc' ==>
          selected_step_match C' OS q n ((NONE,qc)::wc) qe i s j t (OK post))
End

Definition selected_call_exit_certificate_def:
  selected_call_exit_certificate C C' q0 path ES ER OS OutR <=>
    !i s name ops fn args cs r caller q n qc wc qe dc j t.
      decoration_at caller i s q /\ i.inst_opcode = INVOKE /\
      decode_invoke i = SOME (name,ops) /\
      lookup_function name C.ctx_functions = SOME fn /\
      eval_operands ops s = SOME args /\ setup_callee fn args s = SOME cs /\
      joint_transition C q NONE qc /\
      decorated_run C fn cs r qc (n+1) wc qe dc /\
      ((?post. r = Halt post) \/ (?a post. r = Abort a post)) /\
      selected_segment C q0 path n q ((NONE,qc)::wc) qe /\ ES q n i s j t ==>
      ?fn' ct. ER qc (n+1) fn cs fn' ct /\
        (!rc'. finite_run C' fn' ct rc' /\
          OutR qc (n+1) qe (n+1+LENGTH wc) fn cs fn' ct r rc' ==>
          selected_step_match C' OS q n ((NONE,qc)::wc) qe i s j t r)
End

Definition selected_term_certificate_def:
  selected_term_certificate C C' q0 path ES EB OS OB <=>
    !bb s i post fn q n w qe ds bb' t.
      decoration_at fn i s q /\ get_instruction bb s.vs_inst_idx = SOME i /\
      decorated_step C i s (OK post) q n w qe ds /\ is_terminator i.inst_opcode /\
      selected_segment C q0 path n q w qe /\ EB q n bb s bb' t ==>
      ?j. ES q n i s j t /\
        (!rs'. finite_step C' j t rs' /\
          OS q n qe (n+LENGTH w) i s j t (OK post) rs' ==>
          selected_block_match C' OB q n w qe bb s bb' t
            (if post.vs_halted then Halt post else OK post))
End

Definition selected_next_certificate_def:
  selected_next_certificate C C' q0 path ES EB OS OB <=>
    !bb s i post r fn q n ws qm ds ev qn wb qe db bb' t.
      decoration_at fn i s q /\ get_instruction bb s.vs_inst_idx = SOME i /\
      decorated_step C i s (OK post) q n ws qm ds /\
      ~is_terminator i.inst_opcode /\ decoration_consumes C i q post qm ev qn /\
      decoration_entry fn (post with vs_inst_idx := SUC s.vs_inst_idx) qn /\
      decorated_block C bb (post with vs_inst_idx := SUC s.vs_inst_idx)
        r qn (n+LENGTH ws+1) wb qe db /\
      selected_segment C q0 path n q (ws++[(ev,qn)]++wb) qe /\ EB q n bb s bb' t ==>
      ?j. ES q n i s j t /\
        (!rs'. finite_step C' j t rs' /\
          OS q n qm (n+LENGTH ws) i s j t (OK post) rs' ==>
          ?tb. EB qn (n+LENGTH ws+1) bb
            (post with vs_inst_idx := SUC s.vs_inst_idx) bb' tb /\
            (!rb'. finite_block C' bb' tb rb' /\
              OB qn (n+LENGTH ws+1) qe (n+LENGTH ws+1+LENGTH wb) bb
                (post with vs_inst_idx := SUC s.vs_inst_idx) bb' tb r rb' ==>
              selected_block_match C' OB q n (ws++[(ev,qn)]++wb) qe bb s bb' t r))
End

Definition selected_block_exit_certificate_def:
  selected_block_exit_certificate C C' q0 path ES EB OS OB <=>
    !bb s i r fn q n w qe ds bb' t.
      decoration_at fn i s q /\ get_instruction bb s.vs_inst_idx = SOME i /\
      decorated_step C i s r q n w qe ds /\ (!post. r <> OK post) /\
      selected_segment C q0 path n q w qe /\ EB q n bb s bb' t ==>
      ?j. ES q n i s j t /\
        (!rs'. finite_step C' j t rs' /\ OS q n qe (n+LENGTH w) i s j t r rs' ==>
          selected_block_match C' OB q n w qe bb s bb' t r)
End

Definition selected_run_next_certificate_def:
  selected_run_next_certificate C C' q0 path EB ER OB OutR <=>
    !fn s bb phi post r q n wb qm db fuel qn wr qe dr fn' t.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      eval_phis s bb.bb_instructions = OK phi /\
      decoration_entry fn (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) q /\
      decorated_block C bb (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
        (OK post) q n wb qm db /\ ~post.vs_halted /\ local_pending C qm (OK post) /\
      (?stk PG G tn i si oms om hs h.
        qm = JointConfig stk PG G tn fn i si oms om hs h /\
        active_inst fn i si /\ is_terminator i.inst_opcode) /\
      joint_transition C qm (SOME (OriginBlock fuel post)) qn /\
      decorated_run C fn post r qn (n+LENGTH wb+1) wr qe dr /\
      selected_segment C q0 path n q (wb++[(SOME (OriginBlock fuel post),qn)]++wr) qe /\
      ER q n fn s fn' t ==>
      ?bb' tb. EB q n bb (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) bb' tb /\
        (!rb'. finite_block C' bb' tb rb' /\
          OB q n qm (n+LENGTH wb) bb
            (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) bb' tb (OK post) rb' ==>
          ?tr. ER qn (n+LENGTH wb+1) fn post fn' tr /\
            (!rr'. finite_run C' fn' tr rr' /\
              OutR qn (n+LENGTH wb+1) qe (n+LENGTH wb+1+LENGTH wr) fn post fn' tr r rr' ==>
              selected_run_match C' OutR q n
                (wb++[(SOME (OriginBlock fuel post),qn)]++wr) qe fn s fn' t r))
End

Definition selected_run_halt_certificate_def:
  selected_run_halt_certificate C C' q0 path EB ER OB OutR <=>
    !fn s bb phi post q n w qe db fn' t.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      eval_phis s bb.bb_instructions = OK phi /\
      decoration_entry fn (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) q /\
      decorated_block C bb (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
        (OK post) q n w qe db /\ post.vs_halted /\
      selected_segment C q0 path n q w qe /\ ER q n fn s fn' t ==>
      ?bb' tb. EB q n bb (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) bb' tb /\
        (!rb'. finite_block C' bb' tb rb' /\
          OB q n qe (n+LENGTH w) bb
            (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) bb' tb (OK post) rb' ==>
          selected_run_match C' OutR q n w qe fn s fn' t (Halt post))
End

Definition selected_run_exit_certificate_def:
  selected_run_exit_certificate C C' q0 path EB ER OB OutR <=>
    !fn s bb phi r q n w qe db fn' t.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      eval_phis s bb.bb_instructions = OK phi /\
      decoration_entry fn (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) q /\
      decorated_block C bb (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
        r q n w qe db /\ (!post. r <> OK post) /\
      selected_segment C q0 path n q w qe /\ ER q n fn s fn' t ==>
      ?bb' tb. EB q n bb (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) bb' tb /\
        (!rb'. finite_block C' bb' tb rb' /\
          OB q n qe (n+LENGTH w) bb
            (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) bb' tb r rb' ==>
          selected_run_match C' OutR q n w qe fn s fn' t r)
End

Definition selected_simulation_contract_def:
  selected_simulation_contract C C' q0 path ES EB ER OS OB OutR <=>
    selected_base_certificate C C' q0 path ES OS /\
    selected_call_return_certificate C C' q0 path ES ER OS OutR /\
    selected_call_exit_certificate C C' q0 path ES ER OS OutR /\
    selected_term_certificate C C' q0 path ES EB OS OB /\
    selected_next_certificate C C' q0 path ES EB OS OB /\
    selected_block_exit_certificate C C' q0 path ES EB OS OB /\
    selected_run_next_certificate C C' q0 path EB ER OB OutR /\
    selected_run_halt_certificate C C' q0 path EB ER OB OutR /\
    selected_run_exit_certificate C C' q0 path EB ER OB OutR
End

Theorem selected_simulation_induction:
  (!C i s r q n w qe d. decorated_step C i s r q n w qe d ==>
    !C' q0 path ES EB ER OS OB OutR j t.
      selected_simulation_contract C C' q0 path ES EB ER OS OB OutR /\
      selected_segment C q0 path n q w qe /\ ES q n i s j t ==>
      selected_step_match C' OS q n w qe i s j t r) /\
  (!C bb s r q n w qe d. decorated_block C bb s r q n w qe d ==>
    !C' q0 path ES EB ER OS OB OutR bb' t.
      selected_simulation_contract C C' q0 path ES EB ER OS OB OutR /\
      selected_segment C q0 path n q w qe /\ EB q n bb s bb' t ==>
      selected_block_match C' OB q n w qe bb s bb' t r) /\
  (!C fn s r q n w qe d. decorated_run C fn s r q n w qe d ==>
    !C' q0 path ES EB ER OS OB OutR fn' t.
      selected_simulation_contract C C' q0 path ES EB ER OS OB OutR /\
      selected_segment C q0 path n q w qe /\ ER q n fn s fn' t ==>
      selected_run_match C' OutR q n w qe fn s fn' t r)
Proof
  ho_match_mp_tac decorated_step_strongind >> rpt conj_tac
  >- suspend "base"
  >- suspend "invoke_return"
  >- suspend "invoke_exit"
  >- suspend "block_term"
  >- suspend "block_next"
  >- suspend "block_exit"
  >- suspend "run_next"
  >- suspend "run_halt"
  >> suspend "run_exit"
QED

Resume selected_simulation_induction[base]:
  rpt strip_tac >> fs[selected_simulation_contract_def] >>
  qpat_x_assum `selected_base_certificate _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[selected_base_certificate_def] >>
  disch_then drule_all >> simp[]
QED
Resume selected_simulation_induction[invoke_return]:
  rpt strip_tac >>
  qpat_assum `selected_simulation_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[selected_simulation_contract_def] >> strip_tac >>
  qpat_x_assum `selected_call_return_certificate _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[selected_call_return_certificate_def] >>
  disch_then drule_all >> strip_tac >>
  `joint_segment C q' w qe` by metis_tac[cj 3 decorated_execution_segment] >>
  `selected_segment C q0 path (n+1) q' w qe` by
    (`selected_segment C q0 path n q [(NONE,q')] q' /\
      selected_segment C q0 path (n+LENGTH ([(NONE,q')]:(origin_event option # joint_config) list)) q' w qe` by
       (irule selected_segment_parts >> gvs[joint_segment_def]) >> fs[]) >>
  first_x_assum drule_all >>
  simp[selected_run_match_def] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED
Resume selected_simulation_induction[invoke_exit]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `selected_simulation_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[selected_simulation_contract_def] >> strip_tac >>
  qpat_x_assum `selected_call_exit_certificate _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[selected_call_exit_certificate_def] >>
  disch_then drule_all >> strip_tac >>
  `joint_segment C q' w qe` by metis_tac[cj 3 decorated_execution_segment] >>
  `selected_segment C q0 path (n+1) q' w qe` by
    (`selected_segment C q0 path n q [(NONE,q')] q' /\
      selected_segment C q0 path
        (n+LENGTH ([(NONE,q')]:(origin_event option # joint_config) list)) q' w qe` by
       (irule selected_segment_parts >> gvs[joint_segment_def]) >> fs[]) >>
  first_x_assum drule_all >>
  simp[selected_run_match_def] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED
Resume selected_simulation_induction[block_term]:
  rpt strip_tac >>
  qpat_assum `selected_simulation_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[selected_simulation_contract_def] >> strip_tac >>
  qpat_x_assum `selected_term_certificate _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[selected_term_certificate_def] >>
  disch_then drule_all >> strip_tac >>
  first_x_assum drule_all >> simp[selected_step_match_def] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED
Resume selected_simulation_induction[block_next]:
  rpt strip_tac >>
  qpat_assum `selected_simulation_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[selected_simulation_contract_def] >> strip_tac >>
  qpat_x_assum `selected_next_certificate _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[selected_next_certificate_def] >>
  disch_then drule_all >> strip_tac >>
  `joint_segment C q w qe` by metis_tac[cj 1 decorated_execution_segment] >>
  `joint_segment C q' w' qe'` by metis_tac[cj 2 decorated_execution_segment] >>
  `joint_transition C qe ev q'` by fs[decoration_consumes_def] >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  drule_all selected_segment_edge >> strip_tac >>
  qpat_x_assum `!C' q0 path ES EB ER OS OB OutR j t. _` drule_all >>
  simp[selected_step_match_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `!C' q0 path ES EB ER OS OB OutR bb' t. _` drule_all >>
  pure_rewrite_tac[selected_block_match_def] >> strip_tac >>
  first_x_assum drule_all >> simp[selected_block_match_def]
QED
Resume selected_simulation_induction[block_exit]:
  rpt strip_tac >>
  qpat_assum `selected_simulation_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[selected_simulation_contract_def] >> strip_tac >>
  qpat_x_assum `selected_block_exit_certificate _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[selected_block_exit_certificate_def] >>
  disch_then drule_all >> strip_tac >>
  first_x_assum drule_all >> pure_rewrite_tac[selected_step_match_def] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED
Resume selected_simulation_induction[run_next]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `selected_simulation_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[selected_simulation_contract_def] >> strip_tac >>
  qpat_x_assum `selected_run_next_certificate _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[selected_run_next_certificate_def] >>
  disch_then drule_all >> strip_tac >>
  `joint_segment C q w qe` by metis_tac[cj 2 decorated_execution_segment] >>
  `joint_segment C q' w' qe'` by metis_tac[cj 3 decorated_execution_segment] >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  drule_all selected_segment_edge >> strip_tac >>
  qpat_x_assum `!C' q0 path ES EB ER OS OB OutR bb' t. _` drule_all >>
  pure_rewrite_tac[selected_block_match_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `!C' q0 path ES EB ER OS OB OutR fn' t. _` drule_all >>
  pure_rewrite_tac[selected_run_match_def] >> strip_tac >>
  first_x_assum drule_all >> simp[selected_run_match_def]
QED
Resume selected_simulation_induction[run_halt]:
  rpt strip_tac >>
  qpat_assum `selected_simulation_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[selected_simulation_contract_def] >> strip_tac >>
  qpat_x_assum `selected_run_halt_certificate _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[selected_run_halt_certificate_def] >>
  disch_then drule_all >> strip_tac >>
  first_x_assum drule_all >> pure_rewrite_tac[selected_block_match_def] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED
Resume selected_simulation_induction[run_exit]:
  rpt strip_tac >>
  qpat_assum `selected_simulation_contract _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[selected_simulation_contract_def] >> strip_tac >>
  qpat_x_assum `selected_run_exit_certificate _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[selected_run_exit_certificate_def] >>
  disch_then drule_all >> strip_tac >>
  first_x_assum drule_all >> pure_rewrite_tac[selected_block_match_def] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED
Finalise selected_simulation_induction

Theorem selected_run_simulation:
  decorated_run C fn s r q n w qe d /\
  selected_simulation_contract C C' q0 path ES EB ER OS OB OutR /\
  selected_segment C q0 path n q w qe /\ ER q n fn s fn' t ==>
  selected_run_match C' OutR q n w qe fn s fn' t r
Proof
  metis_tac[cj 3 selected_simulation_induction]
QED

val _ = export_theory();
