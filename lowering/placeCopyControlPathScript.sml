Theory placeCopyControlPath
Ancestors
  fragGasMode fragGasPath gasCount venomExecSemantics venomInst venomState
  arithmetic list

Theorem place_copy_iterate_path:
  !(remaining:num) k s.
  (!j q. j <= n /\ Inv j q /\ ~q.vs_halted /\
          q.vs_current_bb = hdr /\ q.vs_inst_idx = 0 ==>
     ?r. gas_marked_path memory ctx func q 0 (OK r) /\ Inv j r /\
         ~r.vs_halted /\ r.vs_inst_idx = 0 /\
         r.vs_current_bb = (if j = n then exit else loop_body)) /\
  (!j q. j < n /\ Inv j q /\ ~q.vs_halted /\
          q.vs_current_bb = loop_body /\ q.vs_inst_idx = 0 ==>
     ?r. gas_marked_path memory ctx func q 0 (OK r) /\ Inv (j+1) r /\
         ~r.vs_halted /\ r.vs_current_bb = hdr /\ r.vs_inst_idx = 0) /\
  k + remaining = n /\ Inv k s /\ ~s.vs_halted /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?t. gas_marked_path memory ctx func s 0 (OK t) /\ Inv n t /\
      ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[] >>
      qpat_x_assum `!j q. j <= k /\ _ ==> _`
        (qspecl_then [`k`, `s`] mp_tac) >> simp[] >> metis_tac[]) >>
  `k < n` by decide_tac >>
  qpat_assum `!j q. j <= n /\ _ ==> _`
    (qspecl_then [`k`, `s`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `r.vs_current_bb = loop_body` by simp[] >>
  qpat_assum `!j q. j < n /\ _ ==> _`
    (qspecl_then [`k`, `r`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (qx_choose_then `u` strip_assume_tac) >>
  qpat_x_assum `!k s. _ /\ _ /\ k + remaining = n /\ _ ==> _`
    (qspecl_then [`k+1`, `u`] mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  qpat_x_assum `!j q. j <= n /\ _ ==> _` kall_tac >>
  qpat_x_assum `!j q. j < n /\ _ ==> _` kall_tac >>
  qpat_assum `gas_marked_path _ _ _ r 0 (OK u)`
    (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qpat_assum `gas_marked_path _ _ _ s 0 (OK r)`
    (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[]
QED

Theorem place_copy_jump_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label target] []) ==>
  gas_marked_path F ctx func s 0 (OK (jump_to target s))
Proof
  strip_tac >>
  `step_inst 0 ctx (mk_inst id JMP [Label target] []) s =
     OK (jump_to target s)` by
    simp[step_inst_non_invoke, mk_inst_def, step_inst_base_def] >>
  `gas_path_edge ctx func s 0 (OK (jump_to target s))` by
    (simp[gas_path_edge_def] >> qexists_tac `0` >>
     simp[gas_count_step_def, mk_inst_def, is_terminator_def] >>
     disj2_tac >> disj1_tac >> qexists_tac `target` >> simp[]) >>
  simp[gas_marked_path_def] >>
  drule (cj 2 gas_path_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[gas_path_rules, jump_to_def]
QED

Theorem place_copy_branch_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id JNZ [test; Label yes; Label no] []) /\
  eval_operand test s = SOME w ==>
  gas_marked_path F ctx func s 0
    (OK (jump_to (if w = 0w then no else yes) s))
Proof
  strip_tac >>
  `step_inst 0 ctx (mk_inst id JNZ [test; Label yes; Label no] []) s =
     OK (jump_to (if w = 0w then no else yes) s)` by
    (Cases_on `w = 0w` >>
     simp[step_inst_non_invoke, mk_inst_def, step_inst_base_def]) >>
  `gas_path_edge ctx func s 0
     (OK (jump_to (if w = 0w then no else yes) s))` by
    (simp[gas_path_edge_def] >> qexists_tac `0` >>
     simp[gas_count_step_def, mk_inst_def, is_terminator_def] >>
     disj2_tac >> disj1_tac >>
     qexists_tac `if w = 0w then no else yes` >> simp[]) >>
  simp[gas_marked_path_def] >>
  drule (cj 2 gas_path_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[gas_path_rules, jump_to_def]
QED
