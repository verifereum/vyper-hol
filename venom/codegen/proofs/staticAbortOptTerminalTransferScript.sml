Theory staticAbortOptTerminalTransfer
Ancestors
  staticAbortProtectedActualPrefix asmSymOwnCode asmSplice codegenSymRel
  asmSymBridge asmDataEnv finalizerContract asmSymSem asmSem asmWf

val names_conv = TOP_DEPTH_CONV (Unwind.UNWIND_FORALL_CONV ORELSEC BETA_CONV)

(* The matching concrete exception and symbolic termination use one count. *)
Theorem protected_terminal_legacy:
  !env. env = asm_data_env orig (assemble orig ++ data) ==>
  !run. run = (\r n. asm_steps (SND (compute_label_offsets r)) (build_offset_to_pc r)
                    r n (s with as_code := assemble r ++ data)) ==>
  s.as_pc = 0 /\ asm_static_wf orig /\ asm_static_wf p /\
  FILTER is_data_inst p = FILTER is_data_inst orig /\ asm_refines p q /\
  (run p n = AsmRevert out \/ run p n = AsmFault out) /\
  sym_terminal (sym_steps p env n (sym_init s)) ==>
  asm_static_wf q /\ FILTER is_data_inst q = FILTER is_data_inst orig /\
  ?m t. (run q m = AsmRevert t \/ run q m = AsmFault t) /\
        sym_terminal (sym_steps q env m (sym_init s)) /\
        t.as_requests = out.as_requests
Proof
  CONV_TAC names_conv >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `env = asm_data_env orig (assemble orig ++ data)` >>
  qabbrev_tac `start = s with as_code := assemble p ++ data` >>
  qabbrev_tac `dest = s with as_code := assemble q ++ data` >>
  `start.as_pc = 0 /\ dest.as_pc = 0 /\ sym_init start = sym_init s /\ sym_init dest = sym_init s` by
    simp[Abbr `start`, Abbr `dest`, sym_init_def] >>
  `asm_static_wf q /\ FILTER is_data_inst q = FILTER is_data_inst orig` by
    fs[asm_refines_def] >>
  `asm_data_env_ok p env start.as_code /\ asm_data_env_ok q env dest.as_code` by
    (simp[Abbr `start`, Abbr `dest`] >> conj_tac
     >- (`env = asm_data_env p (assemble p ++ data)` by
           (simp[Abbr `env`] >> irule asm_data_env_agree >> simp[]) >>
         simp[asm_data_env_ok_asm_data_env]) >>
     `env = asm_data_env q (assemble q ++ data)` by
       (simp[Abbr `env`] >> irule asm_data_env_agree >> simp[]) >>
     simp[asm_data_env_ok_asm_data_env]) >>
  `sym_run p env n (sym_init s) = sym_steps p env n (sym_init s)` by
    (drule_then (qspec_then `0` mp_tac) sym_steps_terminal_run >> simp[]) >>
  `label_disciplined env p start` by
    (irule sym_terminal_disciplined >> (metis_tac[])) >>
  `sym_terminal (asm_result_sym (asm_steps (SND (compute_label_offsets p))
     (build_offset_to_pc p) p n start))` by
    (qpat_assum `_ = AsmRevert out \/ _ = AsmFault out` DISJ_CASES_TAC >>
     simp[asm_result_sym_def,sym_terminal_def]) >>
  drule_all asm_sym_forward >> strip_tac >>
  `sym_run p env fuel (sym_init start) = sym_steps p env n (sym_init s)` by
    (qpat_assum `sym_result_rel _ (sym_run p env fuel _)`
       (strip_assume_tac o MATCH_MP sym_result_rel_terminal) >>
     drule_then (qspec_then `n` mp_tac) (GEN_ALL sym_run_terminal_steps) >>
     simp[] >> Cases_on `sym_steps p env n (sym_init s)` >> fs[sym_terminal_def]) >>
  suspend "refinement"
QED

Resume protected_terminal_legacy[refinement]:
  `?fuel'. sym_result_rel (sym_run p env n (sym_init s))
                       (sym_run q env fuel' (sym_init s))` by
    (qpat_assum `asm_refines p q` (mp_tac o REWRITE_RULE [asm_refines_def]) >>
     impl_tac >- simp[] >> disch_then (mp_tac o cj 3) >>
     disch_then (qspecl_then [`env`,`s`,`n`] mp_tac) >> simp[]) >>
  `sym_terminal (sym_run q env fuel' (sym_init dest))` by
    metis_tac[sym_result_rel_terminal] >>
  drule_all asm_sym_backward >> strip_tac >>
  rename1 `sym_result_rel (sym_run q env fuel' _) (asm_result_sym (asm_steps _ _ q m dest))` >>
  `!a. sym_steps q env m (sym_init dest) <> SymOK a` by
    (rpt strip_tac >>
     `asm_sym_rel q env dest (sym_init dest)` by (irule asm_sym_rel_init >> simp[]) >>
     drule_all asm_sym_steps_lockstep >> strip_tac >>
     qpat_assum `sym_result_rel (sym_run q env fuel' _) _`
       (mp_tac o cj 2 o MATCH_MP sym_result_rel_terminal) >>
     simp[asm_result_sym_def,sym_terminal_def]) >>
  `sym_run q env fuel' (sym_init dest) = sym_steps q env m (sym_init s)` by
    (qpat_assum `sym_terminal (sym_run q env fuel' (sym_init dest))`
       (mp_then Any (qspec_then `m` mp_tac) (GEN_ALL sym_run_terminal_steps)) >> simp[]) >>
  `sym_result_rel (asm_result_sym (asm_steps (SND (compute_label_offsets p))
     (build_offset_to_pc p) p n start))
     (asm_result_sym (asm_steps (SND (compute_label_offsets q))
        (build_offset_to_pc q) q m dest))` by
    metis_tac[sym_result_rel_trans] >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `m` >>
  `sym_terminal (sym_steps q env m (sym_init s))` by metis_tac[] >>
  qpat_assum `_ = AsmRevert out \/ _ = AsmFault out` DISJ_CASES_TAC >>
  Cases_on `asm_steps (SND (compute_label_offsets q)) (build_offset_to_pc q) q m dest` >>
  qpat_x_assum `sym_result_rel (asm_result_sym (asm_steps _ _ p n start)) _` mp_tac >>
  simp[asm_result_sym_def,sym_result_rel_def,sym_obs_def,sym_init_def,
       asm_state_component_equality] >> metis_tac[]
QED

Finalise protected_terminal_legacy

Theorem protected_terminal_mode:
  !env. env = asm_data_env orig (assemble orig ++ data) ==>
  !run. run = (\r n. asm_steps
    (if allow_own then lo_reloc r orig else SND (compute_label_offsets r))
    (build_offset_to_pc r) r n (if allow_own then s else (s with as_code := assemble r ++ data))) ==>
  s.as_pc = 0 /\ s.as_code = assemble orig ++ data /\ asm_static_wf orig /\ asm_static_wf p /\
  FILTER is_data_inst p = FILTER is_data_inst orig /\
  (if allow_own then asm_refines_own p q else asm_refines p q) /\
  (run p n = AsmRevert out \/ run p n = AsmFault out) /\
  sym_terminal (sym_steps_mode allow_own p env s.as_code n (sym_init s)) ==>
  asm_static_wf q /\ FILTER is_data_inst q = FILTER is_data_inst orig /\
  ?m t. (run q m = AsmRevert t \/ run q m = AsmFault t) /\
        sym_terminal (sym_steps_mode allow_own q env s.as_code m (sym_init s)) /\
        t.as_requests = out.as_requests
Proof
  CONV_TAC names_conv >> Cases_on `allow_own` >>
  PURE_REWRITE_TAC [sym_steps_mode_def, COND_CLAUSES] >>
  disch_then (map_every assume_tac o CONJUNCTS)
  >- (`asm_static_wf q /\ FILTER is_data_inst q = FILTER is_data_inst orig` by
        metis_tac[asm_refines_own_def] >>
      `sym_terminal (sym_steps_own p (asm_data_env orig s.as_code) s.as_code n (sym_init s))` by
        (qpat_assum `s.as_code = _` (fn eq =>
           qpat_assum `sym_terminal _` (ACCEPT_TAC o PURE_REWRITE_RULE [GSYM eq]))) >>
      mp_tac (Q.INST [`installed` |-> `orig`] installed_terminal_refinement) >>
      (impl_tac >- (rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >> metis_tac[])) >>
      qpat_assum `s.as_code = _` (pure_rewrite_tac o single o GSYM) >>
      disch_then (qx_choosel_then [`m`,`t`] (map_every assume_tac o CONJUNCTS)) >>
      conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl [`m`,`t`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  mp_tac (CONV_RULE names_conv protected_terminal_legacy) >>
  (impl_tac >- (rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]))) >>
  disch_then ACCEPT_TAC
QED
