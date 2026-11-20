(* Actual-code concretization of a successful protected symbolic prefix. *)
Theory staticAbortProtectedActualPrefix
Ancestors
  asmSymOwnCode asmWf finalizerContract staticAbortOptMergeJumpdestsLayout
  asmDataEnv codegenSymRel asmSymSem asmSymBridge list asmSem
  asmSymForwardOwn asmRelocDataEnv asmSymModeOwn fnPlanPlaceRevertPostamble asmSpliceOwn

Theorem stopped_symbolic_prefix_actual_code:
  s.as_pc = 0 /\ asm_static_wf p /\ asm_static_wf q /\
  FILTER is_data_inst q = FILTER is_data_inst p /\
  s.as_code = assemble p ++ data /\
  sym_steps q (asm_data_env p (assemble p ++ data)) n (sym_init s) = SymOK ss
  ==> ?t.
    asm_steps (SND (compute_label_offsets q)) (build_offset_to_pc q) q n
      (s with as_code := assemble q ++ data) = AsmOK t /\
    asm_sym_rel q (asm_data_env q (assemble q ++ data)) t ss /\
    t.as_pc = ss.sym_base.as_pc /\ LENGTH t.as_stack = LENGTH ss.sym_stack /\
    t.as_call_ctx = ss.sym_base.as_call_ctx /\
    t.as_requests = ss.sym_base.as_requests
Proof
  strip_tac >>
  `asm_data_env p (assemble p ++ data) =
   asm_data_env q (assemble q ++ data)` by
    (irule asm_data_env_agree >> simp[]) >>
  `sym_init (s with as_code := assemble q ++ data) = sym_init s` by
    simp[sym_init_def] >>
  `asm_sym_rel q (asm_data_env q (assemble q ++ data))
     (s with as_code := assemble q ++ data) (sym_init s)` by
    (pop_assum (fn th => rewrite_tac[GSYM th]) >>
     irule asm_sym_rel_init >> simp[asm_data_env_ok_asm_data_env]) >>
  gvs[] >> drule_all asm_sym_steps_lockstep >> strip_tac >>
  qexists_tac `cs'` >> simp[] >>
  `cs'.as_pc = ss.sym_base.as_pc /\
   LENGTH cs'.as_stack = LENGTH ss.sym_stack /\
   cs'.as_call_ctx = ss.sym_base.as_call_ctx /\
   cs'.as_requests = ss.sym_base.as_requests` by
    (gvs[asm_sym_rel_def] >>
     imp_res_tac LIST_REL_LENGTH >> gvs[]) >>
  simp[]
QED

(* The concrete prefix uses the current program's code labels and the
   installed program's data offsets. All own-code reads use s.as_code. *)
Theorem stopped_symbolic_prefix_installed_code:
  s.as_pc = 0 /\ asm_static_wf p /\ asm_static_wf installed /\
  FILTER is_data_inst installed = FILTER is_data_inst p /\
  sym_steps_own p (asm_data_env installed s.as_code) s.as_code n (sym_init s) =
    SymOK ss ==>
  ?t. asm_steps (lo_reloc p installed) (build_offset_to_pc p) p n s = AsmOK t /\
      asm_sym_rel_own (lo_reloc p installed) p
        (asm_data_env installed s.as_code) s.as_code t ss /\
      t.as_pc = ss.sym_base.as_pc /\ LENGTH t.as_stack = LENGTH ss.sym_stack /\
      t.as_call_ctx = ss.sym_base.as_call_ctx /\
      t.as_requests = ss.sym_base.as_requests
Proof
  strip_tac >>
  `asm_sym_rel_own (lo_reloc p installed) p (asm_data_env installed s.as_code)
     s.as_code s (sym_init s)` by
    (irule asm_sym_rel_own_init >> simp[] >>
     drule_all lo_reloc_data_env >> simp[]) >>
  `code_labels_agree p (lo_reloc p installed)` by
    simp[lo_reloc_code_labels_agree] >>
  drule_all (Q.INST [`allow_own` |-> `T`] asm_sym_steps_mode_sim
             |> PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES]) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  fs[asm_sym_rel_own_def] >> imp_res_tac LIST_REL_LENGTH >> gvs[]
QED

(* Terminal symbolic prefixes admit concrete observation at the same fuel. *)
Theorem installed_symbolic_terminal:
  asm_static_wf p /\ code_labels_agree p lo ==>
  !n cs ss.
    asm_sym_rel_own lo p env own cs ss /\
    sym_terminal (sym_steps_own p env own n ss) ==>
    sym_result_rel (sym_steps_own p env own n ss)
      (asm_result_sym (asm_steps lo (build_offset_to_pc p) p n cs))
Proof
  strip_tac >> Induct >- simp[sym_steps_own_def, sym_terminal_def] >>
  rpt gen_tac >> strip_tac >>
  drule asm_sym_rel_own_pc >> strip_tac >>
  Cases_on `cs.as_pc < LENGTH p` >> fs[sym_steps_own_def, sym_terminal_def] >>
  `MEM (EL cs.as_pc p) p` by simp[EL_MEM] >>
  drule_all (Q.INST [`allow_own` |-> `T`] asm_sym_inst_step_mode
             |> PURE_REWRITE_RULE [COND_CLAUSES]) >>
  Cases_on `sym_step_own p env own (EL cs.as_pc p) ss` >>
  simp[asm_steps_def, sym_steps_own_def] >> fs[sym_terminal_def] >>
  FIRST [disch_then (qx_choose_then `cs1` strip_assume_tac) >>
         simp[] >> first_x_assum irule >> simp[],
         strip_tac >> simp[asm_result_sym_def, sym_result_rel_def]]
QED

Theorem own_terminal_run_steps[local]:
  !fuel ss. sym_terminal (sym_run_own p env own fuel ss) ==>
    sym_steps_own p env own fuel ss = sym_run_own p env own fuel ss
Proof
  Induct >- simp[Once sym_run_own_def, sym_terminal_def] >>
  rpt gen_tac >> ONCE_REWRITE_TAC [sym_run_own_def, sym_steps_own_def] >>
  Cases_on `ss.sym_base.as_pc >= LENGTH p` >> simp[sym_terminal_def] >>
  BasicProvers.CASE_TAC >> simp[sym_terminal_def]
QED

Theorem terminal_result_rel_sym[local]:
  sym_result_rel a b ==> sym_result_rel b a
Proof
  Cases_on `a` >> Cases_on `b` >> simp[sym_result_rel_def] >> metis_tac[]
QED

Theorem concrete_result_rel_abort[local]:
  sym_result_rel (asm_result_sym a) (asm_result_sym b) /\
  (a = AsmRevert out \/ a = AsmFault out) ==>
  ?u. (b = AsmRevert u \/ b = AsmFault u) /\ u.as_requests = out.as_requests
Proof
  strip_tac >> gvs[] >> Cases_on `b` >>
  fs[asm_result_sym_def, sym_result_rel_def] >>
  qpat_x_assum `sym_obs _ = sym_obs _`
    (mp_tac o AP_TERM ``asm_state_as_requests``) >>
  simp[sym_obs_def, sym_init_def]
QED

(* A genuinely terminal prefix uses the finalizer's ordinary own-code
   refinement. The mixed row certificate is needed only for a pending cut. *)
Theorem installed_terminal_refinement:
  asm_refines_own p q /\ asm_static_wf p /\ asm_static_wf installed /\
  FILTER is_data_inst installed = FILTER is_data_inst p /\ s.as_pc = 0 /\
  (asm_steps (lo_reloc p installed) (build_offset_to_pc p) p n s = AsmRevert out \/
   asm_steps (lo_reloc p installed) (build_offset_to_pc p) p n s = AsmFault out) /\
  sym_terminal (sym_steps_own p (asm_data_env installed s.as_code) s.as_code n (sym_init s))
  ==>
  ?m u.
    (asm_steps (lo_reloc q installed) (build_offset_to_pc q) q m s = AsmRevert u \/
     asm_steps (lo_reloc q installed) (build_offset_to_pc q) q m s = AsmFault u) /\
    sym_terminal (sym_steps_own q (asm_data_env installed s.as_code) s.as_code m (sym_init s)) /\
    u.as_requests = out.as_requests
Proof
  strip_tac >>
  qabbrev_tac `env = asm_data_env installed s.as_code` >>
  `asm_static_wf q /\ FILTER is_data_inst installed = FILTER is_data_inst q` by
    metis_tac[asm_refines_own_def] >>
  `!g. asm_static_wf g /\ FILTER is_data_inst installed = FILTER is_data_inst g ==>
       asm_sym_rel_own (lo_reloc g installed) g env s.as_code s (sym_init s)` by
    (rpt strip_tac >> irule asm_sym_rel_own_init >> simp[] >>
     simp[Abbr `env`] >> metis_tac[lo_reloc_data_env]) >>
  `sym_run_own p env s.as_code n (sym_init s) =
      sym_steps_own p env s.as_code n (sym_init s)` by
    (drule (Q.INST [`allow_own` |-> `T`] sym_steps_mode_terminal_run
               |> PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES]) >>
     disch_then (qspec_then `0` mp_tac) >> simp[]) >>
  `sym_terminal (sym_run_own p env s.as_code n (sym_init s))` by
    (qpat_assum `sym_run_own _ _ _ _ _ = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `asm_refines_own p q`
    (fn refinement => qpat_assum `asm_static_wf p`
      (mp_tac o SPECL [``env:string |-> byte list``, ``s.as_code``, ``s:asm_state``, ``n:num``]
       o cj 3 o MATCH_MP (REWRITE_RULE [asm_refines_own_def] refinement))) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `m` assume_tac) >>
  `sym_terminal (sym_run_own q env s.as_code m (sym_init s))`
    by metis_tac[sym_result_rel_terminal] >>
  `sym_steps_own q env s.as_code m (sym_init s) =
   sym_run_own q env s.as_code m (sym_init s)` by
    (irule own_terminal_run_steps >> first_assum ACCEPT_TAC) >>
  `sym_terminal (sym_steps_own q env s.as_code m (sym_init s))` by simp[] >>
  `!g k. asm_static_wf g /\ FILTER is_data_inst installed = FILTER is_data_inst g /\
     sym_terminal (sym_steps_own g env s.as_code k (sym_init s)) ==>
     sym_result_rel (sym_steps_own g env s.as_code k (sym_init s))
       (asm_result_sym (asm_steps (lo_reloc g installed) (build_offset_to_pc g) g k s))`
    by (rpt strip_tac >> irule installed_symbolic_terminal >>
        simp[lo_reloc_code_labels_agree]) >>
  `sym_result_rel
     (asm_result_sym (asm_steps (lo_reloc p installed) (build_offset_to_pc p) p n s))
     (sym_run_own p env s.as_code n (sym_init s))` by
    (irule terminal_result_rel_sym >>
     qpat_assum `sym_run_own p env s.as_code n (sym_init s) = _` SUBST1_TAC >>
     qpat_assum `!g k. _ ==> sym_result_rel _ _` (qspecl_then [`p`,`n`] irule) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `sym_result_rel (sym_run_own q env s.as_code m (sym_init s))
     (asm_result_sym (asm_steps (lo_reloc q installed) (build_offset_to_pc q) q m s))` by
    (qpat_assum `sym_steps_own q env s.as_code m (sym_init s) = _`
       (once_rewrite_tac o single o GSYM) >>
     qpat_assum `!g k. _ ==> sym_result_rel _ _` (qspecl_then [`q`,`m`] irule) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `m` >>
  `sym_result_rel
     (asm_result_sym (asm_steps (lo_reloc p installed) (build_offset_to_pc p) p n s))
     (asm_result_sym (asm_steps (lo_reloc q installed) (build_offset_to_pc q) q m s))` by
    metis_tac[sym_result_rel_trans] >>
  drule concrete_result_rel_abort >> simp[]
QED

Theorem stopped_symbolic_prefix_mode:
  s.as_pc = 0 /\ asm_static_wf p /\ asm_static_wf q /\
  FILTER is_data_inst q = FILTER is_data_inst p /\ s.as_code = assemble p ++ data /\
  sym_steps_mode allow_own q (asm_data_env p (assemble p ++ data)) s.as_code n (sym_init s) =
    SymOK ss ==>
  ?t. asm_steps (if allow_own then lo_reloc q p else SND (compute_label_offsets q))
        (build_offset_to_pc q) q n (if allow_own then s else (s with as_code := assemble q ++ data)) =
        AsmOK t /\
      (if allow_own then asm_sym_rel_own (lo_reloc q p) q (asm_data_env p s.as_code) s.as_code
       else asm_sym_rel q (asm_data_env q (assemble q ++ data))) t ss /\
      t.as_pc = ss.sym_base.as_pc /\ LENGTH t.as_stack = LENGTH ss.sym_stack /\
      t.as_call_ctx = ss.sym_base.as_call_ctx /\ t.as_requests = ss.sym_base.as_requests
Proof
  Cases_on `allow_own` >> PURE_REWRITE_TAC [sym_steps_mode_def, COND_CLAUSES]
  >- (strip_tac >>
      `sym_steps_own q (asm_data_env p s.as_code) s.as_code n (sym_init s) = SymOK ss` by
        (qpat_assum `s.as_code = _` (fn eq =>
           qpat_assum `sym_steps_own q _ _ n _ = _`
             (ACCEPT_TAC o PURE_REWRITE_RULE [GSYM eq]))) >>
      mp_tac (Q.INST [`p` |-> `q`, `installed` |-> `p`] stopped_symbolic_prefix_installed_code) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC ORELSE metis_tac[])) >>
      disch_then ACCEPT_TAC) >>
  MATCH_ACCEPT_TAC stopped_symbolic_prefix_actual_code
QED

Theorem protected_cut_relation_pc:
  (if allow_own then asm_sym_rel_own lo p env own else asm_sym_rel p plain_env) cs ss ==>
  ss.sym_base.as_pc = cs.as_pc /\ LENGTH ss.sym_stack = LENGTH cs.as_stack
Proof
  Cases_on `allow_own` >> PURE_REWRITE_TAC [COND_CLAUSES]
  >- (strip_tac >> drule asm_sym_rel_own_pc >> simp[] >>
      fs[asm_sym_rel_own_def] >> metis_tac[LIST_REL_LENGTH]) >>
  MATCH_ACCEPT_TAC asm_sym_rel_pc
QED

Theorem protected_cut_relation_context:
  (if allow_own then asm_sym_rel_own lo p env own else asm_sym_rel p plain_env) cs ss ==>
  ss.sym_base.as_call_ctx = cs.as_call_ctx /\ ss.sym_base.as_requests = cs.as_requests
Proof
  Cases_on `allow_own` >>
  simp[asm_sym_rel_def, asm_sym_rel_own_def] >>
  strip_tac >> first_x_assum (fn th => REWRITE_TAC [th]) >> simp[]
QED

Theorem protected_cut_relation_slots:
  (if allow_own then asm_sym_rel_own (lo_reloc p installed) p env own else asm_sym_rel p plain_env) cs ss ==>
  !k. k < LENGTH ss.sym_stack ==>
    (!w. EL k ss.sym_stack = Val w ==> EL k cs.as_stack = w) /\
    (!l off dest. (allow_own ==> asm_static_wf p) /\ EL k ss.sym_stack = Lab l 0 /\
        FLOOKUP (SND (compute_label_offsets p)) l = SOME off /\
        FLOOKUP (build_offset_to_pc p) off = SOME dest ==>
      EL k cs.as_stack = n2w off)
Proof
  Cases_on `allow_own` >>
  PURE_REWRITE_TAC [COND_CLAUSES, asm_sym_rel_own_def, asm_sym_rel_def] >>
  strip_tac >> gen_tac >> disch_tac >>
  qpat_assum `LIST_REL _ ss.sym_stack cs.as_stack`
    (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >> strip_tac >>
  first_x_assum (qspec_then `k` (drule_then (mk_asm "slot"))) >>
  conj_tac
  >- (rpt strip_tac >> asm_x "slot" mp_tac >> simp[sval_conc_def]) >>
  rpt gen_tac >> strip_tac >>
  TRY (`FLOOKUP (lo_reloc p installed) l = SOME off` by
       (irule canonical_jump_binding_relocated >> metis_tac[])) >>
  asm_x "slot" mp_tac >> simp[sval_conc_def]
QED
