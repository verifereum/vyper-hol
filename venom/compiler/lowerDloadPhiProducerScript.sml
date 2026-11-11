Theory lowerDloadPhiProducer
Ancestors
  lowerDloadVariableTransport lowerDloadOpaqueExecution lowerDloadMaskBounds
  lowerDloadOwnership lowerDloadPairedBoundary lowerDloadFrameCertificate
  lowerDloadAllocation lowerDloadRelocation ptrDiscipline venomExecProofs
  venomExecSemantics venomInst venomState finite_map list pred_set codegenRel

Theorem ld_phis_certificate_backward:
  s.vs_prev_bb = t.vs_prev_bb /\
  (!i. MEM i ins ==> MEM i (fn_insts fn)) /\
  (!i v. MEM i ins /\ MEM (Var v) i.inst_operands ==> v IN V) /\
  LENGTH AP = LENGTH s.vs_params /\ LENGTH BP = LENGTH t.vs_params /\
  LENGTH s.vs_params = LENGTH t.vs_params /\
  (!q. q < LENGTH s.vs_params ==>
    ld_owned_value E (EL q AP) (EL q BP) {} {}
      (EL q s.vs_params) (EL q t.vs_params)) /\
  ld_frame_embedding E L H s t /\
  LIST_REL (ld_owned_selection E) AP BP /\
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
  ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG BH tn un s t /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  ld_alloc_account keys d A s t /\ d = 32 * SUM (MAP CARD suspended) /\
  ld_frame_bound t.vs_alloca_next H BP BH /\
  ld_stack_bound t.vs_alloca_next gstk /\ lo <= t.vs_alloca_next /\
  (!owner bs sz. ld_live astk L AP AG (owner,(bs,sz)) ==>
    owner IN live /\ lo <= bs) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    lo <= bs /\ lo <= bt /\ bs+sz <= s.vs_alloca_next /\
    bt+sz <= t.vs_alloca_next) /\
  (!owner other bs bt sz cs ct cz.
    owner IN live /\ other IN live /\ owner <> other /\
    ld_site_entry E owner bs bt sz /\ ld_site_entry E other cs ct cz ==>
    (bs+sz <= cs \/ cs+cz <= bs) /\ (bt+sz <= ct \/ ct+cz <= bt)) /\
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    tn.t_mem un.t_mem (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  (!v. op_taint tn (Var v) SUBSET count 32) /\
  (!v. op_taint un (Var v) SUBSET count 32) /\
  un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans /\
  un.t_imm SUBSET tn.t_imm /\
  eval_phis t ins = OK t' ==>
  ?s'. eval_phis s ins = OK s' /\
    ld_frame_embedding E L H s' t' /\
    LIST_REL (ld_owned_selection E) AP BP /\
    (!v. ld_owned_selection E (FLOOKUP (ld_phis_prov s.vs_prev_bb AG ins) v)
      (FLOOKUP (ld_phis_prov t.vs_prev_bb BH ins) v)) /\
    ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
      (ld_phis_prov s.vs_prev_bb AG ins) (ld_phis_prov t.vs_prev_bb BH ins)
      (tn with t_var := phis_taint s.vs_prev_bb tn ins)
      (un with t_var := phis_taint t.vs_prev_bb un ins) s' t' /\
    (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    ld_alloc_account keys d A s' t' /\ d = 32 * SUM (MAP CARD suspended) /\
    ld_frame_bound t'.vs_alloca_next H BP (ld_phis_prov t.vs_prev_bb BH ins) /\
    ld_stack_bound t'.vs_alloca_next gstk /\ lo <= t'.vs_alloca_next /\
    (!owner bs sz. ld_live astk L AP (ld_phis_prov s.vs_prev_bb AG ins) (owner,(bs,sz)) ==>
      owner IN live /\ lo <= bs) /\
    (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
      lo <= bs /\ lo <= bt /\ bs+sz <= s'.vs_alloca_next /\
      bt+sz <= t'.vs_alloca_next) /\
    (!owner other bs bt sz cs ct cz.
      owner IN live /\ other IN live /\ owner <> other /\
      ld_site_entry E owner bs bt sz /\ ld_site_entry E other cs ct cz ==>
      (bs+sz <= cs \/ cs+cz <= bs) /\ (bt+sz <= ct \/ ct+cz <= bt)) /\
    ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
      (tn with t_var := phis_taint s.vs_prev_bb tn ins).t_mem
      (un with t_var := phis_taint t.vs_prev_bb un ins).t_mem
      (\a. read_memory a 1 s') (\b. read_memory b 1 t') /\
    (!v. op_taint (tn with t_var := phis_taint s.vs_prev_bb tn ins) (Var v) SUBSET count 32) /\
    (!v. op_taint (un with t_var := phis_taint t.vs_prev_bb un ins) (Var v) SUBSET count 32) /\
    (un with t_var := phis_taint t.vs_prev_bb un ins).t_stor SUBSET
      (tn with t_var := phis_taint s.vs_prev_bb tn ins).t_stor /\
    (un with t_var := phis_taint t.vs_prev_bb un ins).t_trans SUBSET
      (tn with t_var := phis_taint s.vs_prev_bb tn ins).t_trans /\
    (un with t_var := phis_taint t.vs_prev_bb un ins).t_imm SUBSET
      (tn with t_var := phis_taint s.vs_prev_bb tn ins).t_imm /\
    LENGTH AP = LENGTH s'.vs_params /\ LENGTH BP = LENGTH t'.vs_params /\
    LENGTH s'.vs_params = LENGTH t'.vs_params /\
    (!q. q < LENGTH s'.vs_params ==>
      ld_owned_value E (EL q AP) (EL q BP) {} {}
        (EL q s'.vs_params) (EL q t'.vs_params)) /\
    (s' with vs_vars := s.vs_vars) = s /\
    (t' with vs_vars := t.vs_vars) = t
Proof
  strip_tac >>
  `?s'. eval_phis s ins = OK s' /\
    ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
      (ld_phis_prov s.vs_prev_bb AG ins) (ld_phis_prov t.vs_prev_bb BH ins)
      (tn with t_var := phis_taint s.vs_prev_bb tn ins)
      (un with t_var := phis_taint t.vs_prev_bb un ins) s' t' /\
    (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE))` by
    (irule ld_nonopaque_phis_backward >> rpt conj_tac >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `s'` >>
  `!v. ld_owned_selection E (FLOOKUP (ld_phis_prov s.vs_prev_bb AG ins) v)
      (FLOOKUP (ld_phis_prov t.vs_prev_bb BH ins) v)` by
    (simp[] >> irule ld_owned_phis_selection >> simp[]) >>
  `ld_frame_bound t.vs_alloca_next H BP (ld_phis_prov t.vs_prev_bb BH ins)` by
    (irule ld_frame_bound_phis >> simp[]) >>
  `!owner bs sz. ld_live astk L AP (ld_phis_prov s.vs_prev_bb AG ins) (owner,(bs,sz)) ==>
      owner IN live /\ lo <= bs` by metis_tac[ld_live_phis] >>
  `(!v. op_taint (tn with t_var := phis_taint s.vs_prev_bb tn ins) (Var v) SUBSET count 32) /\
   (!v. op_taint (un with t_var := phis_taint t.vs_prev_bb un ins) (Var v) SUBSET count 32)` by
    (conj_tac >> rewrite_tac[ld_var_taint_bound_iff] >>
     simp[] >> metis_tac[ld_phis_taint_bound]) >>
  `s' with vs_vars := s.vs_vars = s` by
    (qpat_assum `eval_phis s ins = OK s'` (mp_tac o MATCH_MP eval_phis_only_updates_vs_vars) >>
     disch_then SUBST1_TAC >> simp[]) >>
  `t' with vs_vars := t.vs_vars = t` by
    (qpat_assum `eval_phis t ins = OK t'` (mp_tac o MATCH_MP eval_phis_only_updates_vs_vars) >>
     disch_then SUBST1_TAC >> simp[]) >>
  `ld_frame_embedding E L H s' t'` by metis_tac[ld_frame_embedding_vars_transport] >>
  `ld_alloc_account keys d A s' t'` by metis_tac[ld_alloc_account_vars_transport] >>
  `ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    tn.t_mem un.t_mem (\a. read_memory a 1 s') (\b. read_memory b 1 t')` by
    metis_tac[ld_byte_rel_vars_transport] >>
  dxrule ld_vars_restore_normalize >> disch_then SUBST_ALL_TAC >>
  dxrule ld_vars_restore_normalize >> disch_then SUBST_ALL_TAC >>
  simp[] >> rpt conj_tac >> fs[] >> metis_tac[]
QED
