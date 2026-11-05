Theory frameRelocationPhi
Ancestors execEquivParamBase frameRelocationGuardedValues frameResolvedOrigins unitShapeDefs
  frameOriginUpdates frameRelocationLocal frameRelocationValues
  frameRelocationGhostCopy venomExecSemantics venomState ptrDiscipline finite_map list

Theorem resolved_op_erasure:
  op_prov (SND o_f rv) op = OPTION_MAP SND (resolved_op rv op)
Proof
  Cases_on `op` >> simp[op_prov_def, resolved_op_def, FLOOKUP_o_f] >>
  Cases_on `FLOOKUP rv s` >> simp[]
QED

Theorem resolved_set_erasure:
  set_prov (SND o_f rv) outs (OPTION_MAP SND p) =
    SND o_f (origin_set rv outs p)
Proof
  Cases_on `outs` >> Cases_on `p` >>
  simp[set_prov_def, origin_set_def, fmap_eq_flookup, FLOOKUP_o_f,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  Cases_on `t` >> simp[set_prov_def, origin_set_def, fmap_eq_flookup,
    FLOOKUP_o_f, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  gen_tac >> rpt IF_CASES_TAC >> simp[]
QED

Theorem resolved_phi_erasure:
  phi_prov prev (SND o_f rv) inst = OPTION_MAP SND (resolved_phi prev rv inst)
Proof
  Cases_on `prev` >> simp[phi_prov_def, resolved_phi_def] >>
  Cases_on `resolve_phi x inst.inst_operands` >> simp[resolved_op_erasure]
QED

Theorem resolved_phis_erasure:
  !insts. phis_prov prev (SND o_f rv) insts = SND o_f (resolved_phis prev rv insts)
Proof
  Induct >> simp[phis_prov_def, resolved_phis_def] >>
  Cases_on `h.inst_opcode = PHI` >>
  simp[resolved_phi_erasure, resolved_set_erasure]
QED

(* Selection reads the original state and maps; destinations are arbitrary. *)
Theorem guarded_selected_operand:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  s.vs_labels = t.vs_labels /\ eval_operand op s = SOME x /\
  (!w. op = Var w ==> (~Opaque v ==> ~Opaque w)) ==>
  ?y. eval_operand op t = SOME y /\
    guarded_ptr Opaque L (origin_set dst [v] (resolved_op rv op)) v x y /\
    guarded_bytes Opaque (origin_set dst [v] (resolved_op rv op))
      (dt with t_var := dt.t_var |+ (v,op_taint tn op)) v x y
Proof
  strip_tac >> Cases_on `op` >>
  gvs[eval_operand_def, resolved_op_def]
  >- (simp[guarded_ptr_def, guarded_bytes_def,
        copy_ptr_def, copy_bytes_def, origin_set_lookup, op_taint_def,
        FLOOKUP_UPDATE, word_agree_except_def])
  >- (drule local_rel_domains >> simp[variable_domains_def] >>
      disch_then (qspec_then `s'` mp_tac) >>
      Cases_on `lookup_var s' t` >> simp[] >>
      `guarded_ptr Opaque L rv s' x x' /\
       guarded_bytes Opaque rv tn s' x x'` by
        metis_tac[local_rel_pointer, local_rel_bytes] >>
      gvs[guarded_ptr_def, guarded_bytes_def, copy_ptr_def, copy_bytes_def,
          origin_set_lookup, op_taint_def, FLOOKUP_UPDATE]) >>
  simp[guarded_ptr_def, guarded_bytes_def, copy_ptr_def, copy_bytes_def,
       origin_set_lookup, op_taint_def, FLOOKUP_UPDATE,
       word_agree_except_def]
QED

Theorem guarded_phi_classification:
  MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
  MEM v inst.inst_outputs /\ resolve_phi lbl inst.inst_operands = SOME (Var w) ==>
  (~retpc_var fn v ==> ~retpc_var fn w)
Proof
  strip_tac >>
  `MEM (Var w) inst.inst_operands` by metis_tac[resolve_phi_MEM] >>
  simp[retpc_var_def] >> strip_tac >> strip_tac >>
  qpat_x_assum `~copy_phi_var _ _ _` mp_tac >> simp[] >>
  irule (cj 3 copy_phi_var_rules) >> goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `inst` >> simp[]
QED

Theorem guarded_parallel_phis:
  !insts s'.
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  s.vs_labels = t.vs_labels /\ s.vs_prev_bb = t.vs_prev_bb /\
  eval_phis s insts = OK s' /\
  (!a b v x y. Obs a b ==> Obs (update_var v x a) (update_var v y b)) /\
  (!inst v lbl w. MEM inst insts /\ inst.inst_opcode = PHI /\
    inst.inst_outputs = [v] /\ s.vs_prev_bb = SOME lbl /\
    resolve_phi lbl inst.inst_operands = SOME (Var w) ==>
    (~Opaque v ==> ~Opaque w)) ==>
  ?t'. eval_phis t insts = OK t' /\
    local_rel (\u. F) (guarded_ptr Opaque L (resolved_phis s.vs_prev_bb rv insts))
      (guarded_bytes Opaque (resolved_phis s.vs_prev_bb rv insts)
        (tn with t_var := phis_taint s.vs_prev_bb tn insts)) R Obs s' t'
Proof
  Induct >> simp[eval_phis_def, resolved_phis_def, phis_taint_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `h.inst_opcode = PHI`
  >- (gvs[] >> gvs[AllCaseEqs()] >>
      gvs[eval_one_phi_def, AllCaseEqs()] >>
      rename1 `eval_operand op s = SOME x` >>
      rename1 `h.inst_outputs = [v]` >>
      `?tt. eval_phis t insts = OK tt /\
        local_rel (\u. F) (guarded_ptr Opaque L (resolved_phis t.vs_prev_bb rv insts))
          (guarded_bytes Opaque (resolved_phis t.vs_prev_bb rv insts)
            (tn with t_var := phis_taint t.vs_prev_bb tn insts)) R Obs s'' tt` by
        (simp[] >> first_x_assum irule >> metis_tac[]) >>
      `?y. eval_operand op t = SOME y /\
        guarded_ptr Opaque L
          (origin_set (resolved_phis (SOME prev) rv insts) [v] (resolved_op rv op)) v x y /\
        guarded_bytes Opaque
          (origin_set (resolved_phis (SOME prev) rv insts) [v] (resolved_op rv op))
          ((tn with t_var := phis_taint (SOME prev) tn insts) with
            t_var := (phis_taint (SOME prev) tn insts) |+ (v,op_taint tn op)) v x y` by
        (simp[] >> irule (SRULE [] (Q.INST
           [`dt` |-> `tn with t_var := phis_taint (SOME prev) tn insts`]
           guarded_selected_operand)) >> conj_tac
         >- metis_tac[] >>
         qexistsl_tac [`Obs`, `R`, `s`] >> simp[]) >>
      qexists_tac `update_var v y tt` >>
      simp[resolved_phi_def, phi_taint_def, set_var_taint_def] >>
      irule local_rel_update_observation_invariant >>
      goal_assum (drule_at Any) >>
      simp[guarded_ptr_other, guarded_bytes_other] >>
      conj_tac >- gvs[] >>
      qexistsl_tac [`guarded_bytes Opaque (resolved_phis (SOME prev) rv insts)
        (tn with t_var := phis_taint (SOME prev) tn insts)`,
        `\u. F`, `guarded_ptr Opaque L (resolved_phis (SOME prev) rv insts)`] >>
      gvs[] >> rpt strip_tac >>
      gvs[guarded_bytes_def, copy_bytes_def, origin_set_lookup,
          op_taint_def, FLOOKUP_UPDATE]) >>
  gvs[]
QED

Theorem retpc_parallel_phis:
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R Obs s t /\
  s.vs_labels = t.vs_labels /\ s.vs_prev_bb = t.vs_prev_bb /\
  eval_phis s insts = OK s' /\
  (!a b v x y. Obs a b ==> Obs (update_var v x a) (update_var v y b)) /\
  EVERY (\inst. MEM inst (fn_insts fn)) insts ==>
  ?t'. eval_phis t insts = OK t' /\
    local_rel (\u. F) (guarded_ptr (retpc_var fn) L (resolved_phis s.vs_prev_bb rv insts))
      (guarded_bytes (retpc_var fn) (resolved_phis s.vs_prev_bb rv insts)
        (tn with t_var := phis_taint s.vs_prev_bb tn insts)) R Obs s' t'
Proof
  strip_tac >> irule guarded_parallel_phis >>
  goal_assum (drule_at Any) >> simp[] >>
  gvs[EVERY_MEM] >> metis_tac[guarded_phi_classification, MEM]
QED

(* Both values are selected before either destination is written. *)
Theorem eval_phis_swap[local]:
  first.inst_opcode = PHI /\ second.inst_opcode = PHI /\
  first.inst_outputs = [a] /\ second.inst_outputs = [b] /\
  s.vs_prev_bb = SOME lbl /\
  resolve_phi lbl first.inst_operands = SOME (Var b) /\
  resolve_phi lbl second.inst_operands = SOME (Var a) /\
  lookup_var a s = SOME x /\ lookup_var b s = SOME y ==>
  eval_phis s [first;second] = OK (update_var a y (update_var b x s))
Proof
  simp[eval_phis_def, eval_one_phi_def, eval_operand_def]
QED

Theorem guarded_parallel_swap[local]:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R Obs s t /\
  s.vs_labels = t.vs_labels /\ s.vs_prev_bb = t.vs_prev_bb /\
  first.inst_opcode = PHI /\ second.inst_opcode = PHI /\
  first.inst_outputs = [a] /\ second.inst_outputs = [b] /\
  s.vs_prev_bb = SOME lbl /\
  resolve_phi lbl first.inst_operands = SOME (Var b) /\
  resolve_phi lbl second.inst_operands = SOME (Var a) /\
  lookup_var a s = SOME x /\ lookup_var b s = SOME y /\
  (~Opaque a ==> ~Opaque b) /\ (~Opaque b ==> ~Opaque a) /\
  (!s t v x y. Obs s t ==> Obs (update_var v x s) (update_var v y t)) ==>
  ?t'. eval_phis t [first;second] = OK t' /\
    local_rel (\u. F)
      (guarded_ptr Opaque L (resolved_phis s.vs_prev_bb rv [first;second]))
      (guarded_bytes Opaque (resolved_phis s.vs_prev_bb rv [first;second])
        (tn with t_var := phis_taint s.vs_prev_bb tn [first;second])) R Obs
      (update_var a y (update_var b x s)) t'
Proof
  strip_tac >> irule guarded_parallel_phis >>
  goal_assum (drule_at Any) >> simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  conj_tac >- (irule eval_phis_swap >> simp[]) >> metis_tac[]
QED
