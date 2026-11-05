Theory frameRelocationPhi
Ancestors execEquivParamBase frameRelocationGuardedValues frameResolvedOrigins unitShapeDefs
  frameOriginUpdates frameRelocationLocal frameRelocationValues
  frameRelocationGhostCopy venomState ptrDiscipline finite_map list

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
