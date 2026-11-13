Theory concretizePtrOwnershipErasure
Ancestors
  concretizePtrPrefixLedger ptrDiscipline finite_map list

Definition ptr_owner_project_def:
  ptr_owner_project (births : (num # num,num # num) fmap) p =
    case p of NONE => NONE | SOME owner => FLOOKUP births owner
End

Definition ptr_params_erases_def:
  ptr_params_erases dyn births tagged numerical <=>
    LIST_REL (ptr_owner_erases dyn births) tagged numerical /\
    EVERY (\p. case p of NONE => T | SOME owner => owner IN FDOM births) tagged
End

Theorem ptr_owner_erases_project:
  (!owner. p = SOME owner ==> owner IN FDOM births) ==>
  ptr_owner_erases dyn births p (ptr_owner_project births p)
Proof
  Cases_on `p` >> simp[ptr_owner_erases_def, ptr_owner_project_def]
QED

Theorem ptr_owner_erases_tagged[local]:
  ptr_owner_erases dyn births (SOME owner) n /\ owner IN FDOM births ==>
  ?site. n = SOME site
Proof
  simp[ptr_owner_erases_def, FLOOKUP_DEF]
QED

Theorem ptr_owner_op_projection:
  ptr_ledger_erases dyn births tagged numerical ==>
  ptr_owner_erases dyn births (op_prov tagged op) (op_prov numerical op) /\
  (!owner. op_prov tagged op = SOME owner ==> owner IN FDOM births)
Proof
  Cases_on `op` >> rw[op_prov_def, ptr_ledger_erases_def] >>
  gvs[ptr_owner_erases_def] >> metis_tac[]
QED

Theorem ptr_owner_op_untagged[local]:
  ptr_ledger_erases dyn births tagged numerical /\ op_prov numerical op = NONE ==>
  op_prov tagged op = NONE
Proof
  strip_tac >> drule ptr_owner_op_projection >>
  disch_then (qspec_then `op` strip_assume_tac) >>
  Cases_on `op_prov tagged op` >> simp[] >>
  metis_tac[ptr_owner_erases_tagged, optionTheory.NOT_NONE_SOME]
QED

Theorem ptr_first_prov_untagged[local]:
  !ops. EVERY (\op. op_prov G op = NONE) ops ==> first_prov G ops = NONE
Proof
  Induct >> simp[first_prov_def]
QED

(* An operand with a site and a tagged operand are the same variable, as
   affine_pointer_ops gives for ADD/SUB: otherwise an untagged dynamic
   operand ahead of a tagged one would make the two first_prov choices
   differ. *)
Theorem ptr_owner_first_projection:
  !ops. ptr_ledger_erases dyn births tagged numerical /\
    (!u1 u2. MEM (Var u1) ops /\ MEM (Var u2) ops /\
       FLOOKUP numerical u1 <> NONE /\ FLOOKUP tagged u2 <> NONE ==> u1 = u2) ==>
    ptr_owner_erases dyn births (first_prov tagged ops) (first_prov numerical ops) /\
    (!owner. first_prov tagged ops = SOME owner ==> owner IN FDOM births)
Proof
  Induct >- simp[first_prov_def, ptr_owner_erases_def] >>
  rpt gen_tac >> strip_tac >>
  drule ptr_owner_op_projection >> disch_then (qspec_then `h` strip_assume_tac) >>
  Cases_on `op_prov numerical h`
  >- (`op_prov tagged h = NONE` by metis_tac[ptr_owner_op_untagged] >>
      simp[first_prov_def] >> first_x_assum irule >> metis_tac[]) >>
  Cases_on `op_prov tagged h` >> gvs[first_prov_def] >>
  `?u. h = Var u` by (Cases_on `h` >> gvs[op_prov_def]) >>
  gvs[op_prov_def] >>
  `EVERY (\op. op_prov tagged op = NONE) ops` by
    (simp[EVERY_MEM] >> Cases >> simp[op_prov_def] >> strip_tac >>
     spose_not_then assume_tac >>
     `u = s` by (first_x_assum irule >> simp[]) >> gvs[]) >>
  `first_prov tagged ops = NONE` by metis_tac[ptr_first_prov_untagged] >>
  simp[]
QED

Theorem ptr_owner_set_projection:
  ptr_ledger_erases dyn births tagged numerical /\
  ptr_owner_erases dyn births p n /\
  (!owner. p = SOME owner ==> owner IN FDOM births) ==>
  ptr_ledger_erases dyn births (set_prov tagged outs p) (set_prov numerical outs n)
Proof
  strip_tac >>
  `!v. ~MEM v outs ==>
     FLOOKUP (set_prov tagged outs p) v = FLOOKUP tagged v /\
     FLOOKUP (set_prov numerical outs n) v = FLOOKUP numerical v` by
    (rpt strip_tac >> simp[set_prov_def] >>
     Cases_on `outs` >> Cases_on `p` >> Cases_on `n` >>
     TRY (Cases_on `t`) >> gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  `!v. MEM v outs ==>
     ptr_owner_erases dyn births (FLOOKUP (set_prov tagged outs p) v)
       (FLOOKUP (set_prov numerical outs n) v) /\
     (!owner. FLOOKUP (set_prov tagged outs p) v = SOME owner ==>
        owner IN FDOM births)` by
    (rpt gen_tac >> strip_tac >>
     Cases_on `p` >> Cases_on `n` >> Cases_on `outs` >> gvs[] >>
     TRY (Cases_on `t`) >>
     gvs[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, ptr_owner_erases_def] >>
     metis_tac[ptr_owner_erases_tagged, optionTheory.NOT_NONE_SOME]) >>
  gvs[ptr_ledger_erases_def] >> rpt strip_tac >>
  Cases_on `MEM v outs` >> metis_tac[]
QED

Theorem ptr_owner_call_params:
  ptr_ledger_erases dyn births tagged numerical ==>
  ptr_params_erases dyn births (MAP (op_prov tagged) ops) (MAP (op_prov numerical) ops)
Proof
  strip_tac >>
  simp[ptr_params_erases_def, EVERY_MAP, EVERY_MEM, LIST_REL_MAP1, LIST_REL_MAP2] >>
  conj_tac
  >- (simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
      metis_tac[ptr_owner_op_projection]) >>
  rpt strip_tac >> drule ptr_owner_op_projection >>
  disch_then (qspec_then `x` strip_assume_tac) >>
  Cases_on `op_prov tagged x` >> gvs[]
QED

Theorem ptr_owner_phi_projection[local]:
  ptr_ledger_erases dyn births tagged numerical ==>
  ptr_owner_erases dyn births (phi_prov prev tagged inst) (phi_prov prev numerical inst) /\
  (!owner. phi_prov prev tagged inst = SOME owner ==> owner IN FDOM births)
Proof
  strip_tac >> Cases_on `prev` >> simp[phi_prov_def, ptr_owner_erases_def] >>
  Cases_on `resolve_phi x inst.inst_operands` >>
  simp[ptr_owner_erases_def] >> drule ptr_owner_op_projection >>
  disch_then (qspec_then `x'` mp_tac) >> simp[ptr_owner_erases_def]
QED

Theorem ptr_owner_phis_projection[local]:
  !insts. ptr_ledger_erases dyn births tagged numerical ==>
    ptr_ledger_erases dyn births (phis_prov prev tagged insts) (phis_prov prev numerical insts)
Proof
  Induct >> simp[phis_prov_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  drule ptr_owner_phi_projection >>
  disch_then (qspecl_then [`prev`,`h`] strip_assume_tac) >>
  irule ptr_owner_set_projection >> simp[]
QED

Theorem ptr_owner_entry_projection:
  ptr_ledger_erases dyn births tagged numerical ==>
    ptr_ledger_erases dyn births (entry_prov fn s tagged) (entry_prov fn s numerical)
Proof
  strip_tac >> simp[entry_prov_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  metis_tac[ptr_owner_phis_projection]
QED

Theorem ptr_owner_param_projection[local]:
  ptr_params_erases dyn births tagged numerical /\ n < LENGTH tagged ==>
  ptr_owner_erases dyn births (EL n tagged) (EL n numerical) /\
  (!owner. EL n tagged = SOME owner ==> owner IN FDOM births)
Proof
  simp[ptr_params_erases_def, EVERY_EL, LIST_REL_EL_EQN] >> rpt strip_tac >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[]
QED

(* The operand clause is what affine_pointer_ops gives for ADD/SUB. *)
Theorem ptr_owner_out_projection[local]:
  ptr_ledger_erases dyn births tagged numerical /\
  ptr_params_erases dyn births PT PG /\
  inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DALLOCA /\
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/ inst.inst_opcode = ASSIGN ==>
    !u1 u2. MEM (Var u1) inst.inst_operands /\ MEM (Var u2) inst.inst_operands /\
      FLOOKUP numerical u1 <> NONE /\ FLOOKUP tagged u2 <> NONE ==> u1 = u2) ==>
  ptr_owner_erases dyn births (out_prov PT tagged inst s') (out_prov PG numerical inst s') /\
  (!owner. out_prov PT tagged inst s' = SOME owner ==> owner IN FDOM births)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = PARAM`
  >- (simp[out_prov_def] >>
      Cases_on `inst.inst_operands` >> simp[ptr_owner_erases_def] >>
      Cases_on `t` >> simp[ptr_owner_erases_def] >>
      Cases_on `h` >> simp[ptr_owner_erases_def] >>
      `LENGTH PG = LENGTH PT` by
        (gvs[ptr_params_erases_def] >> metis_tac[LIST_REL_LENGTH]) >>
      Cases_on `w2n c < LENGTH PT` >> simp[ptr_owner_erases_def] >>
      drule_all ptr_owner_param_projection >> simp[ptr_owner_erases_def]) >>
  Cases_on `inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/ inst.inst_opcode = ASSIGN`
  >- (`ptr_owner_erases dyn births (first_prov tagged inst.inst_operands)
         (first_prov numerical inst.inst_operands) /\
       (!owner. first_prov tagged inst.inst_operands = SOME owner ==>
          owner IN FDOM births)` by
        (irule ptr_owner_first_projection >> metis_tac[]) >>
      gvs[out_prov_def]) >>
  gvs[out_prov_def, ptr_owner_erases_def]
QED

Theorem ptr_owner_step_projection:
  ptr_ledger_erases dyn births tagged numerical /\
  ptr_params_erases dyn births PT PG /\
  inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DALLOCA /\
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/ inst.inst_opcode = ASSIGN ==>
    !u1 u2. MEM (Var u1) inst.inst_operands /\ MEM (Var u2) inst.inst_operands /\
      FLOOKUP numerical u1 <> NONE /\ FLOOKUP tagged u2 <> NONE ==> u1 = u2) ==>
  ptr_ledger_erases dyn births (step_prov PT tagged inst s') (step_prov PG numerical inst s')
Proof
  strip_tac >> drule_all ptr_owner_out_projection >>
  disch_then (qspec_then `s'` strip_assume_tac) >>
  simp[step_prov_def] >> irule ptr_owner_set_projection >> simp[]
QED

Theorem ptr_owner_erases_extend[local]:
  ptr_owner_erases dyn births t n /\
  (!owner. t = SOME owner ==> owner IN FDOM births) /\
  (!owner site. FLOOKUP births owner = SOME site ==> FLOOKUP births' owner = SOME site) ==>
  ptr_owner_erases dyn births' t n /\
  (!owner. t = SOME owner ==> owner IN FDOM births')
Proof
  Cases_on `t` >> simp[ptr_owner_erases_def] >> strip_tac >>
  `?site. FLOOKUP births x = SOME site` by
    metis_tac[FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
  `FLOOKUP births' x = SOME site` by metis_tac[] >>
  gvs[FLOOKUP_DEF]
QED

Theorem ptr_ledger_erases_extend:
  ptr_ledger_erases dyn births tagged numerical /\
  (!owner site. FLOOKUP births owner = SOME site ==> FLOOKUP births' owner = SOME site) ==>
  ptr_ledger_erases dyn births' tagged numerical
Proof
  simp[ptr_ledger_erases_def] >> strip_tac >>
  `!v. ptr_owner_erases dyn births' (FLOOKUP tagged v) (FLOOKUP numerical v) /\
       (!owner. FLOOKUP tagged v = SOME owner ==> owner IN FDOM births')` by
    (gen_tac >> irule ptr_owner_erases_extend >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ptr_params_erases_extend:
  ptr_params_erases dyn births PT PG /\
  (!owner site. FLOOKUP births owner = SOME site ==> FLOOKUP births' owner = SOME site) ==>
  ptr_params_erases dyn births' PT PG
Proof
  cheat
QED

Theorem ptr_owner_alloca_insert:
  ptr_ledger_erases dyn births tagged numerical /\
  owner NOTIN FDOM births /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s'.vs_allocas inst.inst_id = SOME site ==>
  ptr_ledger_erases dyn (births |+ (owner,site))
    (set_prov tagged inst.inst_outputs (SOME owner))
    (step_prov PG numerical inst s')
Proof
  strip_tac >>
  `ptr_ledger_erases dyn (births |+ (owner,site)) tagged numerical` by
    (irule ptr_ledger_erases_extend >> qexists `births` >> simp[] >>
     rpt strip_tac >> `owner' <> owner` by (strip_tac >> gvs[FLOOKUP_DEF]) >>
     simp[FLOOKUP_UPDATE]) >>
  simp[step_prov_def, out_prov_def] >>
  irule ptr_owner_set_projection >> simp[ptr_owner_erases_def, FLOOKUP_UPDATE]
QED
