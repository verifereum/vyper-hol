Theory algebraicOptChainProofs
Ancestors
  algebraicOptMainShapeProofs algebraicOptDefs venomInst
Libs
  listTheory

Definition ao_chain_edges_def:
  ao_chain_edges insts chn <=>
    !j. SUC j < LENGTH chn ==>
      ?prod y. MEM prod insts /\ prod.inst_opcode = ISZERO /\
        prod.inst_operands = [EL j chn] /\ prod.inst_outputs = [y] /\
        EL (SUC j) chn = Var y
End

Theorem ao_chain_edges_mono:
  (!i. MEM i xs ==> MEM i ys) /\ ao_chain_edges xs chn ==>
  ao_chain_edges ys chn
Proof
  simp[ao_chain_edges_def] >> metis_tac[]
QED

Theorem ao_chain_edges_singleton[simp]:
  ao_chain_edges insts [op]
Proof
  simp[ao_chain_edges_def]
QED

Theorem ao_chain_edges_snoc:
  chn <> [] /\ LAST chn = inp /\ ao_chain_edges insts chn /\
  MEM prod insts /\ prod.inst_opcode = ISZERO /\
  prod.inst_operands = [inp] /\ prod.inst_outputs = [y] ==>
  ao_chain_edges insts (SNOC (Var y) chn)
Proof
  strip_tac >> simp[ao_chain_edges_def, LENGTH_SNOC] >>
  rpt strip_tac >>
  Cases_on `SUC j < LENGTH chn`
  >- (simp[EL_SNOC] >> fs[ao_chain_edges_def] >> metis_tac[]) >>
  `SUC j = LENGTH chn` by decide_tac >>
  `j < LENGTH chn` by decide_tac >>
  simp[EL_SNOC, EL_LENGTH_SNOC] >>
  `EL j chn = LAST chn` by
    (Cases_on `chn` >> gvs[LAST_EL] >> decide_tac) >>
  metis_tac[]
QED

Theorem ao_chain_extend_lookup:
  (!v chn. ALOOKUP targets v = SOME chn ==>
     chn <> [] /\ LAST chn = Var v /\ ao_chain_edges insts chn) /\
  MEM prod insts /\ prod.inst_opcode = ISZERO /\
  prod.inst_operands = [inp] /\ prod.inst_outputs = [y] ==>
  ao_chain_edges insts (SNOC (Var y)
    (case inp of Var v => (case ALOOKUP targets v of
       SOME chn => chn | NONE => [inp]) | _ => [inp]))
Proof
  strip_tac >> irule ao_chain_edges_snoc >> simp[] >>
  Cases_on `inp` >> simp[]
  >- metis_tac[]
  >- (Cases_on `ALOOKUP targets s` >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ao_compute_iszero_step_witnesses:
  (!v chn. ALOOKUP targets v = SOME chn ==>
    chn <> [] /\ LAST chn = Var v /\ ao_chain_edges insts chn) ==>
  !v chn. ALOOKUP (ao_compute_iszero_step targets inst) v = SOME chn ==>
    chn <> [] /\ LAST chn = Var v /\ ao_chain_edges (inst::insts) chn
Proof
  strip_tac >>
  `!v chn. ALOOKUP targets v = SOME chn ==>
     chn <> [] /\ LAST chn = Var v /\ ao_chain_edges (inst::insts) chn` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
     irule ao_chain_edges_mono >> qexists_tac `insts` >> simp[]) >>
  reverse (Cases_on `inst.inst_opcode = ISZERO`)
  >- (simp[ao_compute_iszero_step_def] >> metis_tac[]) >>
  simp[ao_compute_iszero_step_def] >>
  Cases_on `inst.inst_operands` >> simp[]
  >- metis_tac[] >>
  Cases_on `t` >> simp[]
  >- (Cases_on `inst.inst_outputs` >> simp[]
      >- metis_tac[] >>
      Cases_on `t` >> simp[]
      >- (rpt strip_tac >> gvs[AllCaseEqs()] >>
          metis_tac[ao_chain_extend_lookup, MEM]) >>
      metis_tac[]) >>
  Cases_on `inst.inst_outputs` >> simp[]
  >- metis_tac[] >>
  Cases_on `t` >> simp[] >> metis_tac[]
QED

Theorem ao_compute_iszero_step_witnesses_in:
  MEM inst all_insts /\
  (!v chn. ALOOKUP targets v = SOME chn ==>
    chn <> [] /\ LAST chn = Var v /\ ao_chain_edges all_insts chn) ==>
  !v chn. ALOOKUP (ao_compute_iszero_step targets inst) v = SOME chn ==>
    chn <> [] /\ LAST chn = Var v /\ ao_chain_edges all_insts chn
Proof
  strip_tac >> drule ao_compute_iszero_step_witnesses >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
  irule ao_chain_edges_mono >> qexists_tac `inst::all_insts` >> simp[] >> metis_tac[]
QED

Theorem ao_compute_iszero_fold_witnesses:
  !insts targets.
  EVERY (\i. MEM i all_insts) insts /\
  (!v chn. ALOOKUP targets v = SOME chn ==>
    chn <> [] /\ LAST chn = Var v /\ ao_chain_edges all_insts chn) ==>
  !v chn. ALOOKUP (FOLDL ao_compute_iszero_step targets insts) v = SOME chn ==>
    chn <> [] /\ LAST chn = Var v /\ ao_chain_edges all_insts chn
Proof
  Induct
  >- (simp[] >> metis_tac[]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum match_mp_tac >> simp[] >>
  match_mp_tac ao_compute_iszero_step_witnesses_in >> simp[] >> metis_tac[]
QED

Theorem ao_compute_iszero_targets_witnesses:
  ALOOKUP (ao_compute_iszero_targets insts) v = SOME chn ==>
  chn <> [] /\ LAST chn = Var v /\ ao_chain_edges insts chn
Proof
  mp_tac (Q.SPECL [`insts`, `[]`]
    (Q.INST [`all_insts` |-> `insts`] ao_compute_iszero_fold_witnesses)) >>
  simp[EVERY_MEM, ao_compute_iszero_targets_def] >> metis_tac[]
QED

Theorem ao_compute_iszero_targets_endpoint:
  ALOOKUP (ao_compute_iszero_targets insts) v = SOME chn ==>
  chn <> [] /\ LAST chn = Var v
Proof
  metis_tac[ao_compute_iszero_targets_witnesses]
QED

Theorem ao_compute_iszero_targets_adjacent:
  ALOOKUP (ao_compute_iszero_targets insts) v = SOME chn /\
  SUC j < LENGTH chn ==>
  ?prod y. MEM prod insts /\ prod.inst_opcode = ISZERO /\
    prod.inst_operands = [EL j chn] /\ prod.inst_outputs = [y] /\
    EL (SUC j) chn = Var y
Proof
  metis_tac[ao_compute_iszero_targets_witnesses, ao_chain_edges_def]
QED
