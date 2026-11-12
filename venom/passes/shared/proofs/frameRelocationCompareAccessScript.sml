Theory frameRelocationCompareAccess
Ancestors frameResolvedTrace ptrDiscipline venomExecSemantics venomState finite_map words

Theorem erased_compare_access[local]:
  access_ok lo G fn inst s /\ SND o_f rv = G /\
  (inst.inst_opcode = LT \/ inst.inst_opcode = GT \/ inst.inst_opcode = EQ) /\
  inst.inst_operands = [Var u; Var w] /\
  (FLOOKUP rv u <> NONE \/ FLOOKUP rv w <> NONE) ==>
  ?tu tw b sz x z.
    FLOOKUP rv u = SOME (tu,(b,sz)) /\
    FLOOKUP rv w = SOME (tw,(b,sz)) /\ 0 < sz /\
    lookup_var u s = SOME x /\ lookup_var w s = SOME z /\
    b <= w2n x /\ w2n x <= b+sz /\
    b <= w2n z /\ w2n z <= b+sz
Proof
  strip_tac >>
  `u IN FDOM G \/ w IN FDOM G` by
    (gvs[FLOOKUP_DEF] >> metis_tac[]) >>
  qpat_x_assum `access_ok lo G fn inst s` mp_tac >>
  simp[access_ok_def] >> strip_tac >>
  Cases_on `FLOOKUP rv u` >> Cases_on `FLOOKUP rv w` >>
  gvs[FLOOKUP_o_f, eval_operand_def] >>
  rename1 `FLOOKUP rv u = SOME pu` >>
  rename1 `FLOOKUP rv w = SOME pw` >>
  PairCases_on `pu` >> PairCases_on `pw` >> gvs[]
QED

Theorem resolved_compare_access:
  access_ok lo G fn inst s /\
  resolved_frame_ok birth cache PG G om rp rv ids frames /\
  (inst.inst_opcode = LT \/ inst.inst_opcode = GT \/ inst.inst_opcode = EQ) /\
  inst.inst_operands = [Var u; Var w] /\
  (FLOOKUP rv u <> NONE \/ FLOOKUP rv w <> NONE) ==>
  ?tu tw b sz x z.
    FLOOKUP rv u = SOME (tu,(b,sz)) /\
    FLOOKUP rv w = SOME (tw,(b,sz)) /\ 0 < sz /\
    lookup_var u s = SOME x /\ lookup_var w s = SOME z /\
    b <= w2n x /\ w2n x <= b+sz /\
    b <= w2n z /\ w2n z <= b+sz
Proof
  strip_tac >> drule resolved_frame_erasure >> strip_tac >>
  irule erased_compare_access >>
  simp[] >> qexistsl_tac [`fn`, `inst`, `lo`] >> simp[]
QED
