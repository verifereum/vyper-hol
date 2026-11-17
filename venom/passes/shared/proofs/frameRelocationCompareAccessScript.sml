Theory frameRelocationCompareAccess
Ancestors frameResolvedTrace ptrDiscipline venomExecSemantics venomState finite_map words

(* An unresolved pointer sits at or above dyn while a resolved one lies in a
   live cache; when every cache lies below dyn the two never share a
   nonempty site. *)
Theorem resolved_compare_mixed[local]:
  resolved_frame_ok dyn birth cache PG G om rp rv ids frames /\
  (!k aid b sz. k < LENGTH frames /\
     FLOOKUP (SND (EL k frames)) aid = SOME (b,sz) ==> b + sz <= dyn) /\
  FLOOKUP G v = SOME (b,sz) /\ FLOOKUP rv v = NONE /\
  FLOOKUP rv w = SOME (t,(b,sz)) ==> sz = 0
Proof
  rpt strip_tac >>
  `dyn <= b` by
    (drule resolved_frame_erasure >> strip_tac >> res_tac >> fs[]) >>
  `resolved_live ids frames (t,(b,sz))` by
    (fs[resolved_frame_ok_def] >> metis_tac[]) >>
  gvs[resolved_live_def] >> res_tac >> decide_tac
QED

Theorem resolved_compare_access:
  access_ok lo G fn inst s /\
  resolved_frame_ok dyn birth cache PG G om rp rv ids frames /\
  ((!k aid b sz. k < LENGTH frames /\
     FLOOKUP (SND (EL k frames)) aid = SOME (b,sz) ==> b + sz <= dyn) \/
   SND o_f rv = G) /\
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!v e. FLOOKUP rv v = SOME e ==> FLOOKUP G v = SOME (SND e)` by
    metis_tac[resolved_frame_erasure] >>
  qpat_x_assum `access_ok _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [access_ok_def]) >>
  qpat_x_assum `!u w. _ /\ inst.inst_operands = [Var u; Var w] /\ _ ==> _`
    (qspecl_then [`u`, `w`] mp_tac) >>
  impl_tac
  >- (fs[] >> Cases_on `FLOOKUP rv u` >> Cases_on `FLOOKUP rv w` >> gvs[] >>
      res_tac >> fs[FLOOKUP_DEF]) >>
  qpat_x_assum `inst.inst_opcode = LT \/ _` kall_tac >>
  `!v v' t b' sz'. FLOOKUP G v = SOME (b',sz') /\ FLOOKUP rv v = NONE /\
     FLOOKUP rv v' = SOME (t,(b',sz')) ==> sz' = 0` by
    (qpat_x_assum `_ \/ SND o_f rv = G` strip_assume_tac >> rpt strip_tac
     >- (drule_all resolved_compare_mixed >> simp[]) >>
     gvs[FLOOKUP_o_f]) >>
  qpat_x_assum `_ \/ SND o_f rv = G` kall_tac >>
  strip_tac >> gvs[eval_operand_def] >>
  namedCases_on `FLOOKUP rv u` ["", "pu"] >>
  namedCases_on `FLOOKUP rv w` ["", "pw"] >> gvs[]
  >~ [`FLOOKUP _ _ = NONE`]
  >- (rename [`FLOOKUP rv pv = SOME e`, `FLOOKUP rv nv = NONE`] >> PairCases_on `e` >>
      `FLOOKUP G pv = SOME (e2,e3)` by
        (qpat_x_assum `!v e. FLOOKUP rv v = SOME e ==> _` drule >> simp[]) >>
      qpat_x_assum `!v v' t b' sz'. _`
        (qspecl_then [`nv`, `pv`, `(e0,e1)`, `e2`, `e3`] mp_tac) >> gvs[])
  >~ [`FLOOKUP _ _ = NONE`]
  >- (rename [`FLOOKUP rv pv = SOME e`, `FLOOKUP rv nv = NONE`] >> PairCases_on `e` >>
      `FLOOKUP G pv = SOME (e2,e3)` by
        (qpat_x_assum `!v e. FLOOKUP rv v = SOME e ==> _` drule >> simp[]) >>
      qpat_x_assum `!v v' t b' sz'. _`
        (qspecl_then [`nv`, `pv`, `(e0,e1)`, `e2`, `e3`] mp_tac) >> gvs[]) >>
  PairCases_on `pu` >> PairCases_on `pw` >>
  `(b,sz) = (pu2,pu3) /\ (b,sz) = (pw2,pw3)` by
    metis_tac[pairTheory.SND, optionTheory.SOME_11] >>
  gvs[]
QED
