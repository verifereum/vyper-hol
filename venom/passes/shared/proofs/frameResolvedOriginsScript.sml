Theory frameResolvedOrigins
Ancestors frameOriginUpdates ptrDiscipline venomInst finite_map list pred_set

(* A cache table attaches a lifetime token to each local allocation id.
   Parameter entries retain the caller's token; numerical sites are checked,
   never inverted to guess allocation identity. *)
Definition resolve_tag_def:
  resolve_tag (ct:(num, (num # num) # (num # num)) fmap)
    (rp:(((num # num) # (num # num)) option) list) tag site =
    case tag of
      OriginLocal aid =>
        (case FLOOKUP ct aid of NONE => NONE | SOME r =>
          if SND r = site then SOME r else NONE)
    | OriginParameter k =>
        if k < LENGTH rp then
          (case EL k rp of NONE => NONE | SOME r =>
            if SND r = site then SOME r else NONE)
        else NONE
    | OriginDynamic => NONE
End

(* The tags a dynamic (DALLOCA-derived) pointer carries: OriginDynamic,
   or a parameter whose actual was itself dynamic. *)
Definition unresolved_tag_def:
  unresolved_tag rp tag <=>
    tag = OriginDynamic \/
    ?k. tag = OriginParameter k /\ k < LENGTH rp /\ EL k rp = NONE
End

(* Only a dynamic pointer resolves to no entry. *)
Definition resolution_def:
  resolution ct rp om rv <=>
    !v. case FLOOKUP om v of
      NONE => FLOOKUP rv v = NONE
    | SOME p => FLOOKUP rv v = resolve_tag ct rp (FST p) (SND p) /\
                (resolve_tag ct rp (FST p) (SND p) = NONE ==>
                 unresolved_tag rp (FST p))
End

Theorem resolve_tag_site:
  resolve_tag ct rp tag site = SOME r ==> SND r = site
Proof
  Cases_on `tag` >> simp[resolve_tag_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem resolution_empty:
  resolution ct rp FEMPTY FEMPTY
Proof
  simp[resolution_def]
QED

Theorem resolution_lookup:
  resolution ct rp om rv /\ FLOOKUP om v = SOME (tag,site) ==>
  FLOOKUP rv v = resolve_tag ct rp tag site /\
  (resolve_tag ct rp tag site = NONE ==> unresolved_tag rp tag)
Proof
  simp[resolution_def] >> strip_tac >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[]
QED

Theorem resolution_none:
  resolution ct rp om rv /\ FLOOKUP om v = NONE ==> FLOOKUP rv v = NONE
Proof
  simp[resolution_def] >> strip_tac >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[]
QED

Theorem resolution_restrict:
  resolution ct rp om rv ==>
  resolution ct rp (DRESTRICT om keys) (DRESTRICT rv keys)
Proof
  simp[resolution_def, FLOOKUP_DRESTRICT] >> rpt strip_tac >>
  IF_CASES_TAC >> simp[]
QED

Theorem resolution_unresolved_update[local]:
  resolution ct rp om rv /\ resolve_tag ct rp tag site = NONE /\
  unresolved_tag rp tag ==>
  resolution ct rp (om |+ (v,(tag,site))) (DRESTRICT rv (COMPL {v}))
Proof
  simp[resolution_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >> rpt strip_tac >>
  Cases_on `v' = v` >> simp[]
QED

Theorem resolution_update:
  resolution ct rp om rv /\ resolve_tag ct rp tag site = SOME r ==>
  resolution ct rp (om |+ (v,(tag,site))) (rv |+ (v,r))
Proof
  simp[resolution_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  Cases_on `v' = v` >> simp[]
QED

Theorem resolution_erasure:
  resolution ct rp om rv /\ FLOOKUP rv v = SOME e ==>
  FLOOKUP (origin_erase om) v = SOME (SND e)
Proof
  simp[resolution_def, origin_erase_lookup] >> strip_tac >>
  first_x_assum (qspec_then `v` mp_tac) >>
  Cases_on `FLOOKUP om v` >> simp[] >>
  PairCases_on `x` >> simp[] >> rpt strip_tac >> metis_tac[resolve_tag_site]
QED

Definition resolved_op_def:
  resolved_op (rv:(string, (num # num) # (num # num)) fmap) op =
    case op of Var v => FLOOKUP rv v | _ => NONE
End

Theorem resolution_operand_erasure:
  resolution ct rp om rv /\ resolved_op rv op = SOME e ==>
  op_prov (origin_erase om) op = SOME (SND e)
Proof
  Cases_on `op` >> simp[resolved_op_def, op_prov_def] >>
  metis_tac[resolution_erasure]
QED

Theorem resolution_arguments_erasure:
  resolution ct rp om rv /\ k < LENGTH ops /\
  EL k (MAP (resolved_op rv) ops) = SOME e ==>
  EL k (MAP (op_prov (origin_erase om)) ops) = SOME (SND e)
Proof
  rpt strip_tac >>
  `EL k (MAP (resolved_op rv) ops) = resolved_op rv (EL k ops)` by
    (irule EL_MAP >> simp[]) >>
  `EL k (MAP (op_prov (origin_erase om)) ops) =
   op_prov (origin_erase om) (EL k ops)` by (irule EL_MAP >> simp[]) >>
  pop_assum SUBST1_TAC >> irule resolution_operand_erasure >> metis_tac[]
QED

Theorem resolution_origin_set:
  resolution ct rp om rv /\
  (case p of NONE => r = NONE | SOME (tag,site) =>
     r = resolve_tag ct rp tag site /\ (r = NONE ==> unresolved_tag rp tag)) ==>
  resolution ct rp (origin_set om outs p) (origin_set rv outs r)
Proof
  Cases_on `p` >> simp[]
  >- (strip_tac >> Cases_on `outs` >>
      gvs[origin_set_def] >> metis_tac[resolution_restrict]) >>
  PairCases_on `x` >> simp[] >> strip_tac >> gvs[] >>
  Cases_on `outs` >- (simp[origin_set_def] >> metis_tac[resolution_restrict]) >>
  reverse (Cases_on `t`)
  >- (Cases_on `resolve_tag ct rp x0 (x1,x2)` >> simp[origin_set_def] >>
      metis_tac[resolution_restrict]) >>
  Cases_on `resolve_tag ct rp x0 (x1,x2)` >> gvs[origin_set_def]
  >- (irule resolution_unresolved_update >> fs[]) >>
  irule resolution_update >> fs[]
QED

Theorem resolve_parameter_forward:
  k < LENGTH ops /\ EL k (MAP (resolved_op rv) ops) = SOME entry ==>
  resolve_tag ct (MAP (resolved_op rv) ops) (OriginParameter k) (SND entry) =
    SOME entry
Proof
  simp[resolve_tag_def]
QED

Definition resolved_phi_def:
  resolved_phi prev rv inst =
    case prev of NONE => NONE | SOME lbl =>
      case resolve_phi lbl inst.inst_operands of
        SOME op => resolved_op rv op | NONE => NONE
End

Definition resolved_phis_def:
  resolved_phis prev rv [] = rv /\
  resolved_phis prev rv (inst::rest) =
    if inst.inst_opcode <> PHI then rv
    else origin_set (resolved_phis prev rv rest) inst.inst_outputs
      (resolved_phi prev rv inst)
End

Theorem resolution_operand:
  resolution ct rp om rv ==>
  (case origin_op om op of
     NONE => resolved_op rv op = NONE
   | SOME (tag,site) => resolved_op rv op = resolve_tag ct rp tag site /\
       (resolve_tag ct rp tag site = NONE ==> unresolved_tag rp tag))
Proof
  strip_tac >> Cases_on `op` >> simp[origin_op_def, resolved_op_def] >>
  Cases_on `FLOOKUP om s`
  >- (drule_all resolution_none >> simp[]) >>
  PairCases_on `x` >> simp[] >> metis_tac[resolution_lookup]
QED

Theorem resolution_phi:
  resolution ct rp om rv ==>
  (case origin_phi prev om inst of
     NONE => resolved_phi prev rv inst = NONE
   | SOME (tag,site) => resolved_phi prev rv inst = resolve_tag ct rp tag site /\
       (resolve_tag ct rp tag site = NONE ==> unresolved_tag rp tag))
Proof
  strip_tac >> Cases_on `prev` >> simp[origin_phi_def, resolved_phi_def] >>
  Cases_on `resolve_phi x inst.inst_operands` >> simp[] >>
  metis_tac[resolution_operand]
QED

Theorem resolution_phis:
  !insts. resolution ct rp om rv ==>
  resolution ct rp (origin_phis prev om insts) (resolved_phis prev rv insts)
Proof
  Induct >> simp[origin_phis_def, resolved_phis_def] >> strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >> strip_tac >>
  irule resolution_origin_set >> fs[] >>
  mp_tac (Q.SPECL [`prev`, `h`] (Q.GENL [`prev`, `inst`] resolution_phi)) >>
  fs[] >> Cases_on `origin_phi prev om h` >> simp[] >>
  PairCases_on `x` >> simp[] >> metis_tac[]
QED

(* Passing a PARAM-derived pointer onwards preserves its ancestor token. *)
Theorem resolved_parameter_to_parameter:
  resolution ct rp om rv /\ FLOOKUP om v = SOME (OriginParameter k,site) /\
  k < LENGTH rp /\ EL k rp = SOME entry ==>
  resolve_tag ct' (MAP (resolved_op rv) [Var v]) (OriginParameter 0) site =
    SOME entry
Proof
  strip_tac >> drule_all resolution_lookup >>
  Cases_on `SND entry = site` >>
  gvs[resolve_tag_def, resolved_op_def, unresolved_tag_def]
QED

(* Parallel PHIs select from the same pre-map, even when the first output
   overwrites a variable selected by a later PHI.  resolution_phis therefore
   requires no artificial sequential-definedness premise. *)
Theorem resolved_parallel_phi_probe[local]:
  resolution ct rp om rv /\ first.inst_opcode = PHI /\ second.inst_opcode = PHI ==>
  resolution ct rp
    (origin_set (origin_set om second.inst_outputs (origin_phi prev om second))
      first.inst_outputs (origin_phi prev om first))
    (origin_set (origin_set rv second.inst_outputs (resolved_phi prev rv second))
      first.inst_outputs (resolved_phi prev rv first))
Proof
  strip_tac >>
  drule resolution_phis >> disch_then (qspecl_then [`prev`, `[first;second]`] mp_tac) >>
  simp[origin_phis_def, resolved_phis_def]
QED
