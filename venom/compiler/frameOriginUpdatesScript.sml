Theory frameOriginUpdates
Ancestors
  ptrDiscipline venomExecSemantics venomState venomInst finite_map list

Datatype:
  frame_origin = OriginLocal num | OriginParameter num | OriginDynamic
End

Definition origin_erase_def:
  origin_erase (om:(string, frame_origin # (num # num)) fmap) = SND o_f om
End

Definition origin_op_def:
  origin_op (om:(string, frame_origin # (num # num)) fmap) op =
    case op of Var u => FLOOKUP om u | _ => NONE
End

Definition origin_first_def:
  origin_first om [] = NONE /\
  origin_first om (op::ops) =
    case origin_op om op of SOME p => SOME p | NONE => origin_first om ops
End

Definition origin_out_def:
  origin_out PG om inst s' =
    if inst.inst_opcode = ALLOCA then
      OPTION_MAP (\site. (OriginLocal inst.inst_id,site))
        (FLOOKUP s'.vs_allocas inst.inst_id)
    else if inst.inst_opcode = DALLOCA then
      (case inst.inst_outputs of
         [out] => (case lookup_var out s' of
           SOME b => SOME (OriginDynamic,(w2n b,w2n s'.vs_fmp - w2n b))
         | NONE => NONE)
       | _ => NONE)
    else if inst.inst_opcode = PARAM then
      (case inst.inst_operands of
         [Lit idx] => if w2n idx < LENGTH PG then
           OPTION_MAP (\site. (OriginParameter (w2n idx),site)) (EL (w2n idx) PG)
           else NONE
       | _ => NONE)
    else if inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
            inst.inst_opcode = ASSIGN then origin_first om inst.inst_operands
    else NONE
End

Definition origin_set_def:
  origin_set om outs p =
    case (outs,p) of
      ([out],SOME pair) => om |+ (out,pair)
    | _ => DRESTRICT om (COMPL (set outs))
End

Definition origin_step_def:
  origin_step PG om inst s' = origin_set om inst.inst_outputs (origin_out PG om inst s')
End

Definition origin_phi_def:
  origin_phi prev om inst =
    case prev of NONE => NONE | SOME lbl =>
      case resolve_phi lbl inst.inst_operands of
        SOME op => origin_op om op | NONE => NONE
End

Definition origin_phis_def:
  origin_phis prev om [] = om /\
  origin_phis prev om (inst::rest) =
    if inst.inst_opcode <> PHI then om
    else origin_set (origin_phis prev om rest) inst.inst_outputs (origin_phi prev om inst)
End

Definition origin_entry_def:
  origin_entry fn s om =
    case lookup_block s.vs_current_bb fn.fn_blocks of
      SOME bb => origin_phis s.vs_prev_bb om bb.bb_instructions | NONE => om
End

Theorem origin_erase_lookup:
  FLOOKUP (origin_erase om) v = OPTION_MAP SND (FLOOKUP om v)
Proof
  simp[origin_erase_def, FLOOKUP_DEF] >> IF_CASES_TAC >> simp[]
QED

Theorem origin_erase_empty[simp]:
  origin_erase FEMPTY = FEMPTY
Proof
  simp[origin_erase_def]
QED

Theorem origin_erase_restrict:
  origin_erase (DRESTRICT om keys) = DRESTRICT (origin_erase om) keys
Proof
  simp[fmap_eq_flookup, origin_erase_lookup, FLOOKUP_DRESTRICT] >>
  gen_tac >> IF_CASES_TAC >> simp[]
QED

Theorem origin_erase_update:
  origin_erase (om |+ (v,p)) = origin_erase om |+ (v,SND p)
Proof
  simp[fmap_eq_flookup, origin_erase_lookup, FLOOKUP_UPDATE] >>
  gen_tac >> IF_CASES_TAC >> simp[]
QED

Theorem origin_op_erase:
  OPTION_MAP SND (origin_op om op) = op_prov (origin_erase om) op
Proof
  Cases_on `op` >> simp[origin_op_def, op_prov_def, origin_erase_lookup]
QED

Theorem origin_first_erase:
  !ops. OPTION_MAP SND (origin_first om ops) = first_prov (origin_erase om) ops
Proof
  Induct >> simp[origin_first_def, first_prov_def, GSYM origin_op_erase] >>
  Cases_on `origin_op om h` >> simp[]
QED

Theorem origin_out_erase:
  OPTION_MAP SND (origin_out PG om inst s') = out_prov PG (origin_erase om) inst s'
Proof
  simp[origin_out_def, out_prov_def] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (simp[] >> Cases_on `FLOOKUP s'.vs_allocas inst.inst_id` >> simp[]) >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (simp[] >> Cases_on `inst.inst_outputs` >> simp[] >>
      Cases_on `t` >> simp[] >> Cases_on `lookup_var h s'` >> simp[]) >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (simp[] >> Cases_on `inst.inst_operands` >> simp[] >>
      Cases_on `t` >> simp[] >> Cases_on `h` >> simp[] >>
      IF_CASES_TAC >> simp[] >> Cases_on `EL (w2n c) PG` >> simp[]) >>
  simp[] >> IF_CASES_TAC >> simp[origin_first_erase]
QED

Theorem origin_set_erase:
  origin_erase (origin_set om outs p) =
    set_prov (origin_erase om) outs (OPTION_MAP SND p)
Proof
  Cases_on `outs` >> Cases_on `p` >>
  simp[origin_set_def, set_prov_def, origin_erase_restrict] >>
  Cases_on `t` >> simp[origin_set_def, set_prov_def,
                        origin_erase_restrict, origin_erase_update]
QED

Theorem origin_step_erase:
  origin_erase (origin_step PG om inst s') = step_prov PG (origin_erase om) inst s'
Proof
  simp[origin_step_def, step_prov_def, origin_set_erase, origin_out_erase]
QED

Theorem origin_phi_erase:
  OPTION_MAP SND (origin_phi prev om inst) = phi_prov prev (origin_erase om) inst
Proof
  Cases_on `prev` >> simp[origin_phi_def, phi_prov_def] >>
  Cases_on `resolve_phi x inst.inst_operands` >> simp[origin_op_erase]
QED

Theorem origin_phis_erase:
  !insts. origin_erase (origin_phis prev om insts) = phis_prov prev (origin_erase om) insts
Proof
  Induct >> simp[origin_phis_def, phis_prov_def] >> gen_tac >>
  IF_CASES_TAC >> simp[origin_set_erase, origin_phi_erase]
QED

Theorem origin_entry_erase:
  origin_erase (origin_entry fn s om) = entry_prov fn s (origin_erase om)
Proof
  simp[origin_entry_def, entry_prov_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[origin_phis_erase]
QED

Theorem origin_equal_site_distinct_roots:
  origin_erase (FEMPTY |+ (v,(OriginLocal aid,site))) =
    origin_erase (FEMPTY |+ (v,(OriginParameter k,site))) /\
  (OriginLocal aid,site) <> (OriginParameter k,site)
Proof
  simp[origin_erase_update]
QED

Theorem origin_op_some:
  origin_op om op = SOME p <=> ?v. op = Var v /\ FLOOKUP om v = SOME p
Proof
  Cases_on `op` >> simp[origin_op_def]
QED

Theorem origin_first_some:
  !ops p. origin_first om ops = SOME p ==>
    ?op. MEM op ops /\ origin_op om op = SOME p
Proof
  Induct >> simp[origin_first_def] >> rpt gen_tac >>
  Cases_on `origin_op om h` >> simp[] >> metis_tac[]
QED

Theorem origin_set_lookup:
  FLOOKUP (origin_set om outs p) v =
    if outs = [v] then p else if MEM v outs then NONE else FLOOKUP om v
Proof
  Cases_on `outs` >> Cases_on `p` >>
  simp[origin_set_def, FLOOKUP_DRESTRICT] >>
  Cases_on `t` >> simp[origin_set_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  rpt IF_CASES_TAC >> gvs[]
QED

Theorem origin_step_lookup:
  FLOOKUP (origin_step PG om inst s') v = SOME p ==>
    (~MEM v inst.inst_outputs /\ FLOOKUP om v = SOME p) \/
    (inst.inst_outputs = [v] /\ origin_out PG om inst s' = SOME p)
Proof
  simp[origin_step_def, origin_set_lookup] >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem origin_out_alloca:
  inst.inst_opcode = ALLOCA ==>
  (origin_out PG om inst s' = SOME p <=>
    ?site. FLOOKUP s'.vs_allocas inst.inst_id = SOME site /\
           p = (OriginLocal inst.inst_id,site))
Proof
  simp[origin_out_def] >> strip_tac >>
  Cases_on `FLOOKUP s'.vs_allocas inst.inst_id` >> simp[]
QED

Theorem origin_out_param:
  inst.inst_opcode = PARAM ==>
  (origin_out PG om inst s' = SOME p <=>
    ?idx site. inst.inst_operands = [Lit idx] /\ w2n idx < LENGTH PG /\
      EL (w2n idx) PG = SOME site /\ p = (OriginParameter (w2n idx),site))
Proof
  strip_tac >> simp[origin_out_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `h` >> simp[] >>
  metis_tac[]
QED

Theorem origin_out_dalloca:
  inst.inst_opcode = DALLOCA ==>
  (origin_out PG om inst s' = SOME p <=>
    ?out b. inst.inst_outputs = [out] /\ lookup_var out s' = SOME b /\
      p = (OriginDynamic,(w2n b,w2n s'.vs_fmp - w2n b)))
Proof
  strip_tac >> simp[origin_out_def] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `lookup_var h s'` >> simp[EQ_SYM_EQ]
QED

Theorem origin_out_inherited:
  inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DALLOCA /\
  inst.inst_opcode <> PARAM /\ origin_out PG om inst s' = SOME p ==>
    (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
     inst.inst_opcode = ASSIGN) /\
    ?op. MEM op inst.inst_operands /\ origin_op om op = SOME p
Proof
  strip_tac >> gvs[origin_out_def] >>
  metis_tac[origin_first_some]
QED

Theorem origin_phi_some:
  origin_phi prev om inst = SOME p <=>
    ?lbl op. prev = SOME lbl /\ resolve_phi lbl inst.inst_operands = SOME op /\
      origin_op om op = SOME p
Proof
  Cases_on `prev` >> simp[origin_phi_def] >>
  Cases_on `resolve_phi x inst.inst_operands` >> simp[]
QED

Theorem origin_phis_lookup:
  !insts v p. FLOOKUP (origin_phis prev om insts) v = SOME p ==>
    FLOOKUP om v = SOME p \/
    ?inst. MEM inst insts /\ inst.inst_opcode = PHI /\
      inst.inst_outputs = [v] /\ origin_phi prev om inst = SOME p
Proof
  Induct >> simp[origin_phis_def] >> rpt gen_tac >>
  IF_CASES_TAC >- simp[] >>
  simp[origin_set_lookup] >> rpt IF_CASES_TAC >> simp[] >> metis_tac[]
QED
