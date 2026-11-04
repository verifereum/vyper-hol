Theory lowerDloadControlPosition
Ancestors
  o1ContractLowerDload lowerDloadDefs venomExecSemantics list rich_list

(* Position inversion is lower_dload_insts_supply_position in the ancestor.
   Retain its offset witness rather than duplicating that theorem. *)
Theorem lower_dload_insts_supply_segment_index:
  lower_dload_insts_supply a pre = (p,a1) /\
  lower_dload_inst_supply a1 i = (c,a2) /\
  lower_dload_insts_supply a2 post = (tail,b) /\
  lower_dload_insts_supply a ins = (outs,b) /\
  ins = pre ++ i::post /\ k < LENGTH c ==>
  EL (LENGTH p + k) outs = EL k c /\
  EL (LENGTH pre) ins = i
Proof
  strip_tac >>
  drule_all lower_dload_insts_supply_segment_reconstruct >>
  strip_tac >> gvs[] >>
  simp[EL_APPEND1, EL_APPEND2]
QED

Theorem lower_dload_inst_supply_nonphi_head[local]:
  lower_dload_inst_supply a i = (c,b) /\ i.inst_opcode <> PHI ==>
  c <> [] /\ (HD c).inst_opcode <> PHI
Proof
  strip_tac >>
  `c <> []` by metis_tac[lower_dload_inst_supply_nonempty] >>
  simp[] >> strip_tac >>
  `MEM (HD c) c` by (Cases_on `c` >> gvs[]) >>
  metis_tac[lower_dload_inst_supply_control]
QED

Theorem lower_dload_insts_supply_phi_length:
  !ins a outs b.
    lower_dload_insts_supply a ins = (outs,b) ==>
    phi_prefix_length outs = phi_prefix_length ins
Proof
  Induct >- simp[lower_dload_insts_supply_def, phi_prefix_length_def] >>
  rpt gen_tac >>
  Cases_on `lower_dload_inst_supply a h` >>
  Cases_on `lower_dload_insts_supply r ins` >>
  simp[lower_dload_insts_supply_def] >> strip_tac >> gvs[] >>
  Cases_on `h.inst_opcode = PHI`
  >- (`lower_dload_inst_supply a h = ([h],a)` by
        (irule lower_dload_inst_supply_special >> simp[]) >>
      gvs[phi_prefix_length_def] >> first_x_assum drule >> simp[]) >>
  drule_all lower_dload_inst_supply_nonphi_head >> strip_tac >>
  Cases_on `q` >> gvs[phi_prefix_length_def]
QED

Theorem lower_dload_insts_supply_eval_phis:
  !ins a outs b s.
    lower_dload_insts_supply a ins = (outs,b) ==>
    eval_phis s outs = eval_phis s ins
Proof
  Induct >- simp[lower_dload_insts_supply_def, eval_phis_def] >>
  rpt gen_tac >>
  Cases_on `lower_dload_inst_supply a h` >>
  Cases_on `lower_dload_insts_supply r ins` >>
  simp[lower_dload_insts_supply_def] >> strip_tac >> gvs[] >>
  Cases_on `h.inst_opcode = PHI`
  >- (`lower_dload_inst_supply a h = ([h],a)` by
        (irule lower_dload_inst_supply_special >> simp[]) >>
      gvs[] >> first_x_assum drule >>
      disch_then (qspec_then `s` assume_tac) >> simp[eval_phis_def]) >>
  drule_all lower_dload_inst_supply_nonphi_head >> strip_tac >>
  Cases_on `q` >> gvs[eval_phis_def]
QED
