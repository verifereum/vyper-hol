Theory fmpStepCallTraversal
Ancestors
  fmpStepCallEnvironment fmpStepRewrite fmpStepFlagTransport
  fmpLowerDefs venomEffects venomInst unitShapeDefs list

Theorem fmp_emit_restores_flag_path:
  fmp_emit_restores runner s bases = (prefix,s') /\
  ~MEM runner vs /\ flag_path bbs vs tail ==>
  flag_path bbs vs (prefix ++ tail)
Proof
  strip_tac >> irule flag_path_pure_prefix >> simp[] >>
  irule fmp_emit_restores_every >>
  qexistsl_tac [`bases`, `runner`, `s`, `s'`] >>
  simp[mk_inst_def, write_effects_def, empty_effects_def]
QED

Theorem fmp_lower_inst_flag_path:
  fmp_lower_inst infos ctx runner s inst = SOME (head,s') /\
  ~MEM runner V /\ EVERY (\x. MEM x V) vs /\
  EVERY (\x. MEM x V) inst.inst_outputs /\
  (!vs i. flag_fails src vs i ==> flag_fails dst vs i) /\
  inst.inst_opcode <> INVOKE /\
  (flag_fails src vs inst \/ flag_path dst (flag_step inst vs) tail) ==>
  flag_path dst vs (head ++ tail)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> (
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (qpat_x_assum `!vs i. _` kall_tac >>
      gvs[fmp_lower_inst_def, AllCaseEqs(), flag_fails_def,
          flag_step_def, write_effects_def, empty_effects_def] >>
      irule dftCallChecksTheory.flag_path_mono >> qexists_tac `[]` >> simp[] >>
      qsuff_tac `flag_path dst []
        ([mk_inst add_id ADD [Lit 31w; size_op] [plus31];
          mk_inst not_id NOT [Lit 31w] [mask];
          mk_inst and_id AND [Var plus31; Var mask] [aligned];
          mk_inst bump_id BUMP [Var runner; Var aligned] [old;runner]] ++ tail)`
      >- simp[APPEND] >>
      irule flag_path_empty_pure_prefix >>
      simp[mk_inst_def, write_effects_def, empty_effects_def]) >>
  Cases_on `inst.inst_opcode = SETFMP`
  >- (qpat_x_assum `!vs i. _` kall_tac >>
      gvs[fmp_lower_inst_def, AllCaseEqs(), flag_fails_def,
          flag_step_def, write_effects_def, empty_effects_def] >>
      irule dftCallChecksTheory.flag_path_mono >> qexists_tac `[]` >> simp[] >>
      qsuff_tac `flag_path dst [] ([inst with <|inst_opcode := ASSIGN; inst_outputs := [runner]|>] ++ tail)`
      >- simp[APPEND] >>
      irule flag_path_empty_pure_prefix >>
      simp[write_effects_def, empty_effects_def]) >>
  Cases_on `inst.inst_opcode = GETFMP`
  >- (qpat_x_assum `!vs i. _` kall_tac >>
      gvs[fmp_lower_inst_def, AllCaseEqs(), flag_fails_def] >>
      simp[Once flag_path_cons_step] >> disj2_tac >>
      irule dftCallChecksTheory.flag_path_mono >>
      qexists_tac `flag_step inst vs` >>
      simp[flag_step_def, write_effects_def, empty_effects_def, MEM_FILTER] >>
      rpt strip_tac >> Cases_on `MEM runner vs` >> gvs[MEM_FILTER]) >>
  Cases_on `inst.inst_opcode = RETFMP`
  >- (qpat_x_assum `!vs i. _` kall_tac >>
      gvs[fmp_lower_inst_def, AllCaseEqs(), flag_fails_def] >>
      simp[Once flag_path_cons_step] >> disj2_tac >>
      gvs[flag_step_def, write_effects_def, empty_effects_def]) >>
  gvs[fmp_lower_inst_def] >> simp[Once flag_path_cons_step] >>
  metis_tac[])
QED

Theorem fmp_lower_indexed_flag_path:
  !insts k s restores out leftover s' vs.
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') /\ ~MEM runner V /\
  EVERY (\i. EVERY (\x. MEM x V) i.inst_outputs) insts /\
  EVERY (\x. MEM x V) vs /\
  (!vs i. flag_fails src vs i ==> flag_fails dst vs i) /\
  flag_path src vs insts ==>
  flag_path dst vs out
Proof
  Induct >- simp[flag_path_def] >> rpt gen_tac >>
  simp[fmpLowerIndexedPropsTheory.fmp_lower_indexed_cons, flag_path_cons_step] >>
  strip_tac >> (
  qpat_x_assum `out = _` SUBST1_TAC >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  `~MEM runner vs` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  irule fmp_emit_restores_flag_path >> conj_tac
  >- metis_tac[] >>
  `flag_fails src vs h \/ flag_path dst (flag_step h vs) tail` by
    (Cases_on `flag_fails src vs h` >- simp[] >>
     disj2_tac >> first_x_assum irule >>
     `EVERY (\x. MEM x V) (flag_step h vs)` by
       (irule flag_step_closed >> simp[]) >>
     metis_tac[]) >>
  irule fmp_lower_inst_flag_path >> metis_tac[])
QED

Theorem calls_flagged_no_calls_prefix:
  !p. EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> STATICCALL) p /\
  calls_flagged bbs tail ==> calls_flagged bbs (p ++ tail)
Proof
  Induct >> simp[calls_flagged_def] >> metis_tac[]
QED

Theorem fmp_lower_inst_calls_flagged:
  fmp_lower_inst infos ctx runner s inst = SOME (head,s') /\
  calls_flagged dst tail /\
  ((inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) ==>
    case inst.inst_outputs of [v] => flag_path dst [v] tail | _ => F) ==>
  calls_flagged dst (head ++ tail)
Proof
  simp[fmp_lower_inst_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[calls_flagged_def, mk_inst_def] >> metis_tac[]
QED

Theorem fmp_lower_indexed_calls_flagged:
  !insts k s restores out leftover s'.
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') /\ ~MEM runner V /\
  EVERY (\i. EVERY (\x. MEM x V) i.inst_outputs) insts /\
  (!vs i. flag_fails src vs i ==> flag_fails dst vs i) /\
  calls_flagged src insts ==>
  calls_flagged dst out
Proof
  Induct >- simp[fmp_lower_indexed_def, calls_flagged_def] >> rpt gen_tac >>
  simp[fmpLowerIndexedPropsTheory.fmp_lower_indexed_cons, calls_flagged_def] >>
  strip_tac >>
  qpat_x_assum `out = _` SUBST1_TAC >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  irule calls_flagged_no_calls_prefix >> conj_tac
  >- (irule fmp_emit_restores_every >>
      goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
  `calls_flagged dst tail` by (first_x_assum irule >> metis_tac[]) >>
  `((h.inst_opcode = CALL \/ h.inst_opcode = STATICCALL) ==>
     case h.inst_outputs of [v] => flag_path dst [v] tail | _ => F)` by
    (strip_tac >> (Cases_on `h.inst_outputs` >> gvs[] >>
     Cases_on `t` >> gvs[] >>
     irule fmp_lower_indexed_flag_path >> simp[] >> metis_tac[])) >>
  irule fmp_lower_inst_calls_flagged >> metis_tac[]
QED

Theorem fmp_lower_blocks_calls_flagged:
  !bbs s restores out leftover s'.
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') /\ ~MEM runner V /\
  EVERY (\bb. EVERY (\i. EVERY (\x. MEM x V) i.inst_outputs)
    bb.bb_instructions) bbs /\
  (!vs i. flag_fails src vs i ==> flag_fails dst vs i) /\
  EVERY (\bb. calls_flagged src bb.bb_instructions) bbs ==>
  EVERY (\bb. calls_flagged dst bb.bb_instructions) out
Proof
  Induct >- simp[fmp_lower_blocks_def] >> rpt gen_tac >>
  simp[fmp_lower_blocks_def, AllCaseEqs()] >> strip_tac >>
  gvs[] >> conj_tac
  >- (drule_all fmp_lower_indexed_calls_flagged >> simp[]) >>
  first_x_assum irule >> metis_tac[]
QED
