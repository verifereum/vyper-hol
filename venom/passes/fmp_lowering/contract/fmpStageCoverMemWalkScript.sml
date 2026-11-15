(* Opcode classification at a single chunk of the indexed lowering walk. *)
Theory fmpStageCoverMemWalk
Ancestors
  fmpStageControlWalk fmpLowerDefs fmpLowerIndexedProps fmpStepRewrite
  fmpLowerSequenceExec venomInst list rich_list finite_map

Theorem fmp_cover_walk_chunk:
  fmp_lower_indexed infos ctx runner lbl k s rs (inst::xs) = SOME (out,left,s') /\
  ALL_DISTINCT (MAP FST rs) /\
  (!j b. MEM ((lbl,j),b) rs <=> k <= j /\ FLOOKUP plan (lbl,j) = SOME b) /\
  P ASSIGN /\ P ADD /\ P NOT /\ P AND /\ P BUMP /\ P RETPC_PARAM /\
  q < (if (lbl,k) IN FDOM plan then 1 else 0) +
      (if inst.inst_opcode = DALLOCA then 4 else 1) /\
  (q = (if (lbl,k) IN FDOM plan then 1 else 0) ==>
   MEM inst.inst_opcode [DALLOCA; RETPC_PARAM]) ==>
  q < LENGTH out /\ P (EL q out).inst_opcode
Proof
  simp[fmp_lower_indexed_cons] >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all fmp_control_select_plan >> strip_tac >>
  drule fmp_control_emit_length >> strip_tac >>
  drule fmp_control_inst_length >> strip_tac >>
  `EVERY (\i. P i.inst_opcode) prefix` by
    (irule fmp_emit_restores_every >> simp[mk_inst_def] >> metis_tac[]) >>
  `q < LENGTH prefix + LENGTH head` by
    (Cases_on `(lbl,k) IN FDOM plan` >>
     Cases_on `inst.inst_opcode = DALLOCA` >> gvs[]) >>
  `q < LENGTH (prefix ++ head ++ tail)` by
    (pure_rewrite_tac[LENGTH_APPEND] >> decide_tac) >>
  conj_tac >- decide_tac >>
  Cases_on `q < LENGTH prefix`
  >- (gvs[EL_APPEND1, EVERY_EL] >> metis_tac[]) >>
  `q - LENGTH prefix < LENGTH head` by decide_tac >>
  simp[EL_APPEND_EQN] >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (`EVERY (\i. P i.inst_opcode) head` by
        (drule_all fmp_lower_inst_dalloca_shape >> strip_tac >>
         gvs[mk_inst_def]) >>
      fs[EVERY_EL] >> metis_tac[]) >>
  `q = LENGTH prefix` by
    (Cases_on `(lbl,k) IN FDOM plan` >> gvs[]) >>
  `inst.inst_opcode = RETPC_PARAM` by gvs[] >>
  `head = [inst]` by
    (qpat_x_assum `fmp_lower_inst _ _ _ _ _ = _` mp_tac >>
     simp[fmp_lower_inst_ordinary, is_raw_fmp_opcode_def]) >>
  gvs[]
QED
