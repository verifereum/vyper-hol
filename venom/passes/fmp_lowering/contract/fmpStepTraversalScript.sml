(* Occurrence-sensitive instruction ID transport through lowering. *)
Theory fmpStepTraversal
Ancestors
  fmpStepIdTransport fmpStepRewrite fmpLowerDefs list venomInst arithmetic

Theorem fmp_lower_inst_id_transport:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  inst.inst_id < B /\ B <= s.irs_next_inst ==>
  ir_id_transport B s.irs_next_inst s'.irs_next_inst
    [inst.inst_id] (MAP (\i. i.inst_id) out)
Proof
  strip_tac >> drule fmp_lower_inst_ids >>
  Cases_on `inst.inst_opcode = DALLOCA` >> simp[] >> rpt strip_tac
  >- (irule ir_id_transport_fresh >> simp[]) >>
  gvs[] >> irule ir_id_transport_retained >> simp[]
QED

Theorem fmp_emit_restores_id_transport:
  fmp_emit_restores runner s bases = (out,s') ==>
  B <= s.irs_next_inst ==>
  ir_id_transport B s.irs_next_inst s'.irs_next_inst
    [] (MAP (\i. i.inst_id) out)
Proof
  strip_tac >> drule fmp_emit_restores_ids >> rpt strip_tac >>
  irule ir_id_transport_fresh_empty_source >> simp[]
QED

Theorem fmp_lower_indexed_id_transport:
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
  EVERY (\i. i.inst_id < B) insts /\ B <= s.irs_next_inst ==>
  ir_id_transport B s.irs_next_inst s'.irs_next_inst
    (MAP (\i. i.inst_id) insts) (MAP (\i. i.inst_id) out)
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`, `k`] >>
  Induct_on `insts`
  >- simp[fmp_lower_indexed_def, ir_id_transport_empty] >>
  rpt gen_tac >> Cases_on `fmp_select_point_restores (label,k) restores` >>
  simp[fmp_lower_indexed_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule fmp_emit_restores_next_mono >> strip_tac >>
  drule fmp_lower_inst_next_mono >> strip_tac >>
  drule fmp_emit_restores_id_transport >>
  disch_then (qspec_then `B` mp_tac) >> simp[] >> strip_tac >>
  drule fmp_lower_inst_id_transport >>
  disch_then (qspec_then `B` mp_tac) >> simp[] >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  `ALL_DISTINCT ([h.inst_id] ++ MAP (\i. i.inst_id) insts)` by simp[] >>
  `ir_id_transport B s0.irs_next_inst s'.irs_next_inst
     ([h.inst_id] ++ MAP (\i. i.inst_id) insts)
     (MAP (\i. i.inst_id) head ++ MAP (\i. i.inst_id) tail)`
    by metis_tac[ir_id_transport_append] >>
  qpat_x_assum `ir_id_transport B s.irs_next_inst _ [] _`
    (mp_then (Pos hd) mp_tac ir_id_transport_append) >>
  disch_then drule >> simp[]
QED

Theorem fmp_lower_blocks_id_transport:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') ==>
  ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)) /\
  EVERY (\bb. EVERY (\i. i.inst_id < B) bb.bb_instructions) bbs /\
  B <= s.irs_next_inst ==>
  ir_id_transport B s.irs_next_inst s'.irs_next_inst
    (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs))
    (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) out))
Proof
  map_every qid_spec_tac [`s'`, `leftover`, `out`, `restores`, `s`] >>
  Induct_on `bbs` >- simp[fmp_lower_blocks_def, ir_id_transport_empty] >>
  simp[fmp_lower_blocks_def, AllCaseEqs(), ALL_DISTINCT_APPEND] >>
  rpt strip_tac >> gvs[] >>
  drule fmp_lower_indexed_next_mono >> strip_tac >>
  drule fmp_lower_indexed_id_transport >>
  disch_then (qspec_then `B` mp_tac) >> simp[] >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  irule ir_id_transport_append >> simp[ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem fmp_lower_indexed_ids_distinct:
  fmp_lower_indexed infos ctx runner label k s restores insts =
    SOME (out,leftover,s') ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
  EVERY (\i. i.inst_id < s.irs_next_inst) insts ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) out)
Proof
  strip_tac >> drule fmp_lower_indexed_id_transport >>
  disch_then (qspec_then `s.irs_next_inst` mp_tac) >> simp[] >>
  metis_tac[ir_id_transport_distinct]
QED

Theorem fmp_lower_blocks_ids_distinct:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') ==>
  ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)) /\
  EVERY (\bb. EVERY (\i. i.inst_id < s.irs_next_inst) bb.bb_instructions) bbs ==>
  ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) out))
Proof
  strip_tac >> drule fmp_lower_blocks_id_transport >>
  disch_then (qspec_then `s.irs_next_inst` mp_tac) >> simp[] >>
  metis_tac[ir_id_transport_distinct]
QED

Theorem fmp_lower_inst_parameter_identity:
  MEM inst.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM] ==>
  fmp_lower_inst infos ctx runner s inst = SOME ([inst],s)
Proof
  simp[] >> strip_tac >> gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def, is_raw_fmp_opcode_def]
QED

Theorem fmp_select_point_restores_absent:
  (!base. ~MEM (p,base) restores) ==>
  fmp_select_point_restores p restores = ([],restores)
Proof
  Induct_on `restores` >- simp[fmp_select_point_restores_def] >>
  gen_tac >> Cases_on `h` >> simp[fmp_select_point_restores_def] >>
  rpt strip_tac >> gvs[] >> Cases_on `q = p` >> gvs[] >> metis_tac[]
QED

Theorem fmp_lower_indexed_parameter_prefix:
  fmp_lower_indexed infos ctx runner label k s restores (prefix ++ suffix) =
    SOME (out,leftover,s') ==>
  EVERY (\i. MEM i.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM]) prefix ==>
  (!n base. n < LENGTH prefix ==> ~MEM ((label,k+n),base) restores) ==>
  ?tail. out = prefix ++ tail /\
    fmp_lower_indexed infos ctx runner label (k + LENGTH prefix) s restores suffix =
      SOME (tail,leftover,s')
Proof
  map_every qid_spec_tac [`out`, `k`] >> Induct_on `prefix`
  >- simp[] >>
  rpt gen_tac >> strip_tac >> simp[] >> rpt strip_tac >>
  `fmp_select_point_restores (label,k) restores = ([],restores)` by
    (irule fmp_select_point_restores_absent >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `fmp_lower_inst infos ctx runner s h = SOME ([h],s)` by
    (irule fmp_lower_inst_parameter_identity >> simp[]) >>
  gvs[fmp_lower_indexed_def, fmp_emit_restores_def, AllCaseEqs()] >>
  `!n base. n < LENGTH prefix ==> ~MEM ((label,SUC k+n),base) restores` by
    (rpt strip_tac >>
     qpat_x_assum `!n base. n < SUC _ ==> _`
       (qspec_then `SUC n` mp_tac) >>
     gvs[ADD_CLAUSES, ADD_COMM] >> metis_tac[]) >>
  first_x_assum drule >> simp[] >> strip_tac >>
  gvs[ADD_CLAUSES, ADD_COMM]
QED

Theorem fmp_lower_indexed_parameter_take_drop:
  fmp_lower_indexed infos ctx runner label k s restores (prefix ++ suffix) =
    SOME (out,leftover,s') ==>
  EVERY (\i. MEM i.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM]) prefix ==>
  (!n base. n < LENGTH prefix ==> ~MEM ((label,k+n),base) restores) ==>
  TAKE (LENGTH prefix) out = prefix /\
  fmp_lower_indexed infos ctx runner label (k + LENGTH prefix) s restores suffix =
    SOME (DROP (LENGTH prefix) out,leftover,s')
Proof
  strip_tac >> drule fmp_lower_indexed_parameter_prefix >>
  rpt strip_tac >> gvs[] >> res_tac >> gvs[TAKE_APPEND1, DROP_APPEND1]
QED

Theorem fmp_lower_blocks_entry_parameter_prefix:
  fmp_lower_blocks infos ctx runner s restores (entry::bbs) =
    SOME (FmpBlocksResult out leftover s') ==>
  entry.bb_instructions = prefix ++ suffix ==>
  EVERY (\i. MEM i.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM]) prefix ==>
  (!n base. n < LENGTH prefix ==> ~MEM ((entry.bb_label,n),base) restores) ==>
  ?entry' rest tail later s2.
    out = entry'::rest /\ entry'.bb_label = entry.bb_label /\
    entry'.bb_instructions = prefix ++ tail /\
    fmp_lower_indexed infos ctx runner entry.bb_label (LENGTH prefix) s restores suffix =
      SOME (tail,later,s2) /\
    fmp_lower_blocks infos ctx runner s2 later bbs =
      SOME (FmpBlocksResult rest leftover s')
Proof
  simp[fmp_lower_blocks_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule fmp_lower_indexed_parameter_prefix >> simp[] >>
  strip_tac >> gvs[] >> metis_tac[]
QED
