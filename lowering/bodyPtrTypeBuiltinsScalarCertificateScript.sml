(* Certificate probes use explicit scalar sets rather than a new predicate:
   the independent invariant is absence in G, not taint cleanliness. *)
Theory bodyPtrTypeBuiltinsScalarCertificate
Ancestors
  bodyPtrTypeBuiltinsScalarTransfer decoderGhostFramePtr
  fragGasPathPtr ptrDiscipline venomInst venomState finite_map pred_set list

Theorem scalar_set_step:
  (!x. x IN scalars ==> FLOOKUP G x = NONE) /\
  out_prov PG G inst t = NONE ==>
  !x. x IN scalars UNION set inst.inst_outputs ==>
    FLOOKUP (step_prov PG G inst t) x = NONE
Proof
  rpt strip_tac >> Cases_on `MEM x inst.inst_outputs`
  >- (irule step_prov_output_none >> simp[]) >>
  simp[step_prov_other_output] >> gvs[]
QED

(* A root (e.g. a scalar load) followed by an actual ASSIGN producer.
   G is arbitrary, including old entries for both output variables. *)
Theorem scalar_root_assign:
  root.inst_opcode = MLOAD /\ root.inst_outputs = [x] /\
  move.inst_opcode = ASSIGN /\ move.inst_outputs = [y] /\
  move.inst_operands = [Var x] ==>
  FLOOKUP (step_prov PG (step_prov PG G root t) move u) y = NONE
Proof
  strip_tac >>
  `out_prov PG G root t = NONE` by
    (irule out_prov_clearing_none >> simp[]) >>
  `FLOOKUP (step_prov PG G root t) x = NONE` by
    (irule step_prov_output_none >> simp[]) >>
  irule step_prov_output_none >> simp[] >>
  irule out_prov_forward_none >> simp[op_prov_def]
QED

(* Parallel PHI entry uses G0 for each selected operand, not the map
   updated by a preceding PHI. This is the join certificate boundary. *)
Theorem scalar_phis_selected:
  (!inst. MEM inst insts ==> inst.inst_opcode = PHI) /\
  (!inst. MEM inst insts ==>
    ?op. resolve_phi lbl inst.inst_operands = SOME op /\
         op_prov G0 op = NONE) ==>
  !x. MEM x (FLAT (MAP (\inst. inst.inst_outputs) insts)) ==>
    FLOOKUP (phis_prov (SOME lbl) G0 insts) x = NONE
Proof
  Induct_on `insts` >> simp[phis_prov_def] >> rpt strip_tac >>
  gvs[] >>
  `phi_prov (SOME lbl) G0 h = NONE` by
    (irule phi_prov_selected_none >> metis_tac[]) >>
  Cases_on `h.inst_outputs` >>
  gvs[set_prov_def, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem scalar_entry_selected:
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
  t.vs_prev_bb = SOME lbl /\
  (!inst. MEM inst bb.bb_instructions ==> inst.inst_opcode = PHI) /\
  (!inst. MEM inst bb.bb_instructions ==>
    ?op. resolve_phi lbl inst.inst_operands = SOME op /\
         op_prov G0 op = NONE) ==>
  !x. MEM x (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions)) ==>
    FLOOKUP (entry_prov fn t G0) x = NONE
Proof
  strip_tac >> simp[entry_prov_def] >>
  rpt strip_tac >> irule scalar_phis_selected >> simp[]
QED

(* A PC-indexed certificate must be closed on actual edges; this lifting
   keeps the original counted path and ghosts, rather than choosing a run. *)
Theorem gas_path_ptr_prov_invariant:
  !D lo ctx fn PG G tn s n G' tn' r.
    gas_path_ptr D lo ctx fn PG G tn s n G' tn' r ==>
    !I. I G s /\
      (!H ts a k H' ts' b.
        I H a /\ gas_path_ptr_edge D lo ctx fn PG H ts a k H' ts' (OK b) ==>
        I H' b) ==>
      !t. r = OK t ==> I G' t
Proof
  ho_match_mp_tac gas_path_ptr_ind >> rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >>
      qpat_x_assum `!I. _` (qspec_then `I'` mp_tac) >>
      impl_tac >- (conj_tac >- metis_tac[] >> first_assum ACCEPT_TAC) >>
      disch_then irule >> simp[]) >>
  rpt strip_tac >> gvs[fragExecTheory.exit_result_def]
QED

Theorem gas_outcome_ptr_prov_invariant:
  certpred G0 s0 /\
  (!H ts a k H' ts' b.
    certpred H a /\ gas_path_ptr_edge D 0 ctx fn PG H ts a k H' ts' (OK b) ==>
    certpred H' b) /\
  gas_outcome_ptr D tops (ctx, fn) PG source (es, s0, G0, tn0) Q R ==>
  gas_outcome_ptr D tops (ctx, fn) PG source (es, s0, G0, tn0)
    (\res ee G tn t. Q res ee G tn t /\ certpred G t) R
Proof
  simp[gas_outcome_ptr_def, gas_summary_ptr_at_def] >>
  rpt strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`res`, `es_end`, `G`, `tn`, `r`] >>
      simp[] >> disj1_tac >>
      drule gas_path_ptr_prov_invariant >>
      disch_then (qspec_then `certpred` mp_tac) >> simp[] >>
      impl_tac >- first_assum ACCEPT_TAC >> simp[]) 
  >- (qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`res`, `es_end`, `G`, `tn`, `r`] >> simp[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[]
QED
