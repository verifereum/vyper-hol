Theory algebraicOptMainPhiProofs
Ancestors
  algebraicOptChainAvailabilityProofs algebraicOptChainObservationProofs
  algebraicOptDemandProofs algebraicOptMainShapeProofs
  venomWf venomExecSemantics venomState dftCommutation
  algebraicOptDefs venomInst passSharedDefs
Libs
  listTheory

Theorem ao_resolve_phi_map:
  !ops f pred.
    phi_well_formed ops /\ (!l. f (Label l) = Label l) ==>
    resolve_phi pred (MAP f ops) = OPTION_MAP f (resolve_phi pred ops)
Proof
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, resolve_phi_def] >> rpt strip_tac >>
  simp[resolve_phi_def] >> IF_CASES_TAC >> simp[]
QED

Theorem ao_main_selected_phi_read:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  2 <= LENGTH trace /\ ao_source_trace ctx fn trace /\ LAST trace = (h,T,s) /\
  (!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
    lookup_var x (SND (SND (HD trace))) = NONE) /\
  MEM bb fn.fn_blocks /\ MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI /\
  s.vs_prev_bb = SOME pred /\ resolve_phi pred phi.inst_operands = SOME op /\
  eval_operand op s = SOME w /\ ao_main_observations fn V s r /\
  s.vs_labels = r.vs_labels /\
  (!i x. MEM i (fn_insts fn) /\
    (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) ==>
  eval_operand (ao_resolve_iszero_op (ao_compute_fn_iszero_targets fn) PHI op) r =
    SOME w
Proof
  strip_tac >>
  `MEM phi (fn_insts fn)` by
    (simp[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `MEM op phi.inst_operands` by metis_tac[resolve_phi_MEM] >>
  Cases_on `op`
  >- gvs[ao_resolve_iszero_op_def, eval_operand_def]
  >~ [`Label lbl`] >- gvs[ao_resolve_iszero_op_def, eval_operand_def] >>
  rename1 `resolve_phi pred phi.inst_operands = SOME (Var v)` >>
  Cases_on `ALOOKUP (ao_compute_fn_iszero_targets fn) v`
  >- (`eval_operand (Var v) s = eval_operand (Var v) r` by
        (irule ao_nontruthy_operand_exact_read >> simp[] >>
         qexistsl [`V`, `fn`, `phi`] >> simp[is_truthy_inst_def] >> metis_tac[]) >>
      gvs[ao_resolve_iszero_op_def]) >>
  drule_all ao_source_selected_phi_computed_chain_values >> strip_tac >>
  `eval_operand (ao_resolve_iszero_op (ao_compute_fn_iszero_targets fn) PHI (Var v)) r =
     eval_operand (Var v) s` by
    (irule ao_main_resolve_chain_exact >> simp[] >>
     metis_tac[]) >> simp[]
QED

Theorem ao_main_eval_one_phi:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  2 <= LENGTH trace /\ ao_source_trace ctx fn trace /\ LAST trace = (h,T,s) /\
  (!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
    lookup_var x (SND (SND (HD trace))) = NONE) /\
  MEM bb fn.fn_blocks /\ MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI /\
  phi_well_formed phi.inst_operands /\
  ao_main_observations fn V s r /\ s.vs_labels = r.vs_labels /\
  s.vs_prev_bb = r.vs_prev_bb /\
  (!i x. MEM i (fn_insts fn) /\
    (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) /\
  eval_one_phi s phi = SOME (out,w) ==>
  eval_one_phi r (ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn) phi) =
    SOME (out,w)
Proof
  strip_tac >>
  qpat_x_assum `eval_one_phi s phi = _` mp_tac >>
  simp[eval_one_phi_def, AllCaseEqs()] >> strip_tac >>
  `resolve_phi prev (MAP (ao_resolve_iszero_op (ao_compute_fn_iszero_targets fn) PHI)
      phi.inst_operands) = SOME (ao_resolve_iszero_op (ao_compute_fn_iszero_targets fn) PHI val_op)` by
    (drule ao_resolve_phi_map >>
     disch_then (qspecl_then [`ao_resolve_iszero_op (ao_compute_fn_iszero_targets fn) PHI`, `prev`] mp_tac) >>
     simp[ao_resolve_iszero_op_def]) >>
  `eval_operand (ao_resolve_iszero_op (ao_compute_fn_iszero_targets fn) PHI val_op) r = SOME w` by
    (irule ao_main_selected_phi_read >> metis_tac[]) >>
  simp[eval_one_phi_def, ao_resolve_iszero_inst_def]
QED

Theorem ao_main_eval_phis_map:
  !insts fn V s r s' f.
    ao_main_observations fn V s r /\
    (!i. MEM i insts ==> (f i).inst_opcode = i.inst_opcode) /\
    (!i x w. MEM i insts /\ i.inst_opcode = PHI /\
      eval_one_phi s i = SOME (x,w) ==> eval_one_phi r (f i) = SOME (x,w)) /\
    eval_phis s insts = OK s' ==>
    ?r'. eval_phis r (MAP f insts) = OK r' /\
      ao_main_observations fn V s' r' /\
      s' = s with vs_vars := s'.vs_vars /\
      r' = r with vs_vars := r'.vs_vars
Proof
  Induct_on `insts`
  >- (simp[eval_phis_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (gvs[eval_phis_def, AllCaseEqs()] >>
      rename1 `eval_one_phi s h = SOME (out,w)` >>
      `eval_one_phi r (f h) = SOME (out,w)` by metis_tac[MEM] >>
      first_x_assum drule >>
      disch_then (qspecl_then [`s''`, `f`] mp_tac) >>
      impl_tac >- metis_tac[MEM] >>
      strip_tac >> qexists `update_var out w r'` >>
      simp[eval_phis_def] >> conj_tac
      >- (irule algebraicOptRelationProofsTheory.ao_main_observations_update >> simp[]) >>
      conj_tac
      >- (qpat_x_assum `s'' = _` (fn th => once_rewrite_tac[th]) >>
          simp[update_var_def]) >>
      qpat_x_assum `r' = _` (fn th => once_rewrite_tac[th]) >>
      simp[update_var_def]) >>
  gvs[eval_phis_def] >> qexists `r` >> simp[eval_phis_def]
QED

Theorem ao_main_eval_phis:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  2 <= LENGTH trace /\ ao_source_trace ctx fn trace /\ LAST trace = (h,T,s) /\
  (!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
    lookup_var x (SND (SND (HD trace))) = NONE) /\
  MEM bb fn.fn_blocks /\ (!i. MEM i insts ==> MEM i bb.bb_instructions) /\
  ao_main_observations fn V s r /\ s.vs_labels = r.vs_labels /\
  s.vs_prev_bb = r.vs_prev_bb /\
  (!i x. MEM i (fn_insts fn) /\
    (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) /\
  eval_phis s insts = OK s' ==>
  ?r'. eval_phis r (MAP (ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn)) insts) = OK r' /\
    ao_main_observations fn V s' r' /\
    s' = s with vs_vars := s'.vs_vars /\ r' = r with vs_vars := r'.vs_vars
Proof
  strip_tac >> irule ao_main_eval_phis_map >> simp[algebraicOptShapeProofsTheory.ao_resolve_iszero_inst_fields] >>
  rpt strip_tac >> irule ao_main_eval_one_phi >>
  `phi_well_formed i.inst_operands` by
    (`inst_wf i` by metis_tac[fn_inst_wf_def] >> gvs[inst_wf_def]) >>
  metis_tac[]
QED

Theorem ao_eval_phis_filter:
  !insts s.
    (!i j. i < j /\ j < LENGTH insts /\ (EL j insts).inst_opcode = PHI ==>
      (EL i insts).inst_opcode = PHI) ==>
    eval_phis s (FILTER (\i. i.inst_opcode = PHI) insts) = eval_phis s insts
Proof
  Induct_on `insts` >- simp[eval_phis_def] >> rpt strip_tac >>
  `!i j. i < j /\ j < LENGTH insts /\ (EL j insts).inst_opcode = PHI ==>
     (EL i insts).inst_opcode = PHI` by
    (rpt strip_tac >> first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
  Cases_on `h.inst_opcode = PHI`
  >- (`eval_phis s (FILTER (\i. i.inst_opcode = PHI) insts) = eval_phis s insts` by
        metis_tac[] >> simp[eval_phis_def]) >>
  `EVERY (\i. i.inst_opcode <> PHI) insts` by
    (simp[EVERY_EL] >> rpt strip_tac >>
     qpat_x_assum `!i j. _ /\ _ < LENGTH (h::insts) /\ _ ==> _`
       (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
  `FILTER (\i. i.inst_opcode = PHI) insts = []` by
    gvs[FILTER_EQ_NIL, EVERY_MEM] >>
  simp[eval_phis_def]
QED

Theorem ao_main_eval_phis_supply:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  2 <= LENGTH trace /\ ao_source_trace ctx fn trace /\ LAST trace = (h,T,s) /\
  (!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
    lookup_var x (SND (SND (HD trace))) = NONE) /\
  MEM bb fn.fn_blocks /\
  ao_main_observations fn V s r /\ s.vs_labels = r.vs_labels /\
  s.vs_prev_bb = r.vs_prev_bb /\
  (!i x. MEM i (fn_insts fn) /\
    (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) /\
  ao_transform_insts_supply dfg ra lbl (ao_compute_fn_iszero_targets fn)
    supply idx bb.bb_instructions = (outs,supply') /\
  eval_phis s bb.bb_instructions = OK s' ==>
  ?r'. eval_phis r outs = OK r' /\ ao_main_observations fn V s' r' /\
    s' = s with vs_vars := s'.vs_vars /\ r' = r with vs_vars := r'.vs_vars
Proof
  strip_tac >>
  `!i j. i < j /\ j < LENGTH bb.bb_instructions /\
     (EL j bb.bb_instructions).inst_opcode = PHI ==>
     (EL i bb.bb_instructions).inst_opcode = PHI` by
    (gvs[wf_function_def, EVERY_MEM, bb_well_formed_def] >> metis_tac[]) >>
  `eval_phis s (FILTER (\i. i.inst_opcode = PHI) bb.bb_instructions) = OK s'` by
    metis_tac[ao_eval_phis_filter] >>
  `?r'. eval_phis r (MAP (ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn))
      (FILTER (\i. i.inst_opcode = PHI) bb.bb_instructions)) = OK r' /\
     ao_main_observations fn V s' r' /\
     s' = s with vs_vars := s'.vs_vars /\ r' = r with vs_vars := r'.vs_vars` by
    (irule ao_main_eval_phis >> simp[MEM_FILTER] >> metis_tac[]) >>
  drule ao_transform_insts_supply_phis >> strip_tac >>
  `!i j. i < j /\ j < LENGTH outs /\ (EL j outs).inst_opcode = PHI ==>
     (EL i outs).inst_opcode = PHI` by
    metis_tac[ao_transform_insts_supply_phi_prefix] >>
  qexists `r'` >> metis_tac[ao_eval_phis_filter]
QED

(* No incoming-edge premise is needed at initial entry: a successful batch
   with no predecessor must stop before its first instruction. *)
Theorem ao_eval_phis_no_predecessor:
  s.vs_prev_bb = NONE /\ eval_phis s insts = OK s' ==> s' = s
Proof
  Cases_on `insts` >> simp[eval_phis_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[eval_phis_def] >>
  strip_tac >> gvs[eval_one_phi_def, AllCaseEqs()]
QED
