Theory algebraicOptChainAvailabilityProofs
Ancestors
  algebraicOptChainProofs algebraicOptFreshnessProofs algebraicOptRangeConditionProofs
  algebraicOptTraceProofs
  venomState venomWf venomInst venomExecSemantics unitShapeDefs
Libs
  listTheory

Theorem ao_chain_producer_location:
  MEM prod (fn_insts fn) /\ prod.inst_opcode <> PHI ==>
  ?bp r. MEM bp fn.fn_blocks /\ get_instruction bp r = SOME prod /\
         phi_prefix_length bp.bb_instructions <= r
Proof
  strip_tac >> fs[fn_insts_def, MEM_fn_insts_blocks_iff] >>
  qpat_x_assum `MEM prod _` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  qexistsl [`bb`,`n`] >> simp[get_instruction_def] >>
  irule ao_non_phi_index_after_prefix >> gvs[]
QED

Theorem ao_source_chain_edge_value:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ trace <> [] /\
  ao_source_trace ctx fn trace /\ LAST trace = (h,F,s) /\
  (!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
    lookup_var x (SND (SND (HD trace))) = NONE) /\
  MEM prod (fn_insts fn) /\ prod.inst_opcode = ISZERO /\
  prod.inst_outputs = [x] /\ prod.inst_operands = [op] /\
  eval_operand (Var x) s = SOME value /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME target /\
  def_available_at fn target use_opt x /\
  (case use_opt of
     SOME use => get_instruction target s.vs_inst_idx = SOME use /\
                 use.inst_opcode <> PHI
   | NONE => ?term. get_instruction target s.vs_inst_idx = SOME term /\
                    is_terminator term.inst_opcode) ==>
  (?word. eval_operand op s = SOME word /\
          value = (if word = 0w then 1w else 0w)) /\
  (!z. op = Var z ==> def_available_at fn target use_opt z)
Proof
  strip_tac >>
  `?bp r. MEM bp fn.fn_blocks /\ get_instruction bp r = SOME prod /\
          phi_prefix_length bp.bb_instructions <= r` by
    (irule ao_chain_producer_location >> simp[] >> metis_tac[]) >>
  `MEM prod bp.bb_instructions` by
    (gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  conj_tac
  >- (irule ao_source_trace_iszero_operand_value >>
      gvs[eval_operand_def] >> metis_tac[MEM]) >>
  rpt strip_tac >> irule ao_available_through_producer >> simp[] >>
  qexistsl [`bp`,`prod`,`x`] >> simp[] >>
  fs[wf_ssa_def, def_dominates_uses_def] >>
  first_x_assum drule_all >> simp[]
QED

Theorem ao_chain_edges_unsnoc:
  chn <> [] /\ ao_chain_edges insts (SNOC op chn) ==>
  ao_chain_edges insts chn /\
  ?prod x. MEM prod insts /\ prod.inst_opcode = ISZERO /\
    prod.inst_operands = [LAST chn] /\ prod.inst_outputs = [x] /\ op = Var x
Proof
  strip_tac >> conj_tac
  >- (fs[ao_chain_edges_def, LENGTH_SNOC] >> rpt strip_tac >>
      first_x_assum (qspec_then `j` mp_tac) >> simp[EL_SNOC]) >>
  fs[ao_chain_edges_def, LENGTH_SNOC] >>
  first_x_assum (qspec_then `LENGTH chn - 1` mp_tac) >>
  `0 < LENGTH chn` by (Cases_on `chn` >> gvs[]) >>
  `SUC (LENGTH chn - 1) = LENGTH chn` by decide_tac >>
  simp[EL_LENGTH_SNOC, EL_SNOC] >>
  `EL (LENGTH chn - 1) chn = LAST chn` by
    (Cases_on `chn` >> gvs[LAST_EL]) >> simp[]
QED

Theorem ao_word_chain_snoc:
  ws <> [] /\ ao_word_chain ws /\
  value = (if LAST ws = 0w then 1w else 0w) ==>
  ao_word_chain (SNOC value ws)
Proof
  strip_tac >> simp[ao_word_chain_def, LENGTH_SNOC] >> rpt strip_tac >>
  Cases_on `SUC j < LENGTH ws`
  >- (simp[EL_SNOC] >> metis_tac[ao_word_chain_def]) >>
  `SUC j = LENGTH ws /\ j < LENGTH ws` by decide_tac >>
  `EL j ws = LAST ws` by
    (Cases_on `ws` >> gvs[LAST_EL] >> decide_tac) >>
  simp[EL_SNOC, EL_LENGTH_SNOC]
QED

Theorem ao_source_chain_values:
  !chn value.
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ trace <> [] /\
  ao_source_trace ctx fn trace /\ LAST trace = (h,F,s) /\
  (!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
    lookup_var x (SND (SND (HD trace))) = NONE) /\
  ao_chain_edges (fn_insts fn) chn /\ chn <> [] /\
  eval_operand (LAST chn) s = SOME value /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME target /\
  (!x. LAST chn = Var x ==> def_available_at fn target use_opt x) /\
  (case use_opt of
     SOME use => get_instruction target s.vs_inst_idx = SOME use /\
                 use.inst_opcode <> PHI
   | NONE => ?term. get_instruction target s.vs_inst_idx = SOME term /\
                    is_terminator term.inst_opcode) ==>
  ?ws. LENGTH ws = LENGTH chn /\ ao_word_chain ws /\ LAST ws = value /\
       (!j. j < LENGTH chn ==> eval_operand (EL j chn) s = SOME (EL j ws))
Proof
  Induct_on `chn` using SNOC_INDUCT
  >- simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `chn = []`
  >- (gvs[] >> qexists_tac `[value]` >> simp[ao_word_chain_def]) >>
  drule_all ao_chain_edges_unsnoc >> strip_tac >>
  `(?word. eval_operand (LAST chn) s = SOME word /\
           value = (if word = 0w then 1w else 0w)) /\
   (!z. LAST chn = Var z ==> def_available_at fn target use_opt z)` by
    (irule ao_source_chain_edge_value >> simp[] >> metis_tac[LAST_SNOC]) >>
  first_x_assum (qspec_then `word` mp_tac) >> simp[] >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  qexists_tac `SNOC value ws` >> simp[] >>
  conj_tac
  >- (irule ao_word_chain_snoc >> simp[] >>
      Cases_on `ws` >> gvs[]) >>
  rpt strip_tac >> Cases_on `j < LENGTH chn`
  >- (simp[EL_SNOC] >> metis_tac[]) >>
  `j = LENGTH chn` by decide_tac >>
  gvs[] >> pure_rewrite_tac[EL_LENGTH_SNOC] >>
  qpat_x_assum `LENGTH ws = LENGTH chn`
    (fn th => pure_rewrite_tac[GSYM th]) >>
  simp[EL_LENGTH_SNOC]
QED

Theorem ao_source_selected_phi_chain_values:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  2 <= LENGTH trace /\ ao_source_trace ctx fn trace /\ LAST trace = (h,T,s) /\
  (!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
    lookup_var x (SND (SND (HD trace))) = NONE) /\
  ao_chain_edges (fn_insts fn) chn /\ chn <> [] /\
  eval_operand (LAST chn) s = SOME value /\
  MEM bb fn.fn_blocks /\ MEM phi bb.bb_instructions /\
  phi.inst_opcode = PHI /\ s.vs_prev_bb = SOME pred /\
  resolve_phi pred phi.inst_operands = SOME (LAST chn) ==>
  ?ws. LENGTH ws = LENGTH chn /\ ao_word_chain ws /\ LAST ws = value /\
       (!j. j < LENGTH chn ==> eval_operand (EL j chn) s = SOME (EL j ws))
Proof
  strip_tac >> drule ao_source_trace_selected_edge >> simp[] >>
  disch_then drule >> strip_tac >> PairCases_on `a` >> gvs[] >>
  `s.vs_labels = a2.vs_labels` by
    (drule ao_source_step_labels >> simp[]) >>
  `!op. eval_operand op s = eval_operand op a2` by
    (Cases >> simp[eval_operand_def]) >>
  drule ao_source_step_exit >> strip_tac >>
  rename1 `lookup_block a2.vs_current_bb fn.fn_blocks = SOME pred_bb` >>
  `!x. LAST chn = Var x ==> def_available_at fn pred_bb NONE x` by
    (rpt strip_tac >>
     `resolve_phi a2.vs_current_bb phi.inst_operands = SOME (Var x)` by metis_tac[] >>
     drule_all ao_selected_phi_available >> strip_tac >>
     `lookup_block pred_bb'.bb_label fn.fn_blocks = SOME pred_bb'` by
       (irule venomExecPropsTheory.MEM_lookup_block >>
        gvs[wf_function_def, fn_labels_def]) >> gvs[]) >>
  `!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
    lookup_var x (SND (SND (HD (front ++ [(a0,F,a2)])))) = NONE` by
    (Cases_on `front` >> gvs[] >> metis_tac[]) >>
  `?ws. LENGTH ws = LENGTH chn /\ ao_word_chain ws /\ LAST ws = value /\
    (!j. j < LENGTH chn ==> eval_operand (EL j chn) a2 = SOME (EL j ws))` by
    (`eval_operand (LAST chn) a2 = SOME value` by metis_tac[] >>
     qpat_x_assum `ao_source_trace ctx fn (front ++ [(a0,F,a2); (h,T,s)])` kall_tac >>
     drule_at (Pat `ao_source_trace _ _ _`) ao_source_chain_values >>
     simp[] >> disch_then (qspecl_then [`NONE`,`chn`,`value`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  qexists_tac `ws` >> simp[]
QED

Theorem ao_source_computed_chain_values:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ trace <> [] /\
  ao_source_trace ctx fn trace /\ LAST trace = (h,F,s) /\
  (!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
    lookup_var x (SND (SND (HD trace))) = NONE) /\
  ALOOKUP (ao_compute_fn_iszero_targets fn) v = SOME chn /\
  eval_operand (Var v) s = SOME value /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME target /\
  def_available_at fn target use_opt v /\
  (case use_opt of
     SOME use => get_instruction target s.vs_inst_idx = SOME use /\
                 use.inst_opcode <> PHI
   | NONE => ?term. get_instruction target s.vs_inst_idx = SOME term /\
                    is_terminator term.inst_opcode) ==>
  1 < LENGTH chn /\ LAST chn = Var v /\ ao_chain_edges (fn_insts fn) chn /\
  ?ws. LENGTH ws = LENGTH chn /\ ao_word_chain ws /\ LAST ws = value /\
       (!j. j < LENGTH chn ==> eval_operand (EL j chn) s = SOME (EL j ws))
Proof
  strip_tac >>
  fs[algebraicOptDefsTheory.ao_compute_fn_iszero_targets_def] >>
  drule ao_compute_iszero_targets_witnesses >> strip_tac >>
  drule ao_compute_iszero_targets_min_length >> strip_tac >> simp[] >>
  irule ao_source_chain_values >> simp[] >> metis_tac[]
QED

Theorem ao_source_selected_phi_computed_chain_values:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  2 <= LENGTH trace /\ ao_source_trace ctx fn trace /\ LAST trace = (h,T,s) /\
  (!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
    lookup_var x (SND (SND (HD trace))) = NONE) /\
  ALOOKUP (ao_compute_fn_iszero_targets fn) v = SOME chn /\
  eval_operand (Var v) s = SOME value /\
  MEM bb fn.fn_blocks /\ MEM phi bb.bb_instructions /\
  phi.inst_opcode = PHI /\ s.vs_prev_bb = SOME pred /\
  resolve_phi pred phi.inst_operands = SOME (Var v) ==>
  1 < LENGTH chn /\ LAST chn = Var v /\ ao_chain_edges (fn_insts fn) chn /\
  ?ws. LENGTH ws = LENGTH chn /\ ao_word_chain ws /\ LAST ws = value /\
       (!j. j < LENGTH chn ==> eval_operand (EL j chn) s = SOME (EL j ws))
Proof
  strip_tac >>
  fs[algebraicOptDefsTheory.ao_compute_fn_iszero_targets_def] >>
  drule ao_compute_iszero_targets_witnesses >> strip_tac >>
  drule ao_compute_iszero_targets_min_length >> strip_tac >> simp[] >>
  irule ao_source_selected_phi_chain_values >> simp[] >> metis_tac[]
QED
