(* One selected block's DLOAD pairs, rewritten throughout the function. *)
Theory mmDloadProofs
Ancestors
  venomFnInstsProofs
  mmWfProofs
  mmTransformSupply mmCopyEquiv dftGasFromListTraceDefs unitMemInv o1PassLift
  venomFnScheduleRunner passSharedDefs irSupply codegenReadyCompute dominatorProofs
  cfgNormBase venomWf stateEquiv dftBlockSim venomState venomInstProofs
  simplifyCfgMergeRuns singleUseExpansionSupplySim rangeAnalysisProofs
  venomExecSemantics finite_map venomExecProofs rich_list
  removeUnusedProofs execEquivProps stateEquivProofs simplifyCfgFrameRf o1ContractCfgNorm
  venomWfProps fnFrameStepsRevertForward dfgAnalysisProps mmScan mmTransform list option localPtrsProps unitShapeDefs

(* The cached equality is used only where the producer is available.  In
   particular, mere presence of an old loop iteration's output is not a
   sufficient availability test. *)
Definition mm_dload_cached_def:
  mm_dload_cached src out s <=>
    ?off. eval_operand src s = SOME off /\
      lookup_var out s = SOME
        (word_of_bytes T (0w:bytes32)
          (TAKE 32 (DROP (w2n off) s.vs_data_section ++ REPLICATE 32 0w)))
End

Theorem mm_dload_cached_establish[local]:
  eval_operand src s = SOME off /\ src <> Var out ==>
  mm_dload_cached src out
    (update_var out
      (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n off) s.vs_data_section ++ REPLICATE 32 0w))) s)
Proof
  Cases_on `src` >>
  simp[mm_dload_cached_def, eval_operand_def, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE]
QED

Theorem mm_dload_cached_load[local]:
  i.inst_opcode = DLOAD /\ i.inst_operands = [src] /\
  i.inst_outputs = [out] /\ src <> Var out /\
  step_inst fuel ctx i s = OK t ==>
  mm_dload_cached src out t
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_read1_def, AllCaseEqs()] >>
  irule mm_dload_cached_establish >> simp[]
QED

Theorem mm_dload_cached_step[local]:
  mm_dload_cached src out s /\
  step_inst fuel ctx i s = OK t /\ ~is_terminator i.inst_opcode /\
  ~MEM out i.inst_outputs /\
  (!v. src = Var v ==> ~MEM v i.inst_outputs) ==>
  mm_dload_cached src out t
Proof
  strip_tac >>
  `eval_operand src t = eval_operand src s` by
    metis_tac[eval_operand_step_pres] >>
  `eval_operand (Var out) t = eval_operand (Var out) s` by
    (irule eval_operand_step_pres >>
     qexistsl [`ctx`, `fuel`, `i`] >> simp[]) >>
  `t.vs_data_section = s.vs_data_section` by
    metis_tac[venomInstProofsTheory.step_preserves_data_section] >>
  gvs[mm_dload_cached_def, eval_operand_def]
QED

Definition mm_dload_ready_def:
  mm_dload_ready fn db (p:num) b (k:num) <=>
    fn_dominates fn db.bb_label b.bb_label /\ (db <> b \/ p < k)
End

Theorem mm_dload_ready_mono[local]:
  mm_dload_ready fn db p b k /\ k <= n ==>
  mm_dload_ready fn db p b n
Proof
  simp[mm_dload_ready_def] >> rpt strip_tac >> gvs[]
QED

Theorem mm_dload_ready_entry[local]:
  wf_function fn /\ MEM db fn.fn_blocks /\ MEM b fn.fn_blocks /\
  fn_entry_label fn = SOME b.bb_label ==>
  ~mm_dload_ready fn db p b 0
Proof
  strip_tac >> spose_not_then assume_tac >>
  gvs[mm_dload_ready_def, fn_dominates_def] >>
  `db.bb_label = b.bb_label` by
    (first_x_assum (qspec_then `[b.bb_label]` mp_tac) >>
     simp[is_fn_path_def]) >>
  metis_tac[same_label_same_block]
QED

Theorem mm_dload_ready_edge[local]:
  wf_function fn /\ MEM db fn.fn_blocks /\ MEM b fn.fn_blocks /\
  MEM c fn.fn_blocks /\ p < LENGTH db.bb_instructions /\
  fn_reachable fn b.bb_label /\ fn_cfg_edge fn b.bb_label c.bb_label /\
  mm_dload_ready fn db p c 0 ==>
  mm_dload_ready fn db p b (LENGTH b.bb_instructions)
Proof
  simp[mm_dload_ready_def] >> strip_tac >>
  `db.bb_label <> c.bb_label` by metis_tac[same_label_same_block] >>
  `fn_dominates fn db.bb_label b.bb_label` by
    metis_tac[fn_dominates_predecessor] >>
  Cases_on `db = b` >> gvs[]
QED

Theorem mm_dload_ready_use[local]:
  wf_function fn /\ wf_ssa fn /\ MEM db fn.fn_blocks /\
  p < LENGTH db.bb_instructions /\ MEM out (EL p db.bb_instructions).inst_outputs /\
  MEM b fn.fn_blocks /\ q < LENGTH b.bb_instructions /\
  (EL q b.bb_instructions).inst_opcode <> PHI /\
  MEM (Var out) (EL q b.bb_instructions).inst_operands ==>
  mm_dload_ready fn db p b q
Proof
  strip_tac >>
  `def_available_at fn b (SOME (EL q b.bb_instructions)) out` by
    (gvs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[EL_MEM]) >>
  gvs[def_available_at_def] >>
  `def_bb = db /\ def_inst = EL p db.bb_instructions` by
    (irule ssa_unique_output_block >> metis_tac[wf_ssa_def, EL_MEM]) >>
  gvs[mm_dload_ready_def] >> strip_tac >> gvs[] >>
  `fn_inst_ids_distinct fn` by gvs[wf_function_def] >>
  `i = p /\ j = q` by metis_tac[inst_ids_el_eq, arithmeticTheory.LESS_TRANS] >>
  gvs[]
QED

Theorem mm_dload_ready_output_not_written[local]:
  wf_function fn /\ wf_ssa fn /\ MEM db fn.fn_blocks /\
  p < LENGTH db.bb_instructions /\ MEM out (EL p db.bb_instructions).inst_outputs /\
  MEM b fn.fn_blocks /\ k < LENGTH b.bb_instructions /\
  mm_dload_ready fn db p b k ==>
  ~MEM out (EL k b.bb_instructions).inst_outputs
Proof
  strip_tac >> strip_tac >>
  `db = b /\ EL p db.bb_instructions = EL k b.bb_instructions` by
    (irule ssa_unique_output_block >> metis_tac[wf_ssa_def, EL_MEM]) >>
  `p = k` by metis_tac[inst_ids_el_eq, wf_function_def] >>
  gvs[mm_dload_ready_def]
QED

Theorem mm_dload_ready_input_not_written[local]:
  wf_function fn /\ wf_ssa fn /\ MEM db fn.fn_blocks /\
  p < LENGTH db.bb_instructions /\
  (EL p db.bb_instructions).inst_opcode <> PHI /\
  MEM (Var v) (EL p db.bb_instructions).inst_operands /\
  MEM b fn.fn_blocks /\ k < LENGTH b.bb_instructions /\
  mm_dload_ready fn db p b k ==>
  ~MEM v (EL k b.bb_instructions).inst_outputs
Proof
  strip_tac >> strip_tac >>
  `mm_dload_ready fn b k db p` by
    (irule mm_dload_ready_use >> metis_tac[]) >>
  qspec_then `fn` strip_assume_tac fn_dominates_strict_measure >>
  `db.bb_label = b.bb_label` by
    (spose_not_then assume_tac >>
     gvs[mm_dload_ready_def] >>
     `depth db.bb_label < depth b.bb_label /\
      depth b.bb_label < depth db.bb_label` by metis_tac[] >>
     decide_tac) >>
  `db = b` by metis_tac[same_label_same_block] >>
  gvs[mm_dload_ready_def]
QED

Theorem mm_dload_source_distinct[local]:
  wf_function fn /\ wf_ssa fn /\ MEM db fn.fn_blocks /\
  p < LENGTH db.bb_instructions /\
  (EL p db.bb_instructions).inst_opcode = DLOAD /\
  (EL p db.bb_instructions).inst_operands = [src] /\
  (EL p db.bb_instructions).inst_outputs = [out] ==>
  src <> Var out
Proof
  strip_tac >> strip_tac >>
  `mm_dload_ready fn db p db p` by
    (irule mm_dload_ready_use >> simp[]) >>
  gvs[mm_dload_ready_def]
QED

Theorem mm_dload_cached_advance[local]:
  wf_function fn /\ wf_ssa fn /\ MEM db fn.fn_blocks /\ MEM b fn.fn_blocks /\
  p < LENGTH db.bb_instructions /\ k < LENGTH b.bb_instructions /\
  (EL p db.bb_instructions).inst_opcode = DLOAD /\
  (EL p db.bb_instructions).inst_operands = [src] /\
  (EL p db.bb_instructions).inst_outputs = [out] /\
  ~is_terminator (EL k b.bb_instructions).inst_opcode /\
  step_inst fuel ctx (EL k b.bb_instructions) s = OK t /\
  (mm_dload_ready fn db p b k ==> mm_dload_cached src out s) /\
  mm_dload_ready fn db p b (SUC k) ==>
  mm_dload_cached src out t
Proof
  strip_tac >> Cases_on `db = b /\ p = k`
  >- (gvs[] >>
      `src <> Var out` by metis_tac[mm_dload_source_distinct] >>
      drule_all mm_dload_cached_load >> simp[]) >>
  `mm_dload_ready fn db p b k` by
    (Cases_on `db = b` >> fs[mm_dload_ready_def]) >>
  `~MEM out (EL k b.bb_instructions).inst_outputs` by
    (irule mm_dload_ready_output_not_written >> metis_tac[MEM]) >>
  `!v. src = Var v ==> ~MEM v (EL k b.bb_instructions).inst_outputs` by
    (gen_tac >> disch_tac >> irule mm_dload_ready_input_not_written >>
     simp[] >> qexistsl [`db`, `fn`, `p`] >> simp[]) >>
  metis_tac[mm_dload_cached_step]
QED

Theorem mm_dload_cached_phis[local]:
  !insts s t.
  mm_dload_cached src out s /\ eval_phis s insts = OK t /\
  EVERY (\i. i.inst_opcode = PHI ==>
    ~MEM out i.inst_outputs /\ (!v. src = Var v ==> ~MEM v i.inst_outputs)) insts ==>
  mm_dload_cached src out t
Proof
  Induct >> simp[eval_phis_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> fs[eval_phis_def] >>
  gvs[AllCaseEqs()] >>
  rename1 `eval_phis s insts = OK tail` >>
  `mm_dload_cached src out tail` by metis_tac[] >>
  qpat_x_assum `eval_one_phi _ _ = _` mp_tac >>
  simp[eval_one_phi_def, AllCaseEqs()] >> strip_tac >>
  Cases_on `src` >>
  gvs[mm_dload_cached_def, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem mm_dload_cached_terminator[local]:
  mm_dload_cached src out s /\
  step_inst fuel ctx i s = OK t /\ is_terminator i.inst_opcode ==>
  mm_dload_cached src out t
Proof
  strip_tac >> drule_all scfg_terminator_jump >> strip_tac >>
  qpat_x_assum `t = _` SUBST1_TAC >>
  Cases_on `src` >>
  gvs[mm_dload_cached_def, eval_operand_def, lookup_var_def, jump_to_def]
QED

Theorem mm_dload_ready_phi_entry[local]:
  p < LENGTH db.bb_instructions /\
  (EL p db.bb_instructions).inst_opcode = DLOAD /\
  mm_dload_ready fn db p c (phi_prefix_length c.bb_instructions) ==>
  mm_dload_ready fn db p c 0
Proof
  strip_tac >> Cases_on `db = c` >> fs[mm_dload_ready_def] >>
  drule venomExecProofsTheory.phi_prefix_length_el_phi >> simp[]
QED

Theorem mm_dload_cached_transfer[local]:
  fn_inst_wf fn /\ wf_function fn /\ wf_ssa fn /\
  MEM db fn.fn_blocks /\ MEM b fn.fn_blocks /\ MEM c fn.fn_blocks /\
  p < LENGTH db.bb_instructions /\ k < LENGTH b.bb_instructions /\
  (EL p db.bb_instructions).inst_opcode = DLOAD /\
  (EL p db.bb_instructions).inst_operands = [src] /\
  (EL p db.bb_instructions).inst_outputs = [out] /\
  fn_reachable fn b.bb_label /\ s.vs_current_bb = b.bb_label /\
  t.vs_current_bb = c.bb_label /\
  is_terminator (EL k b.bb_instructions).inst_opcode /\
  step_inst fuel ctx (EL k b.bb_instructions) s = OK t /\ ~t.vs_halted /\
  eval_phis t c.bb_instructions = OK sp /\
  (mm_dload_ready fn db p b k ==> mm_dload_cached src out s) /\
  mm_dload_ready fn db p c (phi_prefix_length c.bb_instructions) ==>
  mm_dload_cached src out sp
Proof
  strip_tac >>
  `fn_cfg_edge fn b.bb_label c.bb_label` by
    (`bb_well_formed b /\ EVERY inst_wf b.bb_instructions` by
       (fs[wf_function_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
     metis_tac[sue_terminator_cfg_edge]) >>
  `mm_dload_ready fn db p c 0` by metis_tac[mm_dload_ready_phi_entry] >>
  `mm_dload_ready fn db p b (LENGTH b.bb_instructions)` by
    metis_tac[mm_dload_ready_edge] >>
  `mm_dload_ready fn db p b k` by
    (Cases_on `db = b` >> fs[mm_dload_ready_def] >>
     `p <> k` by (strip_tac >> gvs[venomInstTheory.is_terminator_def]) >>
     `k = PRE (LENGTH b.bb_instructions)` by
       metis_tac[wf_function_def, bb_well_formed_def] >> decide_tac) >>
  `mm_dload_cached src out t` by metis_tac[mm_dload_cached_terminator] >>
  irule mm_dload_cached_phis >> qexistsl [`c.bb_instructions`, `t`] >> simp[] >>
  simp[EVERY_EL] >> gen_tac >> strip_tac >> disch_tac >> conj_tac
  >- (irule mm_dload_ready_output_not_written >> simp[] >>
      qexistsl [`db`, `fn`, `p`] >> simp[] >>
      metis_tac[mm_dload_ready_mono, arithmeticTheory.ZERO_LESS_EQ]) >>
  gen_tac >> disch_tac >> irule mm_dload_ready_input_not_written >>
  simp[] >> qexistsl [`db`, `fn`, `p`] >> simp[] >>
  metis_tac[mm_dload_ready_mono, arithmeticTheory.ZERO_LESS_EQ]
QED

Inductive mm_dload_frame_reachable:
  (!b u sp.
    fn_entry_label fn = SOME b.bb_label /\ MEM b fn.fn_blocks /\
    u.vs_current_bb = b.bb_label /\ u.vs_inst_idx = 0 /\
    eval_phis u b.bb_instructions = OK sp ==>
    mm_dload_frame_reachable ctx fn b
      (sp with vs_inst_idx := phi_prefix_length b.bb_instructions)) /\
  (!b s i fuel t.
    mm_dload_frame_reachable ctx fn b s /\
    get_instruction b s.vs_inst_idx = SOME i /\
    ~is_terminator i.inst_opcode /\ step_inst fuel ctx i s = OK t ==>
    mm_dload_frame_reachable ctx fn b
      (t with vs_inst_idx := SUC s.vs_inst_idx)) /\
  (!b s i fuel t c sp.
    mm_dload_frame_reachable ctx fn b s /\
    get_instruction b s.vs_inst_idx = SOME i /\
    is_terminator i.inst_opcode /\ step_inst fuel ctx i s = OK t /\
    ~t.vs_halted /\ lookup_block t.vs_current_bb fn.fn_blocks = SOME c /\
    eval_phis t c.bb_instructions = OK sp ==>
    mm_dload_frame_reachable ctx fn c
      (sp with vs_inst_idx := phi_prefix_length c.bb_instructions))
End

Theorem mm_dload_frame_reachable_location[local]:
  !ctx fn b s. mm_dload_frame_reachable ctx fn b s ==>
  fn_inst_wf fn /\ wf_function fn ==>
  MEM b fn.fn_blocks /\ s.vs_current_bb = b.bb_label /\
  fn_reachable fn b.bb_label
Proof
  ntac 2 gen_tac >> ho_match_mp_tac mm_dload_frame_reachable_ind >> rpt conj_tac
  >- (rpt strip_tac >>
      fs[fn_reachable_def] >>
      metis_tac[eval_phis_preserves_current_bb, relationTheory.RTC_REFL])
  >- (rpt gen_tac >> strip_tac >> strip_tac >> fs[] >>
      drule_all venomInstProofsTheory.step_preserves_control_flow >> simp[]) >>
  rpt gen_tac >> strip_tac >> strip_tac >> fs[] >>
  drule simplifyCfgDefsTheory.lookup_block_member_label >> strip_tac >>
  `bb_well_formed b /\ EVERY inst_wf b.bb_instructions` by
    (fs[wf_function_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  fs[venomInstTheory.get_instruction_def, AllCaseEqs()] >>
  `fn_cfg_edge fn b.bb_label b'.bb_label` by
    metis_tac[sue_terminator_cfg_edge] >>
  metis_tac[eval_phis_preserves_current_bb, fn_reachable_step]
QED

Theorem mm_dload_cached_index[local,simp]:
  mm_dload_cached src out (s with vs_inst_idx := n) = mm_dload_cached src out s
Proof
  simp[mm_dload_cached_def, instIdxIndepTheory.eval_op_inst_idx, lookup_var_def]
QED

Theorem mm_dload_frame_reachable_cached[local]:
  !ctx fn b s. mm_dload_frame_reachable ctx fn b s ==>
  !db p src out.
  fn_inst_wf fn /\ wf_function fn /\ wf_ssa fn /\ MEM db fn.fn_blocks /\
  p < LENGTH db.bb_instructions /\
  (EL p db.bb_instructions).inst_opcode = DLOAD /\
  (EL p db.bb_instructions).inst_operands = [src] /\
  (EL p db.bb_instructions).inst_outputs = [out] /\
  mm_dload_ready fn db p b s.vs_inst_idx ==>
  mm_dload_cached src out s
Proof
  ntac 2 gen_tac >> ho_match_mp_tac mm_dload_frame_reachable_strongind >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> simp[] >> strip_tac >>
      `mm_dload_ready fn db p b 0` by metis_tac[mm_dload_ready_phi_entry] >>
      metis_tac[mm_dload_ready_entry])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> simp[] >> strip_tac >>
      `MEM b fn.fn_blocks` by metis_tac[mm_dload_frame_reachable_location] >>
      fs[venomInstTheory.get_instruction_def, AllCaseEqs()] >>
      irule mm_dload_cached_advance >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> simp[] >> strip_tac >>
  `MEM b fn.fn_blocks /\ s.vs_current_bb = b.bb_label /\
   fn_reachable fn b.bb_label` by
    metis_tac[mm_dload_frame_reachable_location] >>
  drule simplifyCfgDefsTheory.lookup_block_member_label >> strip_tac >>
  fs[venomInstTheory.get_instruction_def, AllCaseEqs()] >>
  irule mm_dload_cached_transfer >> simp[] >> metis_tac[]
QED

Theorem mm_dload_frame_reachable_use[local]:
  mm_dload_frame_reachable ctx fn b s /\
  fn_inst_wf fn /\ wf_function fn /\ wf_ssa fn /\ MEM db fn.fn_blocks /\
  p < LENGTH db.bb_instructions /\
  (EL p db.bb_instructions).inst_opcode = DLOAD /\
  (EL p db.bb_instructions).inst_operands = [src] /\
  (EL p db.bb_instructions).inst_outputs = [out] /\
  get_instruction b s.vs_inst_idx = SOME i /\
  i.inst_opcode <> PHI /\ MEM (Var out) i.inst_operands ==>
  mm_dload_cached src out s
Proof
  strip_tac >>
  `MEM b fn.fn_blocks` by metis_tac[mm_dload_frame_reachable_location] >>
  fs[venomInstTheory.get_instruction_def, AllCaseEqs()] >>
  `mm_dload_ready fn db p b s.vs_inst_idx` by
    (irule mm_dload_ready_use >> simp[]) >>
  metis_tac[mm_dload_frame_reachable_cached]
QED

Theorem mm_dload_frame_block_exit[local]:
  !n s r.
  n = LENGTH b.bb_instructions - s.vs_inst_idx /\
  mm_dload_frame_reachable ctx fn b s /\
  exec_block fuel ctx b s = OK r ==>
  ?u i. mm_dload_frame_reachable ctx fn b u /\
    get_instruction b u.vs_inst_idx = SOME i /\
    is_terminator i.inst_opcode /\ step_inst fuel ctx i u = OK r
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def] >>
  Cases_on `get_instruction b s.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction b s.vs_inst_idx = SOME i` >>
  Cases_on `step_inst fuel ctx i s` >> simp[] >>
  rename1 `step_inst fuel ctx i s = OK t` >>
  Cases_on `is_terminator i.inst_opcode` >> simp[]
  >- (Cases_on `t.vs_halted` >> simp[] >> strip_tac >>
      qexistsl [`s`, `i`] >> simp[]) >>
  strip_tac >>
  `mm_dload_frame_reachable ctx fn b (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    metis_tac[mm_dload_frame_reachable_rules] >>
  first_x_assum irule >> simp[] >>
  qexists `t with vs_inst_idx := SUC s.vs_inst_idx` >> simp[] >>
  fs[venomInstTheory.get_instruction_def, AllCaseEqs()]
QED

(* The block and blocks clauses supply the mutual induction hypothesis
   needed to exclude root-frame events from nested calls in the step clause. *)
Theorem mm_dload_frame_trace[local]:
  (!p d fuel ctx fn inst s.
    !e id f i t. ~MEM (([],e,id),f,i,t) (trace_step p d fuel ctx fn inst s)) /\
  (!p d fuel ctx fn bb s.
    (p = [] ==> mm_dload_frame_reachable ctx fn bb s) ==>
    !e id f i t. MEM (([],e,id),f,i,t) (trace_block p d fuel ctx fn bb s) ==>
      p = [] /\ f = fn /\
      ?b. mm_dload_frame_reachable ctx fn b t /\
          get_instruction b t.vs_inst_idx = SOME i) /\
  (!p d fuel ctx fn s.
    (!bb sp. p = [] /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      eval_phis s bb.bb_instructions = OK sp ==>
      mm_dload_frame_reachable ctx fn bb
        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)) ==>
    !e id f i t. MEM (([],e,id),f,i,t) (trace_blocks p d fuel ctx fn s) ==>
      p = [] /\ f = fn /\
      ?b. mm_dload_frame_reachable ctx fn b t /\
          get_instruction b t.vs_inst_idx = SOME i)
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume mm_dload_frame_trace[step]:
  rpt gen_tac >> strip_tac >>
  simp[Once trace_defs] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >> gvs[]
QED

Resume mm_dload_frame_trace[block]:
  rpt gen_tac >> strip_tac >> disch_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx` >- (once_rewrite_tac[dftGasFromListTraceDefsTheory.trace_defs] >> simp[]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  once_rewrite_tac[dftGasFromListTraceDefsTheory.trace_defs] >>
  simp[MEM_APPEND] >> rpt gen_tac >> strip_tac
  >- (gvs[] >> metis_tac[]) >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[] >>
  rename1 `step_inst fuel ctx inst s = OK out` >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  first_x_assum irule >> simp[] >>
  metis_tac[mm_dload_frame_reachable_rules]
QED

Resume mm_dload_frame_trace[blocks]:
  rpt gen_tac >> strip_tac >> disch_tac >>
  Cases_on `fuel` >- simp[] >>
  rename1 `trace_blocks p d (SUC k) ctx fn s` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (once_rewrite_tac[dftGasFromListTraceDefsTheory.trace_defs] >> simp[]) >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  once_rewrite_tac[dftGasFromListTraceDefsTheory.trace_defs] >>
  qpat_assum `lookup_block _ _ = SOME bb` (fn th => simp[NoAsms, th]) >>
  qpat_assum `eval_phis _ _ = _` (fn th => simp[NoAsms, th, MEM_APPEND]) >>
  rename1 `eval_phis s bb.bb_instructions = OK sp` >>
  rpt gen_tac >> strip_tac
  >- metis_tac[] >>
  Cases_on `exec_block k ctx bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  qpat_x_assum `MEM _ _` mp_tac >> simp[NoAsms] >> disch_tac >>
  rename1 `exec_block k ctx bb _ = OK out` >>
  Cases_on `out.vs_halted` >>
  qpat_x_assum `MEM _ _` mp_tac >>
  pop_assum (fn th => simp[NoAsms, th] >> assume_tac th) >> disch_tac >>
  qpat_x_assum `!fuel' bb sp s''. _` irule >> simp[] >>
  qexistsl [`e`, `id`] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
  `mm_dload_frame_reachable ctx fn bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by metis_tac[] >>
  drule_at (Pat `exec_block _ _ _ _ = _`) mm_dload_frame_block_exit >>
  disch_then (qspecl_then [`fn`, `LENGTH bb.bb_instructions -
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions).vs_inst_idx`] mp_tac) >>
  simp[] >>
  strip_tac >> metis_tac[mm_dload_frame_reachable_rules]) >> simp[]
QED

Finalise mm_dload_frame_trace

Theorem mm_dload_pair_provenance[local]:
  MEM dp (find_dload_pairs (dfg_build_function fn) bb.bb_instructions) ==>
  ?ld st v.
    MEM ld bb.bb_instructions /\
    ld.inst_opcode = DLOAD /\ ld.inst_operands = [dp.dp_src] /\
    ld.inst_outputs = [v] /\ ld.inst_id = dp.dp_dload_id /\
    MEM st (fn_insts fn) /\ st.inst_opcode = MSTORE /\
    st.inst_operands = [dp.dp_dst; Var v] /\
    st.inst_id = dp.dp_mstore_id /\ dp.dp_dst <> Var v /\
    dfg_get_uses (dfg_build_function fn) v = [st] /\
    (!u. MEM u (fn_insts fn) /\ MEM (Var v) u.inst_operands ==> u = st)
Proof
  simp[find_dload_pairs_def, MEM_MAP, MEM_FILTER] >>
  strip_tac >>
  gvs[IS_SOME_EXISTS] >>
  gvs[find_dload_mstore_pair_def, AllCaseEqs()] >>
  rename1 `dfg_get_uses (dfg_build_function fn) v = [st]` >>
  `MEM st (fn_insts fn)` by
    metis_tac[dfg_build_function_uses_sound, MEM] >>
  rename1 `MEM ld bb.bb_instructions` >>
  qexistsl [`ld`, `st`, `v`] >> simp[] >>
  rpt strip_tac >>
  `!ops. MEM (Var v) ops ==> MEM v (venomInst$operand_vars ops)` by
    (Induct >> simp[venomInstTheory.operand_vars_def] >>
     Cases_on `h` >> simp[venomInstTheory.operand_var_def] >> metis_tac[]) >>
  `MEM v (venomInst$operand_vars u.inst_operands)` by metis_tac[] >>
  drule_all dfg_build_function_uses_complete >> simp[]
QED

Theorem mm_dload_frame_store_cached[local]:
  fn_inst_wf fn /\ wf_function fn /\ wf_ssa fn /\ MEM bb fn.fn_blocks /\
  MEM dp (find_dload_pairs (dfg_build_function fn) bb.bb_instructions) /\
  mm_dload_frame_reachable ctx fn b t /\
  get_instruction b t.vs_inst_idx = SOME i /\
  i.inst_id = dp.dp_mstore_id ==>
  ?v. i.inst_opcode = MSTORE /\ i.inst_operands = [dp.dp_dst; Var v] /\
      mm_dload_cached dp.dp_src v t
Proof
  strip_tac >> drule mm_dload_pair_provenance >> strip_tac >>
  `MEM b fn.fn_blocks` by metis_tac[mm_dload_frame_reachable_location] >>
  `MEM i (fn_insts fn)` by
    (simp[venomInstTheory.fn_insts_def, MEM_fn_insts_blocks_iff] >>
     qexists `b` >> simp[] >>
     fs[venomInstTheory.get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  `i = st` by metis_tac[wf_function_def, fn_insts_id_unique] >>
  qexists `v` >> simp[] >>
  qpat_x_assum `MEM ld bb.bb_instructions` mp_tac >>
  simp[MEM_EL] >> strip_tac >>
  irule mm_dload_frame_reachable_use >> simp[] >>
  goal_assum (drule_at (Pat `mm_dload_frame_reachable _ _ _ _`)) >> simp[] >>
  metis_tac[]
QED

Theorem mm_dload_pair_operands_avoid[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  MEM a (find_dload_pairs (dfg_build_function fn) bb.bb_instructions) /\
  MEM b (find_dload_pairs (dfg_build_function fn) bb.bb_instructions) /\
  MEM ld bb.bb_instructions /\ ld.inst_id = a.dp_dload_id /\
  ld.inst_opcode = DLOAD /\ ld.inst_outputs = [v] /\
  ld.inst_operands = [a.dp_src] ==>
  b.dp_src <> Var v /\ b.dp_dst <> Var v
Proof
  strip_tac >>
  qpat_x_assum `MEM a _` (strip_assume_tac o MATCH_MP mm_dload_pair_provenance) >>
  qpat_x_assum `MEM b _` (strip_assume_tac o MATCH_MP mm_dload_pair_provenance) >>
  `!i. MEM i bb.bb_instructions ==> MEM i (fn_insts fn)` by
    metis_tac[MEM_fn_insts_blocks_iff, venomInstTheory.fn_insts_def] >>
  `fn_inst_ids_distinct fn` by gvs[wf_function_def] >>
  `ld = ld'` by metis_tac[fn_insts_id_unique] >>
  `v = v'` by metis_tac[CONS_11] >>
  conj_tac
  >- (strip_tac >>
      `ld'' = st` by metis_tac[MEM] >> gvs[]) >>
  strip_tac >>
  `st' = st` by metis_tac[MEM] >>
  `v'' = v'` by metis_tac[CONS_11, venomStateTheory.operand_11] >>
  metis_tac[]
QED

Theorem mm_dload_transform_cases[local]:
  !pairs i.
  (transform_dload_inst pairs i = mk_nop_from i /\
     ?dp. MEM dp pairs /\ dp.dp_dload_id = i.inst_id) \/
  (transform_dload_inst pairs i = i /\
     (!dp. MEM dp pairs ==> dp.dp_dload_id <> i.inst_id /\
                                dp.dp_mstore_id <> i.inst_id)) \/
  (?dp. MEM dp pairs /\ dp.dp_mstore_id = i.inst_id /\
        transform_dload_inst pairs i =
          mk_dloadbytes_inst i dp.dp_src dp.dp_dst)
Proof
  rpt gen_tac >>
  Cases_on `EXISTS (\dp. dp.dp_dload_id = i.inst_id) pairs`
  >- (disj1_tac >> simp[transform_dload_inst_def] >>
      gvs[EXISTS_MEM] >> metis_tac[]) >>
  Cases_on `FIND (\dp. dp.dp_mstore_id = i.inst_id) pairs`
  >- (disj2_tac >> disj1_tac >> simp[transform_dload_inst_def] >>
      `!dp. MEM dp pairs ==> dp.dp_mstore_id <> i.inst_id` by
        (qpat_x_assum `FIND _ _ = NONE` mp_tac >>
         Induct_on `pairs` >> simp[FIND_thm] >>
         rpt strip_tac >> gvs[] >> metis_tac[]) >>
      gvs[EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  disj2_tac >> disj2_tac >>
  drule_then assume_tac venomExecProofsTheory.FIND_MEM >>
  drule_then assume_tac venomExecProofsTheory.FIND_P >>
  qexists `x` >> simp[transform_dload_inst_def] >> gvs[]
QED

Theorem mm_dload_transform_no_removed_use[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions /\
  MEM a pairs /\ MEM ld bb.bb_instructions /\
  ld.inst_id = a.dp_dload_id /\ ld.inst_opcode = DLOAD /\
  ld.inst_outputs = [v] /\ ld.inst_operands = [a.dp_src] /\
  MEM i (fn_insts fn) ==>
  ~MEM (Var v) (transform_dload_inst pairs i).inst_operands
Proof
  strip_tac >>
  qspecl_then [`pairs`, `i`] strip_assume_tac mm_dload_transform_cases
  >- simp[mk_nop_from_def]
  >- (simp[] >> strip_tac >>
      `MEM a (find_dload_pairs (dfg_build_function fn) bb.bb_instructions)` by metis_tac[] >>
      drule_then strip_assume_tac mm_dload_pair_provenance >>
      `!j. MEM j bb.bb_instructions ==> MEM j (fn_insts fn)` by
        metis_tac[MEM_fn_insts_blocks_iff, venomInstTheory.fn_insts_def] >>
      `fn_inst_ids_distinct fn` by gvs[wf_function_def] >>
      `ld = ld'` by metis_tac[fn_insts_id_unique] >>
      `v = v'` by metis_tac[CONS_11] >>
      `i = st` by metis_tac[] >>
      metis_tac[]) >>
  `dp.dp_src <> Var v /\ dp.dp_dst <> Var v` by
    (irule mm_dload_pair_operands_avoid >> metis_tac[]) >>
  simp[mk_dloadbytes_inst_def] >> metis_tac[]
QED

Theorem mm_dload_transform_id_outputs[local]:
  (transform_dload_inst pairs i).inst_id = i.inst_id /\
  (!v. MEM v (transform_dload_inst pairs i).inst_outputs ==>
       MEM v i.inst_outputs)
Proof
  qspecl_then [`pairs`, `i`] strip_assume_tac mm_dload_transform_cases >>
  simp[mk_nop_from_def, mk_dloadbytes_inst_def]
QED

Theorem mm_dload_function_entry[local]:
  fn_entry_label (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks) =
  fn_entry_label fn
Proof
  Cases_on `fn.fn_blocks` >>
  simp[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def, transform_block_dload_def]
QED

Theorem mm_dload_transform_control[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions /\
  MEM i (fn_insts fn) ==>
  (is_terminator (transform_dload_inst pairs i).inst_opcode =
     is_terminator i.inst_opcode) /\
  (((transform_dload_inst pairs i).inst_opcode = PHI) = (i.inst_opcode = PHI)) /\
  ((is_terminator i.inst_opcode \/ i.inst_opcode = PHI) ==>
     transform_dload_inst pairs i = i)
Proof
  strip_tac >>
  qspecl_then [`pairs`, `i`] strip_assume_tac mm_dload_transform_cases
  >- (`MEM dp (find_dload_pairs (dfg_build_function fn) bb.bb_instructions)` by metis_tac[] >>
      drule_then strip_assume_tac mm_dload_pair_provenance >>
      `MEM ld (fn_insts fn)` by
        metis_tac[MEM_fn_insts_blocks_iff, venomInstTheory.fn_insts_def] >>
      `i = ld` by metis_tac[fn_insts_id_unique, wf_function_def] >>
      simp[mk_nop_from_def, venomInstTheory.is_terminator_def])
  >- simp[] >>
  `MEM dp (find_dload_pairs (dfg_build_function fn) bb.bb_instructions)` by metis_tac[] >>
  drule_then strip_assume_tac mm_dload_pair_provenance >>
  `i = st` by metis_tac[fn_insts_id_unique, wf_function_def] >>
  simp[mk_dloadbytes_inst_def, venomInstTheory.is_terminator_def]
QED

Theorem mm_dload_operand_origin[local]:
  MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions /\
  MEM i (fn_insts fn) /\
  MEM op (transform_dload_inst pairs i).inst_operands ==>
  op = Lit 32w \/ MEM op i.inst_operands \/
  ?ld. MEM ld (fn_insts fn) /\ MEM op ld.inst_operands
Proof
  strip_tac >>
  qspecl_then [`pairs`, `i`] strip_assume_tac mm_dload_transform_cases
  >- gvs[mk_nop_from_def]
  >- metis_tac[] >>
  gvs[mk_dloadbytes_inst_def] >>
  `MEM dp (find_dload_pairs (dfg_build_function fn) bb.bb_instructions)` by metis_tac[] >>
  drule_then strip_assume_tac mm_dload_pair_provenance >>
  `MEM ld (fn_insts fn)` by
    metis_tac[MEM_fn_insts_blocks_iff, venomInstTheory.fn_insts_def] >>
  metis_tac[MEM]
QED

Theorem mm_dload_function_vars[local]:
  MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions ==>
  !v. MEM v (fn_ir_vars
    (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks)) ==>
  MEM v (fn_ir_vars fn)
Proof
  strip_tac >>
  simp[fn_ir_vars_def, block_ir_vars_def, MEM_FLAT, MEM_MAP,
       transform_block_dload_def, PULL_EXISTS] >>
  rpt strip_tac >> gvs[] >>
  rename1 `MEM i b.bb_instructions` >>
  `MEM i (fn_insts fn)` by
    metis_tac[MEM_fn_insts_blocks_iff, venomInstTheory.fn_insts_def] >>
  gvs[inst_ir_vars_def, venomInstTheory.inst_uses_def,
      passSharedDefsTheory.MEM_operand_vars_eq_Var]
  >- metis_tac[mm_dload_transform_id_outputs] >>
  `MEM (Var v) i.inst_operands \/
   ?ld. MEM ld (fn_insts fn) /\ MEM (Var v) ld.inst_operands` by
    metis_tac[mm_dload_operand_origin, venomStateTheory.operand_distinct] >>
  gvs[venomInstTheory.fn_insts_def, MEM_fn_insts_blocks_iff] >>
  metis_tac[]
QED

Theorem mm_dload_function_labels[local]:
  MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions ==>
  !l. MEM l (fn_ir_labels
    (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks)) ==>
  MEM l (fn_ir_labels fn)
Proof
  strip_tac >>
  simp[fn_ir_labels_def, block_ir_labels_def, inst_ir_labels_def,
       MEM_operand_ir_labels, MEM_FLAT, MEM_MAP,
       transform_block_dload_def, PULL_EXISTS] >>
  rpt strip_tac >> gvs[]
  >- metis_tac[] >>
  rename1 `MEM i b.bb_instructions` >>
  `MEM i (fn_insts fn)` by
    metis_tac[MEM_fn_insts_blocks_iff, venomInstTheory.fn_insts_def] >>
  `MEM (Label l) i.inst_operands \/
   ?ld. MEM ld (fn_insts fn) /\ MEM (Label l) ld.inst_operands` by
    metis_tac[mm_dload_operand_origin, venomStateTheory.operand_distinct] >>
  gvs[venomInstTheory.fn_insts_def, MEM_fn_insts_blocks_iff] >>
  metis_tac[]
QED

Theorem mm_dload_function_ids[local]:
  fn_ir_inst_ids
    (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks) =
  fn_ir_inst_ids fn
Proof
  simp[fn_ir_inst_ids_def, block_ir_inst_ids_def, transform_block_dload_def,
       MAP_MAP_o, combinTheory.o_DEF] >>
  AP_TERM_TAC >> irule MAP_CONG >> simp[] >> rpt strip_tac >>
  simp[block_ir_inst_ids_def] >>
  irule MAP_CONG >> simp[mm_dload_transform_id_outputs]
QED

Theorem mm_dload_function_supply[local]:
  ir_supply_covers_fn supply fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions ==>
  ir_supply_covers_fn supply
    (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks)
Proof
  simp[ir_supply_covers_fn_def, mm_dload_function_ids, list_subset_def, EVERY_MEM] >>
  metis_tac[mm_dload_function_vars, mm_dload_function_labels]
QED

Theorem mm_dload_function_cfg[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions ==>
  fn_cfg_edge (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks) =
  fn_cfg_edge fn
Proof
  strip_tac >> simp[FUN_EQ_THM, fn_cfg_edge_def, MEM_MAP] >>
  rpt gen_tac >>
  `!b. MEM b fn.fn_blocks ==>
    (transform_block_dload pairs b).bb_label = b.bb_label /\
    bb_succs (transform_block_dload pairs b) = bb_succs b` by
    (rpt strip_tac >- simp[transform_block_dload_def] >>
     gvs[] >> irule selected_dload_succs >> metis_tac[wf_function_def]) >>
  metis_tac[]
QED

Theorem mm_dload_function_path[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions ==>
  !path. is_fn_path
    (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks) path =
    is_fn_path fn path
Proof
  strip_tac >>
  `fn_cfg_edge (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks) =
   fn_cfg_edge fn` by metis_tac[mm_dload_function_cfg] >>
  Induct >> simp[is_fn_path_def] >> Cases_on `path` >> gvs[is_fn_path_def]
QED

Theorem mm_dload_function_dominates[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions ==>
  !d n. fn_dominates
    (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks) d n =
    fn_dominates fn d n
Proof
  strip_tac >>
  `fn_cfg_edge (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks) =
   fn_cfg_edge fn` by metis_tac[mm_dload_function_cfg] >>
  `!p. is_fn_path (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks) p =
       is_fn_path fn p` by metis_tac[mm_dload_function_path] >>
  simp[fn_dominates_def, fn_reachable_def, mm_dload_function_entry]
QED

Theorem mm_dload_used_def_retained[local]:
  fn_inst_wf fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions /\
  MEM d (fn_insts fn) /\ MEM v d.inst_outputs /\
  MEM i (fn_insts fn) /\ MEM (Var v) (transform_dload_inst pairs i).inst_operands ==>
  MEM v (transform_dload_inst pairs d).inst_outputs
Proof
  strip_tac >>
  qspecl_then [`pairs`, `d`] strip_assume_tac mm_dload_transform_cases
  >- (`MEM dp (find_dload_pairs (dfg_build_function fn) bb.bb_instructions)` by metis_tac[] >>
      drule_then strip_assume_tac mm_dload_pair_provenance >>
      `MEM ld (fn_insts fn)` by
        metis_tac[MEM_fn_insts_blocks_iff, venomInstTheory.fn_insts_def] >>
      `d = ld` by metis_tac[fn_insts_id_unique, wf_function_def] >>
      `v = v'` by metis_tac[MEM] >>
      metis_tac[mm_dload_transform_no_removed_use])
  >- simp[] >>
  `MEM dp (find_dload_pairs (dfg_build_function fn) bb.bb_instructions)` by metis_tac[] >>
  drule_then strip_assume_tac mm_dload_pair_provenance >>
  `d = st` by metis_tac[fn_insts_id_unique, wf_function_def] >>
  `inst_wf d` by
    (gvs[fn_inst_wf_def, venomInstTheory.fn_insts_def, MEM_fn_insts_blocks_iff] >>
     metis_tac[]) >>
  gvs[inst_wf_def]
QED

Theorem mm_dload_available_transport[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions /\
  MEM b fn.fn_blocks /\ def_available_at fn b point v /\
  (!d. MEM d (fn_insts fn) /\ MEM v d.inst_outputs ==>
       MEM v (transform_dload_inst pairs d).inst_outputs) ==>
  def_available_at
    (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks)
    (transform_block_dload pairs b) (OPTION_MAP (transform_dload_inst pairs) point) v
Proof
  strip_tac >>
  qpat_x_assum `def_available_at _ _ _ _` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  qexistsl [`transform_block_dload pairs def_bb`, `transform_dload_inst pairs def_inst`] >>
  `MEM def_inst (fn_insts fn)` by
    metis_tac[MEM_fn_insts_blocks_iff, venomInstTheory.fn_insts_def] >>
  `fn_dominates
     (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks)
     def_bb.bb_label b.bb_label` by metis_tac[mm_dload_function_dominates] >>
  `transform_block_dload pairs def_bb = transform_block_dload pairs b ==> def_bb = b` by
    (strip_tac >>
     `def_bb.bb_label = b.bb_label` by
       (qpat_x_assum `transform_block_dload _ _ = _` mp_tac >>
        simp[transform_block_dload_def, venomInstTheory.basic_block_component_equality]) >>
     metis_tac[same_label_same_block]) >>
  simp[transform_block_dload_def, MEM_MAP] >>
  conj_tac >- metis_tac[transform_block_dload_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  strip_tac >> `def_bb = b` by metis_tac[transform_block_dload_def] >>
  Cases_on `point` >> gvs[] >>
  qexistsl [`i`, `j`] >> simp[EL_MAP] >> decide_tac
QED

Theorem mm_dload_available_ready[local]:
  wf_function fn /\ MEM db fn.fn_blocks /\ MEM b fn.fn_blocks /\
  p < LENGTH db.bb_instructions /\ q < LENGTH b.bb_instructions /\
  def_available_at fn db (SOME (EL p db.bb_instructions)) v /\
  mm_dload_ready fn db p b q ==>
  def_available_at fn b (SOME (EL q b.bb_instructions)) v
Proof
  simp[def_available_at_def, mm_dload_ready_def] >> strip_tac >>
  `fn_dominates fn def_bb.bb_label b.bb_label` by
    (gvs[fn_dominates_cfg_analyze] >> metis_tac[dominates_trans]) >>
  qexistsl [`def_bb`, `def_inst`] >> simp[] >> strip_tac >>
  `db = b` by
    (qspec_then `fn` strip_assume_tac fn_dominates_strict_measure >>
     `db.bb_label = b.bb_label` by
       (spose_not_then assume_tac >>
        `depth db.bb_label < depth b.bb_label /\ depth b.bb_label < depth db.bb_label` by
          metis_tac[] >> decide_tac) >>
     metis_tac[same_label_same_block]) >>
  gvs[] >>
  `p < LENGTH b.bb_instructions` by decide_tac >>
  `j = p` by metis_tac[inst_ids_el_eq, wf_function_def] >>
  qexistsl [`i`, `q`] >> simp[] >> decide_tac
QED

Theorem mm_dload_new_use_available[local]:
  wf_function fn /\ wf_ssa fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions /\
  MEM b fn.fn_blocks /\ MEM i b.bb_instructions /\ i.inst_opcode <> PHI /\
  MEM (Var v) (transform_dload_inst pairs i).inst_operands ==>
  def_available_at fn b (SOME i) v
Proof
  strip_tac >>
  `MEM i (fn_insts fn)` by
    metis_tac[MEM_fn_insts_blocks_iff, venomInstTheory.fn_insts_def] >>
  `!b i v. MEM b fn.fn_blocks /\ MEM i b.bb_instructions /\
     i.inst_opcode <> PHI /\ MEM (Var v) i.inst_operands ==>
     def_available_at fn b (SOME i) v` by
    metis_tac[wf_ssa_def, def_dominates_uses_def] >>
  qspecl_then [`pairs`, `i`] strip_assume_tac mm_dload_transform_cases
  >- gvs[mk_nop_from_def]
  >- metis_tac[] >>
  `MEM dp (find_dload_pairs (dfg_build_function fn) bb.bb_instructions)` by metis_tac[] >>
  drule_then strip_assume_tac mm_dload_pair_provenance >>
  `i = st` by metis_tac[fn_insts_id_unique, wf_function_def] >>
  gvs[mk_dloadbytes_inst_def] >>
  `def_available_at fn bb (SOME ld) v` by simp[MEM] >>
  `?p. p < LENGTH bb.bb_instructions /\ ld = EL p bb.bb_instructions` by metis_tac[MEM_EL] >>
  `?q. q < LENGTH b.bb_instructions /\ i = EL q b.bb_instructions` by metis_tac[MEM_EL] >>
  `mm_dload_ready fn bb p b q` by
    (irule mm_dload_ready_use >> simp[] >>
     qpat_x_assum `ld = EL p _` (fn th => rewrite_tac[GSYM th]) >>
     qpat_x_assum `i = EL q _` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  metis_tac[mm_dload_available_ready]
QED

Theorem mm_dload_ordinary_available[local]:
  fn_inst_wf fn /\ wf_function fn /\ wf_ssa fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions /\
  MEM b fn.fn_blocks /\ MEM i b.bb_instructions /\ i.inst_opcode <> PHI /\
  MEM (Var v) (transform_dload_inst pairs i).inst_operands ==>
  def_available_at
    (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks)
    (transform_block_dload pairs b) (SOME (transform_dload_inst pairs i)) v
Proof
  strip_tac >>
  `def_available_at fn b (SOME i) v` by metis_tac[mm_dload_new_use_available] >>
  `MEM i (fn_insts fn)` by
    metis_tac[MEM_fn_insts_blocks_iff, venomInstTheory.fn_insts_def] >>
  `!d. MEM d (fn_insts fn) /\ MEM v d.inst_outputs ==>
       MEM v (transform_dload_inst pairs d).inst_outputs` by
    metis_tac[mm_dload_used_def_retained] >>
  drule_all mm_dload_available_transport >> simp[]
QED

Theorem mm_dload_phi_transport[local]:
  fn_inst_wf fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions /\
  MEM b fn.fn_blocks /\ MEM i b.bb_instructions /\ i.inst_opcode = PHI /\
  phi_edge_uses_wf fn b i ==>
  phi_edge_uses_wf
    (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks)
    (transform_block_dload pairs b) (transform_dload_inst pairs i)
Proof
  strip_tac >>
  `MEM i (fn_insts fn)` by
    metis_tac[MEM_fn_insts_blocks_iff, venomInstTheory.fn_insts_def] >>
  `transform_dload_inst pairs i = i` by metis_tac[mm_dload_transform_control] >>
  `fn_cfg_edge (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks) =
   fn_cfg_edge fn` by metis_tac[mm_dload_function_cfg] >>
  fs[phi_edge_uses_wf_def] >>
  rpt strip_tac >>
  `?pred_bb. MEM pred_bb fn.fn_blocks /\ pred_bb.bb_label = pred /\
    fn_cfg_edge fn pred b.bb_label /\ def_available_at fn pred_bb NONE v` by metis_tac[] >>
  `MEM (Var v) i.inst_operands` by metis_tac[phi_pairs_mem_var] >>
  `!d. MEM d (fn_insts fn) /\ MEM v d.inst_outputs ==>
       MEM v (transform_dload_inst pairs d).inst_outputs` by
    metis_tac[mm_dload_used_def_retained] >>
  `def_available_at
    (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks)
    (transform_block_dload pairs pred_bb) NONE v` by
    (drule_all mm_dload_available_transport >> simp[]) >>
  qexists_tac `transform_block_dload pairs pred_bb` >>
  simp[transform_block_dload_def, MEM_MAP] >> metis_tac[transform_block_dload_def]
QED

Theorem mm_dload_function_ssa[local]:
  fn_inst_wf fn /\ wf_function fn /\ wf_ssa fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions ==>
  wf_ssa (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks)
Proof
  strip_tac >> rewrite_tac[wf_ssa_def] >> conj_tac
  >- metis_tac[dload_function_ssa, wf_ssa_def] >>
  simp[def_dominates_uses_def, MEM_MAP] >> rpt gen_tac >> strip_tac >>
  rename1 `MEM b fn.fn_blocks` >>
  qpat_x_assum `_ = transform_block_dload _ b` SUBST_ALL_TAC >>
  fs[transform_block_dload_def, MEM_MAP] >>
  rename1 `MEM i b.bb_instructions` >>
  `MEM i (fn_insts fn)` by
    metis_tac[MEM_fn_insts_blocks_iff, venomInstTheory.fn_insts_def] >>
  `((transform_dload_inst pairs i).inst_opcode = PHI) = (i.inst_opcode = PHI)` by
    metis_tac[mm_dload_transform_control] >>
  qpat_assum `pairs = _` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE[GSYM th]) >> pure_rewrite_tac[GSYM th] >> assume_tac th) >>
  Cases_on `i.inst_opcode = PHI` >> fs[]
  >- (`phi_edge_uses_wf fn b i` by metis_tac[wf_ssa_def, def_dominates_uses_def] >>
      drule_all mm_dload_phi_transport >> simp[transform_block_dload_def]) >>
  simp[] >> rpt strip_tac >>
  metis_tac[mm_dload_ordinary_available, transform_block_dload_def]
QED

Theorem mm_dload_store_step[local]:
  i.inst_opcode = MSTORE /\ i.inst_operands = [dst; Var v] /\
  mm_dload_cached src v s /\
  ~(?err. step_inst fuel ctx i s = Error err) ==>
  step_inst fuel ctx (mk_dloadbytes_inst i src dst) s =
    step_inst fuel ctx i s
Proof
  strip_tac >>
  gvs[mm_dload_cached_def] >>
  fs[mk_dloadbytes_inst_def, step_inst_non_invoke] >>
  fs[step_inst_base_def] >>
  gvs[exec_write2_def, eval_operand_def, AllCaseEqs()] >>
  Cases_on `eval_operand dst s` >> gvs[] >>
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  `32 MOD dimword (:256) = 32` by simp[wordsTheory.dimword_def] >>
  qspecl_then [`w2n off`, `w2n x`, `s`] mp_tac
    dload_mstore_eq_dloadbytes >> simp[]
QED

Theorem mm_dload_producer_step[local]:
  i.inst_opcode = DLOAD /\ step_inst fuel ctx i s = OK t /\
  state_equiv vars s u /\ set i.inst_outputs SUBSET vars ==>
  step_inst fuel ctx (mk_nop_from i) u = OK u /\ state_equiv vars t u
Proof
  strip_tac >> conj_tac
  >- simp[step_inst_non_invoke, step_inst_base_def, mk_nop_from_def] >>
  irule state_equiv_effect_free_compose >>
  goal_assum (drule_at Any) >>
  qexists `s` >> simp[] >>
  irule venomInstProofsTheory.step_effect_free_state_equiv >>
  simp[venomInstTheory.is_effect_free_op_def] >> metis_tac[]
QED

Theorem mm_dload_consumer_step[local]:
  i.inst_opcode = MSTORE /\ i.inst_operands = [dst; Var v] /\
  mm_dload_cached src v s /\ state_equiv vars s u /\
  (!x. src = Var x \/ dst = Var x ==> x NOTIN vars) /\
  ~(?err. step_inst fuel ctx i s = Error err) ==>
  result_equiv vars (step_inst fuel ctx i s)
    (step_inst fuel ctx (mk_dloadbytes_inst i src dst) u)
Proof
  strip_tac >>
  `step_inst fuel ctx (mk_dloadbytes_inst i src dst) s =
     step_inst fuel ctx i s` by (irule mm_dload_store_step >> simp[] >> metis_tac[]) >>
  pop_assum (fn th => rewrite_tac[GSYM th]) >>
  irule execEquivPropsTheory.step_inst_result_equiv >>
  simp[mk_dloadbytes_inst_def] >> metis_tac[operand_distinct]
QED

Theorem mm_dload_store_ranges[local]:
  i.inst_opcode = MSTORE /\ i.inst_operands = [dst; Var v] /\
  mm_dload_cached src v s ==>
  inst_mem_ranges (mk_dloadbytes_inst i src dst) s = inst_mem_ranges i s
Proof
  strip_tac >>
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  gvs[mm_dload_cached_def, inst_mem_ranges_def,
      contextCodegenRelTheory.source_memory_read_ranges_def,
      codegenRelTheory.source_memory_write_ranges_def,
      codegenRelTheory.fixed_source_write_range_def,
      codegenRelTheory.sized_source_write_range_def,
      mk_dloadbytes_inst_def, eval_operand_def, wordsTheory.dimword_def] >>
  Cases_on `eval_operand dst s` >> simp[]
QED

Theorem mm_dload_step_back_image[local]:
  (!i. i.inst_opcode = ASSIGN ==> f i = i) /\
  (!i. set (f i).inst_outputs SUBSET set i.inst_outputs) /\
  step_back_assign i p = SOME q ==>
  step_back_assign (f i) p = SOME q
Proof
  strip_tac >> Cases_on `p` >>
  gvs[contextCodegenRelTheory.step_back_assign_def, AllCaseEqs()] >>
  Cases_on `i.inst_opcode = ASSIGN` >> gvs[] >>
  `~MEM s (f i).inst_outputs` by metis_tac[pred_setTheory.SUBSET_DEF] >> simp[]
QED

Theorem mm_dload_same_after_image[local]:
  (!i. i.inst_opcode = ASSIGN ==> f i = i) /\
  (!i. set (f i).inst_outputs SUBSET set i.inst_outputs) ==>
  !xs p q. same_after_assigns xs p q ==> same_after_assigns (MAP f xs) p q
Proof
  strip_tac >> Induct_on `xs` >>
  simp[contextCodegenRelTheory.same_after_assigns_def] >>
  rpt strip_tac >> Cases_on `p = q` >> gvs[] >>
  Cases_on `step_back_assign h p` >> gvs[] >>
  Cases_on `step_back_assign h q` >> gvs[] >>
  `step_back_assign (f h) p = SOME x` by metis_tac[mm_dload_step_back_image] >>
  `step_back_assign (f h) q = SOME x'` by metis_tac[mm_dload_step_back_image] >>
  simp[]
QED

Theorem mm_dload_revert_pair_image[local]:
  (!x. x.inst_opcode = ASSIGN ==> f x = x) /\
  (!x. set (f x).inst_outputs SUBSET set x.inst_outputs) /\
  (!x. (get_instruction bb i = SOME x \/ get_instruction bb j = SOME x) ==>
       f x = x) /\
  cb.bb_instructions = MAP f bb.bb_instructions /\ revert_forward_pair bb i j ==>
  revert_forward_pair cb i j
Proof
  strip_tac >>
  qpat_x_assum `revert_forward_pair bb i j` mp_tac >>
  rewrite_tac[contextCodegenRelTheory.revert_forward_pair_def] >> strip_tac >>
  `!n. get_instruction cb n = OPTION_MAP f (get_instruction bb n)` by
    metis_tac[scfg_get_instruction_map] >>
  `!k. i < k /\ k < j ==> get_instruction cb k = get_instruction bb k` by
    (rpt strip_tac >> Cases_on `get_instruction bb k` >> simp[] >>
     `x.inst_opcode = ASSIGN` by metis_tac[] >> simp[]) >>
  `TAKE (j - SUC i) (DROP (SUC i) cb.bb_instructions) =
    TAKE (j - SUC i) (DROP (SUC i) bb.bb_instructions)` by
    (`j < LENGTH bb.bb_instructions` by fs[venomInstTheory.get_instruction_def] >>
     `j - SUC i <= LENGTH bb.bb_instructions - SUC i` by decide_tac >>
     irule LIST_EQ >> simp[LENGTH_TAKE_EQ, LENGTH_DROP] >> rpt strip_tac >>
     rename1 `n < _` >> gvs[LENGTH_TAKE_EQ, LENGTH_DROP] >>
     `i < SUC i + n /\ SUC i + n < j` by decide_tac >>
     `SUC i + n < LENGTH bb.bb_instructions` by decide_tac >>
     `EL (SUC i + n) cb.bb_instructions = EL (SUC i + n) bb.bb_instructions` by
       (first_x_assum (qspec_then `SUC i + n` mp_tac) >>
        simp[venomInstTheory.get_instruction_def, EL_MAP]) >>
     gvs[EL_TAKE, EL_DROP, EL_MAP, arithmeticTheory.ADD_COMM]) >>
  `f inst1 = inst1 /\ f inst2 = inst2` by metis_tac[] >>
  simp[GSYM MAP_TAKE, GSYM MAP_REVERSE] >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      `z.inst_opcode = ASSIGN` by metis_tac[] >> simp[]) >>
  rpt conj_tac >> irule mm_dload_same_after_image >> simp[]
QED

Theorem mm_dload_other_unchanged[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions /\
  MEM i (fn_insts fn) /\ i.inst_opcode <> DLOAD /\ i.inst_opcode <> MSTORE ==>
  transform_dload_inst pairs i = i
Proof
  strip_tac >>
  qspecl_then [`pairs`, `i`] strip_assume_tac mm_dload_transform_cases
  >- (`MEM dp (find_dload_pairs (dfg_build_function fn) bb.bb_instructions)` by metis_tac[] >>
      drule_then strip_assume_tac mm_dload_pair_provenance >>
      `MEM ld (fn_insts fn)` by
        metis_tac[MEM_fn_insts_blocks_iff, venomInstTheory.fn_insts_def] >>
      `i = ld` by metis_tac[fn_insts_id_unique, wf_function_def] >> gvs[]) >>
  `MEM dp (find_dload_pairs (dfg_build_function fn) bb.bb_instructions)` by metis_tac[] >>
  drule_then strip_assume_tac mm_dload_pair_provenance >>
  `i = st` by metis_tac[fn_insts_id_unique, wf_function_def] >> gvs[]
QED

Theorem mm_dload_block_revert_pair[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\ MEM b fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions /\
  revert_forward_pair b i j ==>
  revert_forward_pair (transform_block_dload pairs b) i j
Proof
  strip_tac >> irule mm_dload_revert_pair_image >>
  qexists `b` >> qexists `\x. if MEM x (fn_insts fn) then transform_dload_inst pairs x else x` >>
  `!x. MEM x b.bb_instructions ==> MEM x (fn_insts fn)` by
    metis_tac[MEM_fn_insts_blocks_iff, venomInstTheory.fn_insts_def] >>
  pure_rewrite_tac[BETA_THM] >> rpt conj_tac
  >- (rpt strip_tac >> BETA_TAC >> IF_CASES_TAC >> simp[] >>
      irule mm_dload_other_unchanged >> simp[] >> metis_tac[])
  >- (rpt strip_tac >> BETA_TAC >> IF_CASES_TAC >> simp[] >>
      irule mm_dload_other_unchanged >>
      fs[contextCodegenRelTheory.revert_forward_pair_def] >> simp[] >> metis_tac[])
  >- (gen_tac >> BETA_TAC >> IF_CASES_TAC >> simp[pred_setTheory.SUBSET_DEF] >>
      metis_tac[mm_dload_transform_id_outputs]) >>
  simp[transform_block_dload_def, MAP_EQ_f]
QED

Theorem mm_dload_revert_forward[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions /\
  state_equiv vars s t /\ in_revert_forward fn s ==>
  in_revert_forward
    (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks) t
Proof
  strip_tac >> fs[contextCodegenRelTheory.in_revert_forward_def] >>
  `s.vs_current_bb = t.vs_current_bb /\ s.vs_inst_idx = t.vs_inst_idx` by
    gvs[state_equiv_def] >>
  qexists `transform_block_dload pairs bb'` >> conj_tac
  >- (mp_tac passSimulationPropsTheory.lookup_block_map >>
      disch_then (qspecl_then [`t.vs_current_bb`, `fn.fn_blocks`,
                              `transform_block_dload pairs`] mp_tac) >>
      simp[transform_block_dload_def] >> metis_tac[]) >>
  `MEM bb' fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  fs[contextCodegenRelTheory.revert_forward_at_def] >> qexists `j` >>
  metis_tac[mm_dload_block_revert_pair]
QED

Theorem mm_dload_unchanged_step[local]:
  state_equiv vars s t /\
  (!x. MEM (Var x) i.inst_operands ==> x NOTIN vars) ==>
  result_equiv vars (step_inst fuel ctx i s) (step_inst fuel ctx i t)
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE`
  >- (irule removeUnusedProofsTheory.step_inst_result_equiv_full >>
      simp[venomInstTheory.is_terminator_def]) >>
  irule execEquivPropsTheory.step_inst_result_equiv >> simp[]
QED

Theorem mm_dload_ranges_equiv[local]:
  state_equiv vars s t /\
  (!x. MEM (Var x) i.inst_operands ==> x NOTIN vars) ==>
  inst_mem_ranges i s = inst_mem_ranges i t
Proof
  strip_tac >> irule o1ContractCfgNormTheory.supply_inst_mem_ranges_cong >>
  reverse conj_tac >- gvs[state_equiv_def, execution_equiv_def] >>
  rpt strip_tac >> irule stateEquivProofsTheory.eval_operand_equiv >>
  qexists `vars` >> metis_tac[]
QED

Theorem mm_dload_removed_operand_avoid[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions /\
  vars = {v | ?dp ld. MEM dp pairs /\ MEM ld bb.bb_instructions /\
    ld.inst_id = dp.dp_dload_id /\ MEM v ld.inst_outputs} /\
  MEM i (fn_insts fn) ==>
  (!x. MEM (Var x) (transform_dload_inst pairs i).inst_operands ==> x NOTIN vars)
Proof
  strip_tac >> rpt strip_tac >>
  qpat_x_assum `vars = _` SUBST_ALL_TAC >>
  fs[pred_setTheory.IN_GSPEC_IFF] >>
  `MEM dp (find_dload_pairs (dfg_build_function fn) bb.bb_instructions)` by metis_tac[] >>
  drule_then strip_assume_tac mm_dload_pair_provenance >>
  `MEM ld (fn_insts fn) /\ MEM ld' (fn_insts fn)` by
    metis_tac[MEM_fn_insts_blocks_iff, venomInstTheory.fn_insts_def] >>
  `ld = ld'` by metis_tac[fn_insts_id_unique, wf_function_def] >>
  gvs[] >> metis_tac[mm_dload_transform_no_removed_use]
QED

Theorem mm_dload_static_mem_ok[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions /\
  MEM i (fn_insts fn) /\ state_equiv vars s t /\
  (!x. MEM (Var x) (transform_dload_inst pairs i).inst_operands ==> x NOTIN vars) /\
  (!dp. MEM dp pairs /\ dp.dp_mstore_id = i.inst_id ==>
    ?v. i.inst_opcode = MSTORE /\ i.inst_operands = [dp.dp_dst; Var v] /\
        mm_dload_cached dp.dp_src v s) /\
  static_mem_ok eom ctx fn i s ==>
  static_mem_ok eom ctx
    (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks)
    (transform_dload_inst pairs i) t
Proof
  strip_tac >> qpat_x_assum `static_mem_ok _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[static_mem_ok_def] >> strip_tac
  >- metis_tac[mm_dload_revert_forward] >>
  `inst_mem_ranges (transform_dload_inst pairs i) s =
   inst_mem_ranges (transform_dload_inst pairs i) t` by
    (irule mm_dload_ranges_equiv >> metis_tac[]) >>
  pop_assum (fn th => rewrite_tac[GSYM th]) >>
  qspecl_then [`pairs`, `i`] strip_assume_tac mm_dload_transform_cases
  >- simp[inst_mem_ranges_def, mk_nop_from_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def]
  >- fs[arithmeticTheory.ADD_COMM] >>
  `?v. i.inst_opcode = MSTORE /\ i.inst_operands = [dp.dp_dst; Var v] /\
       mm_dload_cached dp.dp_src v s` by metis_tac[] >>
  `inst_mem_ranges (mk_dloadbytes_inst i dp.dp_src dp.dp_dst) s =
   inst_mem_ranges i s` by (irule mm_dload_store_ranges >> metis_tac[]) >>
  fs[arithmeticTheory.ADD_COMM]
QED

Theorem mm_dload_step_equiv[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions /\
  vars = {v | ?dp ld. MEM dp pairs /\ MEM ld bb.bb_instructions /\
    ld.inst_id = dp.dp_dload_id /\ MEM v ld.inst_outputs} /\
  MEM i (fn_insts fn) /\ state_equiv vars s t /\
  (!dp. MEM dp pairs /\ dp.dp_mstore_id = i.inst_id ==>
    ?v. i.inst_opcode = MSTORE /\ i.inst_operands = [dp.dp_dst; Var v] /\
        mm_dload_cached dp.dp_src v s) /\
  ~(?err. step_inst fuel ctx i s = Error err) ==>
  result_equiv vars (step_inst fuel ctx i s)
    (step_inst fuel ctx (transform_dload_inst pairs i) t)
Proof
  strip_tac >>
  `!x. MEM (Var x) (transform_dload_inst pairs i).inst_operands ==> x NOTIN vars` by
    metis_tac[mm_dload_removed_operand_avoid] >>
  qspecl_then [`pairs`, `i`] strip_assume_tac mm_dload_transform_cases
  >- (`MEM dp (find_dload_pairs (dfg_build_function fn) bb.bb_instructions)` by metis_tac[] >>
      drule_then strip_assume_tac mm_dload_pair_provenance >>
      `MEM ld (fn_insts fn)` by
        metis_tac[MEM_fn_insts_blocks_iff, venomInstTheory.fn_insts_def] >>
      `i = ld` by metis_tac[fn_insts_id_unique, wf_function_def] >>
      `set i.inst_outputs SUBSET vars` by
        (simp[pred_setTheory.SUBSET_DEF] >> rpt strip_tac >>
         qpat_x_assum `vars = _` SUBST_ALL_TAC >>
         simp[pred_setTheory.IN_GSPEC_IFF] >> metis_tac[MEM]) >>
      `?z. step_inst fuel ctx i s = OK z` by
        (`i.inst_opcode = DLOAD /\ i.inst_operands = [dp.dp_src] /\ i.inst_outputs = [v]` by metis_tac[] >>
         qpat_x_assum `vars = _` kall_tac >>
         fs[step_inst_non_invoke] >> fs[step_inst_base_def] >>
         fs[exec_read1_def, AllCaseEqs()] >>
         Cases_on `eval_operand dp.dp_src s` >> gvs[]) >>
      `step_inst fuel ctx (mk_nop_from i) t = OK t /\ state_equiv vars z t` by
        (irule mm_dload_producer_step >> metis_tac[]) >>
      metis_tac[result_equiv_def])
  >- gvs[mm_dload_unchanged_step] >>
  `?v. i.inst_opcode = MSTORE /\ i.inst_operands = [dp.dp_dst; Var v] /\
       mm_dload_cached dp.dp_src v s` by metis_tac[] >>
  qpat_assum `transform_dload_inst pairs i = _` (fn th => pure_rewrite_tac[th]) >>
  irule mm_dload_consumer_step >>
  qpat_x_assum `vars = _` kall_tac >>
  fs[mk_dloadbytes_inst_def] >> metis_tac[]
QED

Theorem mm_dload_reachable_inst[local]:
  fn_inst_wf fn /\ wf_function fn /\ wf_ssa fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions /\
  vars = {v | ?dp ld. MEM dp pairs /\ MEM ld bb.bb_instructions /\
    ld.inst_id = dp.dp_dload_id /\ MEM v ld.inst_outputs} /\
  mm_dload_frame_reachable ctx fn b s /\
  get_instruction b s.vs_inst_idx = SOME i /\ state_equiv vars s t ==>
  (~(?err. step_inst fuel ctx i s = Error err) ==>
    result_equiv vars (step_inst fuel ctx i s)
      (step_inst fuel ctx (transform_dload_inst pairs i) t)) /\
  (static_mem_ok eom ctx fn i s ==>
    static_mem_ok eom ctx
      (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks)
      (transform_dload_inst pairs i) t)
Proof
  strip_tac >>
  `MEM b fn.fn_blocks` by metis_tac[mm_dload_frame_reachable_location] >>
  `MEM i (fn_insts fn)` by
    (simp[venomInstTheory.fn_insts_def, MEM_fn_insts_blocks_iff] >>
     qexists `b` >> simp[] >>
     fs[venomInstTheory.get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  `!dp. MEM dp pairs /\ dp.dp_mstore_id = i.inst_id ==>
    ?v. i.inst_opcode = MSTORE /\ i.inst_operands = [dp.dp_dst; Var v] /\
        mm_dload_cached dp.dp_src v s` by
    (rpt strip_tac >> irule mm_dload_frame_store_cached >> metis_tac[]) >>
  conj_tac >- metis_tac[mm_dload_step_equiv] >>
  `!x. MEM (Var x) (transform_dload_inst pairs i).inst_operands ==> x NOTIN vars` by
    metis_tac[mm_dload_removed_operand_avoid] >>
  metis_tac[mm_dload_static_mem_ok]
QED

Theorem mm_dload_phi_image[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions ==>
  !xs. EVERY (\i. MEM i (fn_insts fn)) xs ==>
    phi_prefix_length (MAP (transform_dload_inst pairs) xs) = phi_prefix_length xs /\
    eval_phis s (MAP (transform_dload_inst pairs) xs) = eval_phis s xs
Proof
  strip_tac >>
  qpat_assum `pairs = _` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE[GSYM th]) >> assume_tac th) >>
  Induct
  >- simp[phi_prefix_length_def, eval_phis_def] >>
  gen_tac >> pure_rewrite_tac[EVERY_DEF, MAP, BETA_THM] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `((transform_dload_inst pairs h).inst_opcode = PHI) = (h.inst_opcode = PHI)` by
    metis_tac[mm_dload_transform_control] >>
  Cases_on `h.inst_opcode = PHI`
  >- (`transform_dload_inst pairs h = h` by metis_tac[mm_dload_transform_control] >>
      qpat_x_assum `pairs = _` kall_tac >>
      simp[phi_prefix_length_def, eval_phis_def]) >>
  qpat_x_assum `pairs = _` kall_tac >>
  simp[phi_prefix_length_def, eval_phis_def]
QED

Theorem mm_dload_phi_equiv[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions /\
  vars = {v | ?dp ld. MEM dp pairs /\ MEM ld bb.bb_instructions /\
    ld.inst_id = dp.dp_dload_id /\ MEM v ld.inst_outputs} /\
  EVERY (\i. MEM i (fn_insts fn)) xs /\
  state_equiv vars s t /\ eval_phis s xs = OK sp ==>
  ?tp. eval_phis t (MAP (transform_dload_inst pairs) xs) = OK tp /\
       state_equiv vars sp tp
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode = PHI ==> !x. MEM (Var x) i.inst_operands ==> x NOTIN vars) xs` by
    (simp_tac bool_ss [EVERY_MEM] >> rpt strip_tac >>
     rename1 `MEM i xs` >>
     `MEM i (fn_insts fn)` by gvs[EVERY_MEM] >>
     `transform_dload_inst pairs i = i` by metis_tac[mm_dload_transform_control] >>
     metis_tac[mm_dload_removed_operand_avoid]) >>
  `eval_phis t (MAP (transform_dload_inst pairs) xs) = eval_phis t xs` by
    metis_tac[mm_dload_phi_image] >>
  metis_tac[venomExecProofsTheory.eval_phis_state_equiv]
QED

Theorem mm_dload_block_equiv[local]:
  fn_inst_wf fn /\ wf_function fn /\ wf_ssa fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions /\
  vars = {v | ?dp ld. MEM dp pairs /\ MEM ld bb.bb_instructions /\
    ld.inst_id = dp.dp_dload_id /\ MEM v ld.inst_outputs} ==>
  !n s t d. n = LENGTH b.bb_instructions - s.vs_inst_idx /\
    mm_dload_frame_reachable ctx fn b s /\ state_equiv vars s t /\
    ~(?err. exec_block fuel ctx b s = Error err) /\
    EVERY (\((p,k,id),f,i,u). p = [] ==> static_mem_ok eom ctx f i u)
      (trace_block [] d fuel ctx fn b s) ==>
    result_equiv vars (exec_block fuel ctx b s)
      (exec_block fuel ctx (transform_block_dload pairs b) t) /\
    EVERY (\((p,k,id),f,i,u). p = [] ==> static_mem_ok eom ctx f i u)
      (trace_block [] d fuel ctx
        (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks)
        (transform_block_dload pairs b) t)
Proof
  strip_tac >> completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  `s.vs_inst_idx = t.vs_inst_idx` by fs[state_equiv_def] >>
  Cases_on `get_instruction b s.vs_inst_idx`
  >- (qpat_x_assum `~(?err. _)` mp_tac >> simp[Once exec_block_def]) >>
  rename1 `get_instruction b s.vs_inst_idx = SOME i` >>
  `get_instruction (transform_block_dload pairs b) t.vs_inst_idx =
     SOME (transform_dload_inst pairs i)` by
    gvs[venomInstTheory.get_instruction_def, transform_block_dload_def, EL_MAP, AllCaseEqs()] >>
  `~(?err. step_inst fuel ctx i s = Error err)` by
    (strip_tac >> qpat_x_assum `~(?err. exec_block _ _ _ _ = _)` mp_tac >>
     simp[Once exec_block_def]) >>
  `result_equiv vars (step_inst fuel ctx i s)
    (step_inst fuel ctx (transform_dload_inst pairs i) t) /\
   (static_mem_ok eom ctx fn i s ==>
     static_mem_ok eom ctx
       (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks)
       (transform_dload_inst pairs i) t)` by
    metis_tac[mm_dload_reachable_inst] >>
  suspend "steps"
QED

Resume mm_dload_block_equiv[steps]:
  `MEM i (fn_insts fn)` by
    (drule_all mm_dload_frame_reachable_location >> strip_tac >>
     fs[venomInstTheory.get_instruction_def, AllCaseEqs()] >>
     metis_tac[MEM_EL, MEM_fn_insts_blocks_iff, venomInstTheory.fn_insts_def]) >>
  `is_terminator (transform_dload_inst pairs i).inst_opcode = is_terminator i.inst_opcode` by
    metis_tac[mm_dload_transform_control] >>
  qpat_x_assum `pairs = _` kall_tac >>
  qpat_x_assum `vars = _` kall_tac >>
  qpat_x_assum `EVERY _ (trace_block _ _ _ _ _ _ _)` mp_tac >>
  simp[Once trace_defs, EVERY_APPEND] >> strip_tac >>
  `EVERY (\((p,k,id),f,j,u). p = [] ==> static_mem_ok eom ctx f j u)
    (trace_step [] d fuel ctx
      (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks)
      (transform_dload_inst pairs i) t)` by
    (simp_tac bool_ss [EVERY_MEM, pairTheory.FORALL_PROD] >>
     rpt strip_tac >> Cases_on `p = []` >> gvs[] >>
     metis_tac[cj 1 mm_dload_frame_trace]) >>
  Cases_on `step_inst fuel ctx i s` >>
  Cases_on `step_inst fuel ctx (transform_dload_inst pairs i) t` >>
  fs[result_equiv_def] >>
  once_rewrite_tac[exec_block_def] >>
  once_rewrite_tac[trace_defs] >>
  simp[EVERY_APPEND, result_equiv_def] >>
  rename1 `step_inst fuel ctx i s = OK u` >>
  rename1 `step_inst fuel ctx (transform_dload_inst pairs i) t = OK w` >>
  Cases_on `is_terminator i.inst_opcode`
  >- (fs[state_equiv_def] >>
      `u.vs_halted = w.vs_halted` by fs[execution_equiv_def] >>
      Cases_on `u.vs_halted` >> gvs[result_equiv_def, state_equiv_def]) >>
  fs[] >>
  `mm_dload_frame_reachable ctx fn b (u with vs_inst_idx := SUC t.vs_inst_idx)` by
    metis_tac[mm_dload_frame_reachable_rules] >>
  `state_equiv vars (u with vs_inst_idx := SUC t.vs_inst_idx)
     (w with vs_inst_idx := SUC t.vs_inst_idx)` by
    metis_tac[execEquivProofsTheory.state_equiv_inst_idx] >>
  `~(?err. exec_block fuel ctx b (u with vs_inst_idx := SUC t.vs_inst_idx) = Error err)` by
    (qpat_x_assum `!err. exec_block _ _ _ _ <> _` mp_tac >>
     simp[Once exec_block_def]) >>
  first_x_assum irule >> simp[] >>
  gvs[venomInstTheory.get_instruction_def, AllCaseEqs()]
QED

Finalise mm_dload_block_equiv

Theorem mm_dload_blocks_equiv[local]:
  fn_inst_wf fn /\ wf_function fn /\ wf_ssa fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions /\
  vars = {v | ?dp ld. MEM dp pairs /\ MEM ld bb.bb_instructions /\
    ld.inst_id = dp.dp_dload_id /\ MEM v ld.inst_outputs} ==>
  !fuel s t d.
    state_equiv vars s t /\
    (!b sp. lookup_block s.vs_current_bb fn.fn_blocks = SOME b /\
      eval_phis s b.bb_instructions = OK sp ==>
      mm_dload_frame_reachable ctx fn b
        (sp with vs_inst_idx := phi_prefix_length b.bb_instructions)) /\
    ~(?err. run_blocks fuel ctx fn s = Error err) /\
    EVERY (\((p,k,id),f,i,u). p = [] ==> static_mem_ok eom ctx f i u)
      (trace_blocks [] d fuel ctx fn s) ==>
    result_equiv vars (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx
        (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks) t) /\
    EVERY (\((p,k,id),f,i,u). p = [] ==> static_mem_ok eom ctx f i u)
      (trace_blocks [] d fuel ctx
        (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks) t)
Proof
  strip_tac >> Induct
  >- simp[run_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  `s.vs_current_bb = t.vs_current_bb` by fs[state_equiv_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (qpat_x_assum `~(?err. _)` mp_tac >> simp[Once run_blocks_def]) >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME b` >>
  `MEM b fn.fn_blocks` by metis_tac[simplifyCfgDefsTheory.lookup_block_member_label] >>
  `EVERY (\i. MEM i (fn_insts fn)) b.bb_instructions` by
    (simp[EVERY_MEM, venomInstTheory.fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  suspend "phis"
QED

Resume mm_dload_blocks_equiv[phis]:
  `?sp. eval_phis s b.bb_instructions = OK sp` by
    (mp_tac (Q.SPECL [`s`, `b.bb_instructions`] eval_phis_ok_or_error_defs) >>
     strip_tac >- metis_tac[] >>
     qpat_x_assum `~(?err. _)` mp_tac >> simp[Once run_blocks_def]) >>
  `?tp. eval_phis t (MAP (transform_dload_inst pairs) b.bb_instructions) = OK tp /\
    state_equiv vars sp tp` by metis_tac[mm_dload_phi_equiv] >>
  `phi_prefix_length (MAP (transform_dload_inst pairs) b.bb_instructions) =
    phi_prefix_length b.bb_instructions` by metis_tac[mm_dload_phi_image] >>
  `lookup_block t.vs_current_bb
    (MAP (transform_block_dload pairs) fn.fn_blocks) = SOME (transform_block_dload pairs b)` by
    (simp[passSimulationPropsTheory.lookup_block_map, transform_block_dload_def] >>
     gvs[]) >>
  qabbrev_tac `se = sp with vs_inst_idx := phi_prefix_length b.bb_instructions` >>
  qabbrev_tac `te = tp with vs_inst_idx := phi_prefix_length b.bb_instructions` >>
  `mm_dload_frame_reachable ctx fn b se` by metis_tac[] >>
  `state_equiv vars se te` by
    (simp[Abbr `se`, Abbr `te`] >>
     metis_tac[execEquivProofsTheory.state_equiv_inst_idx]) >>
  `~(?err. exec_block fuel ctx b se = Error err)` by
    (qpat_x_assum `~(?err. run_blocks _ _ _ _ = _)` mp_tac >>
     simp[Once run_blocks_def, Abbr `se`] >>
     Cases_on `exec_block fuel ctx b (sp with vs_inst_idx := phi_prefix_length b.bb_instructions)` >> simp[]) >>
  `EVERY (\((p,k,id),f,i,u). p = [] ==> static_mem_ok eom ctx f i u)
    (trace_block [] (SUC d) fuel ctx fn b se)` by
    (qpat_x_assum `EVERY _ (trace_blocks _ _ _ _ _ _)` mp_tac >>
     simp[Once trace_defs, EVERY_APPEND, Abbr `se`]) >>
  `result_equiv vars (exec_block fuel ctx b se)
      (exec_block fuel ctx (transform_block_dload pairs b) te) /\
    EVERY (\((p,k,id),f,i,u). p = [] ==> static_mem_ok eom ctx f i u)
      (trace_block [] (SUC d) fuel ctx
        (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks)
        (transform_block_dload pairs b) te)` by
    (irule mm_dload_block_equiv >> metis_tac[]) >>
  suspend "exits"
QED

Resume mm_dload_blocks_equiv[exits]:
  qpat_x_assum `pairs = _` kall_tac >>
  qpat_x_assum `vars = _` kall_tac >>
  qpat_x_assum `EVERY _ (trace_blocks _ _ _ _ _ _)` mp_tac >>
  simp[Once trace_defs, EVERY_APPEND, Abbr `se`] >>
  strip_tac >>
  `eval_phis t (transform_block_dload pairs b).bb_instructions = OK tp /\
   phi_prefix_length (transform_block_dload pairs b).bb_instructions =
     phi_prefix_length b.bb_instructions` by simp[transform_block_dload_def] >>
  once_rewrite_tac[run_blocks_def] >>
  once_rewrite_tac[trace_defs] >>
  simp[Abbr `te`] >>
  Cases_on `exec_block fuel ctx b (sp with vs_inst_idx := phi_prefix_length b.bb_instructions)` >>
  Cases_on `exec_block fuel ctx (transform_block_dload pairs b)
    (tp with vs_inst_idx := phi_prefix_length b.bb_instructions)` >>
  fs[result_equiv_def] >>
  rename1 `state_equiv vars u w` >>
  `u.vs_halted = w.vs_halted` by fs[state_equiv_def, execution_equiv_def] >>
  Cases_on `u.vs_halted` >- gvs[result_equiv_def, state_equiv_def] >>
  gvs[] >>
  `~(?err. run_blocks fuel ctx fn u = Error err)` by
    (qpat_x_assum `!err. run_blocks (SUC fuel) _ _ _ <> _` mp_tac >>
     simp[Once run_blocks_def]) >>
  first_x_assum irule >> simp[] >>
  conj_tac >- (
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `exec_block _ _ (transform_block_dload _ _) _ = _` kall_tac >>
  drule_at (Pat `exec_block _ _ _ _ = _`) mm_dload_frame_block_exit >>
  disch_then (qspecl_then [`fn`, `LENGTH b.bb_instructions -
    (sp with vs_inst_idx := phi_prefix_length b.bb_instructions).vs_inst_idx`] mp_tac) >>
  simp[] >> strip_tac >>
  metis_tac[mm_dload_frame_reachable_rules]) >> gvs[]
QED

Finalise mm_dload_blocks_equiv

Theorem mm_dload_visit_correct:
  fn_inst_wf fn /\ wf_function fn /\ wf_ssa fn /\
  ir_supply_covers_fn supply fn /\ MEM bb fn.fn_blocks /\
  pairs = find_dload_pairs (dfg_build_function fn) bb.bb_instructions /\
  fn' = fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks ==>
  fn_inst_wf fn' /\ wf_function fn' /\ wf_ssa fn' /\
  ir_supply_covers_fn supply fn' /\
  fn_entry_label fn' = fn_entry_label fn /\
  (!fuel ctx eom s.
    fn_entry_state fn s /\ eom < dimword (:256) /\
    EVERY (\((p,d,id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
      (trace_function fuel ctx fn s) /\
    ~(?err. run_function fuel ctx fn s = Error err) ==>
    lift_result (state_equiv UNIV) (execution_equiv UNIV) revert_equiv
      (run_function fuel ctx fn s) (run_function fuel ctx fn' s) /\
    EVERY (\((p,d,id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
      (trace_function fuel ctx fn' s))
Proof
  strip_tac >> qpat_x_assum `fn' = _` SUBST_ALL_TAC >>
  `fn_inst_wf (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks)` by
    metis_tac[dload_function_inst_wf] >>
  `wf_function (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks)` by
    metis_tac[selected_dload_function_wf] >>
  `wf_ssa (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks)` by
    metis_tac[mm_dload_function_ssa] >>
  `ir_supply_covers_fn supply
    (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks)` by
    metis_tac[mm_dload_function_supply] >>
  simp[mm_dload_function_entry] >> rpt gen_tac >> strip_tac >>
  suspend "execution"
QED

Resume mm_dload_visit_correct[execution]:
  qpat_assum `pairs = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  `fn_entry_label fn = SOME s.vs_current_bb /\ s.vs_inst_idx = 0` by
    fs[o1PassLiftTheory.fn_entry_state_def] >>
  `s with <|vs_current_bb := s.vs_current_bb; vs_inst_idx := 0|> = s` by
    simp[venomStateTheory.venom_state_component_equality] >>
  qabbrev_tac `vars = {v | ?dp ld. MEM dp pairs /\ MEM ld bb.bb_instructions /\
    ld.inst_id = dp.dp_dload_id /\ MEM v ld.inst_outputs}` >>
  `result_equiv vars (run_function fuel ctx fn s)
    (run_function fuel ctx
      (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks) s) /\
   EVERY (\((p,d,id),f,i,t). p = [] ==> static_mem_ok eom ctx f i t)
    (trace_function fuel ctx
      (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks) s)` by
    (simp[run_function_def, trace_function_def, mm_dload_function_entry] >>
     irule mm_dload_blocks_equiv >>
     conj_tac >-
       (rpt gen_tac >> strip_tac >>
        drule simplifyCfgDefsTheory.lookup_block_member_label >> strip_tac >>
        irule (cj 1 mm_dload_frame_reachable_rules) >>
        metis_tac[]) >>
     gvs[Abbr `vars`, run_function_def, trace_function_def,
       stateEquivProofsTheory.state_equiv_refl] >>
     qexists `bb` >> simp[]) >>
  reverse conj_tac >- simp[] >>
  qpat_x_assum `result_equiv _ _ _` mp_tac >>
  Cases_on `run_function fuel ctx fn s` >>
  Cases_on `run_function fuel ctx
    (fn with fn_blocks := MAP (transform_block_dload pairs) fn.fn_blocks) s` >>
  simp[result_equiv_def, lift_result_def, state_equiv_def, execution_equiv_def,
    revert_equiv_def]
QED

Finalise mm_dload_visit_correct
