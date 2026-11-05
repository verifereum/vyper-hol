Theory algebraicOptRangeConditionProofs
Ancestors
  rangeAnalysisProofs rangeAnalysisDefs dfgAnalysis dfgAnalysisProps venomInst finite_map
  algebraicOptFreshnessProofs algebraicOptTraceProofs algebraicOptRangeProofs
  venomExecSemantics venomState venomWf rich_list

(* Conditional interfaces: producer provenance is a separate obligation. *)
Theorem ao_range_condition_assign_local:
  !dfg fuel v inst op b rs env.
    dfg_get_def dfg v = SOME inst /\ inst.inst_opcode = ASSIGN /\
    inst.inst_operands = [op] /\
    in_range_state (range_apply_condition dfg fuel op b rs) env ==>
    in_range_state (range_apply_condition dfg (SUC fuel) (Var v) b rs) env
Proof
  rpt strip_tac >> simp[Once range_apply_condition_def]
QED

Theorem ao_range_condition_iszero_local:
  !dfg fuel v inst u b rs env.
    dfg_get_def dfg v = SOME inst /\ inst.inst_opcode = ISZERO /\
    inst.inst_operands = [Var u] /\ in_range_state rs env /\
    (b ==> FLOOKUP env u = SOME 0w) /\
    (~b ==> !w. FLOOKUP env u = SOME w ==> w <> 0w) ==>
    in_range_state (range_apply_condition dfg (SUC fuel) (Var v) b rs) env
Proof
  rpt strip_tac >> simp[Once range_apply_condition_def] >>
  irule range_apply_iszero_sound >> metis_tac[optionTheory.SOME_11]
QED

(* Runtime-premise audit (not additional asserted invariants).

   range_apply_condition recurses only through ASSIGN. ISZERO, EQ and
   LT/GT/SLT/SGT are terminal refinements; PHI and other producers are identity.
   Thus an ASSIGN chain needs current evaluation equality at every link,
   followed by operand facts for one terminal producer, not global dfg_sound.

   Checked obstruction: algebraicOptFreshnessProbe.ao_fresh_fixture_wf and
   ao_fresh_second_phis describe entry -> header -> body -> header. After
   the second parallel PHI batch, x=1 and old z=1, although z=ISZERO x.
   ao_fresh_unrestricted_transport_fails checks this mismatch by evaluation.
   The PHI selecting old z observes the predecessor state (old x=0), not
   the post-batch state. At the next actual ordinary use of z, its ISZERO
   producer has executed again: ao_fresh_selected_edge_and_ordinary_equations
   checks these two legitimate observation points. This refutes universal
   stored-producer equations, not correctness of a used branch condition.

   Available source boundary: ao_source_trace_last_iszero in
   algebraicOptFreshnessProofs supplies a last successful producer event,
   output-value preservation, and operand-evaluation transport to an ordinary
   observation with def_available_at. Its selected_phi counterpart observes
   the selected predecessor before PHIs. Together with ao_iszero_producer_step
   these justify the ISZERO relation at that observation, conditional on its
   stated lookup, producer-location and availability premises. A branch's
   evaluated Var condition supplies the non-NONE lookup. Frozen wf_ssa gives
   availability for its actual ordinary use. Trace initialization and source
   location bridges must still be discharged, not silently assumed.

   Checked ASSIGN-chain boundary: ao_source_trace_assign_operand below
   gives current operand evaluation and recursive variable availability at
   the same ordinary observation. Var transport uses the generic last-producer
   operand boundary and availability composition. Lit uses the successful
   last-output event; Label additionally uses source-trace label-map
   preservation, not an assumption that labels are state-independent.
   These interfaces do not assert arbitrary all-stored-variable stability.
   EQ/comparison terminal provenance and full condition closure remain separate.

   Terminal signature ledger (rangeAnalysisProofs):
   - range_apply_iszero_sound needs zero/nonzero consequences for the current
     operand lookup; ao_range_condition_iszero_local exposes a sufficient form.
   - range_apply_eq_sound needs, on a true condition, defined variable operands,
     variable/literal equality, and equality of variable/variable values.
     Historical EQ execution alone is insufficient without operand transport.
     False EQ adds no refinement and needs no equality equation.
   - range_apply_compare_sound needs the actual signed/unsigned comparison
     truth equivalence for each variable/literal orientation. Variable/variable
     comparisons do not refine ranges. Again current operand transport is the
     missing provenance obligation, not a new numeric narrowing proof.

   These conditional boundaries do not establish reachable range soundness.
*)

Theorem ao_assign_step_value:
  !q ctx inst u w op x.
    inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
    inst.inst_outputs = [x] /\ step_inst q ctx inst u = OK w ==>
    eval_operand op u = lookup_var x w
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once step_inst_def, step_inst_base_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem ao_source_trace_assign_operand:
  !ctx fn trace bp r prod x op target use_opt h t value.
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ trace <> [] /\
    ao_source_trace ctx fn trace /\ LAST trace = (h,F,t) /\
    lookup_var x (SND (SND (HD trace))) = NONE /\
    lookup_var x t = SOME value /\ MEM bp fn.fn_blocks /\
    get_instruction bp r = SOME prod /\ prod.inst_opcode = ASSIGN /\
    prod.inst_outputs = [x] /\ prod.inst_operands = [op] /\
    phi_prefix_length bp.bb_instructions <= r /\
    lookup_block t.vs_current_bb fn.fn_blocks = SOME target /\
    def_available_at fn target use_opt x /\
    (case use_opt of
       SOME use => get_instruction target t.vs_inst_idx = SOME use /\
                   use.inst_opcode <> PHI
     | NONE => ?term. get_instruction target t.vs_inst_idx = SOME term /\
                      is_terminator term.inst_opcode) ==>
    eval_operand op t = SOME value /\
    (!z. op = Var z ==> def_available_at fn target use_opt z)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM prod bp.bb_instructions` by
    (gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[listTheory.MEM_EL]) >>
  `!z. op = Var z ==> def_available_at fn bp (SOME prod) z` by
    (rpt strip_tac >> fs[wf_ssa_def, def_dominates_uses_def] >>
     first_x_assum drule_all >> simp[]) >>
  reverse conj_tac
  >- (rpt strip_tac >> irule ao_available_through_producer >>
      simp[] >> qexistsl [`bp`,`prod`,`x`] >> simp[]) >>
  `prod.inst_opcode <> PHI /\ ~is_terminator prod.inst_opcode /\
   MEM x prod.inst_outputs` by simp[is_terminator_def] >>
  Cases_on `op`
  >~ [`eval_operand (Var z) t = SOME value`]
  >- (`MEM (Var z) prod.inst_operands /\
      def_available_at fn bp (SOME prod) z` by simp[] >>
     drule_all ao_source_trace_last_producer_operand >> strip_tac >>
     drule_all ao_assign_step_value >>
     gvs[lookup_var_def]) >>
  drule_all ao_source_trace_last_output >> strip_tac >>
  `MEM (q,F,u) trace` by simp[] >>
  `MEM (h,F,t) trace` by metis_tac[rich_listTheory.LAST_MEM] >>
  `t.vs_labels = u.vs_labels` by metis_tac[ao_source_trace_labels] >>
  drule_all ao_assign_step_value >>
  gvs[eval_operand_def, lookup_var_def]
QED

Theorem ao_pure2_step_value[local]:
  !f inst u w lhs rhs x.
    inst.inst_operands = [lhs;rhs] /\ inst.inst_outputs = [x] /\
    exec_pure2 f inst u = OK w ==>
    ?a b. eval_operand lhs u = SOME a /\ eval_operand rhs u = SOME b /\
          lookup_var x w = SOME (f a b)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[exec_pure2_def, AllCaseEqs()] >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED



Theorem ao_source_trace_eq_refine_sound:
  !ctx fn trace bp r prod x lhs rhs target use_opt h t value rs b.
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ trace <> [] /\
    ao_source_trace ctx fn trace /\ LAST trace = (h,F,t) /\
    lookup_var x (SND (SND (HD trace))) = NONE /\
    lookup_var x t = SOME value /\ MEM bp fn.fn_blocks /\
    get_instruction bp r = SOME prod /\ prod.inst_opcode = EQ /\
    prod.inst_outputs = [x] /\ prod.inst_operands = [lhs;rhs] /\
    phi_prefix_length bp.bb_instructions <= r /\
    lookup_block t.vs_current_bb fn.fn_blocks = SOME target /\
    def_available_at fn target use_opt x /\
    (case use_opt of
       SOME use => get_instruction target t.vs_inst_idx = SOME use /\
                   use.inst_opcode <> PHI
     | NONE => ?term. get_instruction target t.vs_inst_idx = SOME term /\
                      is_terminator term.inst_opcode) /\
    in_range_state rs t.vs_vars /\ (b <=> value <> 0w) ==>
    in_range_state (range_apply_eq lhs rhs b rs) t.vs_vars
Proof
  rpt gen_tac >> strip_tac >>
  `prod.inst_opcode <> PHI /\ ~is_terminator prod.inst_opcode /\
   MEM x prod.inst_outputs` by simp[is_terminator_def] >>
  drule_all ao_source_trace_last_producer_operands >> strip_tac >>
  `exec_pure2 (\a b. bool_to_word (a = b)) prod u = OK w` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[Once step_inst_def, step_inst_base_def]) >>
  drule_all ao_pure2_step_value >> strip_tac >>
  `eval_operand lhs t = SOME a /\ eval_operand rhs t = SOME b'` by
    metis_tac[listTheory.MEM] >>
  qpat_x_assum `!op. _` kall_tac >>
  Cases_on `a = b'` >>
  gvs[lookup_var_def, venomExecSemanticsTheory.bool_to_word_def] >>
  irule range_apply_eq_sound >> simp[] >>
  rpt strip_tac >> gvs[eval_operand_def, lookup_var_def] >> metis_tac[]
QED

Theorem ao_compare_step_value[local]:
  !q ctx inst u w lhs rhs x.
    (inst.inst_opcode = LT \/ inst.inst_opcode = GT \/
     inst.inst_opcode = SLT \/ inst.inst_opcode = SGT) /\
    inst.inst_operands = [lhs;rhs] /\ inst.inst_outputs = [x] /\
    step_inst q ctx inst u = OK w ==>
    ?a b. eval_operand lhs u = SOME a /\ eval_operand rhs u = SOME b /\
      lookup_var x w = SOME (bool_to_word
        (if inst.inst_opcode = LT then w2n a < w2n b
         else if inst.inst_opcode = GT then w2n a > w2n b
         else if inst.inst_opcode = SLT then w2i a < w2i b
         else w2i a > w2i b))
Proof
  rpt gen_tac >> strip_tac >> simp[] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once step_inst_def] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  pure_asm_rewrite_tac[opcode_case_def] >> strip_tac >>
  drule_all ao_pure2_step_value >>
  simp[integer_wordTheory.WORD_LTi, integer_wordTheory.WORD_GTi]
QED

Theorem ao_source_trace_compare_refine_sound:
  !ctx fn trace bp r prod x lhs rhs target use_opt h t value rs b.
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ trace <> [] /\
    ao_source_trace ctx fn trace /\ LAST trace = (h,F,t) /\
    lookup_var x (SND (SND (HD trace))) = NONE /\
    lookup_var x t = SOME value /\ MEM bp fn.fn_blocks /\
    get_instruction bp r = SOME prod /\
    (prod.inst_opcode = LT \/ prod.inst_opcode = GT \/
     prod.inst_opcode = SLT \/ prod.inst_opcode = SGT) /\
    prod.inst_outputs = [x] /\ prod.inst_operands = [lhs;rhs] /\
    phi_prefix_length bp.bb_instructions <= r /\
    lookup_block t.vs_current_bb fn.fn_blocks = SOME target /\
    def_available_at fn target use_opt x /\
    (case use_opt of
       SOME use => get_instruction target t.vs_inst_idx = SOME use /\
                   use.inst_opcode <> PHI
     | NONE => ?term. get_instruction target t.vs_inst_idx = SOME term /\
                      is_terminator term.inst_opcode) /\
    in_range_state rs t.vs_vars /\ (b <=> value <> 0w) ==>
    in_range_state (range_apply_compare prod.inst_opcode lhs rhs b rs) t.vs_vars
Proof
  rpt gen_tac >> disch_tac >>
  `prod.inst_opcode <> PHI /\ ~is_terminator prod.inst_opcode /\
   MEM x prod.inst_outputs` by
    (fs[is_terminator_def] >> metis_tac[]) >>
  (* Each opcode case consumes the same generic event and operand boundary. *)
  fs[SF CONJ_ss] >>
  drule_all ao_source_trace_last_producer_operands >> strip_tac >>
  drule_at (Pat `step_inst _ _ _ _ = _`) ao_compare_step_value >>
  simp[] >> strip_tac >>
  `eval_operand lhs t = SOME a /\ eval_operand rhs t = SOME b'` by
    metis_tac[listTheory.MEM] >>
  qpat_x_assum `!op. _` kall_tac >>
  irule range_apply_compare_sound >> simp[] >>
  rpt strip_tac >>
  gvs[eval_operand_def, lookup_var_def] >>
  qmatch_goalsub_abbrev_tac `bool_to_word test` >>
  Cases_on `test` >> simp[venomExecSemanticsTheory.bool_to_word_def]
QED

Theorem ao_non_phi_index_after_prefix:
  !insts r. r < LENGTH insts /\ (EL r insts).inst_opcode <> PHI ==>
    phi_prefix_length insts <= r
Proof
  Induct_on `insts` >- simp[] >>
  Cases_on `r` >> simp[phi_prefix_length_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem ao_dfg_source_producer:
  !fn x prod.
    dfg_get_def (dfg_build_function fn) x = SOME prod /\
    prod.inst_opcode <> PHI ==>
    MEM x prod.inst_outputs /\
    ?bp r. MEM bp fn.fn_blocks /\ get_instruction bp r = SOME prod /\
           phi_prefix_length bp.bb_instructions <= r
Proof
  rpt gen_tac >> strip_tac >>
  drule dfg_build_function_correct >> strip_tac >> simp[] >>
  fs[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
  qpat_x_assum `MEM prod _` (strip_assume_tac o REWRITE_RULE [listTheory.MEM_EL]) >>
  qexistsl [`bb`,`n`] >> simp[get_instruction_def] >>
  irule ao_non_phi_index_after_prefix >> gvs[]
QED

Theorem ao_dfg_singleton_output:
  !fn x prod.
    dfg_get_def (dfg_build_function fn) x = SOME prod /\
    LENGTH prod.inst_outputs = 1 ==> prod.inst_outputs = [x]
Proof
  rpt strip_tac >> drule dfg_build_function_correct >> strip_tac >>
  Cases_on `prod.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[]
QED

Theorem ao_source_trace_condition_sound:
  !fuel ctx fn trace target use_opt h t op value b rs.
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ trace <> [] /\
    ao_source_trace ctx fn trace /\ LAST trace = (h,F,t) /\
    (!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
      lookup_var x (SND (SND (HD trace))) = NONE) /\
    lookup_block t.vs_current_bb fn.fn_blocks = SOME target /\
    (case use_opt of
       SOME use => get_instruction target t.vs_inst_idx = SOME use /\
                   use.inst_opcode <> PHI
     | NONE => ?term. get_instruction target t.vs_inst_idx = SOME term /\
                      is_terminator term.inst_opcode) /\
    (!x. op = Var x ==> def_available_at fn target use_opt x) /\
    eval_operand op t = SOME value /\ (b <=> value <> 0w) /\
    in_range_state rs t.vs_vars ==>
    in_range_state
      (range_apply_condition (dfg_build_function fn) fuel op b rs) t.vs_vars
Proof
  Induct_on `fuel` >- simp[range_apply_condition_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `op`
  >~ [`range_apply_condition _ _ (Lit _) _ _`] >- simp[Once range_apply_condition_def]
  >~ [`range_apply_condition _ _ (Label _) _ _`] >- simp[Once range_apply_condition_def] >>
  rename1 `eval_operand (Var x) t = SOME value` >>
  Cases_on `dfg_get_def (dfg_build_function fn) x`
  >- simp[Once range_apply_condition_def] >>
  rename1 `dfg_get_def (dfg_build_function fn) x = SOME prod` >>
  Cases_on `prod.inst_opcode = PHI`
  >- simp[Once range_apply_condition_def] >>
  drule_all ao_dfg_source_producer >> strip_tac >>
  `MEM prod (fn_insts fn)` by metis_tac[dfg_build_function_correct] >>
  `lookup_var x (SND (SND (HD trace))) = NONE` by metis_tac[] >>
  `lookup_var x t = SOME value /\ def_available_at fn target use_opt x` by
    gvs[eval_operand_def] >>
  `inst_wf prod` by
    (fs[fn_inst_wf_def, fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
     metis_tac[]) >>
  Cases_on `prod.inst_opcode = ASSIGN`
  >- suspend "assign" >>
  Cases_on `prod.inst_opcode = ISZERO`
  >- suspend "iszero" >>
  Cases_on `prod.inst_opcode = EQ`
  >- suspend "eq" >>
  Cases_on `prod.inst_opcode = LT \/ prod.inst_opcode = GT \/
            prod.inst_opcode = SLT \/ prod.inst_opcode = SGT`
  >- suspend "compare" >>
  simp[Once range_apply_condition_def]
QED
Resume ao_source_trace_condition_sound[assign]:
  `LENGTH prod.inst_outputs = 1 /\ LENGTH prod.inst_operands = 1` by
    gvs[inst_wf_def] >>
  `prod.inst_outputs = [x]` by metis_tac[ao_dfg_singleton_output] >>
  Cases_on `prod.inst_operands` >- gvs[] >>
  rename1 `prod.inst_operands = inner::rest` >>
  Cases_on `rest` >> gvs[] >>
  drule_all ao_source_trace_assign_operand >> strip_tac >>
  simp[Once range_apply_condition_def] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  conj_tac
  >- (qexistsl [`ctx`,`h`,`trace`] >> simp[] >> metis_tac[]) >>
  qexists_tac `use_opt` >> simp[]
QED
Resume ao_source_trace_condition_sound[iszero]:
  qpat_x_assum `!ctx fn trace target use_opt h t op value b rs. _` kall_tac >>
  `LENGTH prod.inst_outputs = 1 /\ LENGTH prod.inst_operands = 1` by
    gvs[inst_wf_def] >>
  `prod.inst_outputs = [x]` by metis_tac[ao_dfg_singleton_output] >>
  Cases_on `prod.inst_operands` >- gvs[] >>
  rename1 `prod.inst_operands = inner::rest` >>
  Cases_on `rest` >> gvs[] >> Cases_on `inner`
  >~ [`prod.inst_operands = [Lit _]`] >- simp[Once range_apply_condition_def]
  >~ [`prod.inst_operands = [Label _]`] >- simp[Once range_apply_condition_def] >>
  rename1 `prod.inst_operands = [Var z]` >>
  drule_all ao_source_trace_last_iszero >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once step_inst_def, step_inst_base_def, exec_pure1_def, AllCaseEqs()] >>
  strip_tac >>
  irule ao_range_condition_iszero_local >>
  simp[] >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE, eval_operand_def] >>
  Cases_on `x' = 0w` >> gvs[venomExecSemanticsTheory.bool_to_word_def]
QED
Resume ao_source_trace_condition_sound[eq]:
  qpat_x_assum `!ctx fn trace target use_opt h t op value b rs. _` kall_tac >>
  `LENGTH prod.inst_outputs = 1 /\ LENGTH prod.inst_operands = 2` by
    gvs[inst_wf_def] >>
  `prod.inst_outputs = [x]` by metis_tac[ao_dfg_singleton_output] >>
  Cases_on `prod.inst_operands` >- gvs[] >>
  rename1 `prod.inst_operands = lhs::rest` >>
  Cases_on `rest` >- gvs[] >>
  rename1 `prod.inst_operands = lhs::rhs::rest` >>
  Cases_on `rest` >> gvs[] >>
  simp[Once range_apply_condition_def] >>
  drule_at (Pat `lookup_var _ _ = SOME _`) ao_source_trace_eq_refine_sound >>
  simp[] >> disch_then drule_all >> simp[]
QED
Resume ao_source_trace_condition_sound[compare]:
  qpat_x_assum `!ctx fn trace target use_opt h t op value b rs. _` kall_tac >>
  `LENGTH prod.inst_outputs = 1 /\ LENGTH prod.inst_operands = 2` by
    (fs[SF CONJ_ss] >> gvs[inst_wf_def]) >>
  `prod.inst_outputs = [x]` by metis_tac[ao_dfg_singleton_output] >>
  Cases_on `prod.inst_operands` >- gvs[] >>
  rename1 `prod.inst_operands = lhs::rest` >>
  Cases_on `rest` >- gvs[] >>
  rename1 `prod.inst_operands = lhs::rhs::rest` >>
  Cases_on `rest` >> gvs[] >>
  simp[Once range_apply_condition_def] >>
  drule_at (Pat `lookup_var _ _ = SOME _`) ao_source_trace_compare_refine_sound >>
  disch_then (drule_at (Pat `get_instruction _ _ = SOME _`)) >>
  simp[] >> disch_then drule_all >> simp[]
QED
Finalise ao_source_trace_condition_sound

Theorem ao_source_trace_branch_refine_sound:
  !ctx fn trace k s t bb term rs.
    trace <> [] /\ ao_source_trace ctx fn trace /\ LAST trace = (k,F,s) /\
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
    EVERY label_positions_ok (fn_insts fn) /\
    (!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
      lookup_var x (SND (SND (HD trace))) = NONE) /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME term /\
    is_terminator term.inst_opcode /\ step_inst k ctx term s = OK t /\
    ~t.vs_halted /\ in_range_state rs s.vs_vars ==>
    in_range_state
      (range_branch_refine (dfg_build_function fn) fn.fn_blocks
         s.vs_current_bb t.vs_current_bb rs) t.vs_vars
Proof
  rpt gen_tac >> strip_tac >>
  `t.vs_vars = s.vs_vars` by
    (rw[finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM] >>
     drule_all venomExecPropsTheory.step_terminator_preserves_vars >>
     disch_then (qspec_then `x` mp_tac) >> simp[lookup_var_def]) >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `bb_well_formed bb` by fs[wf_function_def] >>
  `bb.bb_instructions <> [] /\ term = LAST bb.bb_instructions` by
    (fs[get_instruction_def, bb_well_formed_def] >>
     metis_tac[listTheory.LAST_EL]) >>
  simp[range_branch_refine_def] >>
  Cases_on `term.inst_opcode = JNZ` >- suspend "jnz" >>
  gvs[]
QED
Resume ao_source_trace_branch_refine_sound[jnz]:
  `MEM term (fn_insts fn)` by
    (fs[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff,
        get_instruction_def] >> metis_tac[listTheory.MEM_EL]) >>
  `MEM term bb.bb_instructions` by
    (fs[get_instruction_def] >> metis_tac[listTheory.MEM_EL]) >>
  `inst_wf term` by
    (fs[fn_inst_wf_def] >> metis_tac[]) >>
  `?cond yes no. term.inst_operands = [cond;Label yes;Label no]` by
    gvs[inst_wf_def] >>
  `yes <> no` by metis_tac[algebraicOptRangeProofsTheory.ao_range_source_jnz_distinct] >>
  `!x. cond = Var x ==> def_available_at fn bb (SOME term) x` by
    (fs[wf_ssa_def, def_dominates_uses_def] >>
     first_x_assum (drule_at (Pat `MEM _ _.bb_instructions`)) >>
     simp[]) >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once step_inst_def, step_inst_base_def,
       AllCaseEqs()] >> strip_tac >>
  gvs[listTheory.NULL_EQ, jump_to_def] >>
  irule ao_source_trace_condition_sound >>
  goal_assum (drule_at Any) >> simp[] >>
  (conj_tac
   >- (qexistsl [`ctx`,`k`,`trace`] >> simp[] >> metis_tac[]) >>
   qexists_tac `SOME (LAST bb.bb_instructions)` >> simp[] >> metis_tac[])
QED
Finalise ao_source_trace_branch_refine_sound

Theorem ao_range_phis_sound:
  !fn bb s p.
    wf_function fn /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK p /\
    in_range_state (range_at_inst (range_analyze fn) bb.bb_label 0) s.vs_vars ==>
    in_range_state (range_at_inst (range_analyze fn) bb.bb_label
      (phi_prefix_length bb.bb_instructions)) p.vs_vars
Proof
  rpt gen_tac >> strip_tac >>
  `range_sound (df_widen_at NONE (range_analyze fn) bb.bb_label 0) s` by
    (Cases_on `df_widen_at NONE (range_analyze fn) bb.bb_label 0` >>
     gvs[range_at_inst_def, range_sound_def, range_unwrap_def]) >>
  drule_all eval_phis_range_sound >>
  Cases_on `df_widen_at NONE (range_analyze fn) bb.bb_label
    (phi_prefix_length bb.bb_instructions)` >>
  simp[range_at_inst_def, range_sound_def, range_unwrap_def,
       rangeEvalDefsTheory.in_range_state_def]
QED
