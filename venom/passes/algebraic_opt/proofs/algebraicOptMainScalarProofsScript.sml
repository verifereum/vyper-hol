Theory algebraicOptMainScalarProofs
Ancestors
  algebraicOptComposeProofs algebraicOptDemandProofs
  algebraicOptChainAvailabilityProofs algebraicOptChainObservationProofs
  algebraicOptDefs algebraicOptShapeProofs venomWf venomInst venomState
  venomExecSemantics
Libs
  listTheory

Theorem ao_source_resolved_operand_exact:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ trace <> [] /\
  ao_source_trace ctx fn trace /\ LAST trace = (h,F,s) /\
  (!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==>
    lookup_var x (SND (SND (HD trace))) = NONE) /\
  MEM inst (fn_insts fn) /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode <> PHI /\
  ~is_truthy_inst inst.inst_opcode /\ inst.inst_opcode <> ISZERO /\
  MEM a inst.inst_operands /\ eval_operand a s = SOME w /\
  ao_main_observations fn V s r /\ s.vs_labels = r.vs_labels /\
  (!i x. MEM i (fn_insts fn) /\
     (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) ==>
  eval_operand (ao_resolve_iszero_op (ao_compute_fn_iszero_targets fn)
                inst.inst_opcode a) r = SOME w
Proof
  strip_tac >>
  `eval_operand a s = eval_operand a r` by
    (irule ao_nontruthy_operand_exact_read >> simp[] >> metis_tac[]) >>
  Cases_on `a`
  >- gvs[ao_resolve_iszero_op_def]
  >- (gvs[eval_operand_def] >>
      Cases_on `ALOOKUP (ao_compute_fn_iszero_targets fn) s'`
      >- simp[ao_resolve_iszero_op_def, eval_operand_def] >>
      rename1 `ALOOKUP (ao_compute_fn_iszero_targets fn) v = SOME chn` >>
      `def_available_at fn bb (SOME inst) v` by
        (gvs[wf_ssa_def, def_dominates_uses_def] >>
         `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
         `MEM inst bb.bb_instructions` by
           (gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
         metis_tac[]) >>
      `eval_operand (Var v) s = SOME w` by simp[eval_operand_def] >>
      `1 < LENGTH chn /\ LAST chn = Var v /\ ao_chain_edges (fn_insts fn) chn /\
       ?ws. LENGTH ws = LENGTH chn /\ ao_word_chain ws /\ LAST ws = w /\
         (!j. j < LENGTH chn ==> eval_operand (EL j chn) s = SOME (EL j ws))` by
        (irule ao_source_computed_chain_values >> simp[] >>
         conj_tac >- (qexistsl [`ctx`, `h`, `trace`] >> asm_rewrite_tac[]) >>
         qexists_tac `SOME inst` >> simp[]) >>
      `inst.inst_opcode <> JNZ /\ inst.inst_opcode <> ASSERT /\
       inst.inst_opcode <> ASSERT_UNREACHABLE` by
        gvs[is_truthy_inst_def] >>
      drule_all ao_main_resolve_chain_exact >> simp[eval_operand_def]) >>
  gvs[ao_resolve_iszero_op_def]
QED

Theorem ao_source_resolved_scalar_step:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ trace <> [] /\
  ao_source_trace ctx fn trace /\ LAST trace = (h,F,s) /\
  (!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==>
    lookup_var x (SND (SND (HD trace))) = NONE) /\
  MEM inst (fn_insts fn) /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  MEM inst.inst_opcode
    [SHL; SHR; SAR; SIGNEXTEND; Exp; ADD; SUB; XOR; AND; MUL;
     Div; SDIV; Mod; SMOD; OR; EQ; GT; LT; SGT; SLT] /\
  step_inst_base inst s = OK t /\
  ao_main_observations fn V s r /\ s.vs_labels = r.vs_labels /\
  (!i x. MEM i (fn_insts fn) /\
     (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) ==>
  ?x v. inst.inst_outputs = [x] /\ t = update_var x v s /\
    step_inst_base (ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn) inst) r =
      OK (update_var x v r)
Proof
  strip_tac >>
  `inst.inst_opcode <> PHI /\ ~is_truthy_inst inst.inst_opcode /\
   inst.inst_opcode <> ISZERO` by gvs[MEM, is_truthy_inst_def] >>
  `!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
     eval_operand (ao_resolve_iszero_op (ao_compute_fn_iszero_targets fn)
                    inst.inst_opcode a) r = SOME w` by
    (rpt strip_tac >> irule ao_source_resolved_operand_exact >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  qpat_x_assum `MEM inst.inst_opcode _` mp_tac >>
  pure_rewrite_tac[MEM] >> strip_tac >>
  gvs[ao_resolve_iszero_inst_def, step_inst_base_opcode_eqs] >>
  gvs[exec_pure2_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem ao_main_scalar_transform_chunk:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ trace <> [] /\
  ao_source_trace ctx fn trace /\ LAST trace = (h,F,s) /\
  (!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==>
    lookup_var x (SND (SND (HD trace))) = NONE) /\
  MEM inst (fn_insts fn) /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  MEM inst.inst_opcode
    [SHL; SHR; SAR; SIGNEXTEND; Exp; ADD; SUB; XOR; AND; MUL;
     Div; SDIV; Mod; SMOD; OR; EQ; GT; LT; SGT; SLT] /\
  step_inst_base inst s = OK t /\
  ao_main_observations fn V s r /\ s.vs_labels = r.vs_labels /\
  (!i x. MEM i (fn_insts fn) /\
     (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) /\
  inst0 = ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn) inst /\
  p = ao_pre_flip_inst inst0 /\
  ao_opt_producer (dfg_build_function fn) inst0 = NONE /\
  SND (fr "not") <> SND (fr "iz") /\
  SND (fr "not") NOTIN V /\ SND (fr "iz") NOTIN V /\
  (!y. y = SND (fr "not") \/ y = SND (fr "iz") ==>
       ~MEM (Var y) p.inst_operands /\ ~MEM y p.inst_outputs) /\
  fr "xor" = fr "not" /\
  (!a w. MEM a p.inst_operands /\ eval_operand a r = SOME w ==>
       in_range (range_get_range ra lbl idx a) w) ==>
  ?u. ao_cmp_exec_chunk fuel ctx
        (ao_transform_inst (dfg_build_function fn) ra lbl idx
          (ao_compute_fn_iszero_targets fn) fr inst) r = OK u /\
      ao_main_observations fn V t u /\
      (u with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
      u.vs_inst_idx = r.vs_inst_idx + LENGTH
        (ao_transform_inst (dfg_build_function fn) ra lbl idx
          (ao_compute_fn_iszero_targets fn) fr inst)
Proof
  strip_tac >>
  drule_all ao_source_resolved_scalar_step >> strip_tac >>
  `step_inst_base p r = OK (update_var x v r)` by
    metis_tac[ao_pre_flip_base_ok] >>
  `MEM p.inst_opcode
    [SHL; SHR; SAR; SIGNEXTEND; Exp; ADD; SUB; XOR; AND; MUL;
     Div; SDIV; Mod; SMOD; OR; EQ; GT; LT; SGT; SLT] /\
   p.inst_outputs = [x] /\ inst0.inst_outputs = [x] /\
   p.inst_opcode = inst.inst_opcode` by
    metis_tac[ao_pre_flip_inst_shape, ao_resolve_iszero_inst_fields] >>
  drule_all ao_peephole_scalar_write_chunk >>
  disch_then (qspecl_then [`dfg_build_function fn`, `fuel`, `ctx`] strip_assume_tac) >>
  drule ao_post_flip_chunk_ok >> strip_tac >>
  `ao_transform_inst (dfg_build_function fn) ra lbl idx
     (ao_compute_fn_iszero_targets fn) fr inst =
   MAP ao_post_flip_inst (ao_peephole_inst (dfg_build_function fn) ra lbl idx fr p)` by
    (simp[ao_transform_inst_def] >>
     gvs[MEM, ao_resolve_iszero_inst_fields]) >>
  `p.inst_opcode = OR /\ ao_all_truthy (dfg_build_function fn) p ==>
     !y. MEM y p.inst_outputs ==> ~ao_main_exact fn y` by
    (strip_tac >> gen_tac >> disch_tac >> irule ao_all_truthy_output_inexact >>
     conj_tac >- gvs[wf_ssa_def] >>
     qexists_tac `inst` >>
     gvs[ao_all_truthy_def, MEM]) >>
  qpat_x_assum `inst0 = _` kall_tac >>
  qpat_x_assum `p = _` kall_tac >>
  qexists_tac `u` >> asm_rewrite_tac[LENGTH_MAP] >>
  irule (INST_TYPE [alpha |-> ``:num``] ao_scalar_chunk_observations) >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED
