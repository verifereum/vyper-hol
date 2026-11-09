(* Scratch-site execution, including reuse on loop iterations. *)
Theory lowerDloadScratchSafety
Ancestors
  lowerDloadSafetyKernel venomExecSemantics venomState finite_map words
  unitMemInv unitTransformDefs contextCodegenRel codegenRel lowerDloadDefs irSupply

Theorem lower_dload_scratch_alloca:
  inst.inst_outputs = [a] /\
  s.vs_alloca_next < dimword(:256) /\
  (FLOOKUP s.vs_allocas inst.inst_id = NONE ==>
    s.vs_alloca_next + 32 < dimword(:256)) /\
  (!b n. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) ==>
    n = 32 /\ b + 32 <= s.vs_alloca_next) ==>
  ?t c. exec_alloca inst s (32w:bytes32) = OK t /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (c,32) /\
    FLOOKUP t.vs_vars a = SOME (n2w c) /\
    c + 32 <= t.vs_alloca_next /\
    t.vs_alloca_next < dimword(:256) /\
    t.vs_memory = s.vs_memory /\
    (!v. v <> a ==> FLOOKUP t.vs_vars v = FLOOKUP s.vs_vars v)
Proof
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- gvs[exec_alloca_def, update_var_def, FLOOKUP_UPDATE, dimword_def] >>
  PairCases_on `x` >>
  fs[] >>
  simp[exec_alloca_def] >>
  qexists_tac `x0` >>
  simp[update_var_def, FLOOKUP_UPDATE]
QED

(* Only the concrete expansion opcodes are exposed at this boundary. *)
Theorem lower_dload_pure_raw[local]:
  (inst.inst_opcode = ALLOCA \/ inst.inst_opcode = ADD) /\
  s.vs_alloca_next < dimword(:256) ==>
  raw_mem_ok C fn inst s
Proof
  simp[raw_mem_ok_def, inst_mem_ok_in_fn_def,
       inst_mem_below_frontier_def] >> strip_tac >>
  simp[source_memory_read_ranges_def, source_memory_write_ranges_def]
QED

Theorem lower_dload_add_preserves[local]:
  inst.inst_opcode = ADD /\ inst.inst_outputs = [z] /\
  step_inst 0 C inst s = OK t ==>
  t.vs_alloca_next = s.vs_alloca_next /\
  (!a. a <> z ==> FLOOKUP t.vs_vars a = FLOOKUP s.vs_vars a)
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_pure2_def,
      AllCaseEqs(), update_var_def, FLOOKUP_UPDATE]
QED

Theorem lower_dload_codecopy_preserves[local]:
  inst.inst_opcode = CODECOPY /\
  step_inst 0 C inst s = OK t ==>
  t.vs_alloca_next = s.vs_alloca_next /\ t.vs_vars = s.vs_vars
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def,
      AllCaseEqs(), write_memory_with_expansion_def]
QED

Theorem lower_dload_scratch_access_raw[local]:
  ((inst.inst_opcode = MLOAD /\ inst.inst_operands = [Var a]) \/
   (inst.inst_opcode = CODECOPY /\
    inst.inst_operands = [Var a; Var z; Lit 32w])) /\
  FLOOKUP s.vs_vars a = SOME (n2w c) /\
  c + 32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword(:256) ==>
  raw_mem_ok C fn inst s
Proof
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  strip_tac >>
  `c < dimword(:256)` by decide_tac >>
  simp[raw_mem_ok_def, inst_mem_ok_in_fn_def] >> disj1_tac >>
  simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, sized_source_write_range_def,
       eval_operand_def, lookup_var_def] >>
  Cases_on `FLOOKUP s.vs_vars z` >> simp[]
QED

Theorem lower_dload_prefix_scratch[local]:
  X = [<|inst_id := ai; inst_opcode := ALLOCA;
         inst_operands := [Lit 32w]; inst_outputs := [a]|>;
       <|inst_id := zi; inst_opcode := ADD;
         inst_operands := [off; Label "code_end"]; inst_outputs := [z]|>;
       <|inst_id := ci; inst_opcode := CODECOPY;
         inst_operands := [Var a; Var z; Lit 32w]; inst_outputs := []|>;
       <|inst_id := mi; inst_opcode := MLOAD;
         inst_operands := [Var a]; inst_outputs := [out]|>] /\
  a <> z /\ t0.vs_alloca_next < dimword(:256) /\
  (FLOOKUP t0.vs_allocas ai = NONE ==>
    t0.vs_alloca_next + 32 < dimword(:256)) /\
  (!b n. FLOOKUP t0.vs_allocas ai = SOME(b,n) ==>
    n = 32 /\ b + 32 <= t0.vs_alloca_next) ==>
  !h t. ld_prefix C fn X p h t0 t ==>
    t.vs_alloca_next < dimword(:256) /\
    (0 < h ==> ?c. FLOOKUP t.vs_vars a = SOME(n2w c) /\
                       c + 32 <= t.vs_alloca_next)
Proof
  strip_tac >> Induct_on `h`
  >- (simp[ld_prefix_zero] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> disch_tac >>
  drule ld_prefix_bound >> simp[] >> strip_tac >>
  drule ld_prefix_predecessor >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  Cases_on `h = 0`
  >- (fs[ld_prefix_zero] >>
      `(HD X).inst_outputs = [a]` by simp[] >>
      drule lower_dload_scratch_alloca >>
      disch_then (qspec_then `t0` mp_tac) >>
      `(HD X).inst_id = ai` by simp[] >>
      asm_rewrite_tac [] >> strip_tac >>
      qpat_x_assum `!b n. _` kall_tac >>
      qpat_x_assum `!v. v <> a ==> _` kall_tac >>
      qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
      simp[step_inst_non_invoke, step_inst_base_def, eval_operand_def] >>
      fs[] >> metis_tac[]) >>
  qpat_x_assum `!b n. _` kall_tac >>
  Cases_on `h = 1`
  >- (fs[] >>
      `(EL 1 X).inst_opcode = ADD /\ (EL 1 X).inst_outputs = [z]`
        by simp[] >>
      drule_all lower_dload_add_preserves >> strip_tac >>
      conj_tac >- simp[] >> qexists_tac `c` >> simp[]) >>
  `h = 2` by decide_tac >> fs[] >>
  `(EL 2 X).inst_opcode = CODECOPY` by simp[] >>
  drule_all lower_dload_codecopy_preserves >> strip_tac >>
  conj_tac >- simp[] >> qexists_tac `c` >> simp[]
QED

Theorem lower_dload_expansion_prefix_raw:
  X = [<|inst_id := ai; inst_opcode := ALLOCA;
         inst_operands := [Lit 32w]; inst_outputs := [a]|>;
       <|inst_id := zi; inst_opcode := ADD;
         inst_operands := [off; Label "code_end"]; inst_outputs := [z]|>;
       <|inst_id := ci; inst_opcode := CODECOPY;
         inst_operands := [Var a; Var z; Lit 32w]; inst_outputs := []|>;
       <|inst_id := mi; inst_opcode := MLOAD;
         inst_operands := [Var a]; inst_outputs := [out]|>] /\
  a <> z /\ t0.vs_alloca_next < dimword(:256) /\
  (FLOOKUP t0.vs_allocas ai = NONE ==>
    t0.vs_alloca_next + 32 < dimword(:256)) /\
  (!b n. FLOOKUP t0.vs_allocas ai = SOME(b,n) ==>
    n = 32 /\ b + 32 <= t0.vs_alloca_next) /\
  ld_prefix C fn X p h t0 t ==>
  raw_mem_ok C fn (EL h X) t
Proof
  strip_tac >>
  drule_all lower_dload_prefix_scratch >>
  strip_tac >>
  drule ld_prefix_bound >> simp[] >> strip_tac >>
  qpat_x_assum `!b n. _` kall_tac >>
  Cases_on `h = 0 \/ h = 1`
  >- (irule lower_dload_pure_raw >> fs[] >> simp[]) >>
  `0 < h` by decide_tac >> fs[] >>
  irule lower_dload_scratch_access_raw >>
  conj_tac >- simp[] >>
  qexistsl_tac [`a`, `c`, `z`] >>
  `h = 2 \/ h = 3` by decide_tac >> fs[] >> simp[]
QED

Theorem lower_dload_supply_prefix_raw:
  lower_dload_inst_supply u inst = (X,u') /\
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\
  inst.inst_outputs = [out] /\
  t0.vs_alloca_next < dimword(:256) /\
  (FLOOKUP t0.vs_allocas (HD X).inst_id = NONE ==>
    t0.vs_alloca_next + 32 < dimword(:256)) /\
  (!b n. FLOOKUP t0.vs_allocas (HD X).inst_id = SOME(b,n) ==>
    n = 32 /\ b + 32 <= t0.vs_alloca_next) /\
  ld_prefix C fn X p h t0 t ==>
  raw_mem_ok C fn (EL h X) t
Proof
  strip_tac >>
  qpat_x_assum `lower_dload_inst_supply _ _ = _` mp_tac >>
  namedCases_on `fresh_ir_var u` ["a u1"] >>
  namedCases_on `fresh_ir_var u1` ["z u2"] >>
  namedCases_on `fresh_inst_id u2` ["ai u3"] >>
  namedCases_on `fresh_inst_id u3` ["zi u4"] >>
  namedCases_on `fresh_inst_id u4` ["ci u5"] >>
  namedCases_on `fresh_inst_id u5` ["mi u6"] >>
  qpat_assum `inst.inst_opcode = DLOAD` (fn hop =>
    qpat_assum `inst.inst_operands = [off]` (fn hargs =>
      qpat_assum `inst.inst_outputs = [out]` (fn houts =>
        pure_rewrite_tac [lower_dload_inst_supply_def, hop, hargs, houts,
          COND_CLAUSES, listTheory.list_case_def, pairTheory.pair_case_thm]))) >>
  ntac 6 (pure_rewrite_tac [pairTheory.pair_case_thm] >>
          CONV_TAC (DEPTH_CONV BETA_CONV) >>
          pure_asm_rewrite_tac []) >>
  strip_tac >>
  drule_all fresh_ir_var_two_calls_distinct >> strip_tac >>
  fs[] >>
  irule lower_dload_expansion_prefix_raw >>
  goal_assum (drule_at (Pat `ld_prefix _ _ _ _ _ _ _`)) >>
  qpat_assum `[_;_;_;_] = X` (assume_tac o SYM) >>
  goal_assum (drule_at (Pat `_ = [_;_;_;_]`)) >>
  `(HD X).inst_id = ai` by
    (qpat_x_assum `X = [_;_;_;_]` (fn th => rewrite_tac [th]) >>
     simp[NoAsms]) >>
  qpat_x_assum `[_;_;_;_] = X` kall_tac >>
  qpat_x_assum `X = [_;_;_;_]` kall_tac >>
  asm_rewrite_tac [] >> metis_tac[]
QED
