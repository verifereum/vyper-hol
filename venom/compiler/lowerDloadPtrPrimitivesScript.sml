(* Primitive interfaces for the LowerDload pointer contract. *)
Theory lowerDloadPtrPrimitives
Ancestors
  ptrDiscipline venomExecSemantics finite_map words pred_set list

Theorem exec_alloca_fresh_site:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE ==>
  exec_alloca inst s szword =
    OK (update_var out (n2w s.vs_alloca_next)
      (s with <|
        vs_allocas := s.vs_allocas |+
          (inst.inst_id, (s.vs_alloca_next, w2n szword));
        vs_alloca_next := s.vs_alloca_next + w2n szword |>))
Proof
  simp[exec_alloca_def]
QED

Theorem merge_callee_state_allocations[simp]:
  (merge_callee_state caller callee).vs_allocas = caller.vs_allocas /\
  (merge_callee_state caller callee).vs_alloca_next = caller.vs_alloca_next
Proof
  simp[merge_callee_state_def]
QED

Theorem codecopy_clears_written_taint:
  inst.inst_opcode = CODECOPY /\
  i IN range_bytes (step_writes inst s s') ==>
  i NOTIN (step_taint inst s s' tn).t_mem
Proof
  strip_tac >>
  simp[step_taint_def, mem_taint_def, written_taint_def] >>
  namedCases_on `inst.inst_operands` ["", "a rest"] >> simp[] >>
  namedCases_on `rest` ["", "b rest2"] >> simp[] >>
  namedCases_on `rest2` ["", "c rest3"] >> simp[] >>
  Cases_on `rest3` >> simp[]
QED

Theorem codecopy_range_untainted:
  inst.inst_opcode = CODECOPY /\
  inst.inst_operands = [dst; src; n_op] /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
  eval_operand n_op s = SOME n /\
  w2n d <= i /\ i < w2n d + w2n n ==>
  i NOTIN (step_taint inst s s' tn).t_mem
Proof
  strip_tac >> irule codecopy_clears_written_taint >>
  simp[step_writes_def, range_bytes_def,
       codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.sized_source_write_range_def] >>
  metis_tac[]
QED

Theorem exec_alloca_fresh_fields:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  exec_alloca inst s szword = OK s' ==>
  s'.vs_alloca_next = s.vs_alloca_next + w2n szword /\
  FLOOKUP s'.vs_allocas inst.inst_id =
    SOME (s.vs_alloca_next, w2n szword) /\
  (!aid. aid <> inst.inst_id ==>
    FLOOKUP s'.vs_allocas aid = FLOOKUP s.vs_allocas aid)
Proof
  strip_tac >>
  drule_all exec_alloca_fresh_site >>
  disch_then (qspec_then `szword` mp_tac) >>
  gvs[venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Two distinct zero-size sites have identical numeric provenance before
   a scratch allocation is inserted between them. *)
Theorem zero_site_comparison_before:
  access_ok 0
    (FEMPTY |+ ("p", (0,0)) |+ ("q", (0,0))) fn
    (venomInst$mk_inst 3 EQ [Var "p"; Var "q"] ["c"])
    (s with vs_vars := FEMPTY |+ ("p", 0w) |+ ("q", 0w))
Proof
  simp[access_ok_def, venomInstTheory.mk_inst_def,
       codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem zero_site_comparison_after:
  ~access_ok 0
    (FEMPTY |+ ("p", (0,0)) |+ ("q", (32,0))) fn
    (venomInst$mk_inst 3 EQ [Var "p"; Var "q"] ["c"])
    (s with vs_vars := FEMPTY |+ ("p", 0w) |+ ("q", 32w))
Proof
  simp[access_ok_def, venomInstTheory.mk_inst_def,
       codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  qexistsl [`"p"`, `"q"`] >> simp[]
QED
