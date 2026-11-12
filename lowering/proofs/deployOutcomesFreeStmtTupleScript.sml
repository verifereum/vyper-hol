Theory deployOutcomesFreeStmtTuple
Ancestors
  deployOutcomesFreeLowering deployOutcomesFreeTyping
  deployOutcomesFreeStmtValues stmtLowering supportedStmtTraverse compileEnv list

Theorem outcomes_free_compile_tuple_store_all:
  P INVALID /\
  (!env ce bt vt s. type_place_target env bt = SOME vt /\
    ~supported_target_exists constructor_call_root bt /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_get_target_ptr compile_expr ce bt s)))) /\
  (!ce dst loc value prim bounded dt st info bytes s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND
      (compile_assign_value ce dst loc value prim bounded dt st info bytes s)))) /\
  (!imm dst value loc s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_at_loc imm dst value loc s)))) ==>
  !tys targets vals env ce s.
    EVERY (\tgt. ?ty. well_typed_atarget env tgt ty) targets /\
    ~supported_assignments_exists constructor_call_root targets /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_tuple_store_all ce tys targets vals s)))
Proof
  strip_tac >> Induct >> rpt gen_tac >> strip_tac >>
  Cases_on `targets` >> Cases_on `vals` >>
  simp[compile_tuple_store_all_def, outcomes_free_return] >>
  rename1 `compile_tuple_store_all ce (h::tys) (tgt::ts) (v::vs)` >>
  Cases_on `tgt` >>
  gvs[EVERY_DEF, supported_assignment_exists_def]
  >- (simp[compile_tuple_store_all_def] >>
      irule outcomes_free_bind >> reverse conj_tac
      >- metis_tac[outcomes_free_typed_base_atarget] >>
      rpt gen_tac >> strip_tac >> BETA_TAC >>
      simp[comp_bind_def, comp_return_def] >>
      irule outcomes_free_ignore_bind >> reverse conj_tac
      >- (rpt strip_tac >> first_x_assum irule >> simp[] >> qexists `env` >> simp[]) >>
      rpt strip_tac >> IF_CASES_TAC
      >- (IF_CASES_TAC >> simp[outcomes_free_emit_ops]) >> simp[]) >>
  simp[compile_tuple_store_all_def] >>
  irule outcomes_free_ignore_bind >> simp[outcomes_free_emit_ops] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >> qexists `env` >> simp[]
QED

Theorem outcomes_free_compile_tuple_unpack:
  P INVALID /\ P MCOPY /\
  (!bytes s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_alloc_buffer bytes s)))) /\
  (!ce base tys offset s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_tuple_load_all ce base tys offset s)))) /\
  (!tys targets vals env ce s.
    EVERY (\tgt. ?ty. well_typed_atarget env tgt ty) targets /\
    ~supported_assignments_exists constructor_call_root targets /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_tuple_store_all ce tys targets vals s)))) ==>
  !env ce ty stage targets src s.
    EVERY (\tgt. ?ty. well_typed_atarget env tgt ty) targets /\
    ~supported_assignments_exists constructor_call_root targets /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_tuple_unpack ce ty stage targets src s)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  simp[compile_tuple_unpack_def] >> IF_CASES_TAC
  >- simp[outcomes_free_emit_ops] >>
  irule outcomes_free_bind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> BETA_TAC >>
      irule outcomes_free_bind >> conj_tac
      >- (rpt gen_tac >> strip_tac >> BETA_TAC >>
          first_x_assum irule >> simp[] >> qexists `env` >> simp[]) >>
      simp[]) >>
  qmatch_goalsub_abbrev_tac `if stage_ok then _ else _` >>
  Cases_on `stage_ok` >> simp[outcomes_free_return] >>
  rpt gen_tac >> strip_tac >>
  (irule outcomes_free_bind >> reverse conj_tac
      >- simp[] >>
      rpt gen_tac >> strip_tac >> BETA_TAC >>
      simp[comp_bind_def, comp_return_def] >>
      irule outcomes_free_ignore_bind >>
      simp[outcomes_free_emit_ops, outcomes_free_return]) >>
  simp[outcomes_free_return]
QED
