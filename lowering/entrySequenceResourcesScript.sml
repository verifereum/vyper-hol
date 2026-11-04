(* Resource preservation for exact instruction sequences. *)
Theory entrySequenceResources
Ancestors
  exprLoweringProps venomExecSemantics venomState venomInst venomMemProps finite_map list

Theorem step_inst_base_alloca_room[local]:
  !func inst s s' ctx.
    step_inst_base inst s = OK s' /\ MEM inst (fn_insts func) /\
    inst.inst_opcode <> INVOKE /\ alloca_room ctx func s ==>
    alloca_room ctx func s'
Proof
  rpt strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
      asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
      simp[exec_alloca_def, AllCaseEqs()] >> strip_tac >> gvs[]
      >~ [`FLOOKUP s.vs_allocas inst.inst_id = SOME _`]
      >- (irule alloca_room_fields >> qexists_tac `s` >>
          simp[update_var_def]) >>
      `inst.inst_id NOTIN FDOM s.vs_allocas` by fs[FLOOKUP_DEF] >>
      drule_all alloca_room_fresh >> strip_tac >>
      irule alloca_room_fields >>
      qexists_tac `s with <| vs_allocas := s.vs_allocas |+
                               (inst.inst_id, (s.vs_alloca_next, w2n alloc_size));
                             vs_alloca_next := s.vs_alloca_next + w2n alloc_size |>` >>
      simp[update_var_def]) >>
  irule alloca_room_fields >> qexists_tac `s` >> simp[] >>
  metis_tac[step_inst_base_preserves_allocas,
            step_inst_base_preserves_alloca_next]
QED

Theorem run_inst_seq_alloca_room:
  !is func s t ctx.
    run_inst_seq is s = OK t /\
    EVERY (\i. MEM i (fn_insts func) /\ i.inst_opcode <> INVOKE) is /\
    alloca_room ctx func s ==>
    alloca_room ctx func t
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >>
  Cases_on `step_inst_base h s` >> simp[] >> strip_tac >>
  rename1 `run_inst_seq is s1 = OK t` >>
  qpat_x_assum `!func s t. _` irule >> simp[] >> qexists_tac `s1` >> simp[] >>
  irule step_inst_base_alloca_room >> metis_tac[]
QED
