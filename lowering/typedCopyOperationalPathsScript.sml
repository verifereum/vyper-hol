(* Concrete execution boundaries for path-bearing typed memory copies. *)
Theory typedCopyOperationalPaths
Ancestors
  typedArrayLoopControlMem fragGasSeqMem fragGasPathMem fragExec memSafeRun venomExecSemantics
  venomExecProofs venomInstProofs venomInst venomState list rich_list arithmetic

Theorem exec_block_no_phi_path_mem:
  !bb s t.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    EVERY (\i. i.inst_opcode <> INVOKE)
      (DROP s.vs_inst_idx bb.bb_instructions) /\
    ~s.vs_halted /\ exec_block 0 ctx bb s = OK t /\
    mem_safe_block 0 ctx bb s /\ ~t.vs_halted /\ t.vs_inst_idx = 0 /\
    lookup_block t.vs_current_bb fn.fn_blocks = SOME target /\
    phi_prefix_length target.bb_instructions = 0 ==>
    ?n. gas_path_mem ctx fn s n (OK t)
Proof
  gen_tac >> measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  Cases_on `step_inst 0 ctx inst s` >> simp[] >>
  rename1 `step_inst 0 ctx inst s = OK u` >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (Cases_on `u.vs_halted` >> simp[] >> strip_tac >> gvs[] >>
      `gas_path_mem_edge ctx fn s (gas_count_step 0 ctx inst s) (OK t)` by
        (simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
         simp[] >>
         conj_tac >- (qpat_x_assum `mem_safe_block 0 ctx bb s` mp_tac >>
                      simp[Once mem_safe_block_def]) >>
         disj1_tac >> qexists_tac `t` >>
         simp[eval_phis_no_phi]) >>
      qexists_tac `gas_count_step 0 ctx inst s` >>
      metis_tac[cj 1 gas_path_mem_rules, cj 2 gas_path_mem_rules, ADD_0]) >>
  strip_tac >>
  gvs[] >>
  drule_all step_preserves_halted >> strip_tac >>
  drule_all step_preserves_control_flow >> strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   inst = EL s.vs_inst_idx bb.bb_instructions` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  qpat_x_assum `EVERY _ _` mp_tac >>
  drule DROP_CONS_EL >> disch_then SUBST1_TAC >> simp[] >> strip_tac >>
  qpat_x_assum `inst = EL _ _` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `mem_safe_block 0 ctx bb s` mp_tac >>
  simp[Once mem_safe_block_def] >>
  strip_tac >>
  `?n. gas_path_mem ctx fn (u with vs_inst_idx := SUC s.vs_inst_idx) n (OK t)` by
    (first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >> simp[] >>
     disch_then (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
     simp[]) >>
  `gas_path_mem_edge ctx fn s (gas_count_step 0 ctx inst s)
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (simp[gas_path_mem_edge_def] >> qexists_tac `0` >> simp[]) >>
  metis_tac[cj 2 gas_path_mem_rules]
QED

Theorem typed_sa_header_path_mem:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      typed_sa_header_insts id ctr cmp done ncount body_lbl exit_lbl|> /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  eval_operand (Var ctr) s = SOME (n2w i) /\
  i <= ncount /\ ncount < dimword(:256) /\
  lookup_block (if i < ncount then body_lbl else exit_lbl) fn.fn_blocks = SOME next_bb /\
  phi_prefix_length next_bb.bb_instructions = 0 ==>
  ?n. gas_path_mem ctx fn s n
    (OK (jump_to (if i < ncount then body_lbl else exit_lbl)
      (typed_sa_header_state cmp done i ncount s)))
Proof
  strip_tac >>
  drule_all typed_sa_header_control >> disch_then assume_tac >>
  drule typed_sa_header_mem_safe >> disch_then assume_tac >>
  irule exec_block_no_phi_path_mem >> goal_assum (drule_at Any) >>
  simp[] >>
  simp[typed_sa_header_insts_def, mk_inst_def, jump_to_def,
       typed_sa_header_state_def, update_var_def]
QED
