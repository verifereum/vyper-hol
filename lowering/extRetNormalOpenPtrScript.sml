Theory extRetNormalOpenPtr
Ancestors
  fragGasPathPtr fragExec venomExecSemantics venomExecProofs venomInstProofs
  venomState venomInst compileEnv list rich_list arithmetic

Theorem terminator_phi_prefix_bound:
  !xs k inst.
    k < LENGTH xs /\ EL k xs = inst /\
    is_terminator inst.inst_opcode ==>
    phi_prefix_length xs <= k
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `k` >> simp[phi_prefix_length_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `h.inst_opcode = PHI` >> gvs[is_terminator_def] >>
  first_x_assum drule_all >> simp[]
QED

Theorem gas_path_ptr_edge_terminator_barrier:
  lookup_block lbl fn.fn_blocks = SOME bb /\
  get_instruction bb k = SOME last /\ is_terminator last.inst_opcode /\
  (s.vs_current_bb = lbl ==> s.vs_inst_idx <= k) /\
  gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' (OK t) ==>
  (t.vs_current_bb = lbl ==> t.vs_inst_idx <= k)
Proof
  rw[gas_path_ptr_edge_def] >>
  gvs[exit_result_def]
  >- (drule_all step_preserves_control_flow >> strip_tac >> gvs[] >>
      `s.vs_inst_idx <> k` by
        (strip_tac >> gvs[]) >> decide_tac)
  >- (drule eval_phis_preserves_current_bb >> strip_tac >> gvs[] >>
      irule terminator_phi_prefix_bound >>
      gvs[get_instruction_def] >> metis_tac[])
  >- gvs[jump_to_def]
  >> metis_tac[exit_result_def]
QED

Theorem gas_path_ptr_terminator_barrier:
  !D lo ctx fn PG G tn s n G' tn' r.
    gas_path_ptr D lo ctx fn PG G tn s n G' tn' r ==>
    !lbl bb k inst t.
      lookup_block lbl fn.fn_blocks = SOME bb /\
      get_instruction bb k = SOME inst /\ is_terminator inst.inst_opcode /\
      (s.vs_current_bb = lbl ==> s.vs_inst_idx <= k) /\ r = OK t ==>
      (t.vs_current_bb = lbl ==> t.vs_inst_idx <= k)
Proof
  ho_match_mp_tac gas_path_ptr_ind >> rpt strip_tac >> gvs[]
  >- (first_x_assum irule >> simp[] >>
      metis_tac[gas_path_ptr_edge_terminator_barrier])
  >> gvs[exit_result_def]
QED

Theorem gas_path_ptr_normal_endpoint_open:
  fn_has_code sa sm fn /\
  (block_is_terminated sm /\ s.vs_current_bb = sm.cs_current_bb ==>
     s.vs_inst_idx < LENGTH sm.cs_current_insts) /\
  gas_path_ptr D lo ctx fn PG G tn s n G' tn' (OK t) /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ~block_is_terminated sm
Proof
  strip_tac >> strip_tac >>
  `sm.cs_current_insts <> [] /\
   is_terminator (LAST sm.cs_current_insts).inst_opcode` by
    (Cases_on `sm.cs_current_insts` >> gvs[block_is_terminated_def]) >>
  fs[fn_has_code_def] >>
  `get_instruction bb (PRE (LENGTH sm.cs_current_insts)) =
     SOME (LAST sm.cs_current_insts)` by
    (gvs[IS_PREFIX_APPEND] >>
     `PRE (LENGTH sm.cs_current_insts) < LENGTH sm.cs_current_insts` by
       (Cases_on `sm.cs_current_insts` >> gvs[]) >>
     simp[get_instruction_def, EL_APPEND_EQN, LAST_EL]) >>
  `s.vs_current_bb = sm.cs_current_bb ==>
     s.vs_inst_idx <= PRE (LENGTH sm.cs_current_insts)` by
    (strip_tac >> Cases_on `sm.cs_current_insts` >> gvs[]) >>
  `t.vs_inst_idx <= PRE (LENGTH sm.cs_current_insts)` by
    metis_tac[gas_path_ptr_terminator_barrier] >>
  Cases_on `sm.cs_current_insts` >> gvs[]
QED

(* A cs_extends-only initial-barrier argument permits recycling the active
   label. This is a diagnostic of that interface, not a source counterexample. *)
Theorem cs_extends_open_initial_barrier_counterexample:
  !cs0 fn0.
    let halt = mk_inst 0 STOP [] [];
        next = mk_inst 1 ADD [] [];
        bb = <| bb_label := "probe"; bb_instructions := [halt;next] |>;
        sa = cs0 with <| cs_current_bb := "probe";
                         cs_current_insts := [halt;next]; cs_blocks := [] |>;
        sm = cs0 with <| cs_current_bb := "probe";
                         cs_current_insts := [halt]; cs_blocks := [bb] |>;
        fn = fn0 with fn_blocks := [bb]
    in cs_extends sa sm /\ fn_has_code sa sm fn /\
       ~block_is_terminated sa /\ block_is_terminated sm /\
       sa.cs_current_bb = sm.cs_current_bb /\
       ~(LENGTH sa.cs_current_insts < LENGTH sm.cs_current_insts)
Proof
  rpt gen_tac >> simp[LET_THM, cs_extends_def, fn_has_code_def,
    emitted_blocks_def, lookup_block_def, block_is_terminated_def,
    mk_inst_def, is_terminator_def] >>
  EVAL_TAC >> simp[]
QED
