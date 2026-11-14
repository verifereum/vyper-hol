Theory assignPlaceEndpoint
Ancestors
  fragGasMode fragExec compileEnv venomExecProofs venomExecSemantics
  venomInst venomState list rich_list

(* At a positive PC the instruction immediately behind it is the one
   whose nontermination must be retained by an execution invariant. *)
Theorem endpoint_prefix_previous:
  !cs bb.
    isPREFIX cs.cs_current_insts bb.bb_instructions ==>
    ((0 < LENGTH cs.cs_current_insts ==>
      ~is_terminator
        (EL (LENGTH cs.cs_current_insts - 1) bb.bb_instructions).inst_opcode) <=>
    ~block_is_terminated cs)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `cs.cs_current_insts = []` >- simp[block_is_terminated_def] >>
  `0 < LENGTH cs.cs_current_insts` by
    (Cases_on `cs.cs_current_insts` >> gvs[]) >>
  `EL (LENGTH cs.cs_current_insts - 1) bb.bb_instructions =
   LAST cs.cs_current_insts` by
    (qpat_x_assum `isPREFIX _ _` mp_tac >>
     rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >>
     asm_rewrite_tac[] >> simp[EL_APPEND_EQN, LAST_EL, arithmeticTheory.PRE_SUB1]) >>
  Cases_on `cs.cs_current_insts` >> gvs[block_is_terminated_def]
QED

(* Successful edges establish a nonterminator immediately behind any
   positive PC. Reflexive paths instead retain the initial open-prefix
   invariant; fn_has_code_start transports the initial compiler prefix. *)

Theorem endpoint_phi_previous[local]:
  !insts. 0 < phi_prefix_length insts ==>
    ~is_terminator
      (EL (phi_prefix_length insts - 1) insts).inst_opcode
Proof
  Induct >> simp[phi_prefix_length_def] >> gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  Cases_on `phi_prefix_length insts` >> gvs[is_terminator_def]
QED

Theorem endpoint_edge_previous:
  gas_path_edge ctx fn s n (OK t) /\ 0 < t.vs_inst_idx /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME bb ==>
  ~is_terminator (EL (t.vs_inst_idx - 1) bb.bb_instructions).inst_opcode
Proof
  rw[fragGasPathTheory.gas_path_edge_def, exit_result_def] >>
  gvs[jump_to_def]
  >- (drule_all venomInstProofsTheory.step_preserves_control_flow >>
      strip_tac >> gvs[get_instruction_def])
  >- (drule eval_phis_preserves_current_bb >> strip_tac >>
      gvs[] >> irule endpoint_phi_previous >> simp[]) >>
  qpat_x_assum `OK t = _` (SUBST_ALL_TAC o SYM) >>
  fs[exit_result_def]
QED

Theorem endpoint_path_previous:
  !ctx fn s n r.
    gas_path ctx fn s n r ==>
    !t. r = OK t ==>
      (0 < s.vs_inst_idx ==>
        !bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
          ~is_terminator
            (EL (s.vs_inst_idx - 1) bb.bb_instructions).inst_opcode) ==>
      0 < t.vs_inst_idx ==>
      !bb. lookup_block t.vs_current_bb fn.fn_blocks = SOME bb ==>
        ~is_terminator (EL (t.vs_inst_idx - 1) bb.bb_instructions).inst_opcode
Proof
  ho_match_mp_tac fragGasPathTheory.gas_path_ind >>
  rpt strip_tac >> gvs[exit_result_def] >>
  metis_tac[endpoint_edge_previous]
QED

Theorem endpoint_path_open:
  cs_extends sa sb /\ fn_has_code sa sb fn /\
  ~block_is_terminated sa /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_marked_path F ctx fn s n (OK t) /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ~block_is_terminated sb
Proof
  strip_tac >>
  `?bba. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bba /\
         isPREFIX sa.cs_current_insts bba.bb_instructions` by
    metis_tac[fn_has_code_start] >>
  `?bbb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bbb /\
         isPREFIX sb.cs_current_insts bbb.bb_instructions` by
    fs[fn_has_code_def] >>
  `0 < s.vs_inst_idx ==>
     !bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
       ~is_terminator (EL (s.vs_inst_idx - 1) bb.bb_instructions).inst_opcode` by
    (rpt strip_tac >> gvs[] >> metis_tac[endpoint_prefix_previous]) >>
  fs[gas_marked_path_def] >>
  drule endpoint_path_previous >>
  simp[] >> metis_tac[endpoint_prefix_previous]
QED
