Theory exprPtrUnwrapStorageEntry
Ancestors
  exprPtrUnwrapLoopInvariant exprPtrUnwrapScalarSegments exprPtrUnwrapBackedge
  exprPtrUnwrapFrames slotCopyExecution copyExecution fragGasSeqPtr fragGasPathPtr
  ptrDiscipline ptrSafeRun bodyPtrDefs venomExecSemantics venomInst venomState
  list rich_list finite_map

Theorem copy_initial_path:
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = cs.cs_current_insts ++ slot_copy_init_insts cs /\
  s.vs_inst_idx = LENGTH cs.cs_current_insts /\
  run_inst_seq [mk_inst cs.cs_next_id ASSIGN [Lit 0w] [slot_copy_var cs 0]] s = OK t /\
  inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst cs.cs_next_id ASSIGN [Lit 0w] [slot_copy_var cs 0]] s G1 tn1 /\
  t = update_var (slot_copy_var cs 0) 0w s /\
  allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
  gas_path_ptr D lo ctx fn PG G tn s 0 G1 tn1 (OK (slot_copy_initial cs s))
Proof
  strip_tac >>
  drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`) run_inst_seq_gas_path_ptr >>
  disch_then (qspecl_then [`t`, `bb`] mp_tac) >>
  (impl_tac >- simp[slot_copy_init_insts_def, mk_inst_def, is_terminator_def,
                   DROP_LENGTH_APPEND]) >>
  simp[mk_inst_def] >> strip_tac >>
  qabbrev_tac `u = t with vs_inst_idx := s.vs_inst_idx+1` >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    gvs[Abbr `u`, update_var_def] >>
  `gas_path_ptr_edge D lo ctx fn PG G1 tn1 u 0 G1 tn1
    (OK (jump_to (slot_copy_cond cs) u))` by
    (irule copy_jmp_counted_edge >> simp[Abbr `u`] >>
     qexists `cs.cs_next_id+1` >>
     simp[slot_copy_init_insts_def, get_instruction_def, EL_APPEND_EQN, update_var_def]) >>
  `jump_to (slot_copy_cond cs) u = slot_copy_initial cs s` by
    simp[Abbr `u`, slot_copy_initial_def, jump_to_def, update_var_def] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
  qexistsl [`G1`, `u`, `tn1`] >> simp[Abbr `u`] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] (SPEC_ALL (cj 2 gas_path_ptr_rules)))) >>
  qexistsl [`G1`, `slot_copy_initial cs s`, `tn1`] >> simp[] >> conj_tac
  >- (irule (cj 1 gas_path_ptr_rules) >>
      gvs[slot_copy_initial_def, jump_to_def, update_var_def]) >>
  metis_tac[]
QED

Theorem copy_initial_ghost_frame:
  slot_copy_external cs (Var root) /\ ptr_covers G tn root s (32*n) /\
  op_taint tn1 (Var (slot_copy_var cs 0)) = {} /\
  tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
  (!v. v <> slot_copy_var cs 0 ==>
    FLOOKUP G1 v = FLOOKUP G v /\ op_taint tn1 (Var v) = op_taint tn (Var v)) /\
  (!v c. v <> slot_copy_var cs 0 /\ ptr_covers G tn v s c ==>
    ptr_covers G1 tn1 v (update_var (slot_copy_var cs 0) 0w s) c) ==>
  slot_copy_ghost_inv cs load p d root n G tn 0 G1 tn1 (slot_copy_initial cs s)
Proof
  strip_tac >>
  `root <> slot_copy_var cs 0` by
    (fs[slot_copy_external_def] >> metis_tac[DECIDE ``0<7``]) >>
  simp[slot_copy_ghost_inv_def] >> conj_tac
  >- (qpat_x_assum `!v c. _` (qspecl_then [`root`, `32*n`] mp_tac) >>
      simp[] >> simp[slot_copy_initial_def, ptr_covers_def, jump_to_def, lookup_var_def]) >>
  rpt strip_tac >>
  `v <> slot_copy_var cs 0` by
    (fs[slot_copy_external_def] >> metis_tac[DECIDE ``0<7``]) >>
  qpat_x_assum `!v. _ ==> _ /\ _` (qspec_then `v` mp_tac) >> simp[]
QED

Theorem copy_initial_counted_invariants:
  n < 2**256 /\ w2n d+32*n < 2**256 /\
  create_memory_snapshot regions s /\
  EVERY (\(off,bs). off+LENGTH bs <= LENGTH s.vs_memory /\
    (off+LENGTH bs <= w2n d \/ w2n d+32*n <= off)) regions /\
  slot_copy_external cs (Var root) /\ ptr_covers G tn root s (32*n) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = cs.cs_current_insts ++ slot_copy_init_insts cs /\
  s.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~s.vs_halted /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?G1 tn1.
    gas_path_ptr D lo ctx fn PG G tn s 0 G1 tn1 (OK (slot_copy_initial cs s)) /\
    slot_copy_inv cs load s p d n regions 0 (slot_copy_initial cs s) /\
    slot_copy_ghost_inv cs load p d root n G tn 0 G1 tn1 (slot_copy_initial cs s) /\
    allocas_from lo (slot_copy_initial cs s) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp (slot_copy_initial cs s))
Proof
  strip_tac >>
  mp_tac (Q.INST [`id` |-> `cs.cs_next_id`, `arg` |-> `Lit 0w`,
    `tmp` |-> `slot_copy_var cs 0`, `x` |-> `0w`] (SPEC_ALL copy_assign_segment)) >>
  (impl_tac >- simp[eval_operand_def, op_taint_def]) >> strip_tac >>
  qexistsl [`Gf`, `tnf`] >> conj_tac
  >- (irule copy_initial_path >> simp[] >> metis_tac[]) >>
  conj_tac >- simp[slot_copy_initial_invariant] >> conj_tac
  >- (irule copy_initial_ghost_frame >> simp[] >> metis_tac[]) >>
  gvs[slot_copy_initial_def, allocas_from_def, allocas_below_fmp_def,
      jump_to_def, update_var_def] >> metis_tac[]
QED
