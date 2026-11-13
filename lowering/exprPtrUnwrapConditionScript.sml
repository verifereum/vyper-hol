(* Generated conditions use a raw JNZ edge; neither block has entry PHIs. *)
Theory exprPtrUnwrapCondition
Ancestors
  exprPtrUnwrapCopyEdges exprPtrUnwrapFrames copyExecution slotCopyExecution
  fragGasPathPtr fragGasSeqPtr fragExec bodyPtrDefs ptrDiscipline ptrSafeRun
  venomExecSemantics venomInstProofs venomInst venomState finite_map codegenRel

Theorem slot_copy_cond_no_phis[simp]:
  phi_prefix_length (slot_copy_cond_insts cs n) = 0 /\
  eval_phis s (slot_copy_cond_insts cs n) = OK s
Proof
  simp[slot_copy_cond_insts_def, phi_prefix_length_def, eval_phis_def, mk_inst_def]
QED

Theorem slot_copy_body_no_phis[simp]:
  phi_prefix_length (slot_copy_body_insts cs src dst load) = 0 /\
  eval_phis s (slot_copy_body_insts cs src dst load) = OK s
Proof
  simp[slot_copy_body_insts_def, phi_prefix_length_def, eval_phis_def, mk_inst_def]
QED

Theorem copy_condition_counted_path:
  eval_operand (Var ctr) s = SOME x /\ op_taint tn (Var ctr) = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id EQ [Var ctr; Lit bound] [out]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst jid JNZ [Var out; Label yes; Label no] []) /\
  u = (update_var out (bool_to_word (x=bound)) s
    with vs_inst_idx := SUC s.vs_inst_idx) /\
  G1 = step_prov PG G (mk_inst id EQ [Var ctr; Lit bound] [out])
    (update_var out (bool_to_word (x=bound)) s) /\
  tn1 = step_taint (mk_inst id EQ [Var ctr; Lit bound] [out]) s
    (update_var out (bool_to_word (x=bound)) s) tn ==>
  gas_path_ptr D lo ctx fn PG G tn s 0 G1 tn1
    (OK (jump_to (if x=bound then yes else no) u))
Proof
  strip_tac >>
  `gas_path_ptr_edge D lo ctx fn PG G tn s 0 G1 tn1 (OK u)` by
    (simp[] >> irule copy_eq_counted_edge >> metis_tac[]) >>
  `op_taint tn1 (Var out) = {}` by
    simp[step_taint_def, set_var_taint_def, out_taint_def,
         op_taint_def, mk_inst_def, FLOOKUP_UPDATE] >>
  `eval_operand (Var out) u = SOME (bool_to_word (x=bound)) /\
   allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
   ~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
   u.vs_inst_idx = SUC s.vs_inst_idx` by
    (gvs[update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
         allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  `gas_path_ptr_edge D lo ctx fn PG G1 tn1 u 0 G1 tn1
     (OK (jump_to (if x=bound then yes else no) u))` by
    (irule copy_jnz_counted_edge >> simp[] >>
     qexistsl_tac [`jid`, `Var out`] >>
     Cases_on `x=bound` >> gvs[venomExecSemanticsTheory.bool_to_word_def]) >>
  `~(jump_to (if x=bound then yes else no) u).vs_halted` by
    simp[jump_to_def, update_var_def] >>
  qpat_x_assum `gas_path_ptr_edge _ _ _ _ _ _ _ s _ _ _ _` mp_tac >>
  qpat_x_assum `gas_path_ptr_edge _ _ _ _ _ _ _ u _ _ _ _` mp_tac >>
  qpat_x_assum `~(jump_to _ u).vs_halted` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem copy_generated_condition_path:
  i < 2**256 /\ n < 2**256 /\
  lookup_var (slot_copy_var cs 0) s = SOME (n2w i) /\
  op_taint tn (Var (slot_copy_var cs 0)) = {} /\ ~s.vs_halted /\
  s.vs_inst_idx = 0 /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = slot_copy_cond_insts cs n /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  G1 = step_prov PG G
    (mk_inst (cs.cs_next_id+2) EQ [Var (slot_copy_var cs 0); Lit (n2w n)]
      [slot_copy_var cs 1])
    (update_var (slot_copy_var cs 1) (bool_to_word ((n2w i:bytes32)=n2w n)) s) /\
  tn1 = step_taint
    (mk_inst (cs.cs_next_id+2) EQ [Var (slot_copy_var cs 0); Lit (n2w n)]
      [slot_copy_var cs 1]) s
    (update_var (slot_copy_var cs 1) (bool_to_word ((n2w i:bytes32)=n2w n)) s) tn ==>
  gas_path_ptr D lo ctx fn PG G tn s 0 G1 tn1
    (OK (slot_copy_cond_result cs n i s))
Proof
  strip_tac >>
  `gas_path_ptr D lo ctx fn PG G tn s 0 G1 tn1
    (OK (jump_to (if (n2w i:bytes32)=n2w n then slot_copy_exit cs
                 else slot_copy_body cs)
      (update_var (slot_copy_var cs 1)
        (bool_to_word ((n2w i:bytes32)=n2w n)) s with vs_inst_idx := 1)))` by
    (irule copy_condition_counted_path >>
     simp[] >>
     qexistsl_tac [`slot_copy_var cs 0`, `cs.cs_next_id+2`,
                  `cs.cs_next_id+3`, `slot_copy_var cs 1`] >>
     simp[slot_copy_cond_insts_def, get_instruction_def, eval_operand_def]) >>
  `((n2w i:bytes32)=n2w n) <=> (i=n)` by
    (pure_rewrite_tac[wordsTheory.n2w_11] >> fs[wordsTheory.dimword_def]) >>
  gvs[slot_copy_cond_result_def, jump_to_def]
QED

Theorem copy_eq_jump_frames:
  G1 = step_prov PG G (mk_inst id EQ [left; right] [out])
    (update_var out value s) /\
  tn1 = step_taint (mk_inst id EQ [left; right] [out]) s
    (update_var out value s) tn /\
  t = jump_to lbl (update_var out value s) ==>
  tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
  allocas_from lo t = allocas_from lo s /\
  allocas_below_fmp t = allocas_below_fmp s /\
  (!p. p <> out ==>
    FLOOKUP G1 p = FLOOKUP G p /\ op_taint tn1 (Var p) = op_taint tn (Var p)) /\
  (!p c. p <> out /\ ptr_covers G tn p s c ==> ptr_covers G1 tn1 p t c)
Proof
  strip_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       set_var_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
       written_taint_def, source_memory_write_ranges_def, range_bytes_def,
       store_taint_def, imm_taint_def, adopt_reset_def, mk_inst_def, update_var_def,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def,
       allocas_from_def, allocas_below_fmp_def, ptr_covers_def,
       lookup_var_def, jump_to_def] >>
  simp[FLOOKUP_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem copy_generated_condition_framed:
  i < 2**256 /\ n < 2**256 /\
  lookup_var (slot_copy_var cs 0) s = SOME (n2w i) /\
  op_taint tn (Var (slot_copy_var cs 0)) = {} /\ ~s.vs_halted /\
  s.vs_inst_idx = 0 /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = slot_copy_cond_insts cs n /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?G1 tn1.
    gas_path_ptr D lo ctx fn PG G tn s 0 G1 tn1
      (OK (slot_copy_cond_result cs n i s)) /\
    tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    allocas_from lo (slot_copy_cond_result cs n i s) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp (slot_copy_cond_result cs n i s)) /\
    op_taint tn1 (Var (slot_copy_var cs 0)) = {} /\
    (!p. p <> slot_copy_var cs 1 ==>
      FLOOKUP G1 p = FLOOKUP G p /\ op_taint tn1 (Var p) = op_taint tn (Var p)) /\
    (!p c. p <> slot_copy_var cs 1 /\ ptr_covers G tn p s c ==>
      ptr_covers G1 tn1 p (slot_copy_cond_result cs n i s) c)
Proof
  strip_tac >>
  qabbrev_tac `inst = mk_inst (cs.cs_next_id+2) EQ
    [Var (slot_copy_var cs 0); Lit (n2w n)] [slot_copy_var cs 1]` >>
  qabbrev_tac `u = update_var (slot_copy_var cs 1)
    (bool_to_word ((n2w i:bytes32)=n2w n)) s` >>
  qabbrev_tac `G1 = step_prov PG G inst u` >>
  qabbrev_tac `tn1 = step_taint inst s u tn` >>
  qexistsl_tac [`G1`, `tn1`] >> conj_tac
  >- (irule copy_generated_condition_path >> simp[Abbr `G1`, Abbr `tn1`,
        Abbr `inst`, Abbr `u`] >> metis_tac[]) >>
  `((n2w i:bytes32)=n2w n) <=> (i=n)` by
    (pure_rewrite_tac[wordsTheory.n2w_11] >> fs[wordsTheory.dimword_def]) >>
  `tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
   allocas_from lo (slot_copy_cond_result cs n i s) = allocas_from lo s /\
   allocas_below_fmp (slot_copy_cond_result cs n i s) = allocas_below_fmp s /\
   (!p. p <> slot_copy_var cs 1 ==>
     FLOOKUP G1 p = FLOOKUP G p /\ op_taint tn1 (Var p) = op_taint tn (Var p)) /\
   (!p c. p <> slot_copy_var cs 1 /\ ptr_covers G tn p s c ==>
     ptr_covers G1 tn1 p (slot_copy_cond_result cs n i s) c)` by
    (irule copy_eq_jump_frames >>
     simp[Abbr `G1`, Abbr `tn1`, Abbr `inst`, Abbr `u`,
          slot_copy_cond_result_def] >> metis_tac[]) >>
  gvs[] >>
  qpat_x_assum `!p. p <> _ ==> _ /\ _`
    (qspec_then `slot_copy_var cs 0` mp_tac) >>
  simp[slot_copy_var_distinct]
QED
