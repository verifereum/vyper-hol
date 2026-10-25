Theory createSlotCopyExecution
Ancestors
  createCopyExecution createMemoryInterface createSourceCallback createFrameInterface emitHelperProps fragExec
  exprLoweringProps venomExecSemantics venomMemProps
  compileEnv emitHelper venomInst venomState list rich_list words
Libs
  wordsLib

(* Loop locals may be reassigned; only operands outside this set are live. *)
Definition slot_copy_external_def:
  slot_copy_external cs op <=>
    !k. k < 7 ==> op <> Var (slot_copy_var cs k)
End

Definition slot_copy_word_def:
  slot_copy_word load s key =
    if load = SLOAD then sload key s else tload key s
End

Definition slot_copy_body_result_def:
  slot_copy_body_result cs p d load i s =
    let key = p + n2w i;
        value = slot_copy_word load s key;
        off = n2w i * 32w;
        addr = d + off;
        s1 = update_var (slot_copy_var cs 2) key s;
        s2 = update_var (slot_copy_var cs 3) value s1;
        s3 = update_var (slot_copy_var cs 4) off s2;
        s4 = update_var (slot_copy_var cs 5) addr s3;
        s5 = mstore (w2n addr) value s4;
        s6 = update_var (slot_copy_var cs 6) (n2w i + 1w) s5;
        s7 = update_var (slot_copy_var cs 0) (n2w i + 1w) s6
    in jump_to (slot_copy_cond cs) s7
End

Theorem slot_copy_operand_update[simp]:
  eval_operand op (update_var name value s) =
    if op = Var name then SOME value else eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def, update_var_def,
    finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem slot_copy_load_update[simp]:
  slot_copy_word load (update_var name value s) key = slot_copy_word load s key
Proof
  simp[slot_copy_word_def, sload_def, tload_def, contract_storage_def,
    contract_transient_def, update_var_def]
QED

Theorem slot_copy_operand_mstore[simp]:
  eval_operand op (mstore off value s) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def, mstore_def]
QED


Theorem slot_copy_step_add[local]:
  eval_operand a s = SOME x /\ eval_operand b s = SOME y ==>
  step_inst_base (mk_inst id ADD [a;b] [out]) s =
    OK (update_var out (x+y) s)
Proof
  simp[step_inst_base_def, mk_inst_def, exec_pure2_def]
QED

Theorem slot_copy_step_mul[local]:
  eval_operand a s = SOME x /\ eval_operand b s = SOME y ==>
  step_inst_base (mk_inst id MUL [a;b] [out]) s =
    OK (update_var out (x*y) s)
Proof
  simp[step_inst_base_def, mk_inst_def, exec_pure2_def]
QED

Theorem slot_copy_step_load[local]:
  (load = SLOAD \/ load = TLOAD) /\ eval_operand a s = SOME x ==>
  step_inst_base (mk_inst id load [a] [out]) s =
    OK (update_var out (slot_copy_word load s x) s)
Proof
  strip_tac >> gvs[step_inst_base_def, mk_inst_def, exec_read1_def,
    slot_copy_word_def]
QED

Theorem slot_copy_step_store[local]:
  eval_operand a s = SOME x /\ eval_operand b s = SOME y ==>
  step_inst_base (mk_inst id MSTORE [a;b] []) s = OK (mstore (w2n x) y s)
Proof
  simp[step_inst_base_def, mk_inst_def, exec_write2_def]
QED

Theorem slot_copy_step_assign[local]:
  eval_operand a s = SOME x ==>
  step_inst_base (mk_inst id ASSIGN [a] [out]) s = OK (update_var out x s)
Proof
  simp[step_inst_base_def, mk_inst_def]
QED

Theorem slot_copy_step_jump[local]:
  step_inst_base (mk_inst id JMP [Label l] []) s = OK (jump_to l s)
Proof
  simp[step_inst_base_def, mk_inst_def]
QED

Theorem slot_copy_body_execution:
  (load = SLOAD \/ load = TLOAD) /\
  slot_copy_external cs src /\ slot_copy_external cs dst /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  lookup_var (slot_copy_var cs 0) s = SOME (n2w i) ==>
  run_inst_seq (slot_copy_body_insts cs src dst load) s =
    OK (slot_copy_body_result cs p d load i s)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `eval_operand (Var (slot_copy_var cs 0)) s = SOME (n2w i)` by
    simp[eval_operand_def] >>
  `dst <> Var (slot_copy_var cs 2) /\ dst <> Var (slot_copy_var cs 3) /\
   dst <> Var (slot_copy_var cs 4)` by
    metis_tac[slot_copy_external_def, DECIDE ``2 < 7 /\ 3 < 7 /\ 4 < 7``] >>
  qpat_x_assum `slot_copy_external cs src` kall_tac >>
  qpat_x_assum `slot_copy_external cs dst` kall_tac >>
  `step_inst_base (mk_inst (cs.cs_next_id + 4) ADD
    [src; Var (slot_copy_var cs 0)] [slot_copy_var cs 2]) s =
    OK (update_var (slot_copy_var cs 2) (p + n2w i) s)` by
    (irule slot_copy_step_add >> simp[]) >>
  simp[slot_copy_body_insts_def, Once run_inst_seq_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ s1` >>
  `step_inst_base (mk_inst (cs.cs_next_id + 5) load
    [Var (slot_copy_var cs 2)] [slot_copy_var cs 3]) s1 =
    OK (update_var (slot_copy_var cs 3) (slot_copy_word load s1 (p + n2w i)) s1)` by
    (irule slot_copy_step_load >> simp[Abbr `s1`]) >>
  asm_rewrite_tac[Once run_inst_seq_def] >> simp[] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ s2` >>
  `step_inst_base (mk_inst (cs.cs_next_id + 6) MUL
    [Var (slot_copy_var cs 0); Lit 32w] [slot_copy_var cs 4]) s2 =
    OK (update_var (slot_copy_var cs 4) (n2w i * 32w) s2)` by
    (irule slot_copy_step_mul >>
     simp[Abbr `s2`, Abbr `s1`, slot_copy_var_distinct, eval_operand_lit_local]) >>
  asm_rewrite_tac[Once run_inst_seq_def] >> simp[] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ s3` >>
  `step_inst_base (mk_inst (cs.cs_next_id + 7) ADD
    [dst; Var (slot_copy_var cs 4)] [slot_copy_var cs 5]) s3 =
    OK (update_var (slot_copy_var cs 5) (d + n2w i * 32w) s3)` by
    (irule slot_copy_step_add >>
     simp[Abbr `s3`, Abbr `s2`, Abbr `s1`, slot_copy_var_distinct]) >>
  asm_rewrite_tac[Once run_inst_seq_def] >> simp[] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ s4` >>
  `step_inst_base (mk_inst (cs.cs_next_id + 8) MSTORE
    [Var (slot_copy_var cs 5); Var (slot_copy_var cs 3)] []) s4 =
    OK (mstore (w2n (d + n2w i * 32w)) (slot_copy_word load s (p+n2w i)) s4)` by
    (irule slot_copy_step_store >>
     simp[Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`, slot_copy_var_distinct]) >>
  asm_rewrite_tac[Once run_inst_seq_def] >> simp[] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ s5` >>
  `step_inst_base (mk_inst (cs.cs_next_id + 9) ADD
    [Var (slot_copy_var cs 0); Lit 1w] [slot_copy_var cs 6]) s5 =
    OK (update_var (slot_copy_var cs 6) (n2w i + 1w) s5)` by
    (irule slot_copy_step_add >>
     simp[Abbr `s5`, Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`,
          slot_copy_var_distinct, eval_operand_lit_local]) >>
  asm_rewrite_tac[Once run_inst_seq_def] >> simp[] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq _ s6` >>
  `step_inst_base (mk_inst (cs.cs_next_id + 10) ASSIGN
    [Var (slot_copy_var cs 6)] [slot_copy_var cs 0]) s6 =
    OK (update_var (slot_copy_var cs 0) (n2w i + 1w) s6)` by
    (irule slot_copy_step_assign >> simp[Abbr `s6`]) >>
  asm_rewrite_tac[Once run_inst_seq_def] >> simp[] >>
  simp[run_inst_seq_def, slot_copy_step_jump, slot_copy_body_result_def,
       Abbr `s6`, Abbr `s5`, Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`]
QED

(* A pointwise word prefix avoids committing to a particular list-concatenation
   normal form. Source slot addition is intentionally modular. *)
Definition slot_copy_prefix_def:
  slot_copy_prefix load original p d i s <=>
    !j. j < i ==>
      d + 32*j + 32 <= LENGTH s.vs_memory /\
      TAKE 32 (DROP (d + 32*j) s.vs_memory) =
        word_to_bytes (slot_copy_word load original (p + n2w j)) T
End

Theorem slot_copy_prefix_store:
  slot_copy_prefix load original p d i s ==>
  slot_copy_prefix load original p d (i+1)
    (mstore (d+32*i) (slot_copy_word load original (p+n2w i)) s)
Proof
  pure_rewrite_tac[slot_copy_prefix_def] >> disch_tac >> gen_tac >> disch_tac >>
  Cases_on `j = i`
  >- (gvs[LENGTH_mstore_eq, mstore_eq_write_mem] >>
      mp_tac (Q.SPECL [`d+32*i`,
        `word_to_bytes (slot_copy_word load original (p+n2w i)) T`, `s`]
        write_memory_with_expansion_read_self) >>
      simp[byteTheory.LENGTH_word_to_bytes]) >>
  `j < i` by decide_tac >>
  first_x_assum drule >> strip_tac >>
  conj_tac
  >- (mp_tac (Q.SPECL [`d+32*i`,
        `slot_copy_word load original (p+n2w i)`, `s`] mstore_memory_nondecreasing) >>
      decide_tac) >>
  `d+32*j+32 <= d+32*i` by decide_tac >>
  simp[mstore_eq_write_mem] >>
  drule write_memory_with_expansion_disjoint_read >>
  disch_then (qspecl_then [`d+32*i`,
    `word_to_bytes (slot_copy_word load original (p+n2w i)) T`] mp_tac) >>
  simp[]
QED

Definition slot_copy_cond_result_def:
  slot_copy_cond_result cs n i s =
    jump_to (if i = n then slot_copy_exit cs else slot_copy_body cs)
      (update_var (slot_copy_var cs 1) (bool_to_word (i=n)) s)
End

Theorem slot_copy_condition_execution:
  i < 2**256 /\ n < 2**256 /\
  lookup_var (slot_copy_var cs 0) s = SOME (n2w i) ==>
  run_inst_seq (slot_copy_cond_insts cs n) s =
    OK (slot_copy_cond_result cs n i s)
Proof
  strip_tac >>
  `((n2w i : bytes32) = n2w n) <=> (i=n)` by
    (pure_rewrite_tac[n2w_11] >> fs[dimword_def]) >>
  simp[slot_copy_cond_insts_def, run_inst_seq_def,
       step_inst_base_def, mk_inst_def, exec_pure2_def] >>
  simp[slot_copy_cond_result_def, eval_operand_lit_local,
       eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, bool_to_word_def] >>
  Cases_on `i=n` >> simp[venomExecSemanticsTheory.bool_to_word_def]
QED

Theorem slot_copy_body_memory:
  (slot_copy_body_result cs p d load i s).vs_memory =
    (mstore (w2n (d + n2w i * 32w))
      (slot_copy_word load s (p+n2w i)) s).vs_memory
Proof
  simp[slot_copy_body_result_def, update_var_def, jump_to_def, mstore_def]
QED

Theorem slot_copy_body_sources:
  (slot_copy_body_result cs p d load i s).vs_accounts = s.vs_accounts /\
  (slot_copy_body_result cs p d load i s).vs_transient = s.vs_transient /\
  (slot_copy_body_result cs p d load i s).vs_call_ctx = s.vs_call_ctx
Proof
  simp[slot_copy_body_result_def, update_var_def, jump_to_def, mstore_def]
QED

Theorem slot_copy_body_operand:
  slot_copy_external cs op ==>
  eval_operand op (slot_copy_body_result cs p d load i s) = eval_operand op s
Proof
  strip_tac >>
  `op <> Var (slot_copy_var cs 0) /\ op <> Var (slot_copy_var cs 2) /\
   op <> Var (slot_copy_var cs 3) /\ op <> Var (slot_copy_var cs 4) /\
   op <> Var (slot_copy_var cs 5) /\ op <> Var (slot_copy_var cs 6)` by
    (fs[slot_copy_external_def] >> metis_tac[DECIDE ``0<7 /\ 2<7 /\ 3<7 /\ 4<7 /\ 5<7 /\ 6<7``]) >>
  Cases_on `op` >>
  gvs[slot_copy_body_result_def, eval_operand_def, lookup_var_def,
      jump_to_def, mstore_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem slot_copy_body_counter:
  lookup_var (slot_copy_var cs 0) (slot_copy_body_result cs p d load i s) =
    SOME (n2w (i+1)) /\
  (slot_copy_body_result cs p d load i s).vs_current_bb = slot_copy_cond cs /\
  (slot_copy_body_result cs p d load i s).vs_inst_idx = 0
Proof
  simp[slot_copy_body_result_def, lookup_var_def, update_var_def,
       jump_to_def, finite_mapTheory.FLOOKUP_UPDATE, word_add_n2w]
QED

Theorem slot_copy_cond_frame:
  (slot_copy_cond_result cs n i s).vs_memory = s.vs_memory /\
  (slot_copy_cond_result cs n i s).vs_accounts = s.vs_accounts /\
  (slot_copy_cond_result cs n i s).vs_transient = s.vs_transient /\
  (slot_copy_cond_result cs n i s).vs_call_ctx = s.vs_call_ctx /\
  lookup_var (slot_copy_var cs 0) (slot_copy_cond_result cs n i s) =
    lookup_var (slot_copy_var cs 0) s /\
  (slot_copy_cond_result cs n i s).vs_current_bb =
    (if i=n then slot_copy_exit cs else slot_copy_body cs) /\
  (slot_copy_cond_result cs n i s).vs_inst_idx = 0
Proof
  simp[slot_copy_cond_result_def, update_var_def, jump_to_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE, slot_copy_var_distinct]
QED

Theorem slot_copy_cond_operand:
  slot_copy_external cs op ==>
  eval_operand op (slot_copy_cond_result cs n i s) = eval_operand op s
Proof
  strip_tac >>
  `op <> Var (slot_copy_var cs 1)` by
    (fs[slot_copy_external_def] >> metis_tac[DECIDE ``1<7``]) >>
  Cases_on `op` >>
  gvs[slot_copy_cond_result_def, eval_operand_def, lookup_var_def,
      update_var_def, jump_to_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* The invariant is usable at both condition and body entries. Control-point
   information is stated separately by the transition theorems. *)
Definition slot_copy_inv_def:
  slot_copy_inv cs load original p d n regions i s <=>
    i <= n /\ n < 2**256 /\ w2n d + 32*n < 2**256 /\
    lookup_var (slot_copy_var cs 0) s = SOME (n2w i) /\
    s.vs_accounts = original.vs_accounts /\
    s.vs_transient = original.vs_transient /\
    s.vs_call_ctx = original.vs_call_ctx /\
    (!op. slot_copy_external cs op ==> eval_operand op s = eval_operand op original) /\
    slot_copy_prefix load original p (w2n d) i s /\
    create_memory_snapshot regions s /\
    EVERY (\(off,bs). off + LENGTH bs <= LENGTH s.vs_memory /\
      (off + LENGTH bs <= w2n d \/ w2n d + 32*n <= off)) regions
End

Theorem slot_copy_body_nonwrapping:
  i < n /\ w2n (d:bytes32) + 32*n < 2**256 ==>
  w2n (d + n2w i * 32w) = w2n d + 32*i
Proof
  strip_tac >>
  `32*i < 2**256 /\ w2n d + 32*i < 2**256` by decide_tac >>
  `w2n ((n2w i : bytes32) * 32w) = 32*i` by
    (pure_rewrite_tac[word_mul_n2w, w2n_n2w] >>
     `i*32 = 32*i` by decide_tac >>
     `i*32 < dimword (:256)` by (fs[dimword_def] >> decide_tac) >>
     metis_tac[arithmeticTheory.LESS_MOD]) >>
  irule EQ_TRANS >> qexists_tac `w2n d + w2n ((n2w i : bytes32)*32w)` >>
  conj_tac >- (irule wordsTheory.w2n_add_2 >> fs[dimword_def]) >> simp[]
QED

Theorem slot_copy_word_sources:
  s.vs_accounts = original.vs_accounts /\
  s.vs_transient = original.vs_transient /\
  s.vs_call_ctx = original.vs_call_ctx ==>
  slot_copy_word load s key = slot_copy_word load original key
Proof
  simp[slot_copy_word_def, sload_def, tload_def, contract_storage_def,
       contract_transient_def]
QED

Theorem slot_copy_condition_invariant:
  slot_copy_inv cs load original p d n regions i s ==>
  slot_copy_inv cs load original p d n regions i
    (slot_copy_cond_result cs n i s)
Proof
  simp[slot_copy_inv_def, slot_copy_cond_frame, slot_copy_cond_operand,
       slot_copy_prefix_def, create_memory_snapshot_def]
QED

Theorem slot_copy_body_invariant:
  slot_copy_inv cs load original p d n regions i s /\ i < n ==>
  slot_copy_inv cs load original p d n regions (i+1)
    (slot_copy_body_result cs p d load i s)
Proof
  strip_tac >>
  `w2n (d + n2w i * 32w) = w2n d + 32*i` by
    (irule slot_copy_body_nonwrapping >> qexists_tac `n` >> fs[slot_copy_inv_def]) >>
  `slot_copy_word load s (p+n2w i) = slot_copy_word load original (p+n2w i)` by
    (irule slot_copy_word_sources >> fs[slot_copy_inv_def]) >>
  qpat_x_assum `slot_copy_inv _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[slot_copy_inv_def] >> strip_tac >>
  simp[slot_copy_inv_def, slot_copy_body_counter, slot_copy_body_sources,
       slot_copy_body_operand] >>
  conj_tac
  >- (drule slot_copy_prefix_store >>
      simp[slot_copy_prefix_def, slot_copy_body_memory]) >>
  conj_tac
  >- (`create_memory_snapshot regions
         (mstore (w2n d + 32*i) (slot_copy_word load original (p+n2w i)) s)` by
        (simp[mstore_eq_write_mem] >>
         irule create_snapshot_disjoint_write >> simp[] >>
         fs[EVERY_MEM] >> rpt strip_tac >> PairCases_on `e` >> gvs[] >>
         first_x_assum drule >> simp[byteTheory.LENGTH_word_to_bytes] >>
         strip_tac >> decide_tac) >>
      gvs[create_memory_snapshot_def, slot_copy_body_memory]) >>
  simp[slot_copy_body_memory] >>
  `LENGTH s.vs_memory <= LENGTH
      (mstore (w2n d + 32*i) (slot_copy_word load original (p+n2w i)) s).vs_memory` by
    metis_tac[mstore_memory_nondecreasing] >>
  gvs[EVERY_MEM] >> rpt strip_tac >> PairCases_on `e` >> gvs[] >>
  first_x_assum drule >> simp[] >> decide_tac
QED

Theorem slot_copy_iteration:
  slot_copy_inv cs load original p d n regions i s /\ i < n /\
  (load = SLOAD \/ load = TLOAD) /\
  slot_copy_external cs src /\ slot_copy_external cs dst /\
  eval_operand src original = SOME p /\ eval_operand dst original = SOME d ==>
  ?b t.
    run_inst_seq (slot_copy_cond_insts cs n) s = OK b /\
    b.vs_current_bb = slot_copy_body cs /\ b.vs_inst_idx = 0 /\
    run_inst_seq (slot_copy_body_insts cs src dst load) b = OK t /\
    slot_copy_inv cs load original p d n regions (i+1) t /\
    t.vs_current_bb = slot_copy_cond cs /\ t.vs_inst_idx = 0
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac strip_assume_tac))) >>
  qexists_tac `slot_copy_cond_result cs n i s` >>
  qexists_tac `slot_copy_body_result cs p d load i (slot_copy_cond_result cs n i s)` >>
  `i < 2**256` by (fs[slot_copy_inv_def] >> decide_tac) >>
  `run_inst_seq (slot_copy_cond_insts cs n) s = OK (slot_copy_cond_result cs n i s)` by
    (irule slot_copy_condition_execution >> fs[slot_copy_inv_def]) >>
  `slot_copy_inv cs load original p d n regions i (slot_copy_cond_result cs n i s)` by
    metis_tac[slot_copy_condition_invariant] >>
  simp[slot_copy_cond_frame, slot_copy_body_counter] >>
  conj_tac
  >- (irule slot_copy_body_execution >>
      fs[slot_copy_inv_def] >> metis_tac[]) >>
  gvs[] >>
  qpat_x_assum `slot_copy_inv _ _ _ _ _ _ _ _ s` kall_tac >>
  drule_all slot_copy_body_invariant >> simp[]
QED

Theorem slot_copy_finish:
  slot_copy_inv cs load original p d n regions n s ==>
  ?t. run_inst_seq (slot_copy_cond_insts cs n) s = OK t /\
      slot_copy_inv cs load original p d n regions n t /\
      t.vs_current_bb = slot_copy_exit cs /\ t.vs_inst_idx = 0
Proof
  strip_tac >> qexists_tac `slot_copy_cond_result cs n n s` >>
  simp[slot_copy_cond_frame, slot_copy_condition_invariant] >>
  irule slot_copy_condition_execution >> fs[slot_copy_inv_def]
QED

Theorem slot_copy_condition_block:
  i < 2**256 /\ n < 2**256 /\
  lookup_var (slot_copy_var cs 0) s = SOME (n2w i) /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
  exec_block fuel ctx
    <|bb_label := slot_copy_cond cs; bb_instructions := slot_copy_cond_insts cs n|> s =
    OK (slot_copy_cond_result cs n i s)
Proof
  strip_tac >>
  `((n2w i : bytes32) = n2w n) <=> (i=n)` by
    (pure_rewrite_tac[n2w_11] >> fs[dimword_def]) >>
  simp[Once exec_block_def, get_instruction_def, slot_copy_cond_insts_def,
       mk_inst_def, Once step_inst_def, step_inst_base_def, exec_pure2_def,
       eval_operand_def] >>
  simp[Once exec_block_def, get_instruction_def, slot_copy_cond_insts_def,
       mk_inst_def, Once step_inst_def, step_inst_base_def,
       eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, is_terminator_def,
       slot_copy_cond_result_def, jump_to_def, bool_to_word_def] >>
  Cases_on `i=n` >> simp[venomExecSemanticsTheory.bool_to_word_def]
QED

Theorem slot_copy_seq_jmp_block[local]:
  run_inst_seq (insts ++ [mk_inst id JMP [Label target] []]) s = OK t /\
  EVERY (\i. ~is_terminator i.inst_opcode) insts /\
  EVERY (\i. i.inst_opcode <> INVOKE) insts /\
  bb.bb_instructions = prefix ++ insts ++ [mk_inst id JMP [Label target] []] /\
  s.vs_inst_idx = LENGTH prefix /\ ~t.vs_halted ==>
  exec_block fuel ctx bb s = OK t
Proof
  strip_tac >>
  `?u. run_inst_seq insts s = OK u` by
    (spose_not_then assume_tac >>
     drule run_inst_seq_append_err >>
     disch_then (qspec_then `[mk_inst id JMP [Label target] []]` mp_tac) >>
     metis_tac[]) >>
  drule run_inst_seq_append >>
  disch_then (qspec_then `[mk_inst id JMP [Label target] []]` mp_tac) >>
  simp[run_inst_seq_def, slot_copy_step_jump] >> strip_tac >> gvs[] >>
  `~u.vs_halted` by fs[jump_to_def] >>
  `s with vs_inst_idx := LENGTH prefix = s` by simp[venom_state_component_equality] >>
  `exec_block fuel ctx bb (s with vs_inst_idx := LENGTH prefix) =
     OK (jump_to target u)` suffices_by simp[] >>
  irule exec_block_inst_seq_jmp >>
  simp[] >> qexistsl_tac [`insts`, `id`] >>
  simp[get_instruction_def, EL_APPEND_EQN]
QED

Theorem slot_copy_body_block:
  (load = SLOAD \/ load = TLOAD) /\
  slot_copy_external cs src /\ slot_copy_external cs dst /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  lookup_var (slot_copy_var cs 0) s = SOME (n2w i) /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
  exec_block fuel ctx
    <|bb_label := slot_copy_body cs;
      bb_instructions := slot_copy_body_insts cs src dst load|> s =
    OK (slot_copy_body_result cs p d load i s)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `run_inst_seq (slot_copy_body_insts cs src dst load) s =
     OK (slot_copy_body_result cs p d load i s)` by
    (irule slot_copy_body_execution >> simp[]) >>
  `~(slot_copy_body_result cs p d load i s).vs_halted` by
    simp[slot_copy_body_result_def, jump_to_def, update_var_def, mstore_def] >>
  irule slot_copy_seq_jmp_block >> simp[] >>
  qexistsl_tac [`cs.cs_next_id + 11`,
    `TAKE 7 (slot_copy_body_insts cs src dst load)`, `slot_copy_cond cs`] >>
  simp[slot_copy_body_insts_def, mk_inst_def, is_terminator_def] >>
  gvs[slot_copy_body_insts_def, mk_inst_def, is_terminator_def]
QED

Theorem slot_copy_results_fresh:
  fresh_vars_wrt (slot_copy_final cs src dst n load) s ==>
  fresh_vars_wrt (slot_copy_final cs src dst n load) (slot_copy_cond_result cs n i s) /\
  fresh_vars_wrt (slot_copy_final cs src dst n load) (slot_copy_body_result cs p d load i s)
Proof
  simp[fresh_vars_wrt_def, slot_copy_final_def, slot_copy_var_def,
       slot_copy_cond_result_def, slot_copy_body_result_def,
       update_var_def, jump_to_def, mstore_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  `!j. j < 7 ==> "%" ++ toString (cs.cs_next_var+j) <> "%" ++ toString n'` by
    (rpt strip_tac >> drule fresh_var_distinct >> simp[] >> decide_tac) >>
  simp[] >> first_x_assum irule >> decide_tac
QED

Theorem slot_copy_results_halted[simp]:
  (slot_copy_cond_result cs n i s).vs_halted = s.vs_halted /\
  (slot_copy_body_result cs p d load i s).vs_halted = s.vs_halted
Proof
  simp[slot_copy_cond_result_def, slot_copy_body_result_def,
       update_var_def, jump_to_def, mstore_def]
QED

Theorem slot_copy_run_condition:
  fn_has_code cs (slot_copy_final cs src dst n load) fn /\
  i < 2**256 /\ n < 2**256 /\
  lookup_var (slot_copy_var cs 0) s = SOME (n2w i) /\
  s.vs_current_bb = slot_copy_cond cs /\ s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
  run_blocks (SUC fuel) ctx fn s =
    run_blocks fuel ctx fn (slot_copy_cond_result cs n i s)
Proof
  strip_tac >> drule slot_copy_lookup >> strip_tac >>
  simp[Once run_blocks_def, slot_copy_cond_insts_def,
       eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  `s with vs_inst_idx := 0 = s` by simp[venom_state_component_equality] >>
  simp[] >>
  `exec_block fuel ctx
    <|bb_label := slot_copy_cond cs; bb_instructions := slot_copy_cond_insts cs n|> s =
    OK (slot_copy_cond_result cs n i s)` by
    (irule slot_copy_condition_block >> simp[]) >>
  fs[slot_copy_cond_insts_def, mk_inst_def]
QED

Theorem slot_copy_run_body:
  fn_has_code cs (slot_copy_final cs src dst n load) fn /\
  (load = SLOAD \/ load = TLOAD) /\
  slot_copy_external cs src /\ slot_copy_external cs dst /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  lookup_var (slot_copy_var cs 0) s = SOME (n2w i) /\
  s.vs_current_bb = slot_copy_body cs /\ s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
  run_blocks (SUC fuel) ctx fn s =
    run_blocks fuel ctx fn (slot_copy_body_result cs p d load i s)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  drule slot_copy_lookup >> strip_tac >>
  simp[Once run_blocks_def, slot_copy_body_insts_def,
       eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  `s with vs_inst_idx := 0 = s` by simp[venom_state_component_equality] >>
  simp[] >>
  `exec_block fuel ctx
    <|bb_label := slot_copy_body cs; bb_instructions := slot_copy_body_insts cs src dst load|> s =
    OK (slot_copy_body_result cs p d load i s)` by
    (irule slot_copy_body_block >> simp[]) >>
  fs[slot_copy_body_insts_def, mk_inst_def]
QED

Theorem slot_copy_counted_execution:
  !k i s.
  n = i+k /\
  fn_has_code cs (slot_copy_final cs src dst n load) fn /\
  (load = SLOAD \/ load = TLOAD) /\
  slot_copy_external cs src /\ slot_copy_external cs dst /\
  eval_operand src original = SOME p /\ eval_operand dst original = SOME d /\
  slot_copy_inv cs load original p d n regions i s /\
  fresh_vars_wrt (slot_copy_final cs src dst n load) s /\
  s.vs_current_bb = slot_copy_cond cs /\ s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
  ?t. slot_copy_inv cs load original p d n regions n t /\
      fresh_vars_wrt (slot_copy_final cs src dst n load) t /\
      t.vs_current_bb = slot_copy_exit cs /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      !fuel. run_blocks (2*k+1+fuel) ctx fn s = run_blocks fuel ctx fn t
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      qexists_tac `slot_copy_cond_result cs i i s` >>
      simp[slot_copy_condition_invariant, slot_copy_cond_frame,
           slot_copy_results_fresh] >>
      gen_tac >> `fuel+1 = SUC fuel` by decide_tac >>
      pop_assum SUBST1_TAC >> irule slot_copy_run_condition >> fs[slot_copy_inv_def] >> metis_tac[]) >>
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac strip_assume_tac))) >>
  `i < n /\ i < 2**256 /\ n < 2**256` by
    (fs[slot_copy_inv_def] >> decide_tac) >>
  qabbrev_tac `b = slot_copy_cond_result cs n i s` >>
  qabbrev_tac `u = slot_copy_body_result cs p d load i b` >>
  `slot_copy_inv cs load original p d n regions i b` by
    metis_tac[slot_copy_condition_invariant] >>
  `slot_copy_inv cs load original p d n regions (i+1) u` by
    metis_tac[slot_copy_body_invariant] >>
  `fresh_vars_wrt (slot_copy_final cs src dst n load) u /\
   u.vs_current_bb = slot_copy_cond cs /\ u.vs_inst_idx = 0 /\ ~u.vs_halted` by
    simp[Abbr `u`, Abbr `b`, slot_copy_results_fresh,
         slot_copy_body_counter] >>
  first_x_assum (qspecl_then [`i+1`, `u`] mp_tac) >>
  impl_tac >- (simp[] >> decide_tac) >>
  strip_tac >> qexists_tac `t` >> simp[] >> gen_tac >>
  `run_blocks (2*SUC k+1+fuel) ctx fn s =
   run_blocks (2*k+2+fuel) ctx fn b` by
    (simp_tac bool_ss [Abbr `b`] >>
     `2*SUC k+1+fuel = SUC (2*k+2+fuel)` by decide_tac >>
     pop_assum SUBST1_TAC >> irule slot_copy_run_condition >> fs[slot_copy_inv_def] >> metis_tac[]) >>
  `run_blocks (2*k+2+fuel) ctx fn b = run_blocks (2*k+1+fuel) ctx fn u` by
    (simp_tac bool_ss [Abbr `u`] >>
     `2*k+2+fuel = SUC (2*k+1+fuel)` by decide_tac >>
     pop_assum SUBST1_TAC >> irule slot_copy_run_body >>
     simp[Abbr `b`, slot_copy_cond_frame] >>
     fs[slot_copy_inv_def] >> metis_tac[]) >>
  gvs[]
QED

(* A non-error continuation at an empty compiler cutpoint cannot start with
   PHI: direct execution rejects PHI, whereas block entry consumes its prefix. *)
Theorem slot_copy_run_from_entry:
  s.vs_inst_idx = 0 /\ run_from fuel ctx fn s = r /\ (!e. r <> Error e) ==>
  run_blocks (SUC fuel) ctx fn s = r
Proof
  strip_tac >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- gvs[run_from_def] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  `phi_prefix_length bb.bb_instructions = 0` by
    (Cases_on `bb.bb_instructions` >> simp[phi_prefix_length_def] >>
     Cases_on `h.inst_opcode = PHI` >> simp[] >>
     qpat_x_assum `run_from _ _ _ _ = _` mp_tac >>
     simp[run_from_def, Once exec_block_def, get_instruction_def,
          Once step_inst_def, step_inst_base_def] >> metis_tac[]) >>
  drule_all run_blocks_run_from_no_phi >>
  `s with vs_inst_idx := 0 = s` by simp[venom_state_component_equality] >>
  simp[]
QED

Definition slot_copy_initial_def:
  slot_copy_initial cs s =
    jump_to (slot_copy_cond cs) (update_var (slot_copy_var cs 0) 0w s)
End

Theorem slot_copy_initial_block:
  bb.bb_instructions = cs.cs_current_insts ++ slot_copy_init_insts cs /\
  s.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~s.vs_halted ==>
  exec_block fuel ctx bb s = OK (slot_copy_initial cs s)
Proof
  strip_tac >> irule slot_copy_seq_jmp_block >>
  simp[slot_copy_initial_def, update_var_def, jump_to_def] >>
  qexistsl_tac [`cs.cs_next_id + 1`,
    `[mk_inst cs.cs_next_id ASSIGN [Lit 0w] [slot_copy_var cs 0]]`,
    `cs.cs_current_insts`, `slot_copy_cond cs`] >>
  simp[slot_copy_init_insts_def, mk_inst_def, is_terminator_def,
       run_inst_seq_def, step_inst_base_def, eval_operand_def,
       update_var_def, jump_to_def]
QED

Theorem slot_copy_initial_invariant:
  n < 2**256 /\ w2n d + 32*n < 2**256 /\
  create_memory_snapshot regions s /\
  EVERY (\(off,bs). off + LENGTH bs <= LENGTH s.vs_memory /\
    (off + LENGTH bs <= w2n d \/ w2n d + 32*n <= off)) regions ==>
  slot_copy_inv cs load s p d n regions 0 (slot_copy_initial cs s)
Proof
  simp[slot_copy_inv_def, slot_copy_initial_def, slot_copy_prefix_def,
       create_memory_snapshot_def, update_var_def, jump_to_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  `op <> Var (slot_copy_var cs 0)` by
    metis_tac[slot_copy_external_def, DECIDE ``0 < 7``] >>
  Cases_on `op` >> gvs[eval_operand_def, lookup_var_def,
                      finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem slot_copy_initial_fresh:
  fresh_vars_wrt cs s ==>
  fresh_vars_wrt (slot_copy_final cs src dst n load) (slot_copy_initial cs s)
Proof
  simp[fresh_vars_wrt_def, slot_copy_initial_def, slot_copy_final_def,
       update_var_def, jump_to_def, finite_mapTheory.FLOOKUP_UPDATE,
       slot_copy_var_def] >> rpt strip_tac >>
  `"%" ++ toString cs.cs_next_var <> "%" ++ toString n'` by
    (irule fresh_var_distinct >> decide_tac) >>
  simp[] >> first_x_assum irule >> decide_tac
QED

Definition slot_copy_bytes_def:
  slot_copy_bytes load original p n =
    FLAT (GENLIST (\j. word_to_bytes (slot_copy_word load original (p+n2w j)) T) n)
End

Theorem slot_copy_prefix_bytes:
  !n. slot_copy_prefix load original p d n s ==>
      TAKE (32*n) (DROP d s.vs_memory) = slot_copy_bytes load original p n
Proof
  Induct >- simp[slot_copy_bytes_def, GENLIST] >> strip_tac >>
  `slot_copy_prefix load original p d n s` by
    (fs[slot_copy_prefix_def] >> metis_tac[DECIDE ``j<n ==> j<SUC n``]) >>
  first_x_assum drule >> strip_tac >>
  `TAKE 32 (DROP (d+32*n) s.vs_memory) =
    word_to_bytes (slot_copy_word load original (p+n2w n)) T` by
    fs[slot_copy_prefix_def] >>
  qspecl_then [`32*SUC n`, `32*n`, `DROP d s.vs_memory`] mp_tac
    rich_listTheory.take_drop_partition >>
  simp[slot_copy_bytes_def, GENLIST, FLAT_SNOC, DROP_DROP_T] >>
  `32*SUC n - 32*n = 32` by decide_tac >> simp[] >>
  `32*n+d = d+32*n` by decide_tac >> simp[]
QED

Theorem slot_copy_bytes_length:
  LENGTH (slot_copy_bytes load original p n) = 32*n
Proof
  Induct_on `n` >> fs[slot_copy_bytes_def, GENLIST, FLAT_SNOC,
    byteTheory.LENGTH_word_to_bytes] >> decide_tac
QED

Theorem slot_copy_prefix_snapshot:
  slot_copy_prefix load original p d n s ==>
  create_memory_snapshot [(d,slot_copy_bytes load original p n)] s
Proof
  strip_tac >>
  `TAKE (32*n) (DROP d s.vs_memory) = slot_copy_bytes load original p n` by
    metis_tac[slot_copy_prefix_bytes] >>
  simp[create_memory_snapshot_def, slot_copy_bytes_length]
QED

Theorem slot_copy_execution:
  fn_has_code cs (slot_copy_final cs src dst n load) fn /\
  (load = SLOAD \/ load = TLOAD) /\
  fresh_vars_wrt cs s /\
  slot_copy_external cs src /\ slot_copy_external cs dst /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  n < 2**256 /\ w2n d + 32*n < 2**256 /\
  create_memory_snapshot regions s /\
  EVERY (\(off,bs). off + LENGTH bs <= LENGTH s.vs_memory /\
    (off + LENGTH bs <= w2n d \/ w2n d + 32*n <= off)) regions /\
  s.vs_current_bb = cs.cs_current_bb /\
  s.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~s.vs_halted ==>
  ?t. slot_copy_inv cs load s p d n regions n t /\
      fresh_vars_wrt (slot_copy_final cs src dst n load) t /\
      t.vs_current_bb = slot_copy_exit cs /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
               ?fuel'. run_from fuel' ctx fn s = r
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  qabbrev_tac `u = slot_copy_initial cs s` >>
  `slot_copy_inv cs load s p d n regions 0 u` by
    (simp_tac bool_ss [Abbr `u`] >> irule slot_copy_initial_invariant >> simp[]) >>
  `fresh_vars_wrt (slot_copy_final cs src dst n load) u` by
    (simp_tac bool_ss [Abbr `u`] >> irule slot_copy_initial_fresh >> simp[]) >>
  `u.vs_current_bb = slot_copy_cond cs /\ u.vs_inst_idx = 0 /\ ~u.vs_halted` by
    simp[Abbr `u`, slot_copy_initial_def, jump_to_def, update_var_def] >>
  `?t. slot_copy_inv cs load s p d n regions n t /\
      fresh_vars_wrt (slot_copy_final cs src dst n load) t /\
      t.vs_current_bb = slot_copy_exit cs /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      !fuel. run_blocks (2*n+1+fuel) ctx fn u = run_blocks fuel ctx fn t` by
    (irule slot_copy_counted_execution >> simp[]) >>
  qexists_tac `t` >> ntac 5 (conj_tac >- asm_rewrite_tac[]) >> rpt strip_tac >>
  `run_blocks (SUC fuel) ctx fn t = r` by
    (irule slot_copy_run_from_entry >> simp[]) >>
  `run_blocks (2*n+1+SUC fuel) ctx fn u = r` by metis_tac[] >>
  qexists_tac `2*n+1+SUC fuel` >>
  drule slot_copy_lookup >> strip_tac >>
  `exec_block (2*n+1+SUC fuel) ctx
    <|bb_label := cs.cs_current_bb;
      bb_instructions := cs.cs_current_insts ++ slot_copy_init_insts cs|> s = OK u` by
    (simp_tac bool_ss [Abbr `u`] >> irule slot_copy_initial_block >> simp[]) >>
  simp[run_from_def] >> gvs[]
QED

Theorem slot_copy_fresh_operand_external:
  fresh_vars_wrt cs s /\ eval_operand op s = SOME value ==>
  slot_copy_external cs op
Proof
  strip_tac >> simp[slot_copy_external_def] >> rpt strip_tac >>
  Cases_on `op` >> gvs[] >> metis_tac[slot_copy_var_not_live]
QED

Theorem slot_copy_bytes_sources:
  s.vs_accounts = original.vs_accounts /\
  s.vs_transient = original.vs_transient /\
  s.vs_call_ctx = original.vs_call_ctx ==>
  slot_copy_bytes load s p n = slot_copy_bytes load original p n
Proof
  strip_tac >> simp[slot_copy_bytes_def] >> AP_TERM_TAC >>
  irule GENLIST_CONG >> simp[] >> rpt strip_tac >>
  AP_THM_TAC >> AP_TERM_TAC >> irule slot_copy_word_sources >> simp[]
QED

Theorem slot_copy_invariant_post:
  slot_copy_inv cs load s p d n regions n t /\
  fresh_vars_wrt cs s /\ create_live live s /\
  s.vs_accounts = original.vs_accounts /\
  s.vs_transient = original.vs_transient /\
  s.vs_call_ctx = original.vs_call_ctx ==>
  create_live live t /\
  create_memory_snapshot ((w2n d,slot_copy_bytes load original p n)::regions) t /\
  t.vs_accounts = original.vs_accounts /\
  t.vs_transient = original.vs_transient /\
  t.vs_call_ctx = original.vs_call_ctx
Proof
  strip_tac >>
  `create_memory_snapshot [(w2n d,slot_copy_bytes load s p n)] t` by
    (irule slot_copy_prefix_snapshot >> fs[slot_copy_inv_def]) >>
  `slot_copy_bytes load s p n = slot_copy_bytes load original p n` by
    (irule slot_copy_bytes_sources >> simp[]) >>
  conj_tac
  >- (fs[create_live_def, EVERY_MEM] >> rpt strip_tac >> PairCases_on `e` >>
      first_x_assum drule >> simp[] >> strip_tac >>
      `slot_copy_external cs e0` by
        (irule slot_copy_fresh_operand_external >> metis_tac[]) >>
      fs[slot_copy_inv_def]) >>
  fs[slot_copy_inv_def, create_memory_snapshot_def]
QED

Theorem compile_create_slot_to_memory_frag:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_slot_to_memory src dst n loc cs = (result,cs') ==>
  cs_extends cs cs' /\
  frag_exec ctx cs cs'
    (\s. fresh_vars_wrt cs s /\ ~s.vs_halted /\
         eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
         n < 2**256 /\ w2n d + 32*n < 2**256 /\ create_live live s /\
         s.vs_accounts = original.vs_accounts /\
         s.vs_transient = original.vs_transient /\
         s.vs_call_ctx = original.vs_call_ctx /\
         create_memory_snapshot regions s /\
         EVERY (\(off,bs). off + LENGTH bs <= LENGTH s.vs_memory /\
           (off + LENGTH bs <= w2n d \/ w2n d + 32*n <= off)) regions)
    (\t. fresh_vars_wrt cs' t /\ create_live live t /\
         create_memory_snapshot
           ((w2n d,slot_copy_bytes (if loc = LocStorage then SLOAD else TLOAD)
               original p n)::regions) t /\
         t.vs_accounts = original.vs_accounts /\
         t.vs_transient = original.vs_transient /\
         t.vs_call_ctx = original.vs_call_ctx)
    (K F)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  drule_all compile_slot_to_memory_boundary >> strip_tac >>
  conj_tac >- simp[] >>
  simp_tac bool_ss [frag_exec_def] >> rpt strip_tac >>
  `slot_copy_external cs src /\ slot_copy_external cs dst` by
    metis_tac[slot_copy_fresh_operand_external] >>
  `?t. slot_copy_inv cs (if loc = LocStorage then SLOAD else TLOAD)
          s p d n regions n t /\ fresh_vars_wrt cs' t /\
       t.vs_current_bb = slot_copy_exit cs /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
       !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
                ?fuel'. run_from fuel' ctx fn s = r` by
    (pure_asm_rewrite_tac[] >> irule slot_copy_execution >> simp[] >> metis_tac[]) >>
  disj1_tac >> qexists_tac `t` >> simp[] >>
  conj_tac >- (irule slot_copy_invariant_post >> metis_tac[]) >>
  metis_tac[]
QED

val _ = app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("Oracle dependency in " ^ name))
  (DB.thms "createSlotCopyExecution");
