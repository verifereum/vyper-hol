(*
 * Bounded assembly runs against bounded symbolic runs
 *
 * The sufficient-gas proof bounds a concrete assembly run (asm_run_bounded:
 * it ends or reaches a RETURNDATACOPY within N steps, each step before that
 * touching memory below H). asm_refines carries a bound like it through the
 * finalizer on the symbolic side (sym_run_within). This theory moves the
 * bound between the two sides, as asmSymBridge moves terminal runs.
 *
 * TOP-LEVEL:
 *   sym_gas_ok                  - asm_inst_gas_ok on a symbolic stack
 *   sym_within_ok_gas           - the finalizer keeps sym_gas_ok bounds
 *   asm_run_bounded_sym_within  - a bounded concrete run is a bounded
 *                                 symbolic one
 *   sym_within_asm_run_bounded  - and back
 *)

Theory asmSymWithin
Ancestors
  asmSymBridge asmDataEnv asmRunBounded asmSymSem asmSem list

(* A symbolic value as the word asm_inst_gas_ok reads; label values are
   never a memory operand of a step that doesn't go wrong, so their word
   doesn't matter. *)
Definition sval_word_def:
  sval_word (Val w) = w ∧
  sval_word (Lab _ _) = (0w : bytes32)
End

Definition sym_gas_ok_def:
  sym_gas_ok H inst stk ⇔ asm_inst_gas_ok H inst (MAP sval_word stk)
End

Theorem map_sval_word[local]:
  ∀stk stk'. MAP sval_val stk = MAP sval_val stk' ⇒
             MAP sval_word stk = MAP sval_word stk'
Proof
  Induct >> Cases_on `stk'` >> simp[] >> rpt strip_tac >> res_tac >>
  Cases_on `h` >> Cases_on `h'` >> gvs[sval_val_def, sval_word_def]
QED

Theorem sym_within_ok_gas:
  sym_within_ok (sym_gas_ok H) (λi. i = AsmOp "RETURNDATACOPY")
Proof
  simp[sym_within_ok_def, sym_gas_ok_def] >> rpt strip_tac
  >- (rename1 `asm_plain_inst inst` >> Cases_on `inst` >>
      gvs[asm_plain_inst_def, asm_inst_gas_ok_def, asm_mem_ranges_def])
  >- gvs[asm_plain_inst_def]
  >> metis_tac[map_sval_word]
QED

(* ===== One step: the memory operands are words ===== *)

Theorem sval_conc_vals[local]:
  ∀ws cs. LIST_REL (λsv w. sval_conc lo sv = SOME w) (MAP Val ws) cs ⇔
          cs = ws
Proof
  Induct >> Cases_on `cs` >> simp[sval_conc_def] >> metis_tac[]
QED

Theorem opt_mmap_vals[local]:
  ∀stk args. OPT_MMAP sval_val stk = SOME args ⇒ stk = MAP Val args
Proof
  Induct >> simp[] >> Cases >> simp[sval_val_def] >> rpt strip_tac >>
  Cases_on `OPT_MMAP sval_val stk` >> gvs[] >> metis_tac[]
QED

Theorem mem_ranges_prefix[local]:
  LENGTH args = asm_op_arity name ⇒
  asm_mem_ranges (AsmOp name) (args ++ r1) =
  asm_mem_ranges (AsmOp name) (args ++ r2)
Proof
  rw[asm_mem_ranges_def] >>
  qpat_x_assum `LENGTH args = _` (mp_tac o CONV_RULE (RAND_CONV EVAL)) >>
  simp[LENGTH_EQ_NUM_compute] >> rw[] >> simp[]
QED

Theorem concrete_mem_ranges[local]:
  LIST_REL (λsv w. sval_conc lo sv = SOME w) ss.sym_stack cstk ∧
  (∀e. sym_step_concrete name ss ≠ SymError e) ∧
  (∀m. sym_step_concrete name ss ≠ SymBad m) ⇒
  asm_mem_ranges (AsmOp name) (MAP sval_word ss.sym_stack) =
  asm_mem_ranges (AsmOp name) cstk
Proof
  simp[sym_step_concrete_def] >> strip_tac >>
  Cases_on `LENGTH ss.sym_stack < asm_op_arity name` >> gvs[] >>
  Cases_on `OPT_MMAP sval_val (TAKE (asm_op_arity name) ss.sym_stack)` >>
  gvs[] >>
  drule opt_mmap_vals >> strip_tac >>
  `LENGTH x = asm_op_arity name`
    by metis_tac[LENGTH_TAKE, LENGTH_MAP, arithmeticTheory.NOT_LESS] >>
  `ss.sym_stack = MAP Val x ++ DROP (asm_op_arity name) ss.sym_stack`
    by metis_tac[TAKE_DROP] >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >> pop_assum SUBST1_TAC >>
  simp[LIST_REL_SPLIT1, PULL_EXISTS, sval_conc_vals] >> rpt strip_tac >>
  simp[MAP_MAP_o, combinTheory.o_DEF, sval_word_def] >>
  irule mem_ranges_prefix >> simp[]
QED

Theorem concrete_head_val[local]:
  0 < asm_op_arity name ∧
  (∀e. sym_step_concrete name ss ≠ SymError e) ∧
  (∀m. sym_step_concrete name ss ≠ SymBad m) ⇒
  ∃w t. ss.sym_stack = Val w :: t
Proof
  simp[sym_step_concrete_def] >> strip_tac >>
  Cases_on `LENGTH ss.sym_stack < asm_op_arity name` >> gvs[] >>
  Cases_on `ss.sym_stack` >> gvs[] >>
  Cases_on `asm_op_arity name` >> gvs[TAKE_def] >>
  Cases_on `h` >> gvs[sval_val_def]
QED

Theorem sym_mload_shape[local]:
  (∀e. sym_mload ss ≠ SymError e) ∧ (∀m. sym_mload ss ≠ SymBad m) ⇒
  ∃w t. ss.sym_stack = Val w :: t
Proof
  strip_tac >> spose_not_then assume_tac >>
  `sym_mload ss = sym_step_concrete "MLOAD" ss`
    by (simp[sym_mload_def] >> qpat_x_assum `∀w t. _` mp_tac >>
        Cases_on `ss.sym_stack` >> simp[] >> Cases_on `h` >> simp[]) >>
  `0 < asm_op_arity "MLOAD"` by EVAL_TAC >>
  metis_tac[concrete_head_val]
QED

Theorem sym_mstore_shape[local]:
  (∀e. sym_mstore ss ≠ SymError e) ∧ (∀m. sym_mstore ss ≠ SymBad m) ⇒
  ∃w t. ss.sym_stack = Val w :: t
Proof
  strip_tac >> spose_not_then assume_tac >>
  `sym_mstore ss = sym_step_concrete "MSTORE" ss`
    by (simp[sym_mstore_def] >> qpat_x_assum `∀w t. _` mp_tac >>
        Cases_on `ss.sym_stack` >> simp[] >> Cases_on `h` >> simp[] >>
        BasicProvers.every_case_tac >> simp[]) >>
  `0 < asm_op_arity "MSTORE"` by EVAL_TAC >>
  metis_tac[concrete_head_val]
QED

Theorem sym_codecopy_shape[local]:
  (∀e. sym_codecopy p env ss ≠ SymError e) ∧
  (∀m. sym_codecopy p env ss ≠ SymBad m) ⇒
  ∃dst src sz t. ss.sym_stack = Val dst :: src :: Val sz :: t
Proof
  simp[sym_codecopy_def] >> BasicProvers.every_case_tac >> fs[]
QED

(* A step that neither errs nor misuses a label reads every memory operand
   as a word, so its memory ranges are the concrete step's. *)
Theorem sym_step_mem_ranges:
  LIST_REL (λsv w. sval_conc lo sv = SOME w) ss.sym_stack cstk ∧
  (∀e. sym_step p env inst ss ≠ SymError e) ∧
  (∀m. sym_step p env inst ss ≠ SymBad m) ⇒
  asm_mem_ranges inst (MAP sval_word ss.sym_stack) =
  asm_mem_ranges inst cstk
Proof
  strip_tac >> reverse (Cases_on `∃name. inst = AsmOp name`)
  >- (Cases_on `inst` >> gvs[asm_mem_ranges_def]) >>
  gvs[sym_step_def] >>
  Cases_on `name = "MLOAD"`
  >- (gvs[sym_step_op_def] >> drule_all sym_mload_shape >> strip_tac >>
      gvs[LIST_REL_CONS1, sval_conc_def, sval_word_def, asm_mem_ranges_def]) >>
  Cases_on `name = "MSTORE"`
  >- (gvs[sym_step_op_def] >> drule_all sym_mstore_shape >> strip_tac >>
      gvs[LIST_REL_CONS1, sval_conc_def, sval_word_def, asm_mem_ranges_def]) >>
  Cases_on `name = "CODECOPY"`
  >- (gvs[sym_step_op_def] >> drule_all sym_codecopy_shape >> strip_tac >>
      gvs[LIST_REL_CONS1, sval_conc_def, sval_word_def, asm_mem_ranges_def]) >>
  Cases_on `MEM name ["MSTORE8"; "SHA3"; "RETURN"; "REVERT"; "LOG0"; "LOG1";
                      "LOG2"; "LOG3"; "LOG4"; "CALLDATACOPY";
                      "RETURNDATACOPY"; "EXTCODECOPY"; "MCOPY"; "CALL";
                      "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"]`
  >- (`name ≠ "POP" ∧ name ≠ "JUMP" ∧ name ≠ "JUMPI" ∧ name ≠ "ADD" ∧
       name ≠ "CODESIZE" ∧ ALOOKUP dup_table name = NONE ∧
       ALOOKUP swap_table name = NONE` by (gvs[] >> EVAL_TAC) >>
      `sym_step_op p env name ss = sym_step_concrete name ss`
        by simp[sym_step_op_def] >>
      gvs[] >> irule concrete_mem_ranges >> metis_tac[]) >>
  gvs[asm_mem_ranges_def]
QED

Theorem list_cases3[local]:
  ∀l. l = [] ∨ (∃a. l = [a]) ∨ (∃a b. l = [a; b]) ∨
      ∃a b c t. l = a::b::c::t
Proof
  Cases >> simp[] >> Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[]
QED

(* asm_inst_gas_ok reads a stack only through its memory ranges and a
   CREATE's size, which those ranges carry. *)
Theorem gas_ok_ranges[local]:
  LENGTH stk1 = LENGTH stk2 ∧
  asm_mem_ranges inst stk1 = asm_mem_ranges inst stk2 ⇒
  (asm_inst_gas_ok H inst stk1 ⇔ asm_inst_gas_ok H inst stk2)
Proof
  rw[asm_inst_gas_ok_def] >>
  reverse (Cases_on `inst = AsmOp "CREATE" ∨ inst = AsmOp "CREATE2"`)
  >- fs[] >>
  pop_assum strip_assume_tac >> gvs[asm_mem_ranges_def] >>
  qspec_then `stk1` strip_assume_tac list_cases3 >>
  qspec_then `stk2` strip_assume_tac list_cases3 >> gvs[]
QED

Theorem sym_gas_ok_conc:
  asm_sym_rel p env cs ss ∧
  (∀e. sym_step p env inst ss ≠ SymError e) ∧
  (∀m. sym_step p env inst ss ≠ SymBad m) ⇒
  (sym_gas_ok H inst ss.sym_stack ⇔ asm_inst_gas_ok H inst cs.as_stack)
Proof
  strip_tac >>
  `asm_mem_ranges inst (MAP sval_word ss.sym_stack) =
   asm_mem_ranges inst cs.as_stack`
    by (irule sym_step_mem_ranges >> fs[asm_sym_rel_def] >> metis_tac[]) >>
  `LENGTH ss.sym_stack = LENGTH cs.as_stack`
    by (fs[asm_sym_rel_def] >> metis_tac[LIST_REL_LENGTH]) >>
  simp[sym_gas_ok_def] >> irule gas_ok_ranges >> simp[]
QED

(* ===== Runs ===== *)

Theorem asm_run_bounded_sym_within_rel[local]:
  ∀k cs ss.
    asm_static_wf p ∧ asm_sym_rel p env cs ss ∧
    (∀fuel msg. sym_run p env fuel ss ≠ SymBad msg) ∧
    asm_run_bounded (SND (compute_label_offsets p)) (build_offset_to_pc p)
      p H k cs ⇒
    sym_run_within (sym_gas_ok H) (λi. i = AsmOp "RETURNDATACOPY")
      p env k ss
Proof
  Induct >- simp[asm_run_bounded_def] >>
  rpt gen_tac >> strip_tac >>
  `ss.sym_base.as_pc = cs.as_pc` by fs[asm_sym_rel_def] >>
  qpat_x_assum `asm_run_bounded _ _ _ _ _ _` mp_tac >>
  simp[asm_run_bounded_def, sym_run_within_def] >>
  Cases_on `EL cs.as_pc p = AsmOp "RETURNDATACOPY"` >> simp[] >>
  strip_tac >>
  `∀msg. sym_step p env (EL cs.as_pc p) ss ≠ SymBad msg`
    by (rpt strip_tac >>
        qpat_x_assum `∀fuel msg. _` (qspecl_then [`SUC 0`, `msg`] mp_tac) >>
        simp[Once sym_run_def]) >>
  drule_all asm_sym_step >> strip_tac >>
  `∀e. sym_step p env (EL cs.as_pc p) ss ≠ SymError e`
    by (rpt strip_tac >> gvs[asm_sym_step_rel_def]) >>
  `sym_gas_ok H (EL cs.as_pc p) ss.sym_stack` by metis_tac[sym_gas_ok_conc] >>
  simp[] >>
  Cases_on `sym_step p env (EL cs.as_pc p) ss` >>
  gvs[asm_sym_step_rel_def] >>
  rename1 `asm_sym_rel p env cs1 ss1` >>
  first_x_assum (qspecl_then [`cs1`, `ss1`] mp_tac) >> simp[] >>
  disch_then irule >> rpt gen_tac >>
  qpat_x_assum `∀fuel msg. sym_run _ _ _ ss ≠ _`
    (qspecl_then [`SUC fuel`, `msg`] mp_tac) >>
  simp[Once sym_run_def]
QED

Theorem sym_within_asm_run_bounded_rel[local]:
  ∀k cs ss.
    asm_static_wf p ∧ asm_sym_rel p env cs ss ∧
    sym_run_within (sym_gas_ok H) (λi. i = AsmOp "RETURNDATACOPY")
      p env k ss ⇒
    asm_run_bounded (SND (compute_label_offsets p)) (build_offset_to_pc p)
      p H k cs
Proof
  Induct >- simp[sym_run_within_def] >>
  rpt gen_tac >> strip_tac >>
  `ss.sym_base.as_pc = cs.as_pc` by fs[asm_sym_rel_def] >>
  qpat_x_assum `sym_run_within _ _ _ _ _ _` mp_tac >>
  simp[asm_run_bounded_def, sym_run_within_def] >>
  Cases_on `EL cs.as_pc p = AsmOp "RETURNDATACOPY"` >> simp[] >>
  strip_tac >>
  `(∀e. sym_step p env (EL cs.as_pc p) ss ≠ SymError e) ∧
   (∀m. sym_step p env (EL cs.as_pc p) ss ≠ SymBad m)`
    by (rpt strip_tac >> gvs[]) >>
  drule_all asm_sym_step >> strip_tac >>
  `asm_inst_gas_ok H (EL cs.as_pc p) cs.as_stack`
    by metis_tac[sym_gas_ok_conc] >>
  simp[] >>
  Cases_on `sym_step p env (EL cs.as_pc p) ss` >>
  gvs[asm_sym_step_rel_def] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem asm_sym_rel_init_start[local]:
  s.as_pc = 0 ∧ asm_data_env_ok p env s.as_code ⇒
  asm_sym_rel p env s (sym_init s)
Proof
  rw[asm_sym_rel_def, sym_init_def, LIST_REL_MAP1, sval_conc_def,
     asm_state_component_equality] >>
  simp[LIST_REL_EL_EQN, sval_conc_def]
QED

(* TOP-LEVEL: a bounded concrete run of a label-disciplined program is a
   bounded symbolic run, with the same step count. *)
Theorem asm_run_bounded_sym_within:
  label_disciplined env p s ∧ s.as_pc = 0 ∧
  asm_data_env_ok p env s.as_code ∧
  asm_run_bounded (SND (compute_label_offsets p)) (build_offset_to_pc p)
    p H k s ⇒
  sym_run_within (sym_gas_ok H) (λi. i = AsmOp "RETURNDATACOPY")
    p env k (sym_init s)
Proof
  rw[label_disciplined_def] >> irule asm_run_bounded_sym_within_rel >>
  simp[] >> qexists_tac `s` >> simp[asm_sym_rel_init_start]
QED

(* TOP-LEVEL: a bounded symbolic run is a bounded concrete one. *)
Theorem sym_within_asm_run_bounded:
  asm_static_wf p ∧ s.as_pc = 0 ∧ asm_data_env_ok p env s.as_code ∧
  sym_run_within (sym_gas_ok H) (λi. i = AsmOp "RETURNDATACOPY")
    p env k (sym_init s) ⇒
  asm_run_bounded (SND (compute_label_offsets p)) (build_offset_to_pc p)
    p H k s
Proof
  strip_tac >> irule sym_within_asm_run_bounded_rel >>
  simp[] >> qexistsl_tac [`env`, `sym_init s`] >> simp[asm_sym_rel_init_start]
QED

(* TOP-LEVEL: a bounded concrete run of p gives one of a refinement p' of
   it, c times as long, from the same state with p's code swapped for
   p''s, given that p's run uses its labels only as labels. *)
Theorem asm_refines_run_bounded:
  asm_refines p p' ∧ asm_static_wf p ⇒
  ∃c. ∀H k s x.
    label_disciplined (asm_data_env p (assemble p ++ x)) p s ∧
    s.as_pc = 0 ∧ s.as_code = assemble p ++ x ∧
    asm_run_bounded (SND (compute_label_offsets p)) (build_offset_to_pc p)
      p H k s ⇒
    asm_run_bounded (SND (compute_label_offsets p')) (build_offset_to_pc p')
      p' H (c * k) (s with as_code := assemble p' ++ x)
Proof
  strip_tac >> qpat_x_assum `asm_refines _ _` mp_tac >>
  simp[asm_refines_def] >> rpt strip_tac >>
  qexists_tac `c` >> rpt strip_tac >>
  `sym_run_within (sym_gas_ok H) (λi. i = AsmOp "RETURNDATACOPY") p
     (asm_data_env p (assemble p ++ x)) k (sym_init s)`
    by (irule asm_run_bounded_sym_within >>
        simp[asm_data_env_ok_asm_data_env]) >>
  `sym_run_within (sym_gas_ok H) (λi. i = AsmOp "RETURNDATACOPY") p'
     (asm_data_env p (assemble p ++ x)) (c * k) (sym_init s)`
    by (first_x_assum irule >> simp[sym_within_ok_gas]) >>
  `asm_data_env p (assemble p ++ x) = asm_data_env p' (assemble p' ++ x)`
    by (irule asm_data_env_agree >> simp[]) >>
  `sym_init (s with as_code := assemble p' ++ x) = sym_init s`
    by simp[sym_init_def] >>
  irule sym_within_asm_run_bounded >> simp[] >>
  qexists_tac `asm_data_env p' (assemble p' ++ x)` >>
  fs[asm_data_env_ok_asm_data_env]
QED
