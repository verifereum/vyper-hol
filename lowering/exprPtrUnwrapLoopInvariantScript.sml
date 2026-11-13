Theory exprPtrUnwrapLoopInvariant
Ancestors
  exprPtrUnwrapCondition exprPtrUnwrapGeneratedPath slotCopyExecution
  copyExecution bodyPtrDefs ptrDiscipline ptrSafeRun finite_map pred_set
  fragGasPathPtr fragGasSeqPtr venomExecSemantics venomState

(* Ghost companion for the counted loop. This bundles compositional frames;
   the existing runtime slot_copy_inv is not duplicated. *)
Definition slot_copy_ghost_inv_def:
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G tn s <=>
    op_taint tn (Var (slot_copy_var cs 0)) = {} /\
    ptr_covers G tn root s (32*n) /\
    tn.t_stor = tn0.t_stor /\ tn.t_trans = tn0.t_trans /\ tn.t_imm = tn0.t_imm /\
    (!j b. j < i /\ b < 32 /\ w2n d + 32*j + b IN tn.t_mem ==>
      b IN key_taint (if load=SLOAD then tn0.t_stor else tn0.t_trans) (p+n2w j)) /\
    (!a. ~(w2n d <= a /\ a < w2n d + 32*i) ==>
      (a IN tn.t_mem <=> a IN tn0.t_mem)) /\
    (!v. slot_copy_external cs (Var v) ==>
      FLOOKUP G v = FLOOKUP G0 v /\ op_taint tn (Var v) = op_taint tn0 (Var v))
End

Theorem copy_taint_prefix_store:
  (!j b:num. j < i /\ b < 32 /\ (start:num) + 32*j + b IN old ==>
    b IN mask j) /\
  new = (old DIFF {a | start+32*i <= a /\ a < start+32*i+32}) UNION
    {start+32*i+b | b | b IN mask i} ==>
  !j b. j < i+1 /\ b < 32 /\ start+32*j+b IN new ==> b IN mask j
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> Cases_on `j=i`
  >- (gvs[] >> fs[IN_UNION, IN_DIFF, GSPECIFICATION] >> `F` by decide_tac) >>
  `j < i` by decide_tac >>
  `start+32*j+b < start+32*i` by decide_tac >>
  `start+32*j+b IN old` by
    (gvs[] >> fs[IN_UNION, IN_DIFF, GSPECIFICATION] >> `F` by decide_tac) >>
  metis_tac[]
QED

Theorem copy_taint_outside_store:
  (!a:num. ~((start:num) <= a /\ a < start+32*i) ==> (a IN old <=> a IN initial)) /\
  (!b. b IN mask ==> b < 32) /\
  new = (old DIFF {a | start+32*i <= a /\ a < start+32*i+32}) UNION
    {start+32*i+b | b | b IN mask} ==>
  !a. ~(start <= a /\ a < start+32*(i+1)) ==> (a IN new <=> a IN initial)
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `~(start <= a /\ a < start+32*i) /\
   ~(start+32*i <= a /\ a < start+32*i+32)` by decide_tac >>
  `~(?b. a=start+32*i+b /\ b IN mask)` by
    (strip_tac >> first_x_assum drule >> strip_tac >> decide_tac) >>
  gvs[IN_UNION, IN_DIFF, GSPECIFICATION] >> metis_tac[]
QED

Theorem copy_condition_ghost_frame:
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G tn s /\
  slot_copy_external cs (Var root) /\
  tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
  op_taint tn1 (Var (slot_copy_var cs 0)) = {} /\
  (!v. v <> slot_copy_var cs 1 ==>
    FLOOKUP G1 v = FLOOKUP G v /\ op_taint tn1 (Var v) = op_taint tn (Var v)) /\
  (!v c. v <> slot_copy_var cs 1 /\ ptr_covers G tn v s c ==>
    ptr_covers G1 tn1 v t c) ==>
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G1 tn1 t
Proof
  strip_tac >>
  `root <> slot_copy_var cs 1` by
    (fs[slot_copy_external_def] >> metis_tac[DECIDE ``1<7``]) >>
  fs[slot_copy_ghost_inv_def] >> conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `v <> slot_copy_var cs 1` by
    (fs[slot_copy_external_def] >> metis_tac[DECIDE ``1<7``]) >>
  metis_tac[]
QED

Theorem copy_condition_preserves_invariants:
  slot_copy_inv cs load original p d n regions i s /\
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G tn s /\
  slot_copy_external cs (Var root) /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = slot_copy_cond_insts cs n /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?G1 tn1.
    gas_path_ptr D lo ctx fn PG G tn s 0 G1 tn1 (OK (slot_copy_cond_result cs n i s)) /\
    slot_copy_inv cs load original p d n regions i (slot_copy_cond_result cs n i s) /\
    slot_copy_ghost_inv cs load p d root n G0 tn0 i G1 tn1 (slot_copy_cond_result cs n i s) /\
    allocas_from lo (slot_copy_cond_result cs n i s) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp (slot_copy_cond_result cs n i s))
Proof
  strip_tac >>
  `i < 2**256 /\ n < 2**256 /\ lookup_var (slot_copy_var cs 0) s = SOME (n2w i)` by
    (fs[slot_copy_inv_def] >> decide_tac) >>
  `op_taint tn (Var (slot_copy_var cs 0)) = {}` by fs[slot_copy_ghost_inv_def] >>
  drule_all copy_generated_condition_framed >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  qexistsl [`G1`, `tn1`] >> simp[slot_copy_condition_invariant] >>
  irule copy_condition_ghost_frame >> metis_tac[]
QED

Theorem copy_body_ghost_frame:
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G tn s /\
  tn1.t_mem =
    (tn.t_mem DIFF {a | w2n d+32*i <= a /\ a < w2n d+32*i+32}) UNION
    {w2n d+32*i+b | b | b IN
      key_taint (if load=SLOAD then tn.t_stor else tn.t_trans) (p+n2w i)} /\
  tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
  op_taint tn1 (Var (slot_copy_var cs 0)) = {} /\
  ptr_covers G1 tn1 root t (32*n) /\
  (!v. slot_copy_external cs (Var v) ==>
    FLOOKUP G1 v = FLOOKUP G v /\ op_taint tn1 (Var v) = op_taint tn (Var v)) ==>
  slot_copy_ghost_inv cs load p d root n G0 tn0 (i+1) G1 tn1 t
Proof
  strip_tac >> fs[slot_copy_ghost_inv_def, IgnAsm `tn1.t_mem = _`] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule (SRULE [] (Q.INST [`mask` |->
        `\j. key_taint (if load=SLOAD then tn0.t_stor else tn0.t_trans) (p+n2w j)`]
        copy_taint_prefix_store)) >>
      conj_tac >- simp[] >>
      qexistsl [`i`, `tn1.t_mem`, `tn.t_mem`, `w2n d`] >> gvs[] >> metis_tac[]) >>
  gen_tac >> disch_tac >> irule copy_taint_outside_store >>
  qexistsl [`i`,
    `key_taint (if load=SLOAD then tn0.t_stor else tn0.t_trans) (p+n2w i)`,
    `tn.t_mem`, `w2n d`] >> simp[key_taint_def] >> metis_tac[]
QED

Theorem copy_body_parameters:
  slot_copy_inv cs load original p d n regions i s /\ i < n /\
  slot_copy_external cs src /\ slot_copy_external cs (Var root) /\
  eval_operand src original = SOME p /\ lookup_var root original = SOME d ==>
  eval_operand src s = SOME p /\ lookup_var root s = SOME d /\
  eval_operand (Var (slot_copy_var cs 0)) s = SOME (n2w i) /\
  (n2w i:bytes32)*32w = n2w (32*i) /\
  32*i < 32*n /\ 32*i+32 <= 32*n /\
  w2n d+32*i < dimword(:256) /\
  w2n (d+n2w (32*i)) = w2n d+32*i /\
  (!k. k < 7 ==> root <> slot_copy_var cs k)
Proof
  strip_tac >>
  `w2n (d+n2w i*32w) = w2n d+32*i` by
    (irule slot_copy_body_nonwrapping >> qexists `n` >> fs[slot_copy_inv_def]) >>
  `((n2w i:bytes32)*32w = n2w (32*i))` by
    (pure_rewrite_tac[wordsTheory.word_mul_n2w] >> AP_TERM_TAC >> decide_tac) >>
  `lookup_var root s = SOME d` by
    (qpat_x_assum `slot_copy_inv _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[slot_copy_inv_def] >> strip_tac >>
     qpat_x_assum `!op. slot_copy_external _ op ==> _`
       (qspec_then `Var root` mp_tac) >> simp[eval_operand_def]) >>
  fs[slot_copy_inv_def, slot_copy_external_def, eval_operand_def, wordsTheory.dimword_def]
QED

Theorem copy_ghost_external_taint:
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G tn s /\
  slot_copy_external cs op ==> op_taint tn op = op_taint tn0 op
Proof
  Cases_on `op` >> simp[slot_copy_ghost_inv_def, op_taint_def] >> metis_tac[]
QED

Theorem copy_body_preserves_invariants:
  (load=SLOAD \/ load=TLOAD) /\
  slot_copy_inv cs load original p d n regions i s /\ i < n /\
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G tn s /\
  slot_copy_external cs src /\ slot_copy_external cs (Var root) /\
  eval_operand src original = SOME p /\ lookup_var root original = SOME d /\
  op_taint tn src = {} /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = slot_copy_body_insts cs src (Var root) load /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf.
    gas_path_ptr D lo ctx fn PG G tn s 0 Gf tnf
      (OK (slot_copy_body_result cs p d load i s)) /\
    slot_copy_inv cs load original p d n regions (i+1) (slot_copy_body_result cs p d load i s) /\
    slot_copy_ghost_inv cs load p d root n G0 tn0 (i+1) Gf tnf
      (slot_copy_body_result cs p d load i s) /\
    allocas_from lo (slot_copy_body_result cs p d load i s) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp (slot_copy_body_result cs p d load i s))
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >> (
  drule_all copy_body_parameters >> strip_tac >>
  `op_taint tn (Var (slot_copy_var cs 0)) = {} /\
   ptr_covers G tn root s (32*n)` by fs[slot_copy_ghost_inv_def] >>
  `root <> slot_copy_var cs 2 /\ root <> slot_copy_var cs 3 /\
   root <> slot_copy_var cs 4 /\ root <> slot_copy_var cs 5` by simp[] >>
  drule_all copy_generated_body_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `jump_to (slot_copy_cond cs) (t with vs_inst_idx := 7) =
   slot_copy_body_result cs p d load i s` by
    simp[slot_copy_body_result_def, jump_to_def, update_var_def] >>
  qpat_x_assum `t = _` kall_tac >>
  qexistsl [`Gf`, `tnf`] >> gnvs[] >> simp[slot_copy_body_invariant] >>
  irule copy_body_ghost_frame >> conj_tac >- simp[] >> conj_tac
  >- (qpat_x_assum `!v c. _ ==> ptr_covers _ _ _ _ _` irule >>
      simp[] >> metis_tac[DECIDE ``0<7 /\ 2<7 /\ 3<7 /\ 4<7 /\ 5<7 /\ 6<7``]) >>
  qexistsl [`G`, `s`, `tn`] >> simp[] >> conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_x_assum `!v. _ ==> FLOOKUP _ _ = _ /\ _` (qspec_then `v` mp_tac) >>
      (impl_tac >- (fs[slot_copy_external_def] >>
        metis_tac[DECIDE ``0<7 /\ 2<7 /\ 3<7 /\ 4<7 /\ 5<7 /\ 6<7``])) >> simp[]) >>
  AP_TERM_TAC >> POP_ASSUM_LIST (K ALL_TAC) >> simp[EXTENSION] >>
  metis_tac[DECIDE ``!x y z:num. x+(y+z)=y+(x+z)``])
QED

Theorem copy_counted_iteration:
  (load=SLOAD \/ load=TLOAD) /\
  slot_copy_inv cs load original p d n regions i s /\ i < n /\
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G tn s /\
  slot_copy_external cs src /\ slot_copy_external cs (Var root) /\
  eval_operand src original = SOME p /\ lookup_var root original = SOME d /\
  op_taint tn src = {} /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME cond /\
  cond.bb_instructions = slot_copy_cond_insts cs n /\
  lookup_block (slot_copy_body cs) fn.fn_blocks = SOME bodybb /\
  bodybb.bb_instructions = slot_copy_body_insts cs src (Var root) load /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf.
    gas_path_ptr D lo ctx fn PG G tn s 0 Gf tnf
      (OK (slot_copy_body_result cs p d load i (slot_copy_cond_result cs n i s))) /\
    slot_copy_inv cs load original p d n regions (i+1)
      (slot_copy_body_result cs p d load i (slot_copy_cond_result cs n i s)) /\
    slot_copy_ghost_inv cs load p d root n G0 tn0 (i+1) Gf tnf
      (slot_copy_body_result cs p d load i (slot_copy_cond_result cs n i s)) /\
    allocas_from lo (slot_copy_body_result cs p d load i (slot_copy_cond_result cs n i s)) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp
      (slot_copy_body_result cs p d load i (slot_copy_cond_result cs n i s)))
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all copy_condition_preserves_invariants >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `op_taint tn1 src = {}` by metis_tac[copy_ghost_external_taint] >>
  `~(slot_copy_cond_result cs n i s).vs_halted` by
    metis_tac[gas_path_ptr_ok_not_halted] >>
  `i <> n` by decide_tac >>
  `(slot_copy_cond_result cs n i s).vs_inst_idx = 0 /\
   lookup_block (slot_copy_cond_result cs n i s).vs_current_bb fn.fn_blocks = SOME bodybb`
    by simp[slot_copy_cond_frame] >>
  drule_all copy_body_preserves_invariants >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl [`Gf`, `tnf`] >> simp[] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
  qexistsl [`G1`, `slot_copy_cond_result cs n i s`, `tn1`] >> simp[]
QED
