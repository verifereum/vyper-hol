Theory bodyPtrIfExpStorageBody
Ancestors
  bodyPtrIfExpStoragePhases slotCopyExecution copyExecution
  exprLoweringProps fragExec venomExecSemantics venomState venomInst
  finite_map ptrDiscipline instIdxIndep bodyPtrDefs

Theorem ifexp_copy_body_runtime:
  MEM load [SLOAD;TLOAD] /\
  slot_copy_external cs src /\ slot_copy_external cs dst /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  lookup_var (slot_copy_var cs 0) s = SOME (n2w i) ==>
  ?t. run_inst_seq (TAKE 7 (slot_copy_body_insts cs src dst load)) s = OK t /\
    jump_to (slot_copy_cond cs) t = slot_copy_body_result cs p d load i s
Proof
  strip_tac >>
  `run_inst_seq (slot_copy_body_insts cs src dst load) s =
     OK (slot_copy_body_result cs p d load i s)` by
    (irule slot_copy_body_execution >> simp[] >> fs[]) >>
  qabbrev_tac `xs = TAKE 7 (slot_copy_body_insts cs src dst load)` >>
  `slot_copy_body_insts cs src dst load =
    xs ++ [mk_inst (cs.cs_next_id + 11) JMP [Label (slot_copy_cond cs)] []]` by
    simp[Abbr `xs`, slot_copy_body_insts_def] >>
  `?t. run_inst_seq xs s = OK t` by
    (spose_not_then assume_tac >>
     drule run_inst_seq_append_err >>
     disch_then (qspec_then
       `[mk_inst (cs.cs_next_id + 11) JMP [Label (slot_copy_cond cs)] []]` assume_tac) >>
     metis_tac[]) >>
  qexists_tac `t` >> conj_tac >- gvs[Abbr `xs`] >>
  drule run_inst_seq_append >>
  disch_then (qspec_then
    `[mk_inst (cs.cs_next_id + 11) JMP [Label (slot_copy_cond cs)] []]` mp_tac) >>
  gvs[run_inst_seq_def, step_inst_base_def, mk_inst_def]
QED

(* Concrete code conclusions determine all generic phase selectors by matching. *)
Theorem ifexp_copy_body_read:
  MEM load [SLOAD;TLOAD] /\ ~ctx_has_dalloca ctx /\
  eval_operand src s = SOME p /\
  eval_operand (Var (slot_copy_var cs 0)) s = SOME q /\
  op_taint tn src = {} /\ op_taint tn (Var (slot_copy_var cs 0)) = {} ==>
  ?t G' tn'.
    run_inst_seq (TAKE 2 (slot_copy_body_insts cs src dst load)) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn
      (TAKE 2 (slot_copy_body_insts cs src dst load)) s G' tn' /\
    t = update_var (slot_copy_var cs 3) (slot_copy_word load s (p+q))
          (update_var (slot_copy_var cs 2) (p+q) s) /\
    op_prov G' (Var (slot_copy_var cs 3)) = NONE /\
    op_taint tn' (Var (slot_copy_var cs 3)) =
      (if load = SLOAD then key_taint tn.t_stor (p+q)
       else key_taint tn.t_trans (p+q)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x <> slot_copy_var cs 2 /\ x <> slot_copy_var cs 3 ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `TAKE 2 (slot_copy_body_insts cs src dst load) =
    [mk_inst (cs.cs_next_id+4) ADD [src;Var (slot_copy_var cs 0)] [slot_copy_var cs 2];
     mk_inst (cs.cs_next_id+5) load [Var (slot_copy_var cs 2)] [slot_copy_var cs 3]]` by
    simp[slot_copy_body_insts_def] >>
  pop_assum (fn th => pure_rewrite_tac [th]) >>
  irule ifexp_copy_read_phase >> simp[]
QED

Theorem ifexp_copy_body_address:
  ~ctx_has_dalloca ctx /\
  eval_operand (Var (slot_copy_var cs 0)) s = SOME q /\
  eval_operand dst s = SOME d /\
  op_taint tn (Var (slot_copy_var cs 0)) = {} /\ op_taint tn dst = {} /\
  op_prov G dst = SOME (b,n) /\ dst <> Var (slot_copy_var cs 4) /\
  b <= w2n (d+q*32w) /\ w2n (d+q*32w) + 32 <= b+n ==>
  ?t G' tn'.
    run_inst_seq (TAKE 2 (DROP 2 (slot_copy_body_insts cs src dst load))) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn
      (TAKE 2 (DROP 2 (slot_copy_body_insts cs src dst load))) s G' tn' /\
    t = update_var (slot_copy_var cs 5) (d+q*32w)
      (update_var (slot_copy_var cs 4) (q*32w) s) /\
    ptr_covers G' tn' (slot_copy_var cs 5) t 32 /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x <> slot_copy_var cs 4 /\ x <> slot_copy_var cs 5 ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `TAKE 2 (DROP 2 (slot_copy_body_insts cs src dst load)) =
    [mk_inst (cs.cs_next_id+6) MUL [Var (slot_copy_var cs 0);Lit 32w] [slot_copy_var cs 4];
     mk_inst (cs.cs_next_id+7) ADD [dst;Var (slot_copy_var cs 4)] [slot_copy_var cs 5]]` by
    simp[slot_copy_body_insts_def] >>
  pop_assum (fn th => pure_rewrite_tac [th]) >>
  irule ifexp_copy_address_phase >> simp[]
QED

Theorem ifexp_copy_body_store:
  ~ctx_has_dalloca ctx /\ ptr_covers G tn (slot_copy_var cs 5) s 32 /\
  eval_operand (Var (slot_copy_var cs 5)) s = SOME d /\
  eval_operand (Var (slot_copy_var cs 3)) s = SOME w ==>
  ?t tn'.
    run_inst_seq (TAKE 1 (DROP 4 (slot_copy_body_insts cs src dst load))) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn
      (TAKE 1 (DROP 4 (slot_copy_body_insts cs src dst load))) s G tn' /\
    t = mstore (w2n d) w s /\
    tn'.t_mem = (tn.t_mem DIFF {i | w2n d <= i /\ i < w2n d + 32}) UNION
      {w2n d + k | k IN op_taint tn (Var (slot_copy_var cs 3))} /\
    tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >>
  `TAKE 1 (DROP 4 (slot_copy_body_insts cs src dst load)) =
    [mk_inst (cs.cs_next_id+8) MSTORE
      [Var (slot_copy_var cs 5);Var (slot_copy_var cs 3)] []]` by
    simp[slot_copy_body_insts_def] >>
  pop_assum (fn th => pure_rewrite_tac [th]) >>
  irule ifexp_copy_store_phase >> simp[]
QED

Theorem ifexp_copy_body_increment:
  ~ctx_has_dalloca ctx /\ lookup_var (slot_copy_var cs 0) s = SOME w /\
  op_taint tn (Var (slot_copy_var cs 0)) = {} /\
  op_prov G (Var (slot_copy_var cs 0)) = NONE ==>
  ?t G' tn'.
    run_inst_seq (TAKE 2 (DROP 5 (slot_copy_body_insts cs src dst load))) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn
      (TAKE 2 (DROP 5 (slot_copy_body_insts cs src dst load))) s G' tn' /\
    t = update_var (slot_copy_var cs 0) (w+1w)
      (update_var (slot_copy_var cs 6) (w+1w) s) /\
    lookup_var (slot_copy_var cs 0) t = SOME (w+1w) /\
    op_prov G' (Var (slot_copy_var cs 0)) = NONE /\
    op_taint tn' (Var (slot_copy_var cs 0)) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. x <> slot_copy_var cs 6 /\ x <> slot_copy_var cs 0 ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `TAKE 2 (DROP 5 (slot_copy_body_insts cs src dst load)) =
    [mk_inst (cs.cs_next_id+9) ADD [Var (slot_copy_var cs 0);Lit 1w] [slot_copy_var cs 6];
     mk_inst (cs.cs_next_id+10) ASSIGN [Var (slot_copy_var cs 6)] [slot_copy_var cs 0]]` by
    simp[slot_copy_body_insts_def] >>
  pop_assum (fn th => pure_rewrite_tac [th]) >>
  irule ifexp_copy_increment_phase >> simp[]
QED

Theorem ifexp_copy_body_first_four:
  MEM load [SLOAD;TLOAD] /\ ~ctx_has_dalloca ctx /\
  slot_copy_external cs src /\ slot_copy_external cs dst /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  eval_operand (Var (slot_copy_var cs 0)) s = SOME q /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  op_taint tn (Var (slot_copy_var cs 0)) = {} /\
  op_prov G dst = SOME (b,n) /\
  b <= w2n (d+q*32w) /\ w2n (d+q*32w)+32 <= b+n ==>
  ?t G' tn'.
    run_inst_seq (TAKE 4 (slot_copy_body_insts cs src dst load)) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn
      (TAKE 4 (slot_copy_body_insts cs src dst load)) s G' tn' /\
    ptr_covers G' tn' (slot_copy_var cs 5) t 32 /\
    lookup_var (slot_copy_var cs 5) t = SOME (d+q*32w) /\
    lookup_var (slot_copy_var cs 3) t = SOME (slot_copy_word load s (p+q)) /\
    op_taint tn' (Var (slot_copy_var cs 3)) =
      (if load = SLOAD then key_taint tn.t_stor (p+q)
       else key_taint tn.t_trans (p+q)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. (!k. k < 7 ==> x <> slot_copy_var cs k) \/ x = slot_copy_var cs 0 ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `?r G1 tn1.
    run_inst_seq (TAKE 2 (slot_copy_body_insts cs src dst load)) s = OK r /\
    inst_seq_ptr D 0 ctx fn PG G tn
      (TAKE 2 (slot_copy_body_insts cs src dst load)) s G1 tn1 /\
    r = update_var (slot_copy_var cs 3) (slot_copy_word load s (p+q))
          (update_var (slot_copy_var cs 2) (p+q) s) /\
    op_prov G1 (Var (slot_copy_var cs 3)) = NONE /\
    op_taint tn1 (Var (slot_copy_var cs 3)) =
      (if load = SLOAD then key_taint tn.t_stor (p+q)
       else key_taint tn.t_trans (p+q)) /\
    tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
    tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    (!x. x <> slot_copy_var cs 2 /\ x <> slot_copy_var cs 3 ==>
      lookup_var x r = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x))` by
    (irule ifexp_copy_body_read >> simp[]) >>
  suspend "after_read"
QED

Resume ifexp_copy_body_first_four[after_read]:
  `dst <> Var (slot_copy_var cs 2) /\ dst <> Var (slot_copy_var cs 3) /\
   dst <> Var (slot_copy_var cs 4)` by
    metis_tac[slot_copy_external_def, DECIDE ``2 < 7 /\ 3 < 7 /\ 4 < 7``] >>
  `op_prov G1 dst = SOME (b,n) /\ op_taint tn1 dst = {}` by
    (Cases_on `dst` >> gvs[op_prov_def, op_taint_def] >> metis_tac[]) >>
  qabbrev_tac `r1 = r with vs_inst_idx := s.vs_inst_idx + 2` >>
  `eval_operand dst r1 = SOME d /\
   eval_operand (Var (slot_copy_var cs 0)) r1 = SOME q /\
   op_taint tn1 (Var (slot_copy_var cs 0)) = {}` by
    (simp[Abbr `r1`, slot_copy_var_distinct] >>
     metis_tac[slot_copy_var_distinct, DECIDE ``0 <> 2 /\ 0 <> 3``]) >>
  `?u G2 tn2.
    run_inst_seq (TAKE 2 (DROP 2 (slot_copy_body_insts cs src dst load))) r1 = OK u /\
    inst_seq_ptr D 0 ctx fn PG G1 tn1
      (TAKE 2 (DROP 2 (slot_copy_body_insts cs src dst load))) r1 G2 tn2 /\
    u = update_var (slot_copy_var cs 5) (d+q*32w)
      (update_var (slot_copy_var cs 4) (q*32w) r1) /\
    ptr_covers G2 tn2 (slot_copy_var cs 5) u 32 /\
    tn2.t_mem = tn1.t_mem /\ tn2.t_stor = tn1.t_stor /\
    tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm /\
    (!x. x <> slot_copy_var cs 4 /\ x <> slot_copy_var cs 5 ==>
      lookup_var x u = lookup_var x r1 /\ FLOOKUP G2 x = FLOOKUP G1 x /\
      op_taint tn2 (Var x) = op_taint tn1 (Var x))` by
    (irule ifexp_copy_body_address >> simp[]) >>
  suspend "after_address"
QED

Resume ifexp_copy_body_first_four[after_address]:
  `EVERY (\i. ~is_terminator i.inst_opcode)
     (TAKE 2 (DROP 2 (slot_copy_body_insts cs src dst load)))` by
    simp[slot_copy_body_insts_def, mk_inst_def, is_terminator_def] >>
  `run_inst_seq (TAKE 2 (DROP 2 (slot_copy_body_insts cs src dst load)))
     (r1 with vs_inst_idx := s.vs_inst_idx) =
     OK (u with vs_inst_idx := s.vs_inst_idx)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  `r1 with vs_inst_idx := s.vs_inst_idx = r` by
    simp[Abbr `r1`, update_var_def] >>
  `TAKE 4 (slot_copy_body_insts cs src dst load) =
    TAKE 2 (slot_copy_body_insts cs src dst load) ++
    TAKE 2 (DROP 2 (slot_copy_body_insts cs src dst load))` by
    simp[slot_copy_body_insts_def] >>
  qexistsl_tac [`u with vs_inst_idx := s.vs_inst_idx`, `G2`, `tn2`] >>
  conj_tac
  >- (qpat_assum `run_inst_seq (TAKE 2 _) s = OK r`
        (mp_then Any mp_tac run_inst_seq_append) >>
      disch_then (qspec_then
       `TAKE 2 (DROP 2 (slot_copy_body_insts cs src dst load))` mp_tac) >>
      gvs[]) >>
  conj_tac
  >- (qpat_x_assum `TAKE 4 _ = _` (fn th => pure_rewrite_tac [th]) >>
      irule ifexp_inst_seq_ptr_append_at >>
      conj_tac >- (gvs[] >> simp[slot_copy_body_insts_def, mk_inst_def, is_terminator_def]) >>
      qexistsl_tac [`G1`, `r`, `tn1`] >>
      gvs[Abbr `r1`, slot_copy_body_insts_def, mk_inst_def, is_terminator_def]) >>
  simp[ptr_covers_def] >>
  conj_tac >- simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[Abbr `r1`, lookup_var_def, update_var_def,
                   FLOOKUP_UPDATE, slot_copy_var_distinct] >>
  conj_tac
  >- (qpat_x_assum `!x. x <> slot_copy_var cs 4 /\ _ ==> _`
       (qspec_then `slot_copy_var cs 3` mp_tac) >> simp[slot_copy_var_distinct]) >>
  gen_tac >> strip_tac >>
  `x <> slot_copy_var cs 2 /\ x <> slot_copy_var cs 3 /\
   x <> slot_copy_var cs 4 /\ x <> slot_copy_var cs 5` by
    (gvs[slot_copy_var_distinct] >>
     metis_tac[DECIDE ``2 < 7 /\ 3 < 7 /\ 4 < 7 /\ 5 < 7``]) >>
  qpat_x_assum `!x. x <> slot_copy_var cs 4 /\ _ ==> _` (qspec_then `x` mp_tac) >>
  qpat_x_assum `!x. x <> slot_copy_var cs 2 /\ _ ==> _` (qspec_then `x` mp_tac) >>
  simp[Abbr `r1`, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED
Finalise ifexp_copy_body_first_four
