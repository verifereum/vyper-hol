(* Scratch words are initialized before their contents are used as cursors. *)
Theory bodyPtrAbiEncodeScratch
Ancestors
  allocationPtr loweringHalt fragExecPtr typedCopyPtr ghostPcTransportPtr
  bodyPtrAbiEncodeWordChecks exprLoweringProps
  fragGasSeqPtr fragGasPathPtr ptrDiscipline ptrSafeRun bodyPtrDefs
  venomExecSemantics venomInst venomState finite_map words

Theorem abi_encode_scratch_allocation_frame[local]:
  b+32 < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit 32w] [p]) s = OK u /\
  ((FLOOKUP s.vs_allocas id = NONE /\ b = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas id = SOME (b,32)) /\
  Ga = step_prov PG G (mk_inst id ALLOCA [Lit 32w] [p]) u /\
  ta = step_taint (mk_inst id ALLOCA [Lit 32w] [p]) s u tn ==>
  Ga = G |+ (p,(b,32)) /\ ta.t_var = tn.t_var |+ (p,{}) /\
  ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\
  ta.t_mem DIFF {i | b <= i /\ i < b+32} =
    tn.t_mem DIFF {i | b <= i /\ i < b+32} /\
  ptr_covers Ga ta p u 32 /\ lookup_var p u = SOME (n2w b)
Proof
  strip_tac
  >- (`32 < dimword (:256)` by decide_tac >>
      drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
      drule_all step_alloca_fresh >> strip_tac >>
      gvs[] >> simp[ptr_covers_def, lookup_var_def, update_var_def,
        op_taint_def, FLOOKUP_UPDATE, w2n_n2w, pred_setTheory.UNION_DIFF] >>
      simp[pred_setTheory.EXTENSION] >> decide_tac) >>
  drule reused_alloca_ghost >>
  disch_then (qspecl_then [`p`, `PG`, `G`, `tn`] strip_assume_tac) >>
  drule reused_alloca_step >> disch_then (qspec_then `p` assume_tac) >>
  gvs[] >> simp[ptr_covers_def, lookup_var_def, update_var_def,
    op_taint_def, FLOOKUP_UPDATE, w2n_n2w]
QED

Theorem abi_encode_scratch_sequence_checks:
  ~ctx_has_dalloca ctx /\ b+32 < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit 32w] [p]) s = OK u /\
  ((FLOOKUP s.vs_allocas id = NONE /\ b = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas id = SOME (b,32)) ==>
  ?Gf tnf. inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id ALLOCA [Lit 32w] [p];
     mk_inst (id+1) MSTORE [Var p;Lit w] []] s Gf tnf /\
    Gf = G |+ (p,(b,32)) /\ tnf.t_var = tn.t_var |+ (p,{}) /\
    tnf.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    ptr_covers Gf tnf p (mstore b w u) 32 /\
    lookup_var p (mstore b w u) = SOME (n2w b)
Proof
  strip_tac >>
  qabbrev_tac `Ga = step_prov PG G (mk_inst id ALLOCA [Lit 32w] [p]) u` >>
  qabbrev_tac `ta = step_taint (mk_inst id ALLOCA [Lit 32w] [p]) s u tn` >>
  `Ga = G |+ (p,(b,32)) /\ ta.t_var = tn.t_var |+ (p,{}) /\
   ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\
   ta.t_mem DIFF {i | b <= i /\ i < b+32} =
     tn.t_mem DIFF {i | b <= i /\ i < b+32} /\
   ptr_covers Ga ta p u 32 /\ lookup_var p u = SOME (n2w b)` by
    (irule abi_encode_scratch_allocation_frame >>
     simp[Abbr `Ga`, Abbr `ta`] >> metis_tac[]) >>
  `ptr_inst_ok D 0 0 ctx fn Ga ta
    (mk_inst (id+1) MSTORE [Var p;Lit w] [])
    (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule ptr_inst_ok_mstore >> simp[op_taint_def]) >>
  `step_inst_base (mk_inst (id+1) MSTORE [Var p;Lit w] [])
    (u with vs_inst_idx := SUC s.vs_inst_idx) =
    OK (mstore b w (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (simp[Once step_inst_base_def, mk_inst_def, exec_write2_def,
          eval_operand_def, w2n_n2w] >> decide_tac) >>
  `eval_operand (Lit w) u = SOME w /\ op_taint ta (Lit w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `Ga`, `id+1`] mp_tac) >>
  simp[w2n_n2w] >> strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ALLOCA [Lit 32w] [p]) s` by
    (irule ptr_inst_ok_alloca >> simp[]) >>
  simp[inst_seq_ptr_def, Abbr `Ga`, Abbr `ta`, abi_encode_mstore_inst_idx] >>
  gvs[] >> simp[ptr_covers_def, op_taint_def, lookup_var_def, mstore_def,
                FLOOKUP_UPDATE, w2n_n2w]
QED

Theorem abi_encode_scratch_checked_ptr_path:
  ~ctx_has_dalloca ctx /\ b+32 < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit 32w] [p]) s = OK u /\
  ((FLOOKUP s.vs_allocas id = NONE /\ b = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas id = SOME (b,32)) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ALLOCA [Lit 32w] [p];
    mk_inst (id+1) MSTORE [Var p;Lit w] []]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?Gf tnf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
      (OK ((mstore b w u) with vs_inst_idx := s.vs_inst_idx+2)) /\
    Gf = G |+ (p,(b,32)) /\ tnf.t_var = tn.t_var |+ (p,{}) /\
    tnf.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    ptr_covers Gf tnf p (mstore b w u) 32 /\
    lookup_var p (mstore b w u) = SOME (n2w b)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_encode_scratch_sequence_checks >>
  disch_then (qspecl_then [`w`, `tn`, `fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `lookup_var p u = SOME (n2w b)` by fs[lookup_var_def, mstore_def] >>
  `run_inst_seq [mk_inst id ALLOCA [Lit 32w] [p];
     mk_inst (id+1) MSTORE [Var p;Lit w] []] s = OK (mstore b w u)` by
    (simp[run_inst_seq_def] >>
     simp[Once step_inst_base_def, mk_inst_def, exec_write2_def,
          eval_operand_def, w2n_n2w] >> decide_tac) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    [mk_inst id ALLOCA [Lit 32w] [p];
     mk_inst (id+1) MSTORE [Var p;Lit w] []]` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[mk_inst_def] >> strip_tac >>
  qexists_tac `tnf` >> gvs[]
QED
