(* Concrete ghosts for the two readonly raw-call header instructions. *)
Theory bodyFullRawCallHeaderSteps
Ancestors
  bodyPtrHashBuiltinsKeccakBytesRun exprPtrCtorImmStore
  exprPtrUnwrapScalarEdges fragGasSeqPtr bodyPtrDefs ptrDiscipline
  venomState venomInst venomExecSemantics valueEncodingProps words finite_map

Theorem raw_call_header_steps_checked:
  !D lo ctx fn PG G tn s il ia x l p b base cap n.
    ALL_DISTINCT [x;l;p] /\
    eval_operand (Var x) s = SOME (n2w b) /\
    FLOOKUP G x = SOME (base,cap) /\
    base <= b /\ b+32+n <= base+cap /\
    b+32 < dimword (:256) /\ n < dimword (:256) /\
    op_taint tn (Var x) = {} /\
    (!i. b <= i /\ i < b+32+n ==> i NOTIN tn.t_mem) /\
    mem_word_at b s.vs_memory = n2w n /\
    allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
    inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst il MLOAD [Var x] [l];
       mk_inst ia ADD [Var x; Lit 32w] [p]] s
      (DRESTRICT G (COMPL {l}) |+ (p,(base,cap)))
      (tn with t_var := tn.t_var |+ (l,{}) |+ (p,{}))
Proof
  rpt gen_tac >> strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `w2n (n2w b:bytes32) = b` by simp[] >>
  `ptr_covers G tn x s 32` by
    (simp[ptr_covers_def] >> qexists_tac `n2w b` >>
     fs[eval_operand_def] >> decide_tac) >>
  `!i. b <= i /\ i < b+32 ==> i NOTIN tn.t_mem` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` irule >> decide_tac) >>
  `mload b s = n2w n` by fs[mem_word_at_eq_mload] >>
  `step_inst_base (mk_inst il MLOAD [Var x] [l]) s =
    OK (update_var l (n2w n) s)` by
    (pure_once_rewrite_tac[step_inst_base_def] >> simp[mk_inst_def, exec_read1_def]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_mload_lo >> simp[]) >>
  simp[hash_mload_ghost] >>
  qabbrev_tac `s1 = update_var l (n2w n) s with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {l})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (l,{})` >>
  suspend "add"
QED

Resume raw_call_header_steps_checked[add]:
  `step_prov PG G (mk_inst il MLOAD [Var x] [l])
    (update_var l (n2w n) s) = G1` by
    simp[Abbr `G1`, step_prov_def, set_prov_def, out_prov_def, mk_inst_def] >>
  rename1 `FLOOKUP G x = SOME (rootbase,cap)` >>
  `eval_operand (Var x) s1 = SOME (n2w b) /\
   FLOOKUP G1 x = SOME (rootbase,cap) /\ op_taint tn1 (Var x) = {}` by
    gvs[Abbr `s1`, Abbr `G1`, Abbr `tn1`, listTheory.ALL_DISTINCT,
      eval_operand_def, lookup_var_def, update_var_def, op_taint_def,
      FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  `step_inst_base (mk_inst ia ADD [Var x; Lit 32w] [p]) s1 =
    OK (update_var p (n2w b+32w) s1)` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_pure2_def, eval_operand_def]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_copy_arith >>
    simp[op_taint_def, Abbr `s1`, update_var_def, allocas_from_def]) >>
  simp[inst_seq_ptr_def, hash_add_ghost, Abbr `G1`, Abbr `tn1`]
QED

Finalise raw_call_header_steps_checked
