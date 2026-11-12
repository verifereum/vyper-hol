(* The checked call and its success/abort continuation, before GAS. *)
Theory bodyPtrHashBuiltinsShaTailCall
Ancestors bodyPtrHashBuiltinsShaTailSteps bodyPtrHashBuiltinsShaCall
  bodyPtrDefs fragGasSeqPtr ptrSafeRun ptrDiscipline venomInst venomState
  venomExecSemantics words finite_map pred_set

Theorem hash_sha256_call_load_check:
  !D ctx fn PG G tn s t ic ia im gas p len q success out a w n r b sz c cap.
    eval_operand gas s = SOME a /\ eval_operand (Var p) s = SOME w /\
    eval_operand len s = SOME n /\ eval_operand (Var q) s = SOME r /\
    FLOOKUP G p = SOME (b,sz) /\ FLOOKUP G q = SOME (c,cap) /\
    b <= w2n w /\ w2n w+w2n n <= b+sz /\
    c <= w2n r /\ w2n r+32 <= c+cap /\ q <> success /\
    (!op. MEM op [gas;Lit 2w;Var p;len;Var q;Lit 32w] ==> op_taint tn op = {}) /\
    (!i. w2n w <= i /\ i < w2n w+w2n n ==> i NOTIN tn.t_mem) /\
    ~ctx_has_dalloca ctx /\
    step_inst_base (mk_inst ic STATICCALL
      [gas;Lit 2w;Var p;len;Var q;Lit 32w] [success]) s = OK t /\
    t.vs_requests = s.vs_requests /\ t.vs_allocas = s.vs_allocas /\
    t.vs_fmp = s.vs_fmp /\ LENGTH t.vs_returndata = 32 /\
    lookup_var success t = SOME 1w /\ eval_operand (Var q) t = SOME r ==>
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst ic STATICCALL [gas;Lit 2w;Var p;len;Var q;Lit 32w] [success];
       mk_inst ia ASSERT [Var success] []; mk_inst im MLOAD [Var q] [out]] s
      (DRESTRICT (DRESTRICT G (COMPL {success})) (COMPL {out}))
      ((step_taint (mk_inst ic STATICCALL
        [gas;Lit 2w;Var p;len;Var q;Lit 32w] [success]) s t tn)
        with t_var := tn.t_var |+ (success,{}) |+ (out,{}))
Proof
  rpt gen_tac >> strip_tac >> simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule hash_staticcall_inst_ok >> simp[] >> metis_tac[]) >>
  qabbrev_tac `call = mk_inst ic STATICCALL
    [gas;Lit 2w;Var p;len;Var q;Lit 32w] [success]` >>
  qabbrev_tac `u = t with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {success})` >>
  qabbrev_tac `tn1 = step_taint call s t tn` >>
  `step_prov PG G call t = G1` by
    (simp[Abbr `call`, Abbr `G1`] >>
     irule (cj 1 hash_staticcall_ghost) >> metis_tac[]) >>
  `tn1 = tn with <|t_var := tn.t_var |+ (success,{});
     t_mem := tn.t_mem DIFF range_bytes [(w2n r,MIN 32 (LENGTH t.vs_returndata))]|>` by
    (SIMP_TAC (srw_ss()) [Abbr `tn1`, Abbr `call`] >>
     irule (SRULE [] (cj 2 hash_staticcall_ghost)) >> metis_tac[]) >>
  `tn1.t_var = tn.t_var |+ (success,{})` by simp[] >>
  `op_taint tn (Var q) = {}` by
    (qpat_x_assum `!op. MEM op _ ==> _` (qspec_then `Var q` mp_tac) >> simp[]) >>
  `op_taint tn1 (Var success) = {} /\ ptr_covers G1 tn1 q u 32` by
    (gvs[ptr_covers_def, Abbr `G1`, Abbr `u`, eval_operand_def,
       lookup_var_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `!i. w2n r <= i /\ i < w2n r+32 ==> i NOTIN tn1.t_mem` by
    simp[range_bytes_def] >>
  `tn1 with t_var := tn.t_var |+ (success,{}) |+ (out,{}) =
   tn1 with t_var := tn1.t_var |+ (out,{})` by simp[] >>
  `inst_seq_ptr D 0 ctx fn PG G1 tn1
     [mk_inst ia ASSERT [Var success] []; mk_inst im MLOAD [Var q] [out]] u
     (DRESTRICT G1 (COMPL {out})) (tn1 with t_var := tn1.t_var |+ (out,{}))` by
    (irule hash_sha256_load_pair >>
     gvs[Abbr `u`, eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  gvs[Abbr `G1`]
QED

Theorem hash_sha256_call_abort_check:
  !D ctx fn PG G tn s t ic ia im gas p len q success out a w n r b sz c cap.
    eval_operand gas s = SOME a /\ eval_operand (Var p) s = SOME w /\
    eval_operand len s = SOME n /\ eval_operand (Var q) s = SOME r /\
    FLOOKUP G p = SOME (b,sz) /\ FLOOKUP G q = SOME (c,cap) /\
    b <= w2n w /\ w2n w+w2n n <= b+sz /\
    c <= w2n r /\ w2n r+32 <= c+cap /\
    (!op. MEM op [gas;Lit 2w;Var p;len;Var q;Lit 32w] ==> op_taint tn op = {}) /\
    (!i. w2n w <= i /\ i < w2n w+w2n n ==> i NOTIN tn.t_mem) /\
    ~ctx_has_dalloca ctx /\
    step_inst_base (mk_inst ic STATICCALL
      [gas;Lit 2w;Var p;len;Var q;Lit 32w] [success]) s = OK t /\
    t.vs_requests = s.vs_requests /\ t.vs_allocas = s.vs_allocas /\
    t.vs_fmp = s.vs_fmp /\ lookup_var success t = SOME 0w ==>
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst ic STATICCALL [gas;Lit 2w;Var p;len;Var q;Lit 32w] [success];
       mk_inst ia ASSERT [Var success] []; mk_inst im MLOAD [Var q] [out]] s
      (DRESTRICT G (COMPL {success}))
      (step_taint (mk_inst ic STATICCALL
        [gas;Lit 2w;Var p;len;Var q;Lit 32w] [success]) s t tn)
Proof
  rpt gen_tac >> strip_tac >> simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule hash_staticcall_inst_ok >> simp[] >> metis_tac[]) >>
  qabbrev_tac `call = mk_inst ic STATICCALL
    [gas;Lit 2w;Var p;len;Var q;Lit 32w] [success]` >>
  qabbrev_tac `tn1 = step_taint call s t tn` >>
  `step_prov PG G call t = DRESTRICT G (COMPL {success})` by
    (simp[Abbr `call`] >> irule (cj 1 hash_staticcall_ghost) >> metis_tac[]) >>
  `tn1 = tn with <|t_var := tn.t_var |+ (success,{});
     t_mem := tn.t_mem DIFF range_bytes [(w2n r,MIN 32 (LENGTH t.vs_returndata))]|>` by
    (SIMP_TAC (srw_ss()) [Abbr `tn1`, Abbr `call`] >>
     irule (SRULE [] (cj 2 hash_staticcall_ghost)) >> metis_tac[]) >>
  `inst_seq_ptr D 0 ctx fn PG (DRESTRICT G (COMPL {success})) tn1
     [mk_inst ia ASSERT [Var success] []; mk_inst im MLOAD [Var q] [out]]
     (t with vs_inst_idx := SUC s.vs_inst_idx)
     (DRESTRICT G (COMPL {success})) tn1` by
    (irule hash_sha256_assert_abort_check >>
     simp[lookup_var_def, op_taint_def, FLOOKUP_UPDATE] >>
     gvs[lookup_var_def]) >>
  gvs[]
QED
