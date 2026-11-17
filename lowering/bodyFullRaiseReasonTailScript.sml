(* Joint execution of the Error(string) encoding tail. *)
Theory bodyFullRaiseReasonTail
Ancestors
  stmtReasonMemory revertReasonLayout revertReasonCopyPtr
  revertReasonSuffixPathPtr fragGasSeqPtr fragGasEmitCtrl
  fragGasOriginPtrLoop instSeqPtrLo instSeqComposePtr
  bodyPtrDefs venomInst venomState list rich_list arithmetic
  exprLoweringProps fragExecMem opcodeClass bodyPtrPrecompileBuiltinsSeq
  finalAbortSeqPtr bodyPtrHashBuiltinsShaAlloc bodyPtrHashBuiltinsCursor
Libs
  BasicProvers

Theorem reason_tail_chunks:
  reason_tail j u v op =
    revert_reason_copy j u (Var ("%" ++ toString (v+2))) op ++
    revert_reason_suffix (j+1) (u+1)
      (Var ("%" ++ toString v)) (Var ("%" ++ toString (v+1)))
      (Var ("%" ++ toString (v+2)))
Proof
  simp[reason_tail_def, revert_reason_copy_def, revert_reason_suffix_def,
       ADD_ASSOC]
QED

Theorem reason_tail_ops:
  LENGTH (reason_tail j u v op) = 30 /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
    ~is_terminator i.inst_opcode) (TAKE 29 (reason_tail j u v op)) /\
  EL 29 (reason_tail j u v op) =
    mk_inst (j+29) REVERT
      [Var ("%" ++ toString (u+21)); Var ("%" ++ toString (u+22))] []
Proof
  simp[reason_tail_def, mk_inst_def, is_terminator_def]
QED

(* The first six instructions share their run with the memory certificate.
   Keep the pointer frame needed at the suffix entrance. *)
Theorem reason_tail_copy_origin_ptr_path:
  lookup_var ("%" ++ toString (v+2)) s = SOME b /\
  lookup_var src s = SOME a /\ mload (w2n a) s = n2w L /\
  ptr_covers G tn src s (32+contractABI$ceil32 L) /\
  ptr_covers G tn ("%" ++ toString (v+2)) s (32+contractABI$ceil32 L) /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  (!k. k < 5 ==> src <> "%" ++ toString (u+k) /\
    "%" ++ toString (v+2) <> "%" ++ toString (u+k)) /\
  L+63 < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (TAKE 6 (reason_tail j u v (Var src)))
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq_mem_ok (TAKE 6 (reason_tail j u v (Var src))) s /\
  run_inst_seq (TAKE 6 (reason_tail j u v (Var src))) s = OK t /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?Gf tnf.
    (!D. inst_seq_ptr D lo ctx func PG G tn
      (TAKE 6 (reason_tail j u v (Var src))) s Gf tnf /\
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := s.vs_inst_idx+6),Gf,tnf)) /\
    mload (w2n b) t = n2w L /\
    (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tnf.t_mem) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!x C. (!k. k < 5 ==> x <> "%" ++ toString (u+k)) /\
      ptr_covers G tn x s C ==>
      lookup_var x (t with vs_inst_idx := s.vs_inst_idx+6) = lookup_var x s /\
      ptr_covers Gf tnf x (t with vs_inst_idx := s.vs_inst_idx+6) C)
Proof
  strip_tac >>
  `TAKE 6 (reason_tail j u v (Var src)) =
    revert_reason_copy j u (Var ("%" ++ toString (v+2))) (Var src)` by
    simp[reason_tail_def, revert_reason_copy_def] >>
  fs[] >>
  `?Gf tnf. inst_seq_ptr ARB 0 ctx func PG G tn
    (revert_reason_copy j u (Var ("%" ++ toString (v+2))) (Var src)) s Gf tnf /\
    (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tnf.t_mem)` by
    (irule revert_reason_copy_checks >> simp[ADD_COMM] >>
     qexists_tac `L` >> simp[ADD_COMM]) >>
  `!D. inst_seq_ptr D 0 ctx func PG G tn
    (revert_reason_copy j u (Var ("%" ++ toString (v+2))) (Var src)) s Gf tnf` by
    (gen_tac >>
     `?gf tf. inst_seq_ptr D 0 ctx func PG G tn
       (revert_reason_copy j u (Var ("%" ++ toString (v+2))) (Var src)) s gf tf /\
       (!i. w2n b <= i /\ i < w2n b+32 ==> i NOTIN tf.t_mem)` by
       (irule revert_reason_copy_checks >> simp[ADD_COMM] >>
        qexists_tac `L` >> simp[ADD_COMM]) >>
     metis_tac[inst_seq_ptr_ghost_unique]) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn
    (revert_reason_copy j u (Var ("%" ++ toString (v+2))) (Var src)) s Gf tnf` by
    (gen_tac >> irule inst_seq_ptr_zero_to_lo >> simp[] >>
     qexists_tac `D` >> simp[]) >>
  qexistsl_tac [`Gf`,`tnf`] >> conj_tac
  >- (gen_tac >> simp[] >>
      `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (revert_reason_copy j u (Var ("%" ++ toString (v+2))) (Var src))` by
        simp[revert_reason_copy_def, mk_inst_def, is_terminator_def] >>
      first_assum (qspec_then `D` assume_tac) >> fs[] >>
      drule_all run_inst_seq_gas_origin_ptr_path >>
      simp[revert_reason_copy_def, mk_inst_def]) >>
  `mload (w2n b) t = n2w L` by
    (irule revert_reason_copy_mload >> simp[ADD_COMM] >>
     goal_assum (drule_at (Pat `run_inst_seq _ _ = _`)) >>
     simp[ADD_COMM]) >>
  drule revert_reason_copy_allocation_frame >> strip_tac >> simp[] >>
  rpt strip_tac >> fs[] >>
  qpat_assum `!D. inst_seq_ptr D lo _ _ _ _ _ _ _ _ _`
    (qspec_then `ARB` assume_tac) >>
  drule_all (SRULE [ADD_COMM] revert_reason_copy_live_pointer_frame) >>
  simp[lookup_var_def, ptr_covers_def, eval_operand_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem reason_tail_run_mem_split:
  run_inst_seq (reason_tail j u v op) s = Abort Revert_abort z /\
  run_inst_seq_mem_ok (reason_tail j u v op) s ==>
  ?s6 s29.
    run_inst_seq (TAKE 6 (reason_tail j u v op)) s = OK s6 /\
    run_inst_seq (TAKE 23 (DROP 6 (reason_tail j u v op))) s6 = OK s29 /\
    run_inst_seq (TAKE 29 (reason_tail j u v op)) s = OK s29 /\
    step_inst_base (EL 29 (reason_tail j u v op)) s29 = Abort Revert_abort z /\
    run_inst_seq_mem_ok (TAKE 6 (reason_tail j u v op)) s /\
    run_inst_seq_mem_ok (DROP 6 (reason_tail j u v op)) s6 /\
    run_inst_seq_mem_ok (TAKE 29 (reason_tail j u v op)) s /\
    run_inst_seq_mem_ok [EL 29 (reason_tail j u v op)] s29 /\
    run_inst_seq (DROP 6 (reason_tail j u v op)) s6 = Abort Revert_abort z
Proof
  strip_tac >>
  fs[reason_tail_def] >>
  ntac 6
    (qpat_x_assum `run_inst_seq (_::_) _ = Abort Revert_abort _`
       (mp_tac o PURE_ONCE_REWRITE_RULE [run_inst_seq_def]) >>
     reverse TOP_CASE_TAC >> simp[]
     >- (drule step_inst_base_abort_opcodes >> simp[mk_inst_def]) >>
     strip_tac) >>
  rename1 `run_inst_seq _ s6 = Abort Revert_abort z` >>
  ntac 6
    (qpat_x_assum `run_inst_seq (_::_) _ = Abort Revert_abort _`
       (mp_tac o PURE_ONCE_REWRITE_RULE [run_inst_seq_def]) >>
     reverse TOP_CASE_TAC >> simp[]
     >- (drule step_inst_base_abort_opcodes >> simp[mk_inst_def]) >>
     strip_tac) >>
  ntac 6
    (qpat_x_assum `run_inst_seq (_::_) _ = Abort Revert_abort _`
       (mp_tac o PURE_ONCE_REWRITE_RULE [run_inst_seq_def]) >>
     reverse TOP_CASE_TAC >> simp[]
     >- (drule step_inst_base_abort_opcodes >> simp[mk_inst_def]) >>
     strip_tac) >>
  ntac 6
    (qpat_x_assum `run_inst_seq (_::_) _ = Abort Revert_abort _`
       (mp_tac o PURE_ONCE_REWRITE_RULE [run_inst_seq_def]) >>
     reverse TOP_CASE_TAC >> simp[]
     >- (drule step_inst_base_abort_opcodes >> simp[mk_inst_def]) >>
     strip_tac) >>
  ntac 5
    (qpat_x_assum `run_inst_seq (_::_) _ = Abort Revert_abort _`
       (mp_tac o PURE_ONCE_REWRITE_RULE [run_inst_seq_def]) >>
     reverse TOP_CASE_TAC >> simp[]
     >- (drule step_inst_base_abort_opcodes >> simp[mk_inst_def]) >>
     strip_tac) >>
  rename1 `run_inst_seq _ s29 = Abort Revert_abort z` >>
  qexistsl_tac [`s6`, `s29`] >>
  qpat_x_assum `run_inst_seq [_] _ = _` mp_tac >>
  simp[run_inst_seq_def] >>
  reverse TOP_CASE_TAC >> gvs[] >> strip_tac >>
  qpat_x_assum `run_inst_seq_mem_ok _ _` mp_tac >>
  asm_simp_tac std_ss [run_inst_seq_def, run_inst_seq_mem_ok_def,
    venomExecSemanticsTheory.exec_result_case_def] >>
  strip_tac >> asm_simp_tac std_ss []
QED

Theorem reason_tail_checked_origin_ptr_path:
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (reason_tail j u v op) (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (TAKE 29 (reason_tail j u v op)) s = OK t /\
  step_inst_base (EL 29 (reason_tail j u v op)) t = Abort Revert_abort z /\
  run_inst_seq_mem_ok (reason_tail j u v op) s /\
  (!D. inst_seq_ptr D lo ctx func PG G tn (reason_tail j u v op) s Gf tnf) ==>
  ?z'. !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (Abort Revert_abort z',Gf,tnf)
Proof
  strip_tac >>
  qabbrev_tac `pre = TAKE 29 (reason_tail j u v op)` >>
  qabbrev_tac `last = EL 29 (reason_tail j u v op)` >>
  `reason_tail j u v op = pre ++ [last]` by
    simp[Abbr `pre`, Abbr `last`, reason_tail_def] >>
  `LENGTH pre = 29 /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
     ~is_terminator i.inst_opcode) pre /\
   last.inst_opcode = REVERT` by
    simp[Abbr `pre`, Abbr `last`, reason_tail_def, mk_inst_def, is_terminator_def] >>
  `run_inst_seq (reason_tail j u v op) s = Abort Revert_abort z` by
    (asm_rewrite_tac[] >> drule run_inst_seq_append >>
     disch_then (qspec_then `[last]` mp_tac) >> simp[run_inst_seq_def]) >>
  drule_all reason_tail_run_mem_split >> strip_tac >>
  `run_inst_seq pre s = OK s29` by fs[Abbr `pre`] >>
  gvs[] >> rename1 `run_inst_seq pre s = OK t` >>
  `isPREFIX pre (DROP s.vs_inst_idx bb.bb_instructions) /\
   isPREFIX [last] (DROP (s.vs_inst_idx+29) bb.bb_instructions)` by
    (drule bodyPtrHashBuiltinsShaAllocTheory.hash_code_prefix_split >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre` by
    fs[EVERY_MEM] >>
  `~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb` by
    (drule_all fragExecTheory.run_inst_seq_preserves_halted >>
     drule_all bodyPtrHashBuiltinsCursorTheory.hash_run_inst_seq_current_bb >> simp[]) >>
  drule finalAbortSeqPtrTheory.step_inst_base_abort_cursor >>
  disch_then (qspec_then `s.vs_inst_idx+29` strip_assume_tac) >>
  qexists_tac `z with vs_inst_idx := k` >> gen_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) pre` by fs[EVERY_MEM] >>
  `?G1 tn1. inst_seq_ptr D lo ctx func PG G tn pre s G1 tn1 /\
    inst_seq_ptr D lo ctx func PG G1 tn1 [last]
      (t with vs_inst_idx := s.vs_inst_idx+29) Gf tnf` by
    (drule_all bodyPtrPrecompileBuiltinsSeqTheory.inst_seq_ptr_append >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ [last] _ _ _` mp_tac >>
  simp[inst_seq_ptr_def] >> strip_tac >> gvs[] >>
  rename1 `inst_seq_ptr D lo ctx func PG G tn pre s Gf tnf` >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := s.vs_inst_idx+29),Gf,tnf)` by
    (drule_all run_inst_seq_gas_origin_ptr_path >>
     `FILTER (\i. i.inst_opcode = GAS) pre = []` by
       (simp[listTheory.FILTER_EQ_NIL] >> fs[EVERY_MEM]) >> simp[]) >>
  irule gas_origin_ptr_path_trans >>
  goal_assum (drule_at Any) >>
  irule exit_inst_origin_ptr >> simp[fragExecTheory.exit_result_def] >>
  qexists_tac `last` >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke,
       gasCountTheory.gas_count_step_def, gasEventsTheory.gas_events_defs,
       memSafeRunTheory.mem_safe_step_non_invoke] >>
  reverse conj_tac
  >- fs[run_inst_seq_mem_ok_last] >>
  `isPREFIX (last::[]) (DROP (s.vs_inst_idx+29) bb.bb_instructions)` by fs[] >>
  drule fragGasSeqAbortTheory.instruction_prefix_cursor >> simp[]
QED

Theorem reason_tail_suffix_primitive_checks:
  v+2 < u /\
  lookup_var ("%" ++ toString v) r = SOME (n2w B) /\
  lookup_var ("%" ++ toString (v+1)) r = SOME (n2w (B+32)) /\
  lookup_var ("%" ++ toString (v+2)) r = SOME (n2w TP) /\
  ptr_covers G tn ("%" ++ toString v) r (64+M) /\
  ptr_covers G tn ("%" ++ toString (v+1)) r (32+M) /\
  ptr_covers G tn ("%" ++ toString (v+2)) r M /\
  mload TP r = n2w L /\
  (!i. TP <= i /\ i < TP+32 ==> i NOTIN tn.t_mem) /\
  32+contractABI$ceil32 L <= M /\
  B+64+M <= r.vs_alloca_next /\ TP+M <= r.vs_alloca_next /\
  r.vs_alloca_next < dimword(:256) /\ L+63 < dimword(:256) /\
  ~ctx_has_dalloca ctx /\
  (FLOOKUP r.vs_allocas (j+6) = NONE ==>
    r.vs_alloca_next+32 < dimword(:256)) /\
  (!a sz. FLOOKUP r.vs_allocas (j+6) = SOME (a,sz) ==>
    sz=32 /\ a+32 <= r.vs_alloca_next /\ (a+32 <= TP \/ TP+32 <= a)) /\
  run_inst_seq (TAKE 23 (DROP 6 (reason_tail j u v (Var src)))) r = OK t ==>
  ?gf tf. !D. inst_seq_ptr D 0 ctx func PG G tn
    (DROP 6 (reason_tail j u v (Var src))) r gf tf
Proof
  strip_tac >>
  `?sa c. step_inst_base (mk_inst (j+6) ALLOCA [Lit 32w]
      ["%" ++ toString (u+5)]) r = OK sa /\
    FLOOKUP sa.vs_allocas (j+6) = SOME (c,32) /\
    (TP+32 <= c \/ c+32 <= TP)` by
    (Cases_on `FLOOKUP r.vs_allocas (j+6)`
     >- (`r.vs_alloca_next+32 < dimword(:256)` by metis_tac[] >>
         qexistsl_tac [`update_var ("%" ++ toString (u+5))
           (n2w r.vs_alloca_next) (r with <|vs_allocas :=
             r.vs_allocas |+ (j+6,(r.vs_alloca_next,32));
             vs_alloca_next := r.vs_alloca_next+32|>)`,
           `r.vs_alloca_next`] >>
         conj_tac
         >- (mp_tac (actualAllocExecTheory.physical_word_alloca_fresh_run |>
               Q.INST [`inst` |-> `mk_inst (j+6) ALLOCA [Lit 32w]
                 ["%" ++ toString ((u:num)+5)]`, `s` |-> `r`,
                 `out` |-> `"%" ++ toString ((u:num)+5)`]) >>
             simp[NoAsms, mk_inst_def] >>
             disch_then irule >> metis_tac[]) >>
         simp[NoAsms, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> decide_tac) >>
     rename1 `FLOOKUP r.vs_allocas (j+6) = SOME entry` >>
     PairCases_on `entry` >>
     `entry1=32 /\ entry0+32 <= r.vs_alloca_next /\
       (entry0+32 <= TP \/ TP+32 <= entry0)` by metis_tac[] >>
     `?sa. step_inst_base (mk_inst (j+6) ALLOCA [Lit 32w]
       ["%" ++ toString (u+5)]) r = OK sa /\
       sa.vs_allocas = r.vs_allocas` by
       (mp_tac (actualAllocExecTheory.actual_word_alloca_reuse_run |>
          Q.INST [`inst` |-> `mk_inst (j+6) ALLOCA [Lit 32w]
            ["%" ++ toString ((u:num)+5)]`, `s` |-> `r`,
            `out` |-> `"%" ++ toString ((u:num)+5)`, `p` |-> `entry0`]) >>
        simp[NoAsms, mk_inst_def] >>
        impl_tac >- metis_tac[] >>
        strip_tac >> qexists_tac `update_var ("%" ++ toString (u+5)) (n2w entry0) r` >>
        simp[NoAsms, mk_inst_def, update_var_def] >>
        metis_tac[update_var_def]) >>
     qexistsl_tac [`sa`,`entry0`] >> metis_tac[]) >>
  `B < dimword(:256) /\ B+32 < dimword(:256) /\
   TP < dimword(:256) /\
   64+M < dimword(:256) /\ B+64+M < dimword(:256)` by decide_tac >>
  `w2n (n2w B : bytes32) = B /\
   w2n (n2w TP : bytes32) = TP /\
   w2n (n2w (B+32) : bytes32) = B+32` by
    (pure_rewrite_tac[wordsTheory.w2n_n2w] >> metis_tac[LESS_MOD]) >>
  `DROP 6 (reason_tail j u v (Var src)) =
    revert_reason_suffix (j+1) (u+1) (Var ("%" ++ toString v))
      (Var ("%" ++ toString (v+1))) (Var ("%" ++ toString (v+2)))` by
    simp[NoAsms, reason_tail_def, revert_reason_suffix_def, ADD_ASSOC] >>
  `!D. ?gf tf. inst_seq_ptr D 0 ctx func PG G tn
    (DROP 6 (reason_tail j u v (Var src))) r gf tf` by
    (gen_tac >> pure_asm_rewrite_tac[] >>
     irule revert_reason_suffix_checks >>
     pure_rewrite_tac[GSYM ADD_ASSOC, EVAL ``1+5:num``, EVAL ``1+4:num``] >>
     conj_tac >- metis_tac[LESS_EQ_LESS_TRANS] >>
     conj_tac >- (rpt gen_tac >> strip_tac >>
       simp[NoAsms, ASCIInumbersTheory.toString_inj] >> decide_tac) >>
     conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`n2w B`,`L`,`n2w (B+32)`,`n2w TP`,`c`,`M`,`sa`] >>
     pure_asm_rewrite_tac[] >> simp[NoAsms] >> conj_tac >- decide_tac >> conj_tac >- decide_tac >>
     qpat_x_assum `step_inst_base (mk_inst _ ALLOCA _ _) r = OK sa` mp_tac >>
     simp[NoAsms]) >>
  qpat_assum `!D. ?gf tf. inst_seq_ptr D 0 _ _ _ _ _ _ _ _ _`
    (qspec_then `ARB` strip_assume_tac) >>
  qexistsl_tac [`gf`,`tf`] >> metis_tac[inst_seq_ptr_ghost_unique]
QED

Theorem reason_tail_origin_ptr_path:
  v+2 < u /\
  (!k. src <> "%" ++ toString (u+k)) /\
  lookup_var src s = SOME (n2w p) /\
  lookup_var ("%" ++ toString v) s = SOME (n2w B) /\
  lookup_var ("%" ++ toString (v+1)) s = SOME (n2w (B+32)) /\
  lookup_var ("%" ++ toString (v+2)) s = SOME (n2w TP) /\
  mload p s = n2w L /\
  32+contractABI$ceil32 L <= M /\
  p+32+contractABI$ceil32 L <= s.vs_alloca_next /\
  B+64+M <= s.vs_alloca_next /\ TP+M <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword(:256) /\ L+63 < dimword(:256) /\
  (FLOOKUP s.vs_allocas (j+6) = NONE ==>
    s.vs_alloca_next+32 < dimword(:256)) /\
  (!a sz. FLOOKUP s.vs_allocas (j+6) = SOME (a,sz) ==>
    sz=32 /\ a+32 <= s.vs_alloca_next /\ (a+32 <= TP \/ TP+32 <= a)) /\
  ptr_covers G tn src s (32+contractABI$ceil32 L) /\
  ptr_covers G tn ("%" ++ toString v) s (64+M) /\
  ptr_covers G tn ("%" ++ toString (v+1)) s (32+M) /\
  ptr_covers G tn ("%" ++ toString (v+2)) s M /\
  (!i. p <= i /\ i < p+32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (reason_tail j u v (Var src)) (DROP s.vs_inst_idx bb.bb_instructions) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?z Gf tnf. !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (Abort Revert_abort z,Gf,tnf)
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (reason_tail j u v (Var src)) s /\
   ?z. run_inst_seq (reason_tail j u v (Var src)) s = Abort Revert_abort z` by
    (irule reason_tail_run_mem >>
     conj_tac >- metis_tac[operand_11] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`B`,`M`,`TP`,`L`,`p`] >>
     conj_tac >- metis_tac[] >>
     pure_rewrite_tac[GSYM (SRULE [MULT_COMM] contractABITheory.ceil32_def), eval_operand_def] >>
     rule_assum_tac (PURE_REWRITE_RULE [contractABITheory.ceil32_def]) >>
     rpt conj_tac >> metis_tac[MULT_COMM]) >>
  drule_all reason_tail_run_mem_split >> strip_tac >>
  suspend "copy"
QED

Resume reason_tail_origin_ptr_path[copy]:
  `p < dimword(:256) /\ TP < dimword(:256)` by decide_tac >>
  `w2n (n2w p : bytes32) = p /\ w2n (n2w TP : bytes32) = TP` by
    (pure_rewrite_tac[wordsTheory.w2n_n2w] >> metis_tac[LESS_MOD]) >>
  `ptr_covers G tn ("%" ++ toString (v+2)) s (32+contractABI$ceil32 L)` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >>
     qexists_tac `M` >> metis_tac[]) >>
  `!k. k < 5 ==> src <> "%" ++ toString (u+k) /\
    "%" ++ toString (v+2) <> "%" ++ toString (u+k)` by
    (rpt strip_tac >- metis_tac[] >>
     qpat_x_assum `STRCAT _ _ = STRCAT _ _` mp_tac >>
     simp[NoAsms, ASCIInumbersTheory.toString_inj] >> decide_tac) >>
  `isPREFIX (TAKE 6 (reason_tail j u v (Var src)))
    (DROP s.vs_inst_idx bb.bb_instructions)` by
    metis_tac[rich_listTheory.IS_PREFIX_APPEND, TAKE_DROP, APPEND_ASSOC] >>
  `mload (w2n (n2w p : bytes32)) s = n2w L /\
   (!i. w2n (n2w p : bytes32) <= i /\ i < w2n (n2w p : bytes32)+32 ==> i NOTIN tn.t_mem)` by
    metis_tac[] >>
  drule_all reason_tail_copy_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  suspend "suffix"
QED

Resume reason_tail_origin_ptr_path[suffix]:
  `!k. k < 5 ==> "%" ++ toString v <> "%" ++ toString (u+k) /\
    "%" ++ toString (v+1) <> "%" ++ toString (u+k) /\
    "%" ++ toString (v+2) <> "%" ++ toString (u+k)` by
    (rpt gen_tac >> strip_tac >>
     simp[NoAsms, ASCIInumbersTheory.toString_inj] >> decide_tac) >>
  `lookup_var ("%" ++ toString v) s6 = SOME (n2w B) /\
   lookup_var ("%" ++ toString (v+1)) s6 = SOME (n2w (B+32)) /\
   lookup_var ("%" ++ toString (v+2)) s6 = SOME (n2w TP) /\
   ptr_covers Gf tnf ("%" ++ toString v) s6 (64+M) /\
   ptr_covers Gf tnf ("%" ++ toString (v+1)) s6 (32+M) /\
   ptr_covers Gf tnf ("%" ++ toString (v+2)) s6 M` by
    (qpat_assum `!x C. _ ==> _`
       (qspecl_then [`"%" ++ toString v`,`64+M`] mp_tac) >>
     impl_tac >- metis_tac[] >> strip_tac >>
     qpat_assum `!x C. _ ==> _`
       (qspecl_then [`"%" ++ toString (v+1)`,`32+M`] mp_tac) >>
     impl_tac >- metis_tac[] >> strip_tac >>
     qpat_assum `!x C. _ ==> _`
       (qspecl_then [`"%" ++ toString (v+2)`,`M`] mp_tac) >>
     impl_tac >- metis_tac[] >> strip_tac >>
     rule_assum_tac (PURE_REWRITE_RULE
       [ghostPcTransportPtrTheory.ptr_covers_inst_idx,
        blockPrefixEquivTheory.lookup_var_set_inst_idx]) >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
     (TAKE 23 (DROP 6 (reason_tail j u v (Var src))))` by
    simp[NoAsms, reason_tail_def, is_terminator_def, mk_inst_def] >>
  `run_inst_seq (TAKE 23 (DROP 6 (reason_tail j u v (Var src))))
    (s6 with vs_inst_idx := s.vs_inst_idx+6) =
    OK (s29 with vs_inst_idx := s.vs_inst_idx+6)` by
    metis_tac[fragExecTheory.run_inst_seq_inst_idx, instIdxIndepTheory.exec_result_map_def] >>
  `?gf tf. !D. inst_seq_ptr D 0 ctx func PG Gf tnf
    (DROP 6 (reason_tail j u v (Var src)))
    (s6 with vs_inst_idx := s.vs_inst_idx+6) gf tf` by
    (irule reason_tail_suffix_primitive_checks >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- metis_tac[] >>
     conj_tac >- simp[] >>
     qexistsl_tac [`B`,`L`,`M`,`TP`] >>
     pure_rewrite_tac[ghostPcTransportPtrTheory.ptr_covers_inst_idx,
          blockPrefixEquivTheory.lookup_var_set_inst_idx,
          abiEncoderPathPropsTheory.mload_inst_idx,
          venomStateTheory.venom_state_accfupds] >> metis_tac[]) >>
  `allocas_from lo s6 /\ lo <= s6.vs_alloca_next` by
    (pure_asm_rewrite_tac[ptrDisciplineTheory.allocas_from_def] >>
     qpat_x_assum `allocas_from lo s` mp_tac >>
     pure_rewrite_tac[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
  `!D. inst_seq_ptr D lo ctx func PG Gf tnf
    (DROP 6 (reason_tail j u v (Var src)))
    (s6 with vs_inst_idx := s.vs_inst_idx+6) gf tf` by
    (gen_tac >> irule (instSeqPtrLoTheory.inst_seq_ptr_zero_to_lo |> Q.SPEC `DROP 6 (reason_tail j u v (Var src))` |> Q.SPEC `D`) >>
     pure_rewrite_tac[venomStateTheory.venom_state_accfupds,
       ptrDisciplineTheory.allocas_from_def] >>
     metis_tac[ptrDisciplineTheory.allocas_from_def, pred_setTheory.SUBSET_REFL]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    (TAKE 6 (reason_tail j u v (Var src))) /\
    LENGTH (TAKE 6 (reason_tail j u v (Var src))) = 6` by
    simp[NoAsms, reason_tail_def, is_terminator_def, mk_inst_def] >>
  `!D. inst_seq_ptr D lo ctx func PG G tn
    (reason_tail j u v (Var src)) s gf tf` by
    (gen_tac >>
     GEN_REWRITE_TAC (funpow 3 RATOR_CONV o RAND_CONV) empty_rewrites
       [GSYM (Q.SPEC `6` listTheory.TAKE_DROP)] >>
     irule instSeqComposePtrTheory.inst_seq_ptr_append_ok >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`Gf`,`s6`,`tnf`] >> metis_tac[]) >>
  drule_all reason_tail_checked_origin_ptr_path >>
  disch_then (qspec_then `explicit` strip_assume_tac) >>
  qexistsl_tac [`z'`,`gf`,`tf`] >> first_assum ACCEPT_TAC
QED

Finalise reason_tail_origin_ptr_path
