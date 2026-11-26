(* The covered clean header write at the reached memory Pop cursor. *)
Theory bodyPopHeaderWriteMemoryMods
Ancestors
  augAssignFullMstoreSafety bodyFullAbiEncodeStore exprPtrUnwrapCopyEdges
  wordLoadStorePtr valueEncodingProps ghostPcTransportPtr fragGasSeqPtr
  fragExec emitHelperProps memSafeRun exprLoweringProps
  instMemFrontier allocaHistory allocasBelowFmpUpdatesProps ptrDiscipline bodyPtrDefs
  context instIdxIndep venomExecSemantics venomInst venomState
  words finite_map pred_set list arithmetic

Theorem pop_clean_word_untainted[local]:
  mem_word_taint M off = {} ==>
  !i. off <= i /\ i < off + 32 ==> i NOTIN M
Proof
  simp[mem_word_taint_def, EXTENSION] >> strip_tac >> rpt strip_tac >>
  rename1 `off <= i` >> first_x_assum (qspec_then `i - off` mp_tac) >> simp[]
QED

Theorem pop_mstore_clean_ghost[local]:
  eval_operand dst s = SOME a /\ eval_operand value s = SOME v /\
  op_taint tn value = {} /\ mem_word_taint tn.t_mem (w2n a) = {} ==>
  step_prov PG G (mk_inst j MSTORE [dst;value] []) (mstore (w2n a) v s) = G /\
  step_taint (mk_inst j MSTORE [dst;value] []) s (mstore (w2n a) v s) tn = tn
Proof
  strip_tac >> drule pop_clean_word_untainted >> strip_tac >>
  `tn.t_mem DIFF {q | w2n a <= q /\ q < w2n a + 32} = tn.t_mem` by
    (simp[EXTENSION] >> metis_tac[]) >>
  mp_tac (Q.INST [`id` |-> `j`, `w` |-> `v`] augassign_mstore_clean_transition) >>
  simp[taint_component_equality]
QED

Theorem pop_mstore_seq[local]:
  lookup_var p s = SOME a /\ eval_operand value s = SOME v /\
  ptr_covers G tn p s 32 /\ op_taint tn value = {} /\
  mem_word_taint tn.t_mem (w2n a) = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  !D. inst_seq_ptr D lo ctx func PG G tn [mk_inst j MSTORE [Var p;value] []] s G tn
Proof
  strip_tac >>
  `eval_operand (Var p) s = SOME a` by simp[eval_operand_def] >>
  `step_inst_base (mk_inst j MSTORE [Var p;value] []) s = OK (mstore (w2n a) v s)` by
    (irule step_MSTORE >> simp[]) >>
  `step_prov PG G (mk_inst j MSTORE [Var p;value] []) (mstore (w2n a) v s) = G /\
   step_taint (mk_inst j MSTORE [Var p;value] []) s (mstore (w2n a) v s) tn = tn` by
    (irule pop_mstore_clean_ghost >> simp[]) >>
  simp[inst_seq_ptr_def] >> gen_tac >> irule ptr_inst_ok_mstore_tainted >> simp[]
QED

Theorem pop_header_mstore_mods:
  s5.vs_inst_idx = k + 5 /\ ~s5.vs_halted /\
  lookup_block s5.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb (k + 5) = SOME (mk_inst (id+5) MSTORE [Var p;Var x3] []) /\
  ptr_covers G tn p s5 32 /\ lookup_var p s5 = SOME w /\
  lookup_var x3 s5 = SOME (n - 1w) /\ op_taint tn (Var x3) = {} /\
  mem_word_taint tn.t_mem (w2n w) = {} /\ w2n w + 32 <= s5.vs_alloca_next /\
  allocas_from lo s5 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s5) ==>
  ?q u.
    q = mstore (w2n w) (n - 1w) s5 /\
    run_inst_seq [mk_inst (id+5) MSTORE [Var p;Var x3] []] s5 = OK q /\
    u = q with vs_inst_idx := k + 6 /\
    (!D j. inst_seq_ptr D lo ctx func PG G tn [mk_inst (id+5) MSTORE [Var p;Var x3] []]
              (s5 with vs_inst_idx := j) G tn) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s5,G,tn) [] (OK u,G,tn)) /\
    (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
    u.vs_memory =
      (let off = w2n w; mem = s5.vs_memory in
       let expanded = mem ++ REPLICATE (off + 32 - LENGTH mem) 0w in
       TAKE off expanded ++ word_to_bytes (n - 1w) T ++ DROP (off + 32) expanded) /\
    mem_agree_outside {i | w2n w <= i /\ i < w2n w + 32} u.vs_memory s5.vs_memory /\
    mem_word_at (w2n w) u.vs_memory = n - 1w /\
    u = s5 with <| vs_memory := u.vs_memory; vs_inst_idx := k + 6 |> /\
    (!x. lookup_var x u = lookup_var x s5) /\ ptr_covers G tn p u 32 /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (alloca_history func s5 ==> alloca_history func u)
Proof
  strip_tac >>
  `eval_operand (Var p) s5 = SOME w /\ eval_operand (Var x3) s5 = SOME (n - 1w)` by
    simp[eval_operand_def] >>
  qabbrev_tac `i = mk_inst (id+5) MSTORE [Var p;Var x3] []` >>
  qabbrev_tac `q = mstore (w2n w) (n - 1w) s5` >>
  `step_inst_base i s5 = OK q` by
    (simp[Abbr `i`, Abbr `q`] >> irule step_MSTORE >> simp[]) >>
  `!D j. inst_seq_ptr D lo ctx func PG G tn [i] (s5 with vs_inst_idx := j) G tn` by
    (simp[Abbr `i`] >> rpt gen_tac >> irule pop_mstore_seq >>
     fs[eval_operand_def, lookup_var_def, allocas_below_fmp_updates] >>
     fs[allocas_from_def] >> metis_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s5,G,tn) []
          (OK (q with vs_inst_idx := k + 6),G,tn)` by
    (gen_tac >>
     `step_taint i s5 q tn = tn` by
       (simp[Abbr `i`, Abbr `q`] >> metis_tac[pop_mstore_clean_ghost]) >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s5,G,tn) []
          (OK (q with vs_inst_idx := SUC s5.vs_inst_idx),G,step_taint i s5 q tn)`
       suffices_by simp[ADD1] >>
     simp[NoAsms, Abbr `i`, Abbr `q`] >> irule abi_encode_mstore_origin_path >>
     simp[below_frontier_MSTORE, inst_dload_in_section_def, mk_inst_def] >>
     qexists_tac `bb` >> simp[GSYM mk_inst_def]) >>
  qexistsl_tac [`q`,`q with vs_inst_idx := k + 6`] >>
  simp[run_inst_seq_def] >>
  conj_tac
  >- (drule pop_clean_word_untainted >> simp[]) >>
  simp[Abbr `q`, wordLoadStorePtrTheory.mstore_memory_frame, mstore_mem_word_at_same] >>
  conj_tac
  >- (simp[mstore_def] >> IF_CASES_TAC >> simp[] >>
      `w2n w + 32 - LENGTH s5.vs_memory = 0` by decide_tac >> simp[]) >>
  simp[allocas_below_fmp_updates] >>
  fs[mstore_def, ptr_covers_def, lookup_var_def, allocas_from_def] >>
  conj_tac >- metis_tac[] >>
  simp[alloca_history_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `get_instruction _ j = SOME inst` >>
  Cases_on `j < k + 5` >- metis_tac[] >>
  `j = k + 5` by decide_tac >> gvs[Abbr `i`, mk_inst_def]
QED
