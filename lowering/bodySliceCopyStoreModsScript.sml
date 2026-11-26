(* The two checked writes in the ordinary Slice memory suffix. *)
Theory bodySliceCopyStoreMods
Ancestors
  exprSimSliceData fragExecPtr
  wordLoadStorePtr decoderGhostFramePtr reasonCopySourcePtr
  instMemFrontier memSafeRun emitHelperProps
  venomExecSemantics venomState venomInst ptrDiscipline

Theorem slice_copy_store_mods:
  emit_void MCOPY [Var dst;Var copy_var;cnt] se = ((),sf) /\
  emit_void MSTORE [Var root;cnt] sf = ((),sb) /\
  lookup_var dst za = SOME (w+32w) /\
  lookup_var copy_var za = SOME (p+n2w i) /\
  lookup_var root za = SOME w /\
  eval_operand cnt za = SOME (n2w k) /\ op_taint tn3 cnt = {} /\
  w2n (w+32w) = w2n w+32 /\ w2n (p+n2w i) = w2n p+i /\
  k < dimword (:256) /\
  ptr_covers G3 tn3 dst za k /\ ptr_covers G3 tn3 copy_var za k /\
  ptr_covers G3 tn3 root za N /\ 32 <= N /\
  w2n p+i+k <= za.vs_alloca_next /\ w2n w+N <= za.vs_alloca_next /\
  32+k <= N /\ (ctx_has_dalloca ctx ==> allocas_below_fmp za) /\
  mem_bytes_at (w2n p) (LENGTH bs) za.vs_memory = bs /\
  i+k <= LENGTH bs /\ (!j. j<k ==> w2n p+i+j NOTIN tn3.t_mem) ==>
  let copy_inst = mk_inst se.cs_next_id MCOPY [Var dst;Var copy_var;cnt] [] in
  let store_inst = mk_inst sf.cs_next_id MSTORE [Var root;cnt] [] in
  let zc = mcopy (w2n w+32) (w2n p+i) k za in
  let zt = mstore (w2n w) (n2w k) zc in
  let tn4 = step_taint copy_inst za zc tn3 in
  let tm = step_taint store_inst zc zt tn4 in
    emitted_insts se sf = [copy_inst] /\ emitted_insts sf sb = [store_inst] /\
    sf.cs_current_insts = se.cs_current_insts ++ [copy_inst] /\
    sb.cs_current_insts = sf.cs_current_insts ++ [store_inst] /\
    step_inst_base copy_inst za = OK zc /\ step_inst_base store_inst zc = OK zt /\
    step_prov PG G3 copy_inst zc = G3 /\ step_prov PG G3 store_inst zt = G3 /\
    (!D fuel. ptr_inst_ok D 0 fuel ctx func G3 tn3 copy_inst za /\
              ptr_inst_ok D 0 fuel ctx func G3 tn4 store_inst zc) /\
    inst_mem_below_frontier copy_inst za /\ inst_mem_below_frontier store_inst zc /\
    (!s. inst_dload_in_section copy_inst s /\ inst_dload_in_section store_inst s) /\
    zc = write_memory_with_expansion (w2n w+32) (TAKE k (DROP i bs)) za /\
    zt = mstore (w2n w) (n2w k)
           (write_memory_with_expansion (w2n w+32) (TAKE k (DROP i bs)) za) /\
    zc.vs_allocas = za.vs_allocas /\ zt.vs_allocas = za.vs_allocas /\
    zc.vs_alloca_next = za.vs_alloca_next /\ zt.vs_alloca_next = za.vs_alloca_next /\
    zc.vs_vars = za.vs_vars /\ zt.vs_vars = za.vs_vars /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp zt) /\
    ptr_covers G3 tn4 root zc N /\ ptr_covers G3 tm root zt N /\
    tn4.t_var = tn3.t_var /\ tn4.t_stor = tn3.t_stor /\
    tn4.t_trans = tn3.t_trans /\ tn4.t_imm = tn3.t_imm /\
    tm.t_var = tn3.t_var /\ tm.t_stor = tn3.t_stor /\
    tm.t_trans = tn3.t_trans /\ tm.t_imm = tn3.t_imm /\
    tn4.t_mem = tn3.t_mem DIFF {j | w2n w+32 <= j /\ j < w2n w+32+k} /\
    tm.t_mem = tn3.t_mem DIFF {j | w2n w+32 <= j /\ j < w2n w+32+k}
                         DIFF {j | w2n w <= j /\ j < w2n w+32} /\
    (!j. w2n w <= j /\ j < w2n w+32+k ==> j NOTIN tm.t_mem)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `copy_inst = mk_inst se.cs_next_id MCOPY [Var dst;Var copy_var;cnt] []` >>
  qabbrev_tac `store_inst = mk_inst sf.cs_next_id MSTORE [Var root;cnt] []` >>
  qabbrev_tac `zc = mcopy (w2n w+32) (w2n p+i) k za` >>
  qabbrev_tac `zt = mstore (w2n w) (n2w k) zc` >>
  qabbrev_tac `tn4 = step_taint copy_inst za zc tn3` >>
  qabbrev_tac `tm = step_taint store_inst zc zt tn4` >>
  `w2n (n2w k : bytes32) = k` by simp[wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD] >>
  `eval_operand (Var dst) za = SOME (w+32w) /\
   eval_operand (Var copy_var) za = SOME (p+n2w i)` by simp[eval_operand_def] >>
  `step_inst_base copy_inst za = OK zc` by
    simp[Abbr `copy_inst`,Abbr `zc`,step_inst_base_opcode_eqs,mk_inst_def] >>
  `step_prov PG G3 copy_inst zc = G3 /\
   tn4.t_var = tn3.t_var /\ tn4.t_stor = tn3.t_stor /\
   tn4.t_trans = tn3.t_trans /\
   tn4.t_mem = tn3.t_mem DIFF {j | w2n w+32 <= j /\ j < w2n w+32+k}` by
    (`{j+(w2n w+32) | j < k /\ i+(j+w2n p) IN tn3.t_mem} = {}` by
       (simp[pred_setTheory.EXTENSION] >>
        qx_gen_tac `j` >> Cases_on `j < k` >> simp[] >>
        `i + (j + w2n p) = w2n p + i + j` by decide_tac >>
        pure_asm_rewrite_tac[] >> first_x_assum irule >> simp[]) >>
     mp_tac (Q.SPECL [`PG`,`G3`,`tn3`,`za`,`se.cs_next_id`,
       `Var dst`,`Var copy_var`,`cnt`,`p+n2w i`,`w+32w`,`n2w k`]
       mcopy_operand_ghost_frame) >>
     simp[Abbr `copy_inst`,Abbr `zc`,Abbr `tn4`]) >>
  `tn4.t_imm = tn3.t_imm` by
    simp[Abbr `tn4`,Abbr `copy_inst`,step_taint_def,imm_taint_def,mk_inst_def] >>
  suspend "store"
QED

Resume slice_copy_store_mods[store]:
  `zc.vs_allocas = za.vs_allocas /\ zc.vs_alloca_next = za.vs_alloca_next /\
   zc.vs_vars = za.vs_vars /\ zc.vs_fmp = za.vs_fmp /\
   zc.vs_labels = za.vs_labels /\ zc.vs_initial_fmp = za.vs_initial_fmp` by
    simp[Abbr `zc`,mcopy_def,write_memory_with_expansion_def] >>
  `zt.vs_allocas = zc.vs_allocas /\ zt.vs_alloca_next = zc.vs_alloca_next /\
   zt.vs_vars = zc.vs_vars /\ zt.vs_fmp = zc.vs_fmp /\
   zt.vs_initial_fmp = zc.vs_initial_fmp` by
    simp[Abbr `zt`,mstore_def] >>
  `eval_operand (Var root) zc = SOME w /\ eval_operand cnt zc = SOME (n2w k) /\
   op_taint tn4 cnt = {}` by
    (Cases_on `cnt` >> gvs[eval_operand_def,lookup_var_def,op_taint_def]) >>
  `step_inst_base store_inst zc = OK zt` by
    simp[Abbr `store_inst`,Abbr `zt`,step_inst_base_opcode_eqs,mk_inst_def,exec_write2_def] >>
  `step_prov PG G3 store_inst zt = G3 /\ tm.t_var = tn4.t_var /\
   tm.t_stor = tn4.t_stor /\ tm.t_trans = tn4.t_trans /\ tm.t_imm = tn4.t_imm` by
    simp[Abbr `store_inst`,Abbr `zt`,Abbr `tm`,ifexp_materialize_mstore_ghost] >>
  `tm.t_mem = tn4.t_mem DIFF {j | w2n w <= j /\ j < w2n w+32}` by
    (simp[Abbr `store_inst`,Abbr `zt`,Abbr `tm`,
          ifexp_materialize_mstore_taint]) >>
  `!j. w2n w <= j /\ j < w2n w+32+k ==> j NOTIN tm.t_mem` by
    (simp[] >> rpt strip_tac >> decide_tac) >>
  `ptr_covers G3 tn4 root zc N` by
    (irule ptr_covers_frame >> qexistsl_tac [`G3`,`za`,`tn3`] >>
     gvs[lookup_var_def,op_taint_def]) >>
  `ptr_covers G3 tm root zt N` by
    (irule ptr_covers_frame >> qexistsl_tac [`G3`,`za`,`tn3`] >>
     gvs[lookup_var_def,op_taint_def]) >>
  `ptr_covers G3 tn4 root zc 32` by
    (irule ptr_covers_mono >> qexists_tac `N` >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp zc` by
    (qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp za` mp_tac >>
     pure_asm_rewrite_tac[allocas_below_fmp_def] >>
     tautLib.TAUT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp zt` by
    (qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp za` mp_tac >>
     pure_asm_rewrite_tac[allocas_below_fmp_def] >>
     tautLib.TAUT_TAC) >>
  suspend "checks"
QED

Resume slice_copy_store_mods[checks]:
  `!D fuel. ptr_inst_ok D 0 fuel ctx func G3 tn3 copy_inst za` by
    (simp[Abbr `copy_inst`] >> rpt gen_tac >> irule ptr_inst_ok_mcopy_operand >>
     simp[]) >>
  `!D fuel. ptr_inst_ok D 0 fuel ctx func G3 tn4 store_inst zc` by
    (simp[Abbr `store_inst`] >> rpt gen_tac >> irule ptr_inst_ok_mstore >> simp[]) >>
  `inst_mem_below_frontier copy_inst za` by
    (simp[Abbr `copy_inst`,below_frontier_MCOPY] >> decide_tac) >>
  `inst_mem_below_frontier store_inst zc` by
    (simp[Abbr `store_inst`,below_frontier_MSTORE] >> decide_tac) >>
  `zc = write_memory_with_expansion (w2n w+32) (TAKE k (DROP i bs)) za` by
    (drule_all_then mp_tac slice_mcopy_payload >> simp[Abbr `zc`]) >>
  `zt = mstore (w2n w) (n2w k)
          (write_memory_with_expansion (w2n w+32) (TAKE k (DROP i bs)) za)` by
    simp[Abbr `zt`] >>
  qpat_assum `emit_void MCOPY _ _ = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
  qpat_assum `emit_void MSTORE _ _ = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
  simp[inst_dload_in_section_def,Abbr `copy_inst`,Abbr `store_inst`,mk_inst_def]
QED

Finalise slice_copy_store_mods
