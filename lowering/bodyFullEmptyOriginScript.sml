Theory bodyFullEmptyOrigin
Ancestors
  bodyPtrTypeBuiltinsEmptyTail bodyPtrTypeBuiltinsEmptyAlloc
  bodyEmptyBufferMemory bodyFullUnwrapRun instSeqPtrLo bodyFullAllocGeneric
  exprSimBufferEmptyExec exprSimAlloc fragGasSeqPtr ptrDiscipline
  venomState finite_map words list pred_set abiEmptyAllocate abiEmptySequence
  bodyPtrIfExpAllocCompiler emitHelperProps exprLoweringProps compileEnv
  fragExec rich_list loweringHalt instIdxIndep fragExecPtr venomInst
  entrySinkExtraction

(* The tail's physical and ghost endpoint is fixed before its check mask
   or reserved prefix is chosen.  This is an instruction certificate, not
   a transport of an expression simulation judgment. *)
Theorem empty_buffer_tail_effects:
  !header sz sa sb s G tn p w ctx func PG.
    (if header then emit_void MSTORE [Var p; Lit 0w]
     else compile_zero_words (Var p) ((sz+31) DIV 32)) sa = ((),sb) /\
    not_fresh_at sa p /\ lookup_var p s = SOME w /\
    ptr_covers G tn p s sz /\ w2n w+sz < dimword (:256) /\
    (if header then 32 <= sz else sz MOD 32 = 0) /\ ~ctx_has_dalloca ctx ==>
    ?t Gf tnf. run_inst_seq (emitted_insts sa sb) s = OK t /\
      (!D lo. allocas_from lo s /\ lo <= s.vs_alloca_next ==>
        inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tnf) /\
      lookup_var p t = SOME w /\ ptr_covers Gf tnf p t sz /\
      tnf.t_mem = tn.t_mem DIFF
        {a | w2n w <= a /\ a < w2n w+(if header then 32 else sz)} /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
      (!q. not_fresh_at sa q ==> lookup_var q t = lookup_var q s /\
        FLOOKUP Gf q = FLOOKUP G q /\ op_taint tnf (Var q) = op_taint tn (Var q)) /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s
Proof
  rpt gen_tac >> strip_tac >>
  drule_all empty_buffer_tail_certificate >>
  disch_then (qspecl_then [`ARB`, `func`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`t`, `H`, `th`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lookup_var p t = SOME w` kall_tac >>
  qpat_x_assum `ptr_covers H th p t sz` kall_tac >>
  drule_all empty_buffer_tail_certificate >>
  disch_then (qspecl_then [`D`, `func`, `PG`] strip_assume_tac) >>
  `H' = H /\ th' = th` by metis_tac[inst_seq_ptr_ghost_unique] >>
  gvs[] >> irule inst_seq_ptr_zero_to_lo >> simp[] >>
  qexists_tac `D` >> simp[]
QED


Theorem empty_buffer_origin_run:
  !sz header sa sb buf func cenv cx es s t ctx PG G tn.
    compile_builtin_empty_complex sz header sa = (buf,sb) /\
    fn_has_code sa sb func /\
    stmt_state_rel (H : (bool # bytes32 # type_value) list # num list)
      ctx func cenv cx es s /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    sz < dimword (:256) /\
    (if header then 32 <= sz else sz MOD 32 = 0) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    ?p w Gf tnf. buf.buf_operand = Var p /\ lookup_var p t = SOME w /\
      ptr_covers Gf tnf p t sz /\
      (!a. w2n w <= a /\ a < w2n w+(if header then 32 else sz) ==>
        a NOTIN tnf.t_mem) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      s.vs_alloca_next <= t.vs_alloca_next /\
      (!D lo explicit. allocas_from lo s /\ lo <= s.vs_alloca_next ==>
        gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
          (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all empty_buffer_compile_prefix >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (irule buffer_alloc_code >> goal_assum drule >> simp[]) >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  drule_all empty_alloc_checked_coverage >>
  disch_then (qspecl_then [`ARB`, `PG`, `G`, `tn`] strip_assume_tac) >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) s = OK u` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  `lookup_var p u = SOME w` by gvs[eval_operand_def] >>
  `?v K tk. run_inst_seq (emitted_insts sm sb)
      (u with vs_inst_idx := SUC s.vs_inst_idx) = OK v /\
    (!D lo. allocas_from lo (u with vs_inst_idx := SUC s.vs_inst_idx) /\
      lo <= u.vs_alloca_next ==>
      inst_seq_ptr D lo ctx func PG G' tn' (emitted_insts sm sb)
        (u with vs_inst_idx := SUC s.vs_inst_idx) K tk) /\
    lookup_var p v = SOME w /\ ptr_covers K tk p v sz /\
    tk.t_mem = tn'.t_mem DIFF
      {a | w2n w <= a /\ a < w2n w+(if header then 32 else sz)}` by
    suspend "tail" >>
  drule compile_builtin_empty_complex_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (fs[EVERY_MEM] >> metis_tac[MEM]) >>
  `run_inst_seq (emitted_insts sm sb) u = OK t` by
    gvs[run_inst_seq_def] >>
  `v = t with vs_inst_idx := SUC s.vs_inst_idx` by
    (drule run_inst_seq_inst_idx >>
     disch_then (qspecl_then [`u`, `SUC s.vs_inst_idx`] mp_tac) >>
     gvs[run_inst_seq_def, exec_result_map_def]) >>
  rename1 `ptr_covers finalG tk p v sz` >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by
    (gvs[EVERY_MEM, mk_inst_def] >> metis_tac[MEM]) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  qpat_x_assum `stmt_state_rel H ctx func cenv cx es u` kall_tac >>
  drule_all compile_empty_buffer_seq_mem >> strip_tac >>
  qexistsl_tac [`p`, `w`, `finalG`, `tk`] >>
  gvs[lookup_var_def] >>
  rpt gen_tac >> strip_tac >> suspend "path"
QED
Resume empty_buffer_origin_run[tail]:
  gvs[] >>
  `lookup_var p (u with vs_inst_idx := SUC s.vs_inst_idx) = SOME w` by
    fs[lookup_var_def] >>
  `ptr_covers G' tn' p (u with vs_inst_idx := SUC s.vs_inst_idx) sz` by simp[] >>
  qpat_x_assum `lookup_var p u = _` kall_tac >>
  qpat_x_assum `ptr_covers G' tn' p u sz` kall_tac >>
  `w2n w+sz < dimword (:256)` by decide_tac >>
  drule_all empty_buffer_tail_effects >>
  disch_then (qspecl_then [`func`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`t'`, `Gf`, `tnf`] >> gvs[]
QED
Resume empty_buffer_origin_run[path]:
  `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s finalG tk` by
    (qpat_x_assum `inst_seq_ptr ARB 0 _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[inst_seq_ptr_def, ptr_inst_ok_alloca] >> strip_tac >> gvs[] >>
     first_x_assum irule >> simp[allocas_from_def]) >>
  `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s finalG tk` by
    (irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `D` >> gvs[]) >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (qpat_x_assum `isPREFIX sa.cs_current_insts sb.cs_current_insts` mp_tac >>
     rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >>
     simp_tac (srw_ss()) [emitted_insts_def] >>
     qpat_x_assum `sb.cs_current_insts = _` SUBST1_TAC >>
     simp[DROP_LENGTH_APPEND]) >>
  irule emitted_origin_ptr_path >> simp[] >>
  qexistsl_tac [`emitted_insts sa sb`, `sa`] >>
  gvs[EVERY_MEM, mk_inst_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED
Finalise empty_buffer_origin_run
