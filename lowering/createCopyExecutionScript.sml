Theory createCopyExecution
Ancestors
  createMemoryInterface createFrameInterface createSourceCallback fragExec context contextProps
  emitHelperProps exprLoweringProps venomMemProps venomExecSemantics
  compileEnv emitHelper venomInst venomState list rich_list

(* Dynamic copying is one MCOPY, not a compiler-generated loop.  Lift its
   checked execution to the compositional CFG interface. *)
Theorem compile_create_dynamic_copy_frag:
  compile_copy_memory_dynamic dst src len cs = ((),cs') ==>
  cs_extends cs cs' /\
  frag_exec ctx cs cs'
    (\s. fresh_vars_wrt cs s /\
         eval_operand dst s = SOME d /\ eval_operand src s = SOME p /\
         eval_operand len s = SOME n /\ create_live live s /\
         create_memory_snapshot regions s /\
         EVERY (\(off,bs). off + LENGTH bs <= LENGTH s.vs_memory /\
           (off + LENGTH bs <= w2n d \/ w2n d + w2n n <= off)) regions /\
         TAKE (w2n n) (DROP (w2n p) s.vs_memory) = bytes /\
         LENGTH bytes = w2n n)
    (\s. fresh_vars_wrt cs' s /\ create_live live s /\
         create_memory_snapshot ((w2n d,bytes)::regions) s)
    (K F)
Proof
  strip_tac >> conj_tac
  >- (fs[compile_copy_memory_dynamic_def] >>
      metis_tac[cs_appends_def, cs_appends_emit_helpers]) >>
  irule frag_exec_run_inst_seq >>
  `emit_void MCOPY [dst;src;len] cs = ((),cs')` by
    fs[compile_copy_memory_dynamic_def] >>
  drule emit_void_extends >>
  drule emitted_insts_emit_void >>
  simp[same_blocks_def] >> strip_tac >> strip_tac >>
  gvs[IS_PREFIX_APPEND, mk_inst_def, is_terminator_def] >> rpt strip_tac >>
  drule_all compile_create_copy_dynamic_execution >>
  strip_tac >> qexists_tac `s'` >> simp[] >>
  `create_memory_snapshot [(w2n d,bytes)] s'` by
    metis_tac[create_copy_snapshot] >>
  `create_memory_snapshot regions s'` by
    (gvs[mcopy_def] >>
     irule create_snapshot_disjoint_write >> simp[] >>
     gvs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  gvs[fresh_vars_wrt_def, create_live_def, create_memory_snapshot_def,
      eval_operand_def, lookup_var_def, EVERY_MEM] >>
  rpt strip_tac >> PairCases_on `e` >> gvs[] >>
  qpat_x_assum `!e. MEM e live ==> _` (qspec_then `(e0,e1)` mp_tac) >>
  simp[] >> strip_tac >>
  `eval_operand e0 (mcopy (w2n d) (w2n p) (w2n n) s) = SOME e1` by
    metis_tac[] >>
  Cases_on `e0` >> gvs[eval_operand_def, lookup_var_def,
    mcopy_def, write_memory_with_expansion_def]
QED

val _ = app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("Oracle dependency in " ^ name))
  (DB.thms "createCopyExecution");
