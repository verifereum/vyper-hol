(* The empty/default local write initializes only the length word. *)
Theory bodyLocalEmptyWriteMods
Ancestors
  stmtSimDeclMem typedCopyOriginPtrDynArray typedMemoryCopy
  exprPtrUnwrapCopyEdges wordLoadStorePtr bodyPtrBytestringBuiltinsUintGhost
  bodyPtrPrecompileBuiltinsArithmeticValue emitHelperProps
  unitTransformDefs memSafeRun codegenRel contextCodegenRel
  arithmetic emitHelper ptrDiscipline bodyPtrDefs
  venomInst venomState venomExecSemantics valueEncodingProps

(* v is the result of the successful typed/default read at the preceding cut.
   The physical store neither reallocates nor writes a capacity-sized buffer. *)
Theorem local_empty_write_path_mods:
  has_length_word typ /\ evaluate_type tenv typ = SOME tyv /\
  v = default_value tyv /\
  emit_void MSTORE [Var p; Lit 0w] sa = ((),sb) /\
  lookup_var p s = SOME w /\ w2n w + 32 <= s.vs_alloca_next /\
  ptr_covers G tn p s 32 /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t tf.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G,tf)) /\
    t = ((mstore (w2n w) 0w s) with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    typed_copy_state_frame sa (w2n w) 32 s t /\
    (!cap. ptr_covers G tn p s cap ==> ptr_covers G tf p t cap) /\
    tf = tn with t_mem := tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w + 32} /\
    mem_word_at (w2n w) t.vs_memory = 0w /\
    32 <= type_memory_size tyv /\ val_wf tyv v /\
    val_in_memory tyv v (w2n w) t.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory tyv v (w2n w) mem)
Proof
  strip_tac >>
  `emit_inst MSTORE [Var p; Lit 0w] [] sa = ((),sb)` by
    fs[emit_void_def, emit_inst_def] >>
  drule emit_inst_extends >> strip_tac >>
  qabbrev_tac `i = mk_inst sa.cs_next_id MSTORE [Var p; Lit 0w] []` >>
  qabbrev_tac `r = mstore (w2n w) 0w s` >>
  qabbrev_tac `tf = tn with t_mem := tn.t_mem DIFF {j | w2n w <= j /\ j < w2n w + 32}` >>
  `step_inst_base i s = OK r` by
    simp[Abbr `i`, Abbr `r`, mk_inst_def, step_inst_base_opcode_eqs,
         exec_write2_def, eval_operand_def] >>
  `inst_mem_below_frontier i s /\ inst_dload_in_section i s` by
    simp[Abbr `i`, mk_inst_def, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def, fixed_source_write_range_def,
         eval_operand_def] >>
  `step_prov PG G i r = G /\ step_taint i s r tn = tf` by
    simp[Abbr `i`, Abbr `r`, Abbr `tf`, clean_mstore_taint_state,
         mstore_ghost_frame, eval_operand_def, op_taint_def] >>
  `!D. ptr_inst_ok D lo 0 ctx func G tn i s` by
    (simp[Abbr `i`] >> rpt strip_tac >> irule ptr_inst_ok_mstore_tainted >> simp[]) >>
  `SUC s.vs_inst_idx = LENGTH sb.cs_current_insts` by simp[ADD1] >>
  qexistsl_tac [`r with vs_inst_idx := LENGTH sb.cs_current_insts`, `tf`] >>
  conj_tac
  >- (rpt gen_tac >>
      mp_tac (Q.INST [`opc` |-> `MSTORE`, `args` |-> `[Var p; Lit 0w]`,
                      `outs` |-> `[]`, `u` |-> `r`]
        typed_copy_emit_inst_origin_ptr_path) >>
      gvs[Abbr `i`, is_terminator_def, ADD1]) >>
  `mem_word_at (w2n w) r.vs_memory = 0w` by simp[Abbr `r`, mstore_mem_word_at_same] >>
  `val_in_memory tyv (default_value tyv) (w2n w) r.vs_memory /\
   val_wf tyv (default_value tyv) /\ 32 <= type_memory_size tyv` by
    metis_tac[memory_length_word_layout] >>
  `!mem. mem_agree_outside tf.t_mem r.vs_memory mem ==>
     val_in_memory tyv (default_value tyv) (w2n w) mem` by
    (rpt strip_tac >>
     `mem_word_at (w2n w) r.vs_memory = mem_word_at (w2n w) mem` by
       (irule clean_word_mem_agree >> qexists_tac `tf.t_mem` >> simp[Abbr `tf`]) >>
     metis_tac[memory_length_word_layout]) >>
  gvs[Abbr `r`, Abbr `tf`, typed_copy_mstore_state_frame] >>
  simp[mstore_def, lookup_var_def, ptr_covers_def, op_taint_def]
QED
