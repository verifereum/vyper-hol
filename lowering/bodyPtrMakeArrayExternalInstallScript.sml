(* Whole-fragment installation restricted to the actual external-copy pieces. *)
Theory bodyPtrMakeArrayExternalInstall
Ancestors
  bodyPtrMakeArrayExternalCompiler bodyPtrMakeArrayImmutableAlloc
  exprSimStorageCopy loweringHalt exprSimAlloc fragExec exprSimCopy
  exprLoweringProps exprLowering context compileEnv list rich_list

Theorem runtime_imm_copy_extends:
  compile_imm_copy_to_memory F imm src dst n off sa = ((),sb) ==>
  cs_extends sa sb
Proof
  strip_tac >> drule code_copy_insts >> strip_tac >>
  irule cs_extends_same_block >> gvs[same_blocks_def, IS_PREFIX_APPEND]
QED

Theorem allocated_fragment_install:
  compile_alloc_buffer sz sa = (buf,sm) /\ cs_extends sm sb /\
  fn_has_code sa sb func ==>
  fn_has_code sm sb func /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  ?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sm)
      (DROP (LENGTH sa.cs_current_insts) bb.bb_instructions)
Proof
  strip_tac >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  drule_all fn_has_code_split >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  gvs[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> drule emit_op_extends >> strip_tac >>
  gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  metis_tac[]
QED

Theorem storage_allocated_install:
  compile_alloc_buffer sz sa = (buf,sm) /\
  (if n = 1 then
     ?v sl. emit_op (if tr then TLOAD else SLOAD) [src] sm = (v,sl) /\
       emit_void MSTORE [buf.buf_operand; v] sl = ((),sb)
   else ?exit. compile_word_copy_loop src buf.buf_operand n
     (if tr then LocTransient else LocStorage) LocMemory F sm = (exit,sb)) /\
  fn_has_code sa sb func ==>
  fn_has_code sm sb func /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  ?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sm)
      (DROP (LENGTH sa.cs_current_insts) bb.bb_instructions)
Proof
  strip_tac >> irule allocated_fragment_install >>
  goal_assum (drule_at Any) >> simp[] >>
  irule storage_copy_suffix_extends >>
  qexistsl_tac [`buf.buf_operand`, `if tr then LocTransient else LocStorage`,
    `n`, `src`, `()`] >>
  Cases_on `tr` >> Cases_on `n = 1` >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >> metis_tac[]
QED

Theorem immutable_allocated_install:
  compile_alloc_buffer sz sa = (buf,sm) /\
  compile_imm_copy_to_memory F imm src buf.buf_operand n 0 sm = ((),sb) /\
  fn_has_code sa sb func ==>
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  ?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sm ++ emitted_insts sm sb)
      (DROP (LENGTH sa.cs_current_insts) bb.bb_instructions) /\
    isPREFIX (emitted_insts sa sm)
      (DROP (LENGTH sa.cs_current_insts) bb.bb_instructions) /\
    isPREFIX (emitted_insts sm sb)
      (DROP (SUC (LENGTH sa.cs_current_insts)) bb.bb_instructions)
Proof
  strip_tac >>
  `cs_extends sm sb` by metis_tac[runtime_imm_copy_extends] >>
  drule_all allocated_fragment_install >> strip_tac >> simp[] >>
  `same_blocks sa sm /\
   sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[] >>
     drule emit_op_extends >> simp[]) >>
  drule code_copy_insts >> strip_tac >>
  `emitted_insts sm sb = is` by
    (qpat_assum `sb.cs_current_insts = _`
       (fn th => pure_rewrite_tac[emitted_insts_def, th, DROP_LENGTH_APPEND]) >>
     REFL_TAC) >>
  `isPREFIX (emitted_insts sa sm ++ emitted_insts sm sb)
     (DROP (LENGTH sa.cs_current_insts) bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX _ _` kall_tac >>
     qpat_x_assum `fn_has_code sm sb func` kall_tac >>
     fs[fn_has_code_def, same_blocks_def] >>
     gvs[IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     metis_tac[]) >>
  drule_all alloc_buffer_installed_split >> simp[]
QED
