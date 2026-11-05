(* Fresh-allocation producer for the protected immutable-copy prefix. *)
Theory bodyIntCallFreshCodeCopy
Ancestors
  bodyIntCallImmutableCopyPath exprSimAlloc loweringHalt context compileEnv exprLoweringProps fragExec exprSimCopy

Theorem loccode_copy_split:
  compile_ensure_in_memory src LocCode sz wc mode imm sa = (dst,sb) ==>
  ?buf mid. compile_alloc_buffer sz sa = (buf,mid) /\
    compile_imm_copy_to_memory mode imm src buf.buf_operand
      ((sz+31) DIV 32) 0 mid = ((),sb) /\ dst = buf.buf_operand
Proof
  simp[compile_ensure_in_memory_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  rename1 `compile_imm_copy_to_memory _ _ _ _ _ _ _ = (r,_)` >>
  Cases_on `r` >> simp[] >> rpt strip_tac >> goal_assum drule >> simp[]
QED

Theorem loccode_copy_code_split:
  compile_alloc_buffer sz sa = (buf,mid) /\
  compile_imm_copy_to_memory mode imm src dst n off mid = ((),sb) /\
  fn_has_code sa sb func ==>
  fn_has_code sa mid func /\
  mid.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa mid /\
  sb.cs_current_insts = mid.cs_current_insts ++ emitted_insts mid sb /\
  sa.cs_next_var <= mid.cs_next_var
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`sz`, `sa`] ci_mono_compile_alloc_buffer) >>
  mp_tac (Q.SPECL [`n`, `mode`, `imm`, `src`, `dst`, `off`, `mid`]
    ci_mono_compile_imm_copy_to_memory) >>
  simp[] >> rpt strip_tac >>
  `fn_has_code sa mid func` by
    (fs[ci_mono_def] >> drule_all fn_has_code_split >> simp[]) >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  `?is. sb.cs_current_insts = mid.cs_current_insts ++ is` by
    (Cases_on `mode` >-
       (drule code_ctor_copy_insts >> strip_tac >> goal_assum drule) >>
     drule code_copy_insts >> strip_tac >> goal_assum drule) >>
  simp[emitted_insts_def] >>
  gvs[ci_mono_def, rich_listTheory.DROP_APPEND1, listTheory.APPEND_ASSOC]
QED

Theorem fresh_alloc_buffer_base:
  compile_alloc_buffer sz sa = (buf,mid) /\
  FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\
  run_inst_seq (emitted_insts sa mid) s = OK u /\
  eval_operand buf.buf_operand u = SOME w ==>
  w = n2w s.vs_alloca_next
Proof
  strip_tac >> drule compile_alloc_buffer_insts >> strip_tac >>
  gvs[emitted_insts_def, rich_listTheory.DROP_APPEND1,
      run_inst_seq_def, venomExecSemanticsTheory.step_inst_base_def,
      venomExecSemanticsTheory.exec_alloca_def, venomInstTheory.mk_inst_def,
      venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
      venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem aligned_copy_size:
  sz MOD 32 = 0 ==> 32*((sz+31) DIV 32) = sz
Proof
  strip_tac >>
  `sz = (sz DIV 32)*32` by
    (qspec_then `32` mp_tac arithmeticTheory.DIVISION >> simp[] >>
     disch_then (qspec_then `sz` mp_tac) >> simp[]) >>
  pop_assum SUBST1_TAC >> simp[arithmeticTheory.MULT_DIV]
QED

Theorem fresh_loccode_copy_run:
  compile_ensure_in_memory src LocCode sz wc cenv.ce_is_ctor
    cenv.ce_imm_alloca sa = (dst,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\
  (!region. cenv.ce_imm_alloca = SOME region ==> copy_old_operand sa region) /\
  FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\
  cap <= s.vs_alloca_next /\ cap <= LENGTH s.vs_memory /\
  0 < sz /\ sz < dimword (:256) /\ sz MOD 32 = 0 ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      TAKE cap t.vs_memory = TAKE cap s.vs_memory /\
      cap <= LENGTH t.vs_memory
Proof
  strip_tac >> drule loccode_copy_split >> strip_tac >>
  drule_all loccode_copy_code_split >> strip_tac >>
  `!x. src = Var x ==> not_fresh_at sa x` by fs[copy_old_operand_def] >>
  drule_all runtime_code_copy_alloc_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa mid) s = OK u` >>
  `w = n2w s.vs_alloca_next` by (drule_all fresh_alloc_buffer_base >> simp[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt, stmt_state_rel_def] >>
  `w2n w = s.vs_alloca_next` by simp[wordsTheory.w2n_n2w] >>
  `32*((sz+31) DIV 32) = sz` by simp[aligned_copy_size] >>
  `copy_old_operand mid src` by (irule copy_old_operand_mono >> qexists `sa` >> simp[]) >>
  `copy_old_operand mid buf.buf_operand` by
    (gvs[copy_old_operand_def] >> simp[]) >>
  `!region. cenv.ce_imm_alloca = SOME region ==>
     eval_operand region u = SOME 0w /\ copy_old_operand mid region` by
    (rpt strip_tac >-
       (fs[stmt_state_rel_def, immutable_base_zero_def] >> metis_tac[]) >>
     irule copy_old_operand_mono >> qexists `sa` >> simp[]) >>
  `?t. copy_runtime_frame mid u sb t /\
       TAKE cap t.vs_memory = TAKE cap u.vs_memory /\
       cap <= LENGTH t.vs_memory` by
    (irule compile_imm_copy_prefix_frame >> simp[] >>
     goal_assum (drule_at (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`)) >>
     simp[]) >>
  qexists `t` >> fs[copy_runtime_frame_def] >>
  drule_all emitted_insts_append >> strip_tac >>
  simp[] >>
  qpat_x_assum `run_inst_seq (emitted_insts sa mid) s = OK u`
    (mp_then Any mp_tac run_inst_seq_append) >>
  disch_then (qspec_then `emitted_insts mid sb` mp_tac) >> simp[]
QED
