(* Actual-cutoff immutable constructor reads for For element copying. *)
Theory bodyFullForArrayCtorCopy
Ancestors
  bodyFullForArrayImmStart immutableCopySeqPtr immutableSeqCursorPtr
  immutableLoadPtr immutableRegionLoadPtr instSeqPtrLo instSeqComposePtr
  exprSimCopy exprSimStorageCopy immutableCopyExecution immutableWordExecution
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  loweringStateRelDefs fragGasSeqPtr ptrDiscipline venomState venomInst
  finite_map words list

Theorem for_array_constructor_direct_load_full:
  compile_imm_load_word T NONE op sa = (r,sb) /\
  eval_operand op s = SOME a /\ op_taint tn op = {} /\
  op_prov G op = NONE /\ w2n a + 32 <= lo /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?z Gf tf.
    copy_runtime_frame sa s sb z /\ copy_old_operand sb r /\
    eval_operand r z = SOME (immutable_copy_read T a s) /\
    z.vs_memory = s.vs_memory /\
    (!D k. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    op_prov Gf r = NONE /\
    op_taint tf r = mem_word_taint tn.t_mem (w2n a) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  simp[compile_imm_load_word_no_base] >> strip_tac >>
  drule_all (emit_immutable_load_runtime_frame |> Q.INST [`ctor` |-> `T`]
    |> SIMP_RULE (srw_ss()) []) >> strip_tac >>
  qexistsl_tac [`update_var out (immutable_copy_read T a s) s`,
    `DRESTRICT G (COMPL {out})`,
    `tn with t_var := tn.t_var |+ (out,mem_word_taint tn.t_mem (w2n a))`] >>
  simp[copy_old_operand_def,eval_operand_def,lookup_var_def,update_var_def,
    FLOOKUP_UPDATE,op_prov_def,FLOOKUP_DRESTRICT] >>
  conj_tac
  >- (rpt gen_tac >> irule for_array_immutable_header_load_full >>
      simp[eval_operand_def,allocas_from_def]) >>
  simp[op_taint_def,FLOOKUP_UPDATE] >> rpt strip_tac >>
  `x <> out` by metis_tac[] >> simp[]
QED

Theorem for_array_constructor_add_full[local]:
  emit_op ADD [left;right] sa = (r,sb) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?out Gf tf. r = Var out /\
    copy_runtime_frame sa s sb (update_var out (a+b) s) /\
    copy_old_operand sb r /\
    (!D k. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    op_prov Gf r = first_prov G [left;right] /\ op_taint tf r = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all emit_add_runtime_frame >> strip_tac >>
  qexistsl_tac [`out`,
    `step_prov PG G (mk_inst sa.cs_next_id ADD [left;right] [out])
      (update_var out (a+b) s)`, `tn with t_var := tn.t_var |+ (out,{})`] >>
  simp[copy_old_operand_def,add_selected_provenance,op_taint_def,FLOOKUP_UPDATE] >>
  conj_tac
  >- (rpt gen_tac >> irule inst_seq_ptr_zero_to_lo >>
      simp[allocas_from_def] >> qexists_tac `D` >> simp[] >>
      irule clean_add_checked_uniform >> simp[]) >>
  rpt strip_tac >> `x <> out` by metis_tac[] >> simp[stmtAppendStorageRunPtrTheory.scalar_step_old_prov]
QED

Theorem for_array_constructor_load_full:
  compile_imm_load_word T imm op sa = (r,sb) /\
  eval_operand op s = SOME a /\ op_taint tn op = {} /\ op_prov G op = NONE /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w /\
    op_taint tn region = {} /\ op_prov G region = NONE) /\
  w2n a + 32 <= lo /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?z Gf tf.
    copy_runtime_frame sa s sb z /\ copy_old_operand sb r /\
    eval_operand r z = SOME (immutable_copy_read T a s) /\
    z.vs_memory = s.vs_memory /\
    (!D k. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    op_prov Gf r = NONE /\ op_taint tf r = mem_word_taint tn.t_mem (w2n a) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> Cases_on `imm`
  >- (gvs[] >> drule_all for_array_constructor_direct_load_full >> simp[]) >>
  gvs[] >>
  qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
  simp[compile_imm_load_word_def,comp_bind_def] >>
  pairarg_tac >> strip_tac >>
  drule_all for_array_constructor_add_full >>
  disch_then (qspecl_then [`func`,`PG`,`G`] strip_assume_tac) >>
  gvs[first_prov_def,WORD_ADD_0] >>
  `eval_operand (Var out) (update_var out a s) = SOME a /\
   allocas_from lo (update_var out a s)` by
    simp[eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE,allocas_from_def] >>
  `compile_imm_load_word T NONE (Var out) cs' = (r,sb)` by
    simp[compile_imm_load_word_no_base] >>
  drule_all for_array_constructor_direct_load_full >>
  disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa cs')` by
    (drule_all emit_add_runtime_frame >> strip_tac >> simp[mk_inst_def,is_terminator_def]) >>
  `emitted_insts sa sb = emitted_insts sa cs' ++ emitted_insts cs' sb` by
    (irule emitted_insts_append >> gvs[copy_runtime_frame_def]) >>
  qexistsl_tac [`z`,`Gf'`,`tf'`] >>
  conj_tac
  >- (irule copy_runtime_frame_trans >>
      qexistsl_tac [`update_var out a s`,`cs'`] >> simp[]) >>
  simp[immutable_copy_read_def,update_var_def] >> conj_tac
  >- (gen_tac >> irule inst_seq_ptr_uniform_append >>
      reverse conj_tac >- simp[] >>
      qexistsl_tac [`Gf`,`update_var out a s`,`tf`] >>
      gvs[copy_runtime_frame_def]) >>
  rpt strip_tac >> rename1 `not_fresh_at sa old` >>
  `not_fresh_at cs' old` by
    (gvs[copy_runtime_frame_def,not_fresh_at_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem for_array_constructor_store_full[local]:
  emit_void MSTORE [Var p;v] sa = ((),sb) /\
  copy_old_operand sa (Var p) /\ copy_old_operand sa v /\
  eval_operand (Var p) s = SOME b /\ eval_operand v s = SOME value /\
  ptr_covers G tn p s 32 /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  copy_runtime_frame sa s sb (mstore (w2n b) value s) /\
  (!D k. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb)
    (s with vs_inst_idx := k) G
    (tn with t_mem :=
      (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 32}) UNION
      {w2n b + j | j IN op_taint tn v}))
Proof
  strip_tac >> conj_tac
  >- (irule copy_runtime_store >> qexistsl_tac [`Var p`,`v`] >> simp[]) >>
  rpt gen_tac >> irule inst_seq_ptr_zero_to_lo >>
  simp[allocas_from_def] >> qexists_tac `D` >> simp[] >>
  drule_all emit_mstore_payload_checked_uniform >> simp[]
QED

Theorem for_array_constructor_scalar_copy_full:
  compile_iter_elem_copy cenv src (Var p) bytes LocCode F ty ty sa = ((),sb) /\
  cenv.ce_is_ctor /\ bytes <= 32 /\
  copy_old_operand sa (Var p) /\ lookup_var p s = SOME b /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  (!region. cenv.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ op_taint tn region = {} /\
    op_prov G region = NONE) /\
  w2n a + 32 <= lo /\ ptr_covers G tn p s 32 /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?z Gf tf.
    copy_runtime_frame sa s sb z /\
    z.vs_memory = (mstore (w2n b) (immutable_copy_read T a s) s).vs_memory /\
    (!D k. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    tf.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 32}) UNION
      {w2n b + j | j IN mem_word_taint tn.t_mem (w2n a)} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  simp[stmtLoweringTheory.compile_iter_elem_copy_def,
    compile_ptr_load_def] >> strip_tac >> gvs[immutable_comp_bind_cases] >>
  drule_all for_array_constructor_load_full >>
  disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >>
  `not_fresh_at sa p` by gvs[copy_old_operand_def] >>
  `copy_old_operand st1 (Var p) /\ lookup_var p z = SOME b /\
   ptr_covers Gf tf p z 32` by
    (conj_tac
     >- metis_tac[copy_old_operand_mono,copy_runtime_frame_def] >>
     conj_tac >- metis_tac[copy_runtime_frame_def] >>
     drule_all ptr_covers_copy_runtime_frame >> simp[]) >>
  `z.vs_allocas = s.vs_allocas /\ z.vs_alloca_next = s.vs_alloca_next` by
    metis_tac[copy_runtime_frame_def,copy_static_fields] >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by metis_tac[allocas_from_def] >>
  `eval_operand (Var p) z = SOME b` by simp[eval_operand_def] >>
  drule_all for_array_constructor_store_full >>
  disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >>
  `emitted_insts sa sb = emitted_insts sa st1 ++ emitted_insts st1 sb` by
    (irule emitted_insts_append >> gvs[copy_runtime_frame_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa st1)` by
    metis_tac[immutable_load_nonterminators] >>
  qexistsl_tac [`mstore (w2n b) (immutable_copy_read T a s) z`,`Gf`,
    `tf with t_mem := (tf.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 32}) UNION
       {w2n b + j | j IN op_taint tf val_op}`] >>
  conj_tac
  >- (irule copy_runtime_frame_trans >> qexistsl_tac [`z`,`st1`] >> simp[]) >>
  simp[mstore_def] >> reverse conj_tac
  >- (rpt strip_tac >> simp[op_taint_def] >>
      (gvs[op_taint_def])) >>
  gen_tac >> irule inst_seq_ptr_uniform_append >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`,`z`,`tf`] >> gvs[copy_runtime_frame_def]
QED

Theorem for_array_constructor_offset_full[local]:
  compile_lit_byte_offset op off sa = (r,sb) /\
  copy_old_operand sa op /\ eval_operand op s = SOME a /\
  op_taint tn op = {} /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?z Gf tf.
    copy_runtime_frame sa s sb z /\
    eval_operand r z = SOME (a + n2w off) /\ copy_old_operand sb r /\
    z.vs_memory = s.vs_memory /\
    (!D k. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    op_taint tf r = {} /\ op_prov Gf r = op_prov G op /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> Cases_on `off = 0`
  >- (gvs[compile_lit_byte_offset_def,comp_return_def] >>
      qexistsl_tac [`s`,`G`,`tn`] >>
      simp[copy_runtime_frame_def,emitted_insts_def,inst_seq_ptr_def,
        run_inst_seq_def,same_blocks_def,WORD_ADD_0]) >>
  Cases_on `op`
  >- (gvs[compile_lit_byte_offset_def,comp_return_def,eval_operand_def] >>
      qexistsl_tac [`s`,`G`,`tn`] >>
      simp[copy_runtime_frame_def,copy_old_operand_def,emitted_insts_def,
        inst_seq_ptr_def,eval_operand_def,op_taint_def,op_prov_def,
        run_inst_seq_def,same_blocks_def]) >>
  gvs[compile_lit_byte_offset_def] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
   op_taint tn (Lit (n2w off)) = {}` by simp[eval_operand_def,op_taint_def] >>
  drule_all for_array_constructor_add_full >>
  disch_then (qspecl_then [`func`,`PG`,`G`] strip_assume_tac) >>
  qexistsl_tac [`update_var out (a + n2w off) s`,`Gf`,`tf`] >>
  gvs[first_prov_def,op_prov_def,eval_operand_def,lookup_var_def,
    update_var_def,FLOOKUP_UPDATE] >>
  Cases_on `FLOOKUP G s'` >> simp[]
QED

Theorem for_array_constructor_offset_load_full[local]:
  compile_lit_byte_offset src off sa = (sop,sm) /\
  compile_imm_load_word T imm sop sm = (r,sb) /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  (!region. imm = SOME region ==> copy_old_operand sa region /\
    eval_operand region s = SOME 0w /\ op_taint tn region = {} /\
    op_prov G region = NONE) /\
  w2n (a + n2w off) + 32 <= lo /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?z Gf tf.
    copy_runtime_frame sa s sb z /\ copy_old_operand sb r /\
    eval_operand r z = SOME (immutable_copy_read T (a + n2w off) s) /\
    z.vs_memory = s.vs_memory /\
    (!D k. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    op_prov Gf r = NONE /\
    op_taint tf r = mem_word_taint tn.t_mem (w2n (a + n2w off)) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all for_array_constructor_offset_full >>
  disch_then (qspecl_then [`func`,`PG`,`G`] strip_assume_tac) >>
  `!region. imm = SOME region ==> eval_operand region z = SOME 0w /\
    op_taint tf region = {} /\ op_prov Gf region = NONE` by
    (gen_tac >> strip_tac >>
     `copy_old_operand sa region /\ eval_operand region s = SOME 0w /\
      op_taint tn region = {} /\ op_prov G region = NONE` by metis_tac[] >>
     conj_tac >- metis_tac[copy_runtime_frame_operand] >>
     conj_tac
     >- (Cases_on `region` >> gvs[copy_old_operand_def,op_taint_def]) >>
     Cases_on `region` >> gvs[copy_old_operand_def,op_prov_def]) >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by
    metis_tac[copy_runtime_frame_def,copy_static_fields,allocas_from_def] >>
  `op_prov Gf sop = NONE` by metis_tac[] >>
  drule_all for_array_constructor_load_full >>
  disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm)` by
    (drule code_offset_insts >> simp[EVERY_MEM] >> metis_tac[is_terminator_def]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> gvs[copy_runtime_frame_def]) >>
  qexistsl_tac [`z'`,`Gf'`,`tf'`] >>
  conj_tac >- (irule copy_runtime_frame_trans >> qexistsl_tac [`z`,`sm`] >> simp[]) >>
  `immutable_copy_read T (a + n2w off) z =
   immutable_copy_read T (a + n2w off) s` by simp[immutable_copy_read_def,mload_def] >>
  simp[] >> conj_tac
  >- (gen_tac >> irule inst_seq_ptr_uniform_append >>
      reverse conj_tac >- simp[] >>
      qexistsl_tac [`Gf`,`z`,`tf`] >> gvs[copy_runtime_frame_def]) >>
  rpt strip_tac >> rename1 `not_fresh_at sa old` >>
  `not_fresh_at sm old` by
    (gvs[copy_runtime_frame_def,not_fresh_at_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem for_array_constructor_offset_covered_full[local]:
  compile_lit_byte_offset (Var p) off sa = (r,sb) /\
  not_fresh_at sa p /\ lookup_var p s = SOME a /\
  ptr_covers G tn p s cap /\ off < cap /\ off + n <= cap /\
  w2n a + off < dimword(:256) /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?q z Gf tf.
    r = Var q /\ copy_runtime_frame sa s sb z /\
    lookup_var q z = SOME (a + n2w off) /\ not_fresh_at sb q /\
    z.vs_memory = s.vs_memory /\
    (!D k. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    ptr_covers Gf tf q z n /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `copy_old_operand sa (Var p) /\ eval_operand (Var p) s = SOME a /\
   op_taint tn (Var p) = {}` by
    gvs[copy_old_operand_def,eval_operand_def,bodyPtrDefsTheory.ptr_covers_def] >>
  drule_all for_array_constructor_offset_full >>
  disch_then (qspecl_then [`func`,`PG`,`G`] strip_assume_tac) >>
  `?q. r = Var q` by
    (Cases_on `off = 0` >>
     gvs[compile_lit_byte_offset_def,comp_return_def] >>
     drule emitted_insts_emit_op >> metis_tac[]) >>
  gvs[eval_operand_def,copy_old_operand_def] >>
  qexistsl_tac [`z`,`Gf`,`tf`] >> simp[] >>
  gvs[bodyPtrDefsTheory.ptr_covers_def,op_prov_def] >>
  `off < dimword(:256)` by decide_tac >>
  simp[w2n_add_2,w2n_n2w,arithmeticTheory.LESS_MOD] >> decide_tac
QED

Theorem for_array_constructor_offset_store_full[local]:
  compile_lit_byte_offset (Var p) off sa = (dop,sm) /\
  emit_void MSTORE [dop;v] sm = ((),sb) /\
  not_fresh_at sa p /\ lookup_var p s = SOME b /\
  copy_old_operand sa v /\ eval_operand v s = SOME value /\
  ptr_covers G tn p s cap /\ off < cap /\ off + 32 <= cap /\
  w2n b + off < dimword(:256) /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?z Gf tf.
    copy_runtime_frame sa s sb z /\
    z.vs_memory = (mstore (w2n (b + n2w off)) value s).vs_memory /\
    (!D k. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    tf.t_mem = (tn.t_mem DIFF {i | w2n (b + n2w off) <= i /\
      i < w2n (b + n2w off) + 32}) UNION
      {w2n (b + n2w off) + j | j IN op_taint tn v} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all for_array_constructor_offset_covered_full >>
  disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >> gvs[] >>
  `eval_operand v z = SOME value /\ copy_old_operand sm v` by
    metis_tac[copy_runtime_frame_operand,copy_old_operand_mono,copy_runtime_frame_def] >>
  `op_taint tf v = op_taint tn v` by
    (Cases_on `v` >> gvs[copy_old_operand_def,op_taint_def]) >>
  `copy_old_operand sm (Var q) /\ eval_operand (Var q) z = SOME (b + n2w off)` by
    simp[copy_old_operand_def,eval_operand_def] >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by
    metis_tac[copy_runtime_frame_def,copy_static_fields,allocas_from_def] >>
  drule_all for_array_constructor_store_full >>
  disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm)` by
    (drule code_offset_insts >> simp[EVERY_MEM] >> metis_tac[is_terminator_def]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> gvs[copy_runtime_frame_def]) >>
  qexistsl_tac [`mstore (w2n (b + n2w off)) value z`,`Gf`,
    `tf with t_mem := (tf.t_mem DIFF {i | w2n (b + n2w off) <= i /\
      i < w2n (b + n2w off) + 32}) UNION
      {w2n (b + n2w off) + j | j IN op_taint tf v}`] >>
  conj_tac >- (irule copy_runtime_frame_trans >> qexistsl_tac [`z`,`sm`] >> simp[]) >>
  simp[mstore_def] >> reverse conj_tac
  >- (rpt strip_tac >> gvs[op_taint_def]) >>
  gen_tac >> irule inst_seq_ptr_uniform_append >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`,`z`,`tf`] >> gvs[copy_runtime_frame_def]
QED

Theorem for_array_constructor_copy_one_full[local]:
  immutable_copy_one T imm src (Var p) off sa = ((),sb) /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  (!region. imm = SOME region ==> copy_old_operand sa region /\
    eval_operand region s = SOME 0w /\ op_taint tn region = {} /\
    op_prov G region = NONE) /\
  w2n (a + n2w off) + 32 <= lo /\
  not_fresh_at sa p /\ lookup_var p s = SOME b /\
  ptr_covers G tn p s cap /\ off < cap /\ off + 32 <= cap /\
  w2n b + off < dimword(:256) /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?z Gf tf.
    copy_runtime_frame sa s sb z /\
    z.vs_memory = (immutable_word_transfer F T a b off s).vs_memory /\
    (!D k. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  simp[immutable_copy_one_def,immutable_comp_bind_cases] >> strip_tac >>
  drule_all for_array_constructor_offset_load_full >>
  disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >>
  rename1 `compile_imm_load_word T imm src_op st1 = (val_op,s2)` >>
  `not_fresh_at s2 p /\ lookup_var p z = SOME b /\ ptr_covers Gf tf p z cap` by
    (conj_tac
     >- (gvs[copy_runtime_frame_def,not_fresh_at_def] >> metis_tac[]) >>
     conj_tac >- metis_tac[copy_runtime_frame_def] >>
     drule_all ptr_covers_copy_runtime_frame >> simp[]) >>
  `copy_old_operand s2 val_op /\
   allocas_from lo z /\ lo <= z.vs_alloca_next` by
    metis_tac[copy_old_operand_def,copy_runtime_frame_def,copy_static_fields,allocas_from_def] >>
  `w2n b + off < dimword(:256)` by decide_tac >>
  drule_all for_array_constructor_offset_store_full >>
  disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa s2)` by
    metis_tac[immutable_offset_load_nonterminators] >>
  `emitted_insts sa sb = emitted_insts sa s2 ++ emitted_insts s2 sb` by
    (irule emitted_insts_append >> gvs[copy_runtime_frame_def]) >>
  qexistsl_tac [`z'`,`Gf'`,`tf'`] >>
  conj_tac >- (irule copy_runtime_frame_trans >> qexistsl_tac [`z`,`s2`] >> simp[]) >>
  simp[immutable_word_transfer_def,immutable_mstore_memory_cong] >> conj_tac
  >- (gen_tac >> irule inst_seq_ptr_uniform_append >>
      reverse conj_tac >- simp[] >>
      qexistsl_tac [`Gf`,`z`,`tf`] >> gvs[copy_runtime_frame_def]) >>
  rpt strip_tac >> rename1 `not_fresh_at sa old` >>
  `not_fresh_at s2 old` by
    (gvs[copy_runtime_frame_def,not_fresh_at_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem for_array_constructor_copy_words_full[local]:
  !n off sa sb s G tn.
  compile_imm_copy_to_memory T imm src (Var p) n off sa = ((),sb) /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  (!region. imm = SOME region ==> copy_old_operand sa region /\
    eval_operand region s = SOME 0w /\ op_taint tn region = {} /\
    op_prov G region = NONE) /\
  (!j. j < n ==> w2n (a + n2w (off + 32*j)) + 32 <= lo) /\
  not_fresh_at sa p /\ lookup_var p s = SOME b /\
  ptr_covers G tn p s cap /\ off + 32*n <= cap /\
  w2n b + off + 32*n <= dimword(:256) /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?z Gf tf.
    copy_runtime_frame sa s sb z /\
    z.vs_memory = (immutable_transfers F T a b n off s).vs_memory /\
    (!D k. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  Induct
  >- (simp[compile_imm_copy_to_memory_def,comp_return_def] >> rpt strip_tac >>
      qexistsl_tac [`s`,`G`,`tn`] >>
      simp[copy_runtime_frame_refl,immutable_transfers_def,emitted_insts_def,inst_seq_ptr_def]) >>
  simp[immutable_copy_suc,comp_ignore_bind_def,immutable_comp_bind_cases] >>
  rpt gen_tac >> strip_tac >> suspend "step"
QED

Resume for_array_constructor_copy_words_full[step]:
  rename1 `immutable_copy_one T imm src (Var p) off sa = ((),sm)` >>
  `off < cap /\ off + 32 <= cap /\ w2n b + off < dimword(:256)` by
    (gvs[arithmeticTheory.MULT_SUC] >> decide_tac) >>
  `w2n (a + n2w off) + 32 <= lo` by
    (qpat_x_assum `!j. j < SUC n ==> _` (qspec_then `0` mp_tac) >> simp[]) >>
  drule_all for_array_constructor_copy_one_full >>
  disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >>
  `copy_old_operand sm src /\ eval_operand src z = SOME a /\
   op_taint tf src = {} /\ op_prov Gf src = NONE` by
    (`op_taint tf src = op_taint tn src /\ op_prov Gf src = op_prov G src` by
       (Cases_on `src` >> gvs[copy_old_operand_def,op_taint_def,op_prov_def]) >>
     metis_tac[copy_old_operand_mono,copy_runtime_frame_def,copy_runtime_frame_operand]) >>
  `!region. imm = SOME region ==> copy_old_operand sm region /\
    eval_operand region z = SOME 0w /\ op_taint tf region = {} /\
    op_prov Gf region = NONE` by
    (gen_tac >> strip_tac >>
     `copy_old_operand sa region /\ eval_operand region s = SOME 0w /\
      op_taint tn region = {} /\ op_prov G region = NONE` by metis_tac[] >>
     `op_taint tf region = op_taint tn region /\ op_prov Gf region = op_prov G region` by
       (Cases_on `region` >> gvs[copy_old_operand_def,op_taint_def,op_prov_def]) >>
     metis_tac[copy_old_operand_mono,copy_runtime_frame_def,copy_runtime_frame_operand]) >>
  suspend "tail"
QED

Resume for_array_constructor_copy_words_full[tail]:
  `not_fresh_at sm p /\ lookup_var p z = SOME b /\ ptr_covers Gf tf p z cap` by
    (conj_tac >- (gvs[copy_runtime_frame_def,not_fresh_at_def] >> metis_tac[]) >>
     conj_tac >- metis_tac[copy_runtime_frame_def] >>
     drule_all ptr_covers_copy_runtime_frame >> simp[]) >>
  `!j. j < n ==> w2n (a + n2w (off + 32 + 32*j)) + 32 <= lo` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!j. j < SUC n ==> _` (qspec_then `SUC j` mp_tac) >>
     `off + 32 * SUC j = off + 32 + 32*j` by
       (simp[arithmeticTheory.MULT_SUC] >> decide_tac) >>
     simp[arithmeticTheory.MULT_SUC,NoAsms] >> simp[]) >>
  `off + 32 + 32*n <= cap /\ w2n b + (off + 32) + 32*n <= dimword(:256)` by
    (gvs[arithmeticTheory.MULT_SUC] >> decide_tac) >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by
    metis_tac[copy_runtime_frame_def,copy_static_fields,allocas_from_def] >>
  qpat_x_assum `!off sa sb s G tn. _` drule >>
  disch_then (qspecl_then [`z`,`Gf`,`tf`] mp_tac) >>
  simp[] >> strip_tac >> suspend "compose"
QED

Resume for_array_constructor_copy_words_full[compose]:
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm)` by
    metis_tac[immutableCopyWordsPtrTheory.immutable_copy_one_nonterminators] >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> gvs[copy_runtime_frame_def]) >>
  `(immutable_transfers F T a b n (off + 32) z).vs_memory =
   (immutable_transfers F T a b n (off + 32)
     (immutable_word_transfer F T a b off s)).vs_memory` by
    (irule (cj 1 immutable_transfers_cong) >> simp[] >>
     gvs[copy_runtime_frame_def,copy_static_def,venom_state_component_equality,
       immutable_transfer_data,immutable_word_transfer_fields]) >>
  qexistsl_tac [`z'`,`Gf'`,`tf'`] >>
  conj_tac >- (irule copy_runtime_frame_trans >> qexistsl_tac [`z`,`sm`] >> simp[]) >>
  simp[immutable_transfers_def] >> conj_tac
  >- (gen_tac >> irule inst_seq_ptr_uniform_append >>
      reverse conj_tac >- simp[] >>
      qexistsl_tac [`Gf`,`z`,`tf`] >> gvs[copy_runtime_frame_def]) >>
  rpt strip_tac >> rename1 `not_fresh_at sa old` >>
  `not_fresh_at sm old` by
    (gvs[copy_runtime_frame_def,not_fresh_at_def] >> metis_tac[]) >>
  metis_tac[]
QED
Finalise for_array_constructor_copy_words_full

Theorem for_array_constructor_copy_checked_full:
  compile_iter_elem_copy cenv src (Var p) bytes LocCode F ty ty sa = ((),sb) /\
  cenv.ce_is_ctor /\ copy_old_operand sa src /\
  not_fresh_at sa p /\ lookup_var p s = SOME b /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  (!region. cenv.ce_imm_alloca = SOME region ==> copy_old_operand sa region /\
    eval_operand region s = SOME 0w /\ op_taint tn region = {} /\
    op_prov G region = NONE) /\
  w2n a + (if bytes <= 32 then 32 else 32*((bytes+31) DIV 32)) <= lo /\
  lo <= w2n b /\
  ptr_covers G tn p s (if bytes <= 32 then 32 else 32*((bytes+31) DIV 32)) /\
  w2n b + (if bytes <= 32 then 32 else 32*((bytes+31) DIV 32)) <= dimword(:256) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?z Gf tf.
    run_inst_seq (emitted_insts sa sb) s = OK z /\ copy_runtime_frame sa s sb z /\
    z.vs_memory =
      (if bytes <= 32 then (mstore (w2n b) (immutable_copy_read T a s) s).vs_memory
       else (immutable_transfers F T a b ((bytes+31) DIV 32) 0 s).vs_memory) /\
    (!D k. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> Cases_on `bytes <= 32`
  >- (`copy_old_operand sa (Var p)` by simp[copy_old_operand_def] >>
      gvs[] >>
      `!region. cenv.ce_imm_alloca = SOME region ==>
        eval_operand region s = SOME 0w /\ op_taint tn region = {} /\
        op_prov G region = NONE` by metis_tac[] >>
      drule_all for_array_constructor_scalar_copy_full >>
      disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >>
      qexistsl_tac [`z`,`Gf`,`tf`] >> simp[] >>
      metis_tac[copy_runtime_frame_def]) >>
  gvs[] >>
  `!j. j < (bytes+31) DIV 32 ==> w2n (a + n2w (0 + 32*j)) + 32 <= lo` by
    (gen_tac >> strip_tac >>
     `32*j < 32*((bytes+31) DIV 32) /\
      32*j + 32 <= 32*((bytes+31) DIV 32)` by decide_tac >>
     `w2n a + 32*j < dimword(:256) /\ 32*j < dimword(:256)` by decide_tac >>
     simp[w2n_add_2,w2n_n2w,arithmeticTheory.LESS_MOD] >> decide_tac) >>
  `compile_imm_copy_to_memory T cenv.ce_imm_alloca src (Var p)
    ((bytes+31) DIV 32) 0 sa = ((),sb)` by
    gvs[stmtLoweringTheory.compile_iter_elem_copy_def] >>
  `0 + 32*((bytes+31) DIV 32) <= 32*((bytes+31) DIV 32) /\
   w2n b + 0 + 32*((bytes+31) DIV 32) <= dimword(:256)` by simp[] >>
  drule_all for_array_constructor_copy_words_full >>
  disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`z`,`Gf`,`tf`] >> simp[] >> metis_tac[copy_runtime_frame_def]
QED
