(* Selected one-word immutable For copy at the actual allocation cutoff. *)
Theory bodyFullForArrayImmScalarCopy
Ancestors
  bodyFullForArrayCtorCopy immutableLoadPtr immutableSeqCursorPtr immutableCopySeqPtr
  instSeqPtrLo instSeqComposePtr exprSimCopy exprSimStorageCopy
  immutableCopyExecution immutableWordExecution stmtLowering context compileEnv
  emitHelper emitHelperProps exprLoweringProps loweringStateRelDefs
  fragGasSeqPtr ptrDiscipline venomState venomInst finite_map words list

Theorem for_immutable_runtime_word_load[local]:
  compile_imm_load_word F imm op sa = (r,sb) /\
  eval_operand op s = SOME a /\ op_taint tn op = {} /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?z Gf tf.
    copy_runtime_frame sa s sb z /\ copy_old_operand sb r /\
    eval_operand r z = SOME (immutable_copy_read F a s) /\
    z.vs_memory = s.vs_memory /\
    (!D k. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    op_prov Gf r = NONE /\ op_taint tf r = {} /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  simp[compile_imm_load_word_runtime] >> strip_tac >>
  drule_all (emit_immutable_load_runtime_frame |> Q.INST [`ctor` |-> `F`]
    |> SIMP_RULE (srw_ss()) []) >> strip_tac >>
  qexistsl_tac [`update_var out (immutable_copy_read F a s) s`,
    `DRESTRICT G (COMPL {out})`, `tn with t_var := tn.t_var |+ (out,{})`] >>
  simp[copy_old_operand_def,eval_operand_def,lookup_var_def,update_var_def,
    FLOOKUP_UPDATE,op_prov_def,FLOOKUP_DRESTRICT] >>
  conj_tac
  >- (rpt gen_tac >> irule inst_seq_ptr_zero_to_lo >>
      simp[allocas_from_def] >> qexists_tac `D` >> simp[] >>
      irule (immutable_load_checked_uniform |> Q.INST [`ctor` |-> `F`]
        |> SIMP_RULE (srw_ss()) []) >> simp[]) >>
  simp[op_taint_def,FLOOKUP_UPDATE] >> rpt strip_tac >>
  `x <> out` by metis_tac[] >> simp[]
QED

Theorem for_array_immutable_scalar_copy_full:
  compile_iter_elem_copy cenv src (Var p) 32 LocCode F typ typ sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa (Var p) /\
  eval_operand src s = SOME a /\ lookup_var p s = SOME b /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  ptr_covers G tn p s 32 /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  (cenv.ce_is_ctor ==>
    w2n a + 32 <= lo /\ mem_word_taint tn.t_mem (w2n a) = {} /\
    (!region. cenv.ce_imm_alloca = SOME region ==>
      copy_old_operand sa region /\ eval_operand region s = SOME 0w /\
      op_taint tn region = {} /\ op_prov G region = NONE)) ==>
  ?z Gf tf.
    copy_runtime_frame sa s sb z /\
    z.vs_memory = (mstore (w2n b) (immutable_copy_read cenv.ce_is_ctor a s) s).vs_memory /\
    (!D k. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tf) /\
    tf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> Cases_on `cenv.ce_is_ctor`
  >- (gvs[] >>
      `!region. cenv.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w /\
        op_taint tn region = {} /\ op_prov G region = NONE` by metis_tac[] >>
      drule_all (for_array_constructor_scalar_copy_full |> Q.INST [`bytes` |-> `32`]
        |> SIMP_RULE (srw_ss()) []) >>
      disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >>
      qexistsl_tac [`z`,`Gf`,`tf`] >> simp[]) >>
  gvs[] >>
  qpat_x_assum `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_iter_elem_copy_def,compile_ptr_load_def,immutable_comp_bind_cases] >>
  strip_tac >>
  drule_all for_immutable_runtime_word_load >>
  disch_then (qspecl_then [`func`,`PG`,`G`] strip_assume_tac) >>
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
  `copy_runtime_frame st1 z sb (mstore (w2n b) (immutable_copy_read F a s) z)` by
    (irule copy_runtime_store >> qexistsl_tac [`Var p`,`val_op`] >> simp[]) >>
  `!D k. inst_seq_ptr D lo ctx func PG Gf tf (emitted_insts st1 sb)
    (z with vs_inst_idx := k) Gf
    (tf with t_mem := tf.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32})` by
    (rpt gen_tac >> irule inst_seq_ptr_zero_to_lo >>
     simp[allocas_from_def] >> qexists_tac `D` >> simp[] >>
     drule_all emit_mstore_payload_checked_uniform >> simp[]) >>
  `emitted_insts sa sb = emitted_insts sa st1 ++ emitted_insts st1 sb` by
    (irule emitted_insts_append >> gvs[copy_runtime_frame_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa st1)` by
    metis_tac[immutable_load_nonterminators] >>
  qexistsl_tac [`mstore (w2n b) (immutable_copy_read F a s) z`,`Gf`,
    `tf with t_mem := tf.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32}`] >>
  conj_tac
  >- (irule copy_runtime_frame_trans >> qexistsl_tac [`z`,`st1`] >> simp[]) >>
  simp[mstore_def] >> reverse conj_tac
  >- (rpt strip_tac >> gvs[op_taint_def]) >>
  gen_tac >> irule inst_seq_ptr_uniform_append >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`,`z`,`tf`] >> gvs[copy_runtime_frame_def]
QED
