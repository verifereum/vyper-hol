(* Allocation/bounds prefix boundaries for self.code slicing. *)
Theory bodyPtrCodeSliceSelfPrefix
Ancestors
  bodyPtrHashBuiltinsAllocFrame exprSimPtrLiteralOps exprSimSliceMemory
  bodyPtrHashBuiltinsGhostFrame fragGasSeqPtr fragExecPtr
  bodyPtrDefs ptrDiscipline venomState venomInst venomExecSemantics
  compileEnv loweringStateRelDefs codegenRel ptrSafeRun memLocDefs
  contextCodegenRel words finite_map pred_set

Theorem self_code_data_add_frame:
  !d cenv cx es G tn s sa dst src site off v PG id.
    ghost_inv d cenv cx es G tn s /\
    local_ptrs_reserved cenv sa /\
    (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
    (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
    (!p. not_fresh_at sa p ==> p <> dst) /\
    FLOOKUP G src = SOME site ==>
    ghost_inv d cenv cx es
      (step_prov PG G (mk_inst id ADD [Var src; Lit off] [dst])
        (update_var dst v s))
      (step_taint (mk_inst id ADD [Var src; Lit off] [dst]) s
        (update_var dst v s) tn) (update_var dst v s) /\
    ghost_kept cenv es sa G tn s
      (step_prov PG G (mk_inst id ADD [Var src; Lit off] [dst])
        (update_var dst v s))
      (step_taint (mk_inst id ADD [Var src; Lit off] [dst]) s
        (update_var dst v s) tn)
Proof
  rpt gen_tac >> strip_tac >> drule literal_add_ghost >> strip_tac >>
  simp[] >> conj_tac
  >- (irule hash_readonly_ghost_inv >> qexistsl_tac [`G`, `s`, `sa`, `tn`] >>
      simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def] >>
      rpt strip_tac >> metis_tac[]) >>
  irule hash_ghost_kept_frame >>
  simp[op_taint_def, FLOOKUP_UPDATE] >> rpt strip_tac >> metis_tac[]
QED

Theorem self_code_data_add_checked:
  !D ctx fn PG G tn s id src dst p b sz k.
    lookup_var src s = SOME p /\ FLOOKUP G src = SOME (b,sz) /\
    op_taint tn (Var src) = {} /\ ~ctx_has_dalloca ctx /\
    b <= w2n p /\ w2n p + 32 + k <= b+sz /\
    w2n p + 32 < dimword (:256) ==>
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id ADD [Var src; Lit 32w] [dst]] s
      (G |+ (dst,(b,sz))) (tn with t_var := tn.t_var |+ (dst,{})) /\
    ptr_covers (G |+ (dst,(b,sz)))
      (tn with t_var := tn.t_var |+ (dst,{})) dst
      (update_var dst (n2w (w2n p + 32)) s) k
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst id ADD [Var src; Lit 32w] [dst]) s =
    OK (update_var dst (n2w (w2n p + 32)) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
      eval_operand_def, GSYM word_add_n2w] >>
  drule literal_add_ghost >> strip_tac >> conj_tac
  >- simp[inst_seq_ptr_def, literal_add_ptr_inst_ok] >>
  simp[ptr_covers_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    op_taint_def, w2n_n2w]
QED

Theorem self_code_codesize_ghost:
  !PG G tn s id dst.
    step_prov PG G (mk_inst id CODESIZE [] [dst])
      (update_var dst (n2w (LENGTH s.vs_code)) s) = G \\ dst /\
    step_taint (mk_inst id CODESIZE [] [dst]) s
      (update_var dst (n2w (LENGTH s.vs_code)) s) tn =
      tn with t_var := tn.t_var |+ (dst,{})
Proof
  rpt gen_tac >>
  simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
    step_taint_def, set_var_taint_def, out_taint_def, mem_taint_def,
    new_site_bytes_def, update_var_def, step_writes_def,
    source_memory_write_ranges_def, range_bytes_def, written_taint_def,
    store_taint_def, imm_taint_def, adopt_reset_def,
    taint_component_equality, FLOOKUP_DEF, DRESTRICT_DOMSUB,
    EXTENSION] >>
  conj_tac >- simp[fmap_domsub] >> metis_tac[]
QED

Theorem self_code_codesize_checked:
  !D ctx fn PG G tn s id dst.
    ~ctx_has_dalloca ctx ==>
    inst_seq_ptr D 0 ctx fn PG G tn [mk_inst id CODESIZE [] [dst]] s
      (G \\ dst) (tn with t_var := tn.t_var |+ (dst,{}))
Proof
  rpt gen_tac >> strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id CODESIZE [] [dst]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, step_inst_non_invoke] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def] >>
     simp[exec_read0_def, update_var_def]) >>
  `step_inst_base (mk_inst id CODESIZE [] [dst]) s =
    OK (update_var dst (n2w (LENGTH s.vs_code)) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read0_def] >>
  simp[inst_seq_ptr_def, self_code_codesize_ghost]
QED
