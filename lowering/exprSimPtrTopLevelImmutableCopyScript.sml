(* Runtime immutable-copy layout and counted pointer boundaries. *)
Theory exprSimPtrTopLevelImmutableCopy
Ancestors
  exprSimPtrTopLevelCopy immutableCopyExecution compileEnv emitHelper
  fragGasSeqPtr context exprLoweringProps emitHelperProps venomInst list
  bodyPtrDefs typedCopyPtr ptrDiscipline ptrSafeRun venomState words

Theorem toplevel_immutable_copy_one_layout:
  compile_imm_copy_to_memory F imm src dst (SUC 0) 0 sa = ((),sb) ==>
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id DLOAD [src]
       [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id+1) MSTORE
       [dst; Var (STRING #"%" (toString sa.cs_next_var))] []]
Proof
  simp[compile_imm_copy_to_memory_def, compile_lit_byte_offset_def,
       compile_imm_load_word_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_APPEND]
QED

Theorem toplevel_immutable_copy_one_counted:
  compile_imm_copy_to_memory F imm src dst (SUC 0) 0 sa = ((),sb) /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (emitted_insts sa sb) s = OK r ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
    (OK (r with vs_inst_idx := s.vs_inst_idx + 2))
Proof
  strip_tac >> drule toplevel_immutable_copy_one_layout >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0 /\
   LENGTH (emitted_insts sa sb) = 2` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem toplevel_immutable_offset_coverage:
  ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
  off+len <= capacity /\ w2n a+capacity < dimword (:256) ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var root; Lit (n2w off)] [out])
      (update_var out (a+n2w off) s))
    (step_taint (mk_inst id ADD [Var root; Lit (n2w off)] [out]) s
      (update_var out (a+n2w off) s) tn)
    out (update_var out (a+n2w off) s) len
Proof
  strip_tac >> gvs[ptr_covers_def] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, finite_mapTheory.FLOOKUP_UPDATE,
       lookup_var_def, update_var_def] >>
  conj_tac
  >- (simp[step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
           mk_inst_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      Cases_on `eval_operand (Var root) s` >> simp[]) >>
  `w2n (a+n2w off) = w2n a+off` by
    (Cases_on `a` >> gvs[wordsTheory.word_add_n2w] >> decide_tac) >>
  simp[] >> decide_tac
QED
