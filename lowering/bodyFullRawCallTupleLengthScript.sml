(* The actual capped-length store, including its mask-independent ghosts. *)
Theory bodyFullRawCallTupleLength
Ancestors
  rawCallBufferPtr exprPtrUnwrapCopyEdges augAssignPtrScalarSafety augAssignPtrScalarCertificate
  ghostPcTransportPtr instIdxIndep codegenRel contextCodegenRel ptrSafeRun
  decoderGhostFramePtr exprSafeOperand builtinSimple emitHelper compileEnv
  exprLoweringProps loweringStateRelDefs fragGasSeqPtr venomExecSemantics venomState venomInst
  finite_map words rich_list list pred_set ptrDiscipline bodyPtrDefs

Theorem raw_call_tuple_length_checked:
 emit_op RETURNDATASIZE [] sa = (z,s1) /\
 emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
 compile_select cmp z (Lit (n2w n)) s2 = (cap,s3) /\
 emit_void MSTORE [Var x;cap] s3 = ((),sb) /\
 0 < n /\ n < dimword (:256) /\
 64 + ((n+31) DIV 32)*32 < dimword (:256) /\
 safe_operand sa (Var x) /\
 lookup_var x s = SOME (n2w b) /\
 b + (32 + ((n+31) DIV 32)*32) < dimword (:256) /\
 ptr_covers G tn x s (32 + ((n+31) DIV 32)*32) /\
 LENGTH s.vs_returndata < dimword (:256) /\
 mem_bytes_at (b+32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
   TAKE n s.vs_returndata /\
 (!i. b+32 <= i /\ i < b+32+LENGTH (TAKE n s.vs_returndata) ==>
      i NOTIN tn.t_mem) /\
 allocas_from lo s /\ ~ctx_has_dalloca ctx /\
 run_inst_seq (emitted_insts sa sb) s = OK t ==>
 ?Gf tnf.
   (!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tnf) /\
   ptr_covers Gf tnf x t (32 + ((n+31) DIV 32)*32) /\
   (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic n)))
        (BytesV (TAKE n s.vs_returndata)) b mem) /\
   tnf.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32} /\
   tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
   (!v. not_fresh_at sa v ==>
    lookup_var v t = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
    op_taint tnf (Var v) = op_taint tn (Var v)) /\
   (t with vs_vars := s.vs_vars) =
    mstore b (n2w (LENGTH (TAKE n s.vs_returndata))) s
Proof
  strip_tac >>
  gvs[compile_select_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  fs[emitted_insts_def] >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
  qabbrev_tac `a0 = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `a1 = STRING #"%" (toString (sa.cs_next_var+1))` >>
  qabbrev_tac `a2 = STRING #"%" (toString (sa.cs_next_var+2))` >>
  qabbrev_tac `a3 = STRING #"%" (toString (sa.cs_next_var+3))` >>
  qabbrev_tac `a4 = STRING #"%" (toString (sa.cs_next_var+4))` >>
  `ALL_DISTINCT [x;a0;a1;a2;a3;a4]` by
    (gvs[safe_operand_def, not_fresh_at_def, Abbr `a0`, Abbr `a1`,
         Abbr `a2`, Abbr `a3`, Abbr `a4`, ALL_DISTINCT] >> decide_tac) >>
  fs[ALL_DISTINCT, lookup_var_def] >>
  qabbrev_tac `r = n2w (LENGTH s.vs_returndata):bytes32` >>
  qabbrev_tac `c = if LENGTH s.vs_returndata < n then 1w else 0w:bytes32` >>
  qabbrev_tac `u0 = update_var a0 r s` >>
  qabbrev_tac `u1 = update_var a1 c u0` >>
  qabbrev_tac `u2 = update_var a2 (word_xor r (n2w n)) u1` >>
  qabbrev_tac `u3 = update_var a3 (c * word_xor r (n2w n)) u2` >>
  qabbrev_tac `u4 = update_var a4 (word_xor (n2w n) (c * word_xor r (n2w n))) u3` >>
  `step_inst_base (mk_inst sa.cs_next_id RETURNDATASIZE [] [a0]) s = OK u0` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accessors, opcode_case_def] >>
     simp[mk_inst_def, exec_read0_def, Abbr `u0`, Abbr `r`]) >>
  `step_inst_base (mk_inst (sa.cs_next_id+1) LT [Var a0;Lit (n2w n)] [a1]) u0 = OK u1` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accessors, opcode_case_def] >>
     simp[mk_inst_def, exec_pure2_def, Abbr `u1`, Abbr `u0`, Abbr `c`, Abbr `r`,
          eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     Cases_on `LENGTH s.vs_returndata < n` >> simp[bool_to_word_def]) >>
  `step_inst_base (mk_inst (sa.cs_next_id+2) XOR [Var a0;Lit (n2w n)] [a2]) u1 = OK u2` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accessors, opcode_case_def] >>
     simp[mk_inst_def, exec_pure2_def, Abbr `u2`, Abbr `u1`, Abbr `u0`,
          eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst (sa.cs_next_id+3) MUL [Var a1;Var a2] [a3]) u2 = OK u3` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accessors, opcode_case_def] >>
     simp[mk_inst_def, exec_pure2_def, Abbr `u3`, Abbr `u2`, Abbr `u1`,
          eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst (sa.cs_next_id+4) XOR [Lit (n2w n);Var a3] [a4]) u3 = OK u4` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accessors, opcode_case_def] >>
     simp[mk_inst_def, exec_pure2_def, Abbr `u4`, Abbr `u3`,
          eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `word_xor (n2w n) (c * word_xor r (n2w n)) = n2w (LENGTH (TAKE n s.vs_returndata)):bytes32` by
    (simp[Abbr `c`, Abbr `r`, LENGTH_TAKE_EQ] >>
     Cases_on `LENGTH s.vs_returndata < n` >> simp[arithmeticTheory.MIN_DEF] >>
     wordsLib.WORD_DECIDE_TAC) >>
  `b < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  `eval_operand (Var x) u4 = SOME (n2w b) /\
   eval_operand (Var a4) u4 = SOME (n2w (LENGTH (TAKE n s.vs_returndata)))` by
    simp[Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`, Abbr `u0`,
         eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst (sa.cs_next_id+5) MSTORE [Var x;Var a4] []) u4 =
     OK (mstore b (n2w (LENGTH (TAKE n s.vs_returndata))) u4)` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accessors, opcode_case_def] >>
     simp[mk_inst_def, exec_write2_def]) >>
  gvs[run_inst_seq_def] >>
  qabbrev_tac `Gf = DRESTRICT G (COMPL {a0;a1;a2;a3;a4})` >>
  qabbrev_tac `tn5 = tn with t_var := tn.t_var |+ (a0,{}) |+ (a1,{}) |+ (a2,{}) |+ (a3,{}) |+ (a4,{})` >>
  qabbrev_tac `tnf = tn5 with t_mem := tn.t_mem DIFF {i | b <= i /\ i < b+32}` >>
  qexistsl_tac [`Gf`, `tnf`] >>
  conj_tac >- suspend "pointer" >>
  conj_tac >- suspend "covers" >>
  conj_tac >- suspend "robust" >>
  simp[Abbr `tnf`, Abbr `tn5`] >>
  conj_tac >- suspend "oldvars" >>
  simp[Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`, Abbr `u0`,
       mstore_def, update_var_def] >> gvs[]
QED

Resume raw_call_tuple_length_checked[covers]:
  gvs[ptr_covers_def, Abbr `Gf`, Abbr `tnf`, Abbr `tn5`,
      FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def,
      Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`, Abbr `u0`,
      lookup_var_def, update_var_def, mstore_def]
QED

Resume raw_call_tuple_length_checked[robust]:
  simp[Abbr `tnf`, Abbr `tn5`, Abbr `u4`, Abbr `u3`, Abbr `u2`,
       Abbr `u1`, Abbr `u0`, update_var_def, mstore_def] >>
  mp_tac (Q.INST [`bs` |-> `TAKE n s.vs_returndata`, `cap` |-> `n`,
                  `dirty` |-> `tn.t_mem`] bytes_length_store_robust) >>
  simp[LENGTH_TAKE_EQ, mstore_def]
QED

Resume raw_call_tuple_length_checked[oldvars]:
  rpt strip_tac >>
  `v <> a0 /\ v <> a1 /\ v <> a2 /\ v <> a3 /\ v <> a4` by
    (gvs[not_fresh_at_def, Abbr `a0`, Abbr `a1`, Abbr `a2`,
         Abbr `a3`, Abbr `a4`] >> decide_tac) >>
  simp[Abbr `Gf`, FLOOKUP_DRESTRICT,
       FLOOKUP_UPDATE, op_taint_def,
       Abbr `u4`, Abbr `u3`, Abbr `u2`, Abbr `u1`, Abbr `u0`,
       update_var_def] >> gvs[]
QED

Resume raw_call_tuple_length_checked[pointer]:
  gen_tac >>
  qabbrev_tac `tn0 = tn with t_var := tn.t_var |+ (a0,{})` >>
  `step_taint (mk_inst sa.cs_next_id RETURNDATASIZE [] [a0]) s u0 tn = tn0` by
    (simp[step_taint_def, set_var_taint_def, out_taint_def, mk_inst_def,
          mem_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
          new_site_bytes_def, step_writes_def, written_taint_def,
          source_memory_write_ranges_def, range_bytes_def, Abbr `u0`,
          update_var_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss,
          taint_component_equality, Abbr `tn0`]) >>
  qabbrev_tac `tn1 = tn0 with t_var := tn0.t_var |+ (a1,{})` >>
  qabbrev_tac `tn2 = tn1 with t_var := tn1.t_var |+ (a2,{})` >>
  qabbrev_tac `tn3 = tn2 with t_var := tn2.t_var |+ (a3,{})` >>
  `step_taint (mk_inst (sa.cs_next_id+1) LT [Var a0;Lit (n2w n)] [a1])
       u0 u1 tn0 = tn1` by suspend "taint1" >>
  `step_taint (mk_inst (sa.cs_next_id+2) XOR [Var a0;Lit (n2w n)] [a2])
       u1 u2 tn1 = tn2` by suspend "taint2" >>
  `step_taint (mk_inst (sa.cs_next_id+3) MUL [Var a1;Var a2] [a3])
       u2 u3 tn2 = tn3` by suspend "taint3" >>
  `step_taint (mk_inst (sa.cs_next_id+4) XOR [Lit (n2w n);Var a3] [a4])
       u3 u4 tn3 = tn5` by suspend "taint4" >>
  `step_taint (mk_inst (sa.cs_next_id+5) MSTORE [Var x;Var a4] [])
       u4 (mstore b (n2w (LENGTH (TAKE n s.vs_returndata))) u4) tn5 = tnf`
     by suspend "taint5" >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- suspend "readsafe" >>
  simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def] >>
  simp[Once inst_seq_ptr_def, step_inst_inst_idx_indep, is_terminator_def,
       exec_result_map_def, GSYM mk_inst_def] >>
  conj_tac >- suspend "lt_safe" >>
  simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def] >>
  simp[Once inst_seq_ptr_def, step_inst_inst_idx_indep, is_terminator_def,
       exec_result_map_def, GSYM mk_inst_def] >>
  conj_tac >- suspend "xor1_safe" >>
  simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def] >>
  simp[Once inst_seq_ptr_def, step_inst_inst_idx_indep, is_terminator_def,
       exec_result_map_def, GSYM mk_inst_def] >>
  conj_tac >- suspend "mul_safe" >>
  simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def] >>
  simp[Once inst_seq_ptr_def, step_inst_inst_idx_indep, is_terminator_def,
       exec_result_map_def, GSYM mk_inst_def] >>
  conj_tac >- suspend "xor2_safe" >>
  simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def] >>
  simp[Once inst_seq_ptr_def, step_inst_inst_idx_indep, is_terminator_def,
       exec_result_map_def, GSYM mk_inst_def] >>
  conj_tac >- suspend "store_safe" >>
  simp[inst_seq_ptr_def, step_prov_def, set_prov_def, mk_inst_def,
       Abbr `Gf`] >> AP_TERM_TAC >> simp[EXTENSION] >> metis_tac[]
QED

Resume raw_call_tuple_length_checked[taint1]:
  simp[Abbr `tn1`, step_taint_def, set_var_taint_def, out_taint_def, mk_inst_def,
       mem_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
       new_site_bytes_def, step_writes_def, written_taint_def,
       source_memory_write_ranges_def, range_bytes_def, Abbr `u1`,
       update_var_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss,
       taint_component_equality] >>
  Cases_on `eval_operand (Var a0) u0` >> simp[]
QED

Resume raw_call_tuple_length_checked[taint2]:
  simp[Abbr `tn2`, step_taint_def, set_var_taint_def, out_taint_def, mk_inst_def,
       mem_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
       new_site_bytes_def, step_writes_def, written_taint_def,
       source_memory_write_ranges_def, range_bytes_def, Abbr `u2`,
       update_var_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss,
       taint_component_equality] >>
  Cases_on `eval_operand (Var a0) u1` >> simp[]
QED

Resume raw_call_tuple_length_checked[taint3]:
  simp[Abbr `tn3`, step_taint_def, set_var_taint_def, out_taint_def, mk_inst_def,
       mem_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
       new_site_bytes_def, step_writes_def, written_taint_def,
       source_memory_write_ranges_def, range_bytes_def, Abbr `u3`,
       update_var_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss,
       taint_component_equality, op_taint_def,
       Abbr `tn2`, Abbr `tn1`, Abbr `tn0`, FLOOKUP_UPDATE,
       FAPPLY_FUPDATE_THM]
QED

Resume raw_call_tuple_length_checked[taint4]:
  simp[Abbr `tn5`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`, Abbr `tn0`,
       step_taint_def, set_var_taint_def, out_taint_def, mk_inst_def,
       mem_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
       new_site_bytes_def, step_writes_def, written_taint_def,
       source_memory_write_ranges_def, range_bytes_def, Abbr `u4`,
       update_var_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss,
       taint_component_equality, eval_operand_def]
QED

Resume raw_call_tuple_length_checked[taint5]:
  `b < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  simp[Abbr `tnf`, Abbr `tn5`, step_taint_def, taint_component_equality,
       set_var_taint_def, mem_taint_def, store_taint_def, imm_taint_def,
       adopt_reset_def, new_site_bytes_def, step_writes_def, written_taint_def,
       source_memory_write_ranges_def, fixed_source_write_range_def,
       range_bytes_def, mk_inst_def, mstore_def, FLOOKUP_DEF,
       op_taint_def, FAPPLY_FUPDATE_THM, EXTENSION, SF CONJ_ss, DRESTRICT_UNIV]
QED

Resume raw_call_tuple_length_checked[readsafe]:
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def,
       exec_read0_def, update_var_def] >> rpt strip_tac >> gvs[]
QED

Resume raw_call_tuple_length_checked[lt_safe]:
  fs[allocas_from_def] >> irule scalar_ptr_inst_ok_lo >>
  simp[FAPPLY_FUPDATE_THM, scalar_shape_def, scalar_binary_def, mk_inst_def,
       op_prov_def, FLOOKUP_DRESTRICT, op_taint_def, Abbr `tn0`,
       FLOOKUP_UPDATE, allocas_from_def, Abbr `u0`, update_var_def]
  >> (gvs[])
QED

Resume raw_call_tuple_length_checked[xor1_safe]:
  fs[allocas_from_def] >> irule scalar_ptr_inst_ok_lo >>
  simp[FAPPLY_FUPDATE_THM, scalar_shape_def, scalar_binary_def, mk_inst_def,
       op_prov_def, FLOOKUP_DRESTRICT, op_taint_def, Abbr `tn1`, Abbr `tn0`,
       FLOOKUP_UPDATE, allocas_from_def, Abbr `u1`, Abbr `u0`, update_var_def] >> gvs[]
QED

Resume raw_call_tuple_length_checked[mul_safe]:
  fs[allocas_from_def] >> irule scalar_ptr_inst_ok_lo >>
  simp[FAPPLY_FUPDATE_THM, scalar_shape_def, scalar_binary_def, mk_inst_def,
       op_prov_def, FLOOKUP_DRESTRICT, op_taint_def,
       Abbr `tn2`, Abbr `tn1`, Abbr `tn0`,
       FLOOKUP_UPDATE, allocas_from_def, Abbr `u2`, Abbr `u1`, Abbr `u0`, update_var_def] >> gvs[]
QED

Resume raw_call_tuple_length_checked[xor2_safe]:
  fs[allocas_from_def] >> irule scalar_ptr_inst_ok_lo >>
  simp[FAPPLY_FUPDATE_THM, scalar_shape_def, scalar_binary_def, mk_inst_def,
       op_prov_def, FLOOKUP_DRESTRICT, op_taint_def,
       Abbr `tn3`, Abbr `tn2`, Abbr `tn1`, Abbr `tn0`,
       FLOOKUP_UPDATE, allocas_from_def,
       Abbr `u3`, Abbr `u2`, Abbr `u1`, Abbr `u0`, update_var_def] >> gvs[]
QED

Resume raw_call_tuple_length_checked[store_safe]:
  irule ptr_inst_ok_mstore_tainted >>
  simp[allocas_from_def, Abbr `u4`, Abbr `u3`, Abbr `u2`,
       Abbr `u1`, Abbr `u0`, update_var_def] >>
  conj_tac >- gvs[allocas_from_def] >>
  qpat_x_assum `ptr_covers G tn x s _` mp_tac >>
  simp[ptr_covers_def, FLOOKUP_DRESTRICT, op_taint_def,
       FAPPLY_FUPDATE_THM, FLOOKUP_UPDATE, Abbr `tn5`, lookup_var_def] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

Finalise raw_call_tuple_length_checked
