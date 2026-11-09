(* Fresh two-word scratch hashing for mapping slots. *)
Theory bodyPtrPopTargetSimMapScratchRun
Ancestors bodyPtrPopTargetSimMapKeyRun exprSimMapKey exprLowering
  exprLoweringProps emitHelper emitHelperProps compileEnv context
  codegenRel ASCIInumbers rich_list venomInst
  bodyPtrEnvBuiltinsSelectorSuffix assignBasePtrLiteralGhost
  bodyPtrHashBuiltinsKeccakBytesRun bodyPtrHashBuiltinsKeccak
  exprSimPtrTopLevelImmutableCopy typedCopyPtr fragExecPtr fragGasSeqPtr
  venomState venomExecSemantics ptrDiscipline bodyPtrDefs words finite_map pred_set
  instIdxIndep exprSimHash

Theorem map_scratch_emission:
  !base key sa op sb.
    compile_mapping_subscript base key sa = (op,sb) ==>
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id ALLOCA [Lit 64w]
         [STRING #"%" (toString sa.cs_next_var)];
       mk_inst (sa.cs_next_id+1) MSTORE
         [Var (STRING #"%" (toString sa.cs_next_var));base] [];
       mk_inst (sa.cs_next_id+2) ADD
         [Var (STRING #"%" (toString sa.cs_next_var));Lit 32w]
         [STRING #"%" (toString (sa.cs_next_var+1))];
       mk_inst (sa.cs_next_id+3) MSTORE
         [Var (STRING #"%" (toString (sa.cs_next_var+1)));key] [];
       mk_inst (sa.cs_next_id+4) SHA3
         [Var (STRING #"%" (toString sa.cs_next_var));Lit 64w]
         [STRING #"%" (toString (sa.cs_next_var+2))]] /\
    op = Var (STRING #"%" (toString (sa.cs_next_var+2)))
Proof
  rpt gen_tac >>
  simp[compile_mapping_subscript_def, compile_alloc_buffer_def,
    emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_id_def, fresh_var_def, emit_def,
    emitted_insts_def, DROP_LENGTH_APPEND, arithmeticTheory.ADD_ASSOC] >>
  strip_tac >> gvs[listTheory.APPEND_ASSOC, DROP_LENGTH_APPEND]
QED

Theorem map_scratch_shape:
  !base key sa op sb.
    compile_mapping_subscript base key sa = (op,sb) ==>
    ?ia is ip ik ih p q h.
      emitted_insts sa sb =
        [mk_inst ia ALLOCA [Lit 64w] [p];
         mk_inst is MSTORE [Var p;base] [];
         mk_inst ip ADD [Var p;Lit 32w] [q];
         mk_inst ik MSTORE [Var q;key] [];
         mk_inst ih SHA3 [Var p;Lit 64w] [h]] /\
      op = Var h /\ ALL_DISTINCT [p;q;h] /\
      (!z. not_fresh_at sa z ==> z <> p /\ z <> q /\ z <> h)
Proof
  rpt gen_tac >> strip_tac >> drule map_scratch_emission >> strip_tac >>
  qexistsl_tac [`sa.cs_next_id`, `sa.cs_next_id+1`, `sa.cs_next_id+2`,
    `sa.cs_next_id+3`, `sa.cs_next_id+4`,
    `STRING #"%" (toString sa.cs_next_var)`,
    `STRING #"%" (toString (sa.cs_next_var+1))`,
    `STRING #"%" (toString (sa.cs_next_var+2))`] >>
  simp[toString_inj] >>
  rpt strip_tac >> gvs[not_fresh_at_def, toString_inj]
QED

Theorem map_scratch_store_hash_checked:
  !D ctx fn PG G tn s is ip ik ih p q h base key b root cap w0 w1.
    p <> q /\ q <> h /\ p <> h /\
    (!x. key = Var x ==> x <> q) /\
    eval_operand base s = SOME w0 /\ eval_operand key s = SOME w1 /\
    op_taint tn base = {} /\ op_taint tn key = {} /\
    lookup_var p s = SOME (n2w b) /\ FLOOKUP G p = SOME (root,cap) /\
    root <= b /\ b+64 <= root+cap /\ b+64 < dimword (:256) /\
    op_taint tn (Var p) = {} /\ ~ctx_has_dalloca ctx ==>
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst is MSTORE [Var p;base] [];
       mk_inst ip ADD [Var p;Lit 32w] [q];
       mk_inst ik MSTORE [Var q;key] [];
       mk_inst ih SHA3 [Var p;Lit 64w] [h]] s
      (DRESTRICT (G |+ (q,(root,cap))) (COMPL {h}))
      (tn with <|t_var := tn.t_var |+ (q,{}) |+ (h,{});
        t_mem := (tn.t_mem DIFF {i | b <= i /\ i < b+32})
          DIFF {i | b+32 <= i /\ i < b+64}|>)
Proof
  rpt gen_tac >> strip_tac >> rename1 `eval_operand slot s = SOME w0` >>
  `b < dimword (:256) /\ b+32 < dimword (:256)` by decide_tac >>
  qabbrev_tac `s1 = mstore b w0 s` >>
  qabbrev_tac `tn1 = tn with t_mem := tn.t_mem DIFF {i | b <= i /\ i < b+32}` >>
  `step_inst_base (mk_inst is MSTORE [Var p;slot] []) s = OK s1` by
    simp[Abbr `s1`, step_inst_base_opcode_eqs, mk_inst_def,
      exec_write2_def, eval_operand_def] >>
  `step_prov PG G (mk_inst is MSTORE [Var p;slot] []) s1 = G /\
   step_taint (mk_inst is MSTORE [Var p;slot] []) s s1 tn = tn1` by
    (simp[Abbr `s1`, Abbr `tn1`] >>
     qpat_assum `eval_operand slot s = SOME w0`
       (mp_then Any mp_tac toplevel_immutable_mstore_ghost_frame) >>
     disch_then drule >>
     disch_then (qspecl_then [`tn`, `is`, `PG`, `G`] mp_tac) >> simp[]) >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_mstore >> simp[] >>
    simp[ptr_covers_def] >> qexists_tac `n2w b` >> simp[] >> decide_tac) >>
  simp[] >> suspend "add"
QED

Resume map_scratch_store_hash_checked[add]:
  qabbrev_tac `s2 = update_var q (n2w (b+32)) s1` >>
  qabbrev_tac `G2 = G |+ (q,(root,cap))` >>
  qabbrev_tac `tn2 = tn1 with t_var := tn1.t_var |+ (q,{})` >>
  `eval_operand (Var p) s1 = SOME (n2w b)` by
    simp[Abbr `s1`, eval_operand_def, mstore_def, lookup_var_def] >>
  `step_inst_base (mk_inst ip ADD [Var p;Lit 32w] [q]) s1 = OK s2` by
    simp[Abbr `s2`, step_inst_base_opcode_eqs, mk_inst_def,
      exec_pure2_def, eval_operand_def, word_add_n2w] >>
  `step_prov PG G (mk_inst ip ADD [Var p;Lit 32w] [q]) s2 = G2 /\
   step_taint (mk_inst ip ADD [Var p;Lit 32w] [q]) s1 s2 tn1 = tn2` by
    (simp[Abbr `s2`, Abbr `G2`, Abbr `tn2`] >>
     metis_tac[hash_add_ghost]) >>
  `~is_terminator MSTORE /\ ~is_terminator ADD` by simp[is_terminator_def] >>
  simp[Once inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def] >>
  conj_tac >- (irule ptr_inst_ok_copy_len_binop >> gvs[Abbr `tn1`, op_taint_def]) >>
  simp[] >> suspend "store"
QED

Resume map_scratch_store_hash_checked[store]:
  `lookup_var q s2 = SOME (n2w (b+32)) /\
   eval_operand key s2 = SOME w1 /\ op_taint tn2 key = {} /\
   FLOOKUP G2 q = SOME (root,cap) /\ op_taint tn2 (Var q) = {}` by
    (Cases_on `key` >>
     gvs[Abbr `s2`, Abbr `s1`, Abbr `G2`, Abbr `tn2`, Abbr `tn1`,
       eval_operand_def, lookup_var_def, update_var_def, mstore_def,
       op_taint_def, FLOOKUP_UPDATE]) >>
  qabbrev_tac `s3 = mstore (b+32) w1 s2` >>
  qabbrev_tac `tn3 = tn2 with t_mem := tn2.t_mem DIFF {i | b+32 <= i /\ i < b+64}` >>
  `step_inst_base (mk_inst ik MSTORE [Var q;key] []) s2 = OK s3` by
    simp[Abbr `s3`, step_inst_base_opcode_eqs, mk_inst_def,
      exec_write2_def, eval_operand_def] >>
  `step_prov PG G2 (mk_inst ik MSTORE [Var q;key] []) s3 = G2 /\
   step_taint (mk_inst ik MSTORE [Var q;key] []) s2 s3 tn2 = tn3` by
    (simp[Abbr `s3`, Abbr `tn3`] >>
     drule_all toplevel_immutable_mstore_ghost_frame >> simp[]) >>
  simp[Once inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def] >>
  conj_tac >- (irule ptr_inst_ok_mstore >> simp[] >>
    simp[ptr_covers_def] >> qexists_tac `n2w (b+32)` >> simp[] >> decide_tac) >>
  simp[] >> suspend "hash"
QED

Resume map_scratch_store_hash_checked[hash]:
  `eval_operand (Var p) s3 = SOME (n2w b) /\
   FLOOKUP G2 p = SOME (root,cap) /\ op_taint tn3 (Var p) = {}` by
    (simp[Abbr `s3`, Abbr `s2`, Abbr `s1`, Abbr `G2`, Abbr `tn3`, Abbr `tn2`,
       Abbr `tn1`, eval_operand_def, lookup_var_def, update_var_def,
       mstore_def, op_taint_def, FLOOKUP_UPDATE] >>
     gvs[op_taint_def, lookup_var_def]) >>
  `!i. b <= i /\ i < b+64 ==> i NOTIN tn3.t_mem` by
    (simp[Abbr `tn3`, Abbr `tn2`, Abbr `tn1`] >> rpt strip_tac >> decide_tac) >>
  `step_inst_base (mk_inst ih SHA3 [Var p;Lit 64w] [h]) s3 =
    OK (update_var h (word_of_bytes T (0w:bytes32)
      (Keccak_256_w64 (mem_bytes_at b 64 s3.vs_memory))) s3)` by
    (irule step_SHA3_bytes >> simp[eval_operand_def, dimword_def]) >>
  simp[Once inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def] >>
  conj_tac >- (irule hash_sha3_inst_ok >> simp[eval_operand_def, op_taint_def] >>
    qexists_tac `n2w b` >> gvs[eval_operand_def, lookup_var_def]) >>
  `~is_terminator (mk_inst ih SHA3 [Var p;Lit 64w] [h]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  simp[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def,
    hash_sha3_ghost, Abbr `G2`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`]
QED

Finalise map_scratch_store_hash_checked
