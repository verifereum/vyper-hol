(* Physical bands of the bytestring hash and digest comparison. *)
Theory entryCreateBopBytestringBands
Ancestors
  entryCreateAdminSequence entryCreateFocusSpec entryCreateCompletedCut
  createSizeCutCode exprSimAbiEncodeSiteResources localPtrsProps
  exprSimAbiGasBridge bytestringHashProps exprBopSimProps
  abiEncoderProps exprLowering exprLoweringProps fragExec emitHelper compileEnv fragFuel
  venomExecSemantics venomInst venomWf list rich_list pred_set arithmetic

(* The ID band is exact here: all its IDs are emitted, despite the presence
   of compiler temporaries. This lets us identify an installed fetch without
   requiring any successful execution of the suffix. *)
Theorem bop_bytestring_band_layout:
  (compile_bytestring_hash m a = (h,b) \/
   (if bop = vyperAST$Eq then emit_op EQ [h1;h2] a
    else emit_op ISZERO [FST (emit_op EQ [h1;h2] a)]
                         (SND (emit_op EQ [h1;h2] a))) = (h,b)) ==>
  create_cut_code {} a b /\ ci_mono a b /\
  b.cs_blocks = a.cs_blocks /\ b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  frag_code a b = emitted_insts a b /\ emitted_blocks a b = [] /\
  b.cs_next_id = a.cs_next_id + LENGTH (emitted_insts a b) /\
  MAP (\i. i.inst_id) (emitted_insts a b) =
    GENLIST (\j. a.cs_next_id + j) (LENGTH (emitted_insts a b)) /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ ~is_terminator i.inst_opcode /\
             MEM i.inst_opcode [ADD;MLOAD;SHA3;EQ;ISZERO] /\
             ~MEM i.inst_opcode [GAS;INVOKE;CREATE;CREATE2]) (emitted_insts a b)
Proof
  Cases_on `bop = vyperAST$Eq` >> simp[] >> strip_tac >>
  gvs[compile_bytestring_hash_def, emit_op_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  simp[frag_code_same_blocks, emitted_insts_def, emitted_blocks_def, create_cut_code_def,
       ci_mono_def, cs_extends_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, create_cut_targets_def, IS_PREFIX_APPEND,
       frag_ids_def, mk_inst_def, is_terminator_def, GENLIST_CONS] >>
  rpt strip_tac >> gvs[]
QED

Theorem bop_bytestring_band_raw_scope:
  (compile_bytestring_hash m a = (h,b) \/
   (if bop = vyperAST$Eq then emit_op EQ [h1;h2] a
    else emit_op ISZERO [FST (emit_op EQ [h1;h2] a)]
                         (SND (emit_op EQ [h1;h2] a))) = (h,b)) /\
  fn_has_code a b f /\ create_operand_at a s /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts a b) s = OK raw ==>
  create_operand_full_scope a b E ctx f s []
    (OK (raw with vs_inst_idx := LENGTH b.cs_current_insts))
Proof
  disch_then (CONJUNCTS_THEN2 (strip_assume_tac o MATCH_MP bop_bytestring_band_layout)
    strip_assume_tac) >>
  irule create_admin_sequence_scope >> simp[] >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem bop_bytestring_band_hit:
  (compile_bytestring_hash m a = (h,b) \/
   (if bop = vyperAST$Eq then emit_op EQ [h1;h2] a
    else emit_op ISZERO [FST (emit_op EQ [h1;h2] a)]
                         (SND (emit_op EQ [h1;h2] a))) = (h,b)) /\
  fn_has_code a b f /\ fn_inst_ids_distinct f /\
  create_interior_visit a b E ctx f (p,d,k) s (before,(key,g,i,u),after) ==>
  i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2
Proof
  disch_then (CONJUNCTS_THEN2 (strip_assume_tac o MATCH_MP bop_bytestring_band_layout)
    strip_assume_tac) >>
  `!q. MEM q (emitted_insts a b) ==> MEM q (fn_insts f)` by
    (fs[create_cut_code_def] >> metis_tac[abi_encode_frag_code_members]) >>
  `!x j. create_operand_fetch a b f x j ==> MEM j (emitted_insts a b)` by
    (rpt strip_tac >> fs[create_operand_fetch_def] >>
     drule_all lookup_block_get_instruction_fn_insts >> strip_tac >>
     `MEM j.inst_id (MAP (\q. q.inst_id) (emitted_insts a b))` by
       (simp[MEM_GENLIST, frag_ids_def] >>
        qexists_tac `j.inst_id - a.cs_next_id` >> fs[frag_ids_def] >> decide_tac) >>
     pop_assum (strip_assume_tac o REWRITE_RULE [MEM_MAP]) >>
     metis_tac[fn_inst_ids_distinct_inj]) >>
  drule create_interior_visit_cases >> strip_tac >> gvs[] >> fs[EVERY_MEM] >> metis_tac[]
QED
