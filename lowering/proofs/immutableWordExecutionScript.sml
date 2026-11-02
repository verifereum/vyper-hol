Theory immutableWordExecution
Ancestors
  immutableRelation context fragExec exprLoweringProps venomExecSemantics
  venomState venomInst

(* Reuse run_inst_seq: it propagates every non-OK result and its existing
   exec_block_run_inst_seq boundary accounts for the block instruction index. *)
Theorem immutable_operand_update_frame:
  (case op of Var x => x <> tmp | _ => T) ==>
  eval_operand op (update_var tmp w s) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, update_var_def, lookup_var_def,
                        finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem immutable_word_assign_zero:
  run_inst_seq [mk_inst id ASSIGN [Lit 0w] [out]] s =
    OK (update_var out 0w s)
Proof
  simp[run_inst_seq_def, mk_inst_def, step_inst_base_def,
       eval_operand_def]
QED

Theorem immutable_word_add_zero:
  eval_operand off s = SOME a /\ eval_operand region s = SOME 0w ==>
  step_inst_base (mk_inst id ADD [off; region] [tmp]) s =
    OK (update_var tmp a s)
Proof
  simp[mk_inst_def, step_inst_base_def, exec_pure2_def, wordsTheory.WORD_ADD_0]
QED

Theorem immutable_word_ctor_load:
  eval_operand off s = SOME a /\ eval_operand region s = SOME 0w ==>
  run_inst_seq
    [mk_inst id ADD [off; region] [tmp];
     mk_inst (id + 1) ILOAD [Var tmp] [out]] s =
    OK (update_var out (mload (w2n a) s) (update_var tmp a s))
Proof
  strip_tac >> simp[run_inst_seq_def, immutable_word_add_zero] >>
  simp[mk_inst_def, step_inst_base_def, exec_read1_def, exec_pure2_def, wordsTheory.WORD_ADD_0,
       eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, mload_def]
QED

Theorem immutable_word_ctor_store:
  eval_operand region s = SOME 0w /\ eval_operand off s = SOME a /\
  eval_operand value (update_var tmp a s) = SOME v ==>
  run_inst_seq
    [mk_inst id ADD [region; off] [tmp];
     mk_inst (id + 1) ISTORE [Var tmp; value] []] s =
    OK (istore (w2n a) v (update_var tmp a s))
Proof
  simp[run_inst_seq_def, mk_inst_def, step_inst_base_def,
       exec_pure2_def, wordsTheory.WORD_ADD_0, eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem immutable_word_runtime_load:
  eval_operand off s = SOME a ==>
  run_inst_seq [mk_inst id DLOAD [off] [out]] s =
    OK (update_var out
      (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) s)
Proof
  simp[run_inst_seq_def, mk_inst_def, step_inst_base_def,
       exec_read1_def]
QED

Theorem immutable_word_assign_base_zero:
  cenv.ce_imm_alloca = SOME (Var out) ==>
  run_inst_seq [mk_inst id ASSIGN [Lit 0w] [out]] s =
    OK (update_var out 0w s) /\
  immutable_base_zero cenv (update_var out 0w s)
Proof
  simp[immutable_word_assign_zero, immutable_base_zero_assigned]
QED

(* Reads and the address temporary leave both byte representations untouched. *)
Theorem immutable_word_read_frame:
  (update_var out w (update_var tmp a s)).vs_memory = s.vs_memory /\
  (update_var out w (update_var tmp a s)).vs_data_section = s.vs_data_section /\
  (update_var out w (update_var tmp a s)).vs_immutables = s.vs_immutables
Proof
  simp[update_var_def]
QED

Theorem immutable_word_store_frame:
  (istore off v (update_var tmp a s)).vs_memory = (mstore off v s).vs_memory /\
  (istore off v (update_var tmp a s)).vs_data_section = s.vs_data_section /\
  FLOOKUP (istore off v (update_var tmp a s)).vs_immutables off = SOME v
Proof
  simp[istore_def, mstore_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem immutable_word_ctor_store_fresh:
  eval_operand region s = SOME 0w /\ eval_operand off s = SOME a /\
  eval_operand value s = SOME v /\
  (case value of Var x => x <> tmp | _ => T) ==>
  run_inst_seq
    [mk_inst id ADD [region; off] [tmp];
     mk_inst (id + 1) ISTORE [Var tmp; value] []] s =
    OK (istore (w2n a) v (update_var tmp a s))
Proof
  strip_tac >> irule immutable_word_ctor_store >> fs[] >>
  drule immutable_operand_update_frame >> simp[]
QED

(* Compilation-to-execution interfaces for the exact generated suffix. The
   store's value stability premise is explicit: freshness is not implied by
   the compiler's numeric supply in an arbitrary semantic state. *)
Theorem compile_imm_load_word_ctor_execution:
  compile_imm_load_word T (SOME region) off st = (result, st') /\
  eval_operand off s = SOME a /\ eval_operand region s = SOME 0w ==>
  run_inst_seq (emitted_insts st st') s =
    OK (update_var ("%" ++ toString (st.cs_next_var + 1)) (mload (w2n a) s)
      (update_var ("%" ++ toString st.cs_next_var) a s))
Proof
  strip_tac >> drule compile_imm_load_word_ctor_result >> strip_tac >>
  simp[emitted_insts_def, listTheory.DROP_APPEND] >> irule immutable_word_ctor_load >> simp[]
QED

Theorem compile_imm_store_word_execution:
  compile_imm_store_word (SOME region) off value st = ((), st') /\
  eval_operand region s = SOME 0w /\ eval_operand off s = SOME a /\
  eval_operand value (update_var ("%" ++ toString st.cs_next_var) a s) = SOME v ==>
  run_inst_seq (emitted_insts st st') s =
    OK (istore (w2n a) v (update_var ("%" ++ toString st.cs_next_var) a s))
Proof
  strip_tac >> drule compile_imm_store_word_result >> strip_tac >>
  simp[emitted_insts_def, listTheory.DROP_APPEND] >> irule immutable_word_ctor_store >> fs[]
QED

Theorem immutable_word_ctor_load_continuation:
  isPREFIX [mk_inst id ADD [off; region] [tmp];
            mk_inst (id + 1) ILOAD [Var tmp] [out]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand off s = SOME a /\ eval_operand region s = SOME 0w ==>
  exec_block fuel ctx bb s =
    exec_block fuel ctx bb
      ((update_var out (mload (w2n a) s) (update_var tmp a s))
        with vs_inst_idx := s.vs_inst_idx + 2)
Proof
  strip_tac >>
  `run_inst_seq [mk_inst id ADD [off; region] [tmp];
     mk_inst (id + 1) ILOAD [Var tmp] [out]] s =
   OK (update_var out (mload (w2n a) s) (update_var tmp a s))` by
    (irule immutable_word_ctor_load >> simp[]) >>
  drule exec_block_run_inst_seq >>
  simp[mk_inst_def, is_terminator_def] >>
  fs[mk_inst_def] >> metis_tac[]
QED

Theorem immutable_word_ctor_store_continuation:
  isPREFIX [mk_inst id ADD [region; off] [tmp];
            mk_inst (id + 1) ISTORE [Var tmp; value] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand region s = SOME 0w /\ eval_operand off s = SOME a /\
  eval_operand value (update_var tmp a s) = SOME v ==>
  exec_block fuel ctx bb s =
    exec_block fuel ctx bb
      ((istore (w2n a) v (update_var tmp a s))
        with vs_inst_idx := s.vs_inst_idx + 2)
Proof
  strip_tac >>
  `run_inst_seq [mk_inst id ADD [region; off] [tmp];
     mk_inst (id + 1) ISTORE [Var tmp; value] []] s =
   OK (istore (w2n a) v (update_var tmp a s))` by
    (irule immutable_word_ctor_store >> simp[]) >>
  drule exec_block_run_inst_seq >>
  simp[mk_inst_def, is_terminator_def] >>
  fs[mk_inst_def] >> metis_tac[]
QED

Theorem compile_fixed_region_execution:
  compile_fixed_region_with_id nbytes st = ((id, buf), st') ==>
  run_inst_seq (emitted_insts st st') s =
    OK (update_var ("%" ++ toString st.cs_next_var) 0w s) /\
  eval_operand buf.buf_operand
    (update_var ("%" ++ toString st.cs_next_var) 0w s) = SOME 0w
Proof
  strip_tac >> drule compile_fixed_region_with_id_result >> strip_tac >>
  simp[emitted_insts_def, listTheory.DROP_APPEND, immutable_word_assign_zero,
       eval_operand_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem compile_imm_load_word_runtime_execution:
  compile_imm_load_word F imm off st = (result, st') /\
  eval_operand off s = SOME a ==>
  run_inst_seq (emitted_insts st st') s =
    OK (update_var ("%" ++ toString st.cs_next_var)
      (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) s)
Proof
  simp[compile_imm_load_word_runtime, emitHelperTheory.emit_op_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, listTheory.DROP_APPEND, immutable_word_runtime_load]
QED

Theorem immutable_word_read_preserves_relation:
  immutables_rel cenv addr src ctor vs s ==>
  immutables_rel cenv addr src ctor vs (update_var out w (update_var tmp a s))
Proof
  strip_tac >> irule immutable_relation_same_bytes >>
  qexists_tac `s` >> simp[update_var_def]
QED

Theorem immutable_word_istore_operand_frame:
  eval_operand op (istore off v s) = eval_operand op s
Proof
  Cases_on `op` >>
  simp[eval_operand_def, istore_def, mstore_def, lookup_var_def]
QED

Theorem immutable_word_runtime_load_continuation:
  isPREFIX [mk_inst id DLOAD [off] [out]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand off s = SOME a ==>
  exec_block fuel ctx bb s =
    exec_block fuel ctx bb
      ((update_var out
        (word_of_bytes T (0w:bytes32)
          (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) s)
        with vs_inst_idx := s.vs_inst_idx + 1)
Proof
  strip_tac >>
  `run_inst_seq [mk_inst id DLOAD [off] [out]] s =
   OK (update_var out
      (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) s)` by
    (irule immutable_word_runtime_load >> simp[]) >>
  drule exec_block_run_inst_seq >>
  simp[mk_inst_def, is_terminator_def] >>
  fs[mk_inst_def] >> metis_tac[]
QED

val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then
       print ("IMMUTABLE_WORD_KERNEL_CLOSED " ^ name ^ "\n")
     else raise Fail ("Unclosed immutable word theorem: " ^ name)
  end) (DB.thms "immutableWordExecution");
