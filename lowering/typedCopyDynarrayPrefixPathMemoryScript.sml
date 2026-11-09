(* Reachable safe execution of the dynamic typed-copy prologue. *)
Theory typedCopyDynarrayPrefixPathMemory
Ancestors
  typedNormalizeDynarray typedCopyDynarrayMemory placedSequenceMemory
  typedMemoryCopy context compileEnv emitHelper emitHelperProps
  exprLoweringProps venomExecSemantics venomInst venomState venomMemDefs
  valueEncoding valueEncodingProps words list rich_list arithmetic

Theorem typed_copy_dyn_prefix_sequence[local]:
  emit_op MLOAD [src] a = (length,a1) /\
  emit_op GT [length; Lit (n2w C)] a1 = (too_long,a2) /\
  emit_op ISZERO [too_long] a2 = (ok,a3) /\
  emit_void ASSERT [ok] a3 = ((),a4) /\
  emit_void MSTORE [dst; length] a4 = ((),a5) /\
  emit_op ADD [src; Lit 32w] a5 = (sd,a6) /\
  emit_op ADD [dst; Lit 32w] a6 = (dd,b) ==>
  same_blocks a b /\ isPREFIX a.cs_current_insts b.cs_current_insts /\
  length = Var ("%" ++ toString a.cs_next_var) /\
  sd = Var ("%" ++ toString (a.cs_next_var+3)) /\
  dd = Var ("%" ++ toString (a.cs_next_var+4)) /\
  emitted_insts a b =
    [mk_inst a.cs_next_id MLOAD [src] ["%" ++ toString a.cs_next_var];
     mk_inst (a.cs_next_id+1) GT [length; Lit (n2w C)]
       ["%" ++ toString (a.cs_next_var+1)];
     mk_inst (a.cs_next_id+2) ISZERO [too_long]
       ["%" ++ toString (a.cs_next_var+2)];
     mk_inst (a.cs_next_id+3) ASSERT [ok] [];
     mk_inst (a.cs_next_id+4) MSTORE [dst; length] [];
     mk_inst (a.cs_next_id+5) ADD [src; Lit 32w]
       ["%" ++ toString (a.cs_next_var+3)];
     mk_inst (a.cs_next_id+6) ADD [dst; Lit 32w]
       ["%" ++ toString (a.cs_next_var+4)]] /\
  too_long = Var ("%" ++ toString (a.cs_next_var+1)) /\
  ok = Var ("%" ++ toString (a.cs_next_var+2))
Proof
  simp[emit_op_def, emit_void_def, emit_inst_def, fresh_var_def,
       fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >>
  simp[same_blocks_def, IS_PREFIX_APPEND, emitted_insts_def,
       DROP_LENGTH_APPEND, APPEND_ASSOC, ADD_ASSOC]
QED

Theorem typed_copy_dynarray_prefix_path_mem:
  emit_op MLOAD [src] a = (length,a1) /\
  emit_op GT [length; Lit (n2w C)] a1 = (too_long,a2) /\
  emit_op ISZERO [too_long] a2 = (ok,a3) /\
  emit_void ASSERT [ok] a3 = ((),a4) /\
  emit_void MSTORE [dst; length] a4 = ((),a5) /\
  emit_op ADD [src; Lit 32w] a5 = (sd,a6) /\
  emit_op ADD [dst; Lit 32w] a6 = (dd,b) /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  LENGTH vs <= C /\ C < dimword (:256) /\
  val_wf (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
    (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) < dimword (:256) /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic C)) < dimword (:256) /\
  (w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= w2n dw \/
   w2n dw + type_memory_size (ArrayTV dtv (Dynamic C)) <= w2n sw) /\
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= s.vs_alloca_next /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic C)) <= s.vs_alloca_next /\
  fn_has_code a b func /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    eval_operand length t = SOME (n2w (LENGTH vs)) /\
    eval_operand sd t = SOME (sw + 32w) /\ eval_operand dd t = SOME (dw + 32w) /\
    mem_bytes_at (w2n dw) 32 t.vs_memory = word_to_bytes (n2w (LENGTH vs) : bytes32) T /\
    (!i. i < LENGTH vs ==> val_in_memory stv (EL i vs)
       (w2n sw + 32 + i * type_memory_size stv) t.vs_memory) /\
    typed_copy_state_frame a (w2n dw) 32 s t /\
    t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\ ~t.vs_halted
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all typed_copy_dyn_prefix_sequence >> strip_tac >>
  suspend "run"
QED

Resume typed_copy_dynarray_prefix_path_mem[run]:
  `ALL_DISTINCT ["%" ++ toString a.cs_next_var;
    "%" ++ toString (a.cs_next_var+1); "%" ++ toString (a.cs_next_var+2);
    "%" ++ toString (a.cs_next_var+3); "%" ++ toString (a.cs_next_var+4)]` by
    simp[ASCIInumbersTheory.toString_inj] >>
  `!x. src = Var x \/ dst = Var x ==>
    ~MEM x ["%" ++ toString a.cs_next_var;
    "%" ++ toString (a.cs_next_var+1); "%" ++ toString (a.cs_next_var+2);
    "%" ++ toString (a.cs_next_var+3); "%" ++ toString (a.cs_next_var+4)]` by
    (rpt gen_tac >> disch_tac >>
     `not_fresh_at a x` by metis_tac[] >>
     gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
     rpt strip_tac >> gvs[ASCIInumbersTheory.toString_inj]) >>
  `mload (w2n sw) s = n2w (LENGTH vs)` by
    gvs[typed_copy_dynarray_representation, mload_def, mem_word_at_def] >>
  `32 <= type_memory_size (ArrayTV stv (Dynamic scap)) /\
   32 <= type_memory_size (ArrayTV dtv (Dynamic C))` by
    simp[type_memory_size_def] >>
  map_every (fn pat => qpat_x_assum pat SUBST_ALL_TAC)
    [`length = _`, `too_long = _`, `ok = _`, `sd = _`, `dd = _`] >>
  drule_all typed_dynarray_prologue_window_run >> strip_tac >>
  suspend "lift"
QED
Resume typed_copy_dynarray_prefix_path_mem[lift]:
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts a b) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts a b) = []` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all placed_sequence_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `q with vs_inst_idx := LENGTH b.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def, GSYM word_add_n2w] >>
  suspend "posts"
QED
Resume typed_copy_dynarray_prefix_path_mem[posts]:
  ntac 3 (conj_tac >-
    gvs[eval_operand_def, lookup_var_def, GSYM word_add_n2w]) >>
  conj_tac >- simp[mem_bytes_at_mstore_same] >>
  `typed_copy_state_frame a (w2n dw) 32 s
     (q with vs_inst_idx := LENGTH b.cs_current_insts)` by
    suspend "frame" >>
  simp[] >>
  `val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
      (w2n sw) q.vs_memory` suffices_by
    gvs[typed_copy_dynarray_representation] >>
  irule typed_copy_frame_preserves_source >> conj_tac >- simp[] >>
  qexistsl_tac [`32`, `w2n dw`, `s.vs_memory`] >> simp[] >>
  gvs[typed_copy_state_frame_def]
QED
Resume typed_copy_dynarray_prefix_path_mem[frame]:
  simp[typed_copy_state_frame_def, typed_copy_frame_def] >>
  conj_tac >- gvs[venom_state_component_equality] >>
  conj_tac
  >- (rpt strip_tac >> simp[lookup_var_def] >>
      qpat_x_assum `!x. ~MEM x _ ==> _` (qspec_then `x` mp_tac) >>
      `~MEM x ["%" ++ toString a.cs_next_var;
        "%" ++ toString (a.cs_next_var+1); "%" ++ toString (a.cs_next_var+2);
        "%" ++ toString (a.cs_next_var+3); "%" ++ toString (a.cs_next_var+4)]` by
        (gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
         rpt strip_tac >> gvs[ASCIInumbersTheory.toString_inj]) >>
      simp[lookup_var_def]) >>
  conj_tac >- metis_tac[] >>
  simp[immutableMemoryFrameTheory.immutable_mstore_capacity, MAX_DEF]
QED
Finalise typed_copy_dynarray_prefix_path_mem
