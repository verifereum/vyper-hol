(* Task-owned raw memory copy execution; zero bytes carry no source bound. *)
Theory externalReturnCopyBulk
Ancestors
  externalReturnCopyTransport externalReturnCopyBoundary
  context compileEnv emitHelper emitHelperProps fragExec exprLoweringProps
  venomExecSemantics venomState venomInst words arithmetic
  immutableMemoryFrame valueEncoding valueEncodingProps valueEncodingProofs valueCopy
  externalReturnCopyFrame externalReturnCopyArrayLoop externalReturnCopyDynamic

Theorem return_copy_mcopy_frag:
  emit_void MCOPY [dst; src; Lit (n2w n)] sa = ((),sb) /\
  eval_operand dst s0 = SOME d /\ eval_operand src s0 = SOME a /\
  n < dimword (:256) ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\t. t = ((mcopy (w2n d) (w2n a) n s0)
                with vs_inst_idx := LENGTH sb.cs_current_insts)) (\r. F)
Proof
  strip_tac >> drule_all emit_mcopy_run >> strip_tac >>
  irule frag_exec_run_inst_seq >>
  gvs[same_blocks_def] >> simp[]
QED

Theorem return_copy_fixed_raw_frag:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s0 = SOME d /\ eval_operand src s0 = SOME a /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\ n < dimword (:256) ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\t. t = ((if n = 0 then s0 else mcopy (w2n d) (w2n a) n s0)
                with vs_inst_idx := LENGTH sb.cs_current_insts)) (\r. F)
Proof
  Cases_on `n` >> simp[compile_copy_memory_def, comp_return_def] >> strip_tac
  >- (gvs[] >> irule frag_exec_refl >> simp[venom_state_component_equality]) >>
  irule return_copy_mcopy_frag >> simp[] >> qexistsl_tac [`dst`, `src`] >> simp[]
QED

Theorem return_copy_dynamic_run_seq:
  compile_copy_memory_dynamic dst src len sa = ((),sb) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
  eval_operand len s = SOME w ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK (mcopy (w2n d) (w2n a) (w2n w) s)
Proof
  simp[compile_copy_memory_dynamic_def] >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  simp[same_blocks_def, mk_inst_def,
       is_terminator_def, run_inst_seq_def] >>
  gvs[emit_void_def, comp_bind_def, fresh_id_def, emit_def,
      comp_ignore_bind_def, comp_return_def] >>
  simp[step_inst_base_def, mk_inst_def]
QED

Theorem return_copy_dynamic_raw_frag:
  compile_copy_memory_dynamic dst src len sa = ((),sb) /\
  eval_operand dst s0 = SOME d /\ eval_operand src s0 = SOME a /\
  eval_operand len s0 = SOME w ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\t. t = ((mcopy (w2n d) (w2n a) (w2n w) s0)
                with vs_inst_idx := LENGTH sb.cs_current_insts)) (\r. F)
Proof
  strip_tac >> drule_all return_copy_dynamic_run_seq >> strip_tac >>
  irule frag_exec_run_inst_seq >> gvs[same_blocks_def] >> simp[]
QED

Theorem return_copy_mcopy_state_frame:
  return_copy_frame sa dst n s
    ((mcopy dst src n s) with vs_inst_idx := idx)
Proof
  rw[return_copy_frame_def]
  >- simp[mcopy_def, write_memory_with_expansion_def,
          venom_state_component_equality]
  >- simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
  simp[return_copy_memory_frame_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule mem_bytes_at_mcopy_disjoint >> simp[]) >>
  simp[mcopy_def, immutable_write_memory_capacity, MAX_DEF]
QED

(* Zero dynamic copying still executes, possibly expanding destination memory,
   but never reads or depends on the source address. *)
Theorem return_copy_mcopy_zero_source:
  mcopy dst src 0 s = mcopy dst 0 0 s
Proof
  simp[mcopy_def]
QED

Theorem return_copy_dynamic_zero_frag:
  compile_copy_memory_dynamic dst src len sa = ((),sb) /\
  eval_operand dst s0 = SOME d /\ eval_operand src s0 = SOME a /\
  eval_operand len s0 = SOME 0w ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\t. t = ((mcopy (w2n d) 0 0 s0)
               with vs_inst_idx := LENGTH sb.cs_current_insts)) (\r. F)
Proof
  strip_tac >> drule_all return_copy_dynamic_raw_frag >>
  simp[return_copy_mcopy_zero_source]
QED

Theorem return_copy_mcopy_indexed:
  (!i. i < N ==> val_wf tv (f i) /\
    val_in_memory tv (f i) (src + i * type_memory_size tv) s.vs_memory) ==>
  !i. i < N ==> val_in_memory tv (f i)
    (dst + i * type_memory_size tv)
    (mcopy dst src (N * type_memory_size tv) s).vs_memory
Proof
  rpt strip_tac >> irule val_in_memory_relocate >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`src + i * type_memory_size tv`, `type_memory_size tv`, `s.vs_memory`] >>
  simp[] >> conj_tac
  >- metis_tac[return_footprint_le_layout] >>
  irule valueEncodingProofsTheory.mem_bytes_at_translated_window >>
  qexists_tac `N * type_memory_size tv` >>
  simp[mcopy_mem_bytes_at_same] >>
  `SUC i <= N` by decide_tac >>
  irule LESS_EQ_TRANS >> qexists_tac `SUC i * type_memory_size tv` >>
  simp[MULT_CLAUSES]
QED

Theorem return_copy_sarray_bulk_frag:
  compile_copy_sarray_typed cenv dst dty src sty N sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size tv /\
  type_memory_bytes cenv sty = type_memory_size tv /\
  ~is_abi_dynamic cenv.ce_struct_fields dty /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  N * type_memory_size tv < dimword (:256) /\
  (!i. i < N ==> val_wf tv (f i) /\
    val_in_memory tv (f i) (w2n sw + i * type_memory_size tv) s.vs_memory) ==>
  frag_exec ctx sa sb (\u. u = s)
    (\t. (!i. i < N ==> val_in_memory tv (f i)
        (w2n dw + i * type_memory_size tv) t.vs_memory) /\
      return_copy_frame sa (w2n dw) (N * type_memory_size tv) s t) (\r. F)
Proof
  strip_tac >>
  `compile_copy_memory dst src (N * type_memory_size tv) sa = ((),sb)` by
    (qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def]) >>
  drule_all return_copy_fixed_raw_frag >>
  disch_then (qspec_then `ctx` (mp_then Any irule frag_exec_conseq)) >> simp[] >>
  Cases_on `N * type_memory_size tv = 0` >> simp[]
  >- (conj_tac
      >- (rpt strip_tac >>
          `type_memory_size tv = 0` by gvs[] >>
          simp[] >> metis_tac[return_zero_layout_memory_address]) >>
      `N = 0 \/ type_memory_size tv = 0` by gvs[] >>
      simp[return_copy_frame_def, lookup_var_def, venom_state_component_equality]) >>
  `type_memory_size tv <> 0 /\ N <> 0` by gvs[] >> simp[] >>
  conj_tac
  >- (match_mp_tac return_copy_mcopy_indexed >> simp[]) >>
  irule return_copy_mcopy_state_frame
QED

Theorem return_copy_dynarray_bulk_data_frag:
  emit_op MUL [length; Lit (n2w (type_memory_size tv))] sa = (bytes,b) /\
  compile_copy_memory_dynamic dst src bytes b = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand length s = SOME (n2w N) /\
  (!i. i < N ==> val_wf tv (f i) /\
    val_in_memory tv (f i) (w2n sw + i * type_memory_size tv) s.vs_memory) /\
  N * type_memory_size tv < dimword (:256) ==>
  frag_exec ctx sa sb (\u. u = s)
    (\t. (!i. i < N ==> val_in_memory tv (f i)
      (w2n dw + i * type_memory_size tv) t.vs_memory) /\
      return_copy_frame sa (w2n dw) (N * type_memory_size tv) s t) (\r. F)
Proof
  strip_tac >>
  `frag_exec ctx sa b (\u. u = s)
     (\t. eval_operand bytes t = SOME (n2w (N * type_memory_size tv)) /\
          t.vs_memory = s.vs_memory /\
          return_copy_frame sa (w2n dw) (N * type_memory_size tv) s t) (\r. F)` by
    (irule return_copy_emit_op_frag >> simp[is_terminator_def] >>
     goal_assum (drule_at Any) >>
     simp[is_terminator_def, step_inst_base_opcode_eqs, mk_inst_def,
          exec_pure2_def, eval_operand_def, GSYM word_mul_n2w]) >>
  drule frag_exec_then >> disch_then irule >> simp[emit_op_extends] >>
  conj_tac
  >- (rpt strip_tac >>
      `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
        metis_tac[return_copy_frame_operand] >>
      drule_all return_copy_dynamic_raw_frag >>
      disch_then (qspec_then `ctx` (mp_then Any irule frag_exec_conseq)) >>
      simp[w2n_n2w, LESS_MOD] >> conj_tac
      >- (match_mp_tac return_copy_mcopy_indexed >> simp[]) >>
      irule return_copy_frame_trans >> qexists_tac `t` >>
      simp[return_copy_mcopy_state_frame]) >>
  conj_tac
  >- (gvs[compile_copy_memory_dynamic_def] >>
      `ci_mono b sb` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
      gvs[ci_mono_def]) >>
  drule return_copy_emit_op_mono >> simp[ci_mono_def]
QED

Theorem return_copy_dynarray_bulk_frag:
  compile_copy_dynarray_typed cenv dst dty capacity src sty sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size tv /\
  type_memory_bytes cenv sty = type_memory_size tv /\ dty = sty /\
  N <= capacity /\ capacity < dimword (:256) /\
  (!i. i < N ==> val_wf tv (f i)) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  mload (w2n sw) s = n2w N /\
  (!i. i < N ==> val_in_memory tv (f i)
     (w2n sw + 32 + i * type_memory_size tv) s.vs_memory) /\
  w2n dw + 32 + capacity * type_memory_size tv < dimword (:256) /\
  (!i. i < N /\ 0 < val_footprint tv (f i) ==>
    w2n sw + 32 + i * type_memory_size tv + val_footprint tv (f i) < dimword (:256) /\
    (w2n sw + 32 + i * type_memory_size tv + val_footprint tv (f i) <= w2n dw \/
     w2n dw + 32 + capacity * type_memory_size tv <= w2n sw + 32 + i * type_memory_size tv)) ==>
  frag_exec ctx sa sb (\u. u = s)
    (\t. mem_word_at (w2n dw) t.vs_memory = n2w N /\
         (!i. i < N ==> val_in_memory tv (f i)
           (w2n dw + 32 + i * type_memory_size tv) t.vs_memory) /\
         return_copy_frame sa (w2n dw) (32 + capacity * type_memory_size tv) s t) (\r. F)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gnvs[] >>
  rename1 `emit_op MLOAD [src] sa = (length,a1)` >>
  rename1 `emit_op GT [length; Lit (n2w capacity)] a1 = (too_long,a2)` >>
  rename1 `emit_op ISZERO [too_long] a2 = (ok,a3)` >>
  rename1 `emit_void ASSERT [ok] a3 = ((),a4)` >>
  rename1 `emit_void MSTORE [dst; length] a4 = ((),a5)` >>
  rename1 `emit_op ADD [src; Lit 32w] a5 = (src_data,a6)` >>
  rename1 `emit_op ADD [dst; Lit 32w] a6 = (dst_data,start)` >>
  rename1 `emit_op MUL _ start = (bytes,last)` >>
  `ci_mono sa a1 /\ ci_mono a1 a2 /\ ci_mono a2 a3 /\ ci_mono a3 a4 /\
   ci_mono a4 a5 /\ ci_mono a5 a6 /\ ci_mono a6 start /\ ci_mono start last /\ ci_mono last sb` by
    metis_tac[return_copy_emit_op_mono, ci_mono_emit_void, pairTheory.SND, compile_copy_memory_dynamic_def] >>
  `ci_mono sa start /\ ci_mono a1 start /\ ci_mono sa sb` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `(!x. length = Var x ==> not_fresh_at start x) /\
   (!x. src_data = Var x ==> not_fresh_at start x) /\
   (!x. dst_data = Var x ==> not_fresh_at start x)` by
    metis_tac[return_copy_emit_op_fresh, return_copy_operand_fresh_mono] >>
  `frag_exec ctx sa start (\u. u = s)
    (\t. eval_operand length t = SOME (n2w N) /\
         eval_operand src_data t = SOME (sw + 32w) /\
         eval_operand dst_data t = SOME (dw + 32w) /\
         mem_word_at (w2n dw) t.vs_memory = n2w N /\
         return_copy_frame sa (w2n dw) 32 s t) (\r. F)` by
    (irule return_copy_dynamic_setup_frag >> simp[] >>
     goal_assum (drule_at (Pat `emit_op MLOAD _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op GT _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ISZERO [too_long] _ = _`)) >>
     goal_assum (drule_at (Pat `emit_void ASSERT _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_void MSTORE _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD [src; Lit 32w] _ = _`)) >> simp[]) >>
  drule frag_exec_then >> disch_then irule >> conj_tac
  >- suspend "continuation" >>
  gvs[ci_mono_def] >> metis_tac[cs_extends_trans]
QED

Resume return_copy_dynarray_bulk_frag[continuation]:
  rpt strip_tac >> gvs[] >>
  `w2n (dw + 32w) = w2n dw + 32 /\
   w2n (dw + 32w) + N * type_memory_size tv < dimword (:256)` by
    (irule return_copy_dynamic_data_window >> qexists_tac `capacity` >> simp[]) >>
  `N * type_memory_size tv < dimword (:256)` by decide_tac >>
  `!i. i < N ==> val_in_memory tv (f i)
    (w2n (sw + 32w) + i * type_memory_size tv) t.vs_memory` by
    (rpt strip_tac >> irule return_copy_dynamic_source_after_setup >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`capacity`, `type_memory_size tv`, `dw`, `s`, `sa`] >>
     simp[] >> metis_tac[]) >>
  `frag_exec ctx start sb (\u. u = t)
    (\u. (!i. i < N ==> val_in_memory tv (f i)
      (w2n (dw + 32w) + i * type_memory_size tv) u.vs_memory) /\
      return_copy_frame start (w2n (dw + 32w)) (N * type_memory_size tv) t u) (\r. F)` by
    (irule return_copy_dynarray_bulk_data_frag >> simp[] >>
     goal_assum (drule_at (Pat `emit_op MUL _ _ = _`)) >>
     goal_assum (drule_at (Pat `compile_copy_memory_dynamic _ _ _ _ = _`)) >> simp[]) >>
  pop_assum (mp_then Any irule frag_exec_conseq) >> simp[] >>
  rpt strip_tac >> rename1 `return_copy_frame start _ _ t u` >>
  `mem_word_at (w2n dw) u.vs_memory = mem_word_at (w2n dw) t.vs_memory` by
    (irule return_copy_dynamic_header_frame >>
     goal_assum (drule_at Any) >> simp[]) >>
  simp[] >>
  `N * type_memory_size tv <= capacity * type_memory_size tv` by
    simp[LE_MULT_RCANCEL] >>
  irule return_copy_frame_trans >> qexists_tac `t` >> conj_tac
  >- (irule return_copy_frame_subinterval >>
      qexistsl_tac [`w2n dw`, `32`] >> simp[]) >>
  irule return_copy_frame_subinterval >>
  qexistsl_tac [`w2n dw + 32`, `N * type_memory_size tv`] >>
  simp[] >> irule return_copy_frame_mono >>
  qexists_tac `start` >> simp[]
QED
Finalise return_copy_dynarray_bulk_frag
