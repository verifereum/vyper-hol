Theory stmtSimCustomErrorMemCopyPrimitive
Ancestors
  placeMemoryTypedPrimitive bodyCopyMemory exprSimMemUnwrap
  externalReturnNormalizeMem list venomState venomExecSemantics
  placeMemoryTypedBase exprSimBufferStore bodyMemAggregateStore
  context compileEnv exprLoweringProps valueCopyBytes typedCopyAgreement
  vfmConstants

Theorem compile_copy_memory_checked_path:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  n < dimword (:256) /\
  w2n sw + n <= s.vs_alloca_next /\
  w2n dw + n <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  let t = (if n = 0 then s else mcopy (w2n dw) (w2n sw) n s)
            with vs_inst_idx := LENGTH sb.cs_current_insts in
  gas_path_mem ctx func s 0 (OK t) /\
  alloca_history func t /\ ~t.vs_halted /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  drule_all compile_copy_memory_sequence >> strip_tac >>
  drule_all compile_copy_memory_body_mem_ok >> strip_tac >>
  simp[LET_THM] >>
  qmatch_goalsub_abbrev_tac `gas_path_mem ctx func s 0 (OK (u with vs_inst_idx := _))` >>
  `gas_path_mem ctx func s 0 (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb` by
    (irule straight_path_mem >> simp[] >> qexists_tac `sa` >>
     simp[EVERY_MEM] >> gvs[EVERY_MEM]) >>
  simp[] >> Cases_on `n = 0` >>
  gvs[Abbr `u`, mcopy_def, write_memory_with_expansion_def]
QED

Theorem typed_memory_word_checked_path:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  is_word_type dty /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME d /\
  w2n a + 32 <= s.vs_alloca_next /\ w2n d + 32 <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\ alloca_history func t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_memory = (mstore (w2n d) (mload (w2n a) s) s).vs_memory
Proof
  strip_tac >>
  `!x. dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all typed_memory_word_sequence >> strip_tac >>
  drule_all typed_copy_word_mem_ok >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ s = OK u` >>
  `gas_path_mem ctx func s 0 (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb` by
    (irule straight_path_mem >> simp[] >> qexists_tac `sa` >>
     simp[EVERY_MEM] >> gvs[EVERY_MEM]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[Abbr `u`, mstore_def, update_var_def, write_memory_with_expansion_def]
QED

Theorem store_bytestring_checked_path:
  compile_store_bytestring src dst sa = ((),sb) /\
  is_bytestring_type ty /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  mload (w2n p) s = n2w len /\
  32 + 32 * word_size len < dimword (:256) /\
  w2n p + (32 + 32 * word_size len) <= s.vs_alloca_next /\
  w2n d + (32 + 32 * word_size len) <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\ alloca_history func t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_memory = (mcopy (w2n d) (w2n p) (32 + 32 * word_size len) s).vs_memory /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  drule_all buffer_store_bytestring_run >> strip_tac >>
  drule buffer_store_bytestring_shape >> strip_tac >>
  drule_all store_bytestring_mem_ok >> strip_tac >>
  `compile_store_memory ARB src dst ty ty sa = ((),sb)` by
    simp[compile_store_memory_def, is_bytestring_word_type] >>
  drule aggregate_store_memory_no_gas >> strip_tac >>
  `gas_path_mem ctx func s 0 (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   alloca_history func (q with vs_inst_idx := LENGTH sb.cs_current_insts) /\
   ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb` by
    (irule straight_path_mem >> simp[] >> qexists_tac `sa` >> simp[]) >>
  qexists_tac `q with vs_inst_idx := LENGTH sb.cs_current_insts` >> simp[] >>
  conj_tac
  >- (qpat_x_assum `_ = s` (mp_tac o Q.AP_TERM `\z. z.vs_alloca_next`) >> simp[]) >>
  gvs[lookup_var_def]
QED

(* Exercise tuple dispatch and its recursive field continuation, not just
   the primitive compiler in isolation. *)
Theorem widened_single_bytes_field_checked[local]:
  compile_store_memory_typed cenv dst
    (TupleT [BaseT (BytesT (Dynamic 2))]) src
    (TupleT [BaseT (BytesT (Dynamic 1))]) sa = ((),sb) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  mload (w2n p) s = n2w len /\ len <= 1 /\
  64 < dimword (:256) /\
  w2n p + 64 <= s.vs_alloca_next /\ w2n d + 64 <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\ alloca_history func t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `compile_store_bytestring src dst sa = ((),sb)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def, is_word_type_def,
          is_bytestring_type_def] >>
     simp[Once compile_store_memory_typed_def, compile_with_byte_offset_def,
          comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
     simp[compile_store_memory_typed_bytes, is_bytestring_type_def] >>
     simp[Once compile_store_memory_typed_def, comp_bind_def,
          comp_return_def, comp_ignore_bind_def] >>
     pairarg_tac >> simp[]) >>
  `32 + 32 * word_size len <= 64` by
    (`len = 0 \/ len = 1` by decide_tac >> gvs[word_size_def]) >>
  drule store_bytestring_checked_path >>
  disch_then (qspec_then `BaseT (BytesT (Dynamic 1))` mp_tac) >>
  simp[is_bytestring_type_def] >>
  strip_tac >>
  `32 * word_size len + 32 < dimword (:256) /\
   w2n p + (32 * word_size len + 32) <= s.vs_alloca_next /\
   w2n d + (32 * word_size len + 32) <= s.vs_alloca_next` by decide_tac >>
  first_x_assum drule_all >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[]
QED
