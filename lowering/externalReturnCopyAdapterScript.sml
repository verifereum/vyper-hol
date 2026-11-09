(* Actual-footprint and execution-point adapters for recursive return copies. *)
Theory externalReturnCopyAdapter
Ancestors
  externalReturnCopyFrame externalReturnCopyTransport externalReturnCopyBase
  fragExec context compileEnv valueEncoding valueEncodingProps
  vyperTypeSystem vyperTyping vyperValue vfmConstants loweringPosts arithmetic words list

Theorem return_copy_at_start:
  (s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    frag_exec ctx sa sb (\u. u = s) Q R) ==>
  frag_exec ctx sa sb (\u. u = s) Q R
Proof
  rw[frag_exec_def] >> gvs[] >> metis_tac[]
QED

Theorem return_copy_entry_layout_footprint:
  return_copy_entry cenv ctx tenv dty sty dtv stv v /\
  val_footprint stv v = type_memory_size stv /\
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  evaluate_type tenv dty = SOME dtv /\ evaluate_type tenv sty = SOME stv /\
  type_widens_to tenv sty dty /\ value_has_type stv v /\ value_has_type dtv v /\
  val_wf stv v /\ val_wf dtv v /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (0 < val_footprint stv v ==>
    w2n sw + val_footprint stv v < dimword (:256) /\
    (w2n sw + val_footprint stv v <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw)) ==>
  frag_exec ctx sa sb (\u. u = s)
    (\t. val_in_memory dtv v (w2n dw) t.vs_memory /\
         return_copy_frame sa (w2n dw) (type_memory_size dtv) s t) (\r. F)
Proof
  rw[return_copy_entry_def] >> first_x_assum irule >>
  simp[] >> qexistsl_tac [`dst`, `src`, `sw`] >> simp[] >> decide_tac
QED

Theorem return_copy_bytes_extent_frame:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  ~is_word_type dty /\ is_bytestring_type dty /\ is_bytestring_type sty /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  mem_word_at (w2n sw) s.vs_memory = n2w L /\
  32 + 32 * word_size L < dimword (:256) /\
  val_in_memory stv v (w2n sw) s.vs_memory /\ val_wf stv v /\
  val_footprint stv v <= 32 + 32 * word_size L /\
  32 + 32 * word_size L <= type_memory_size dtv /\
  (!p mem. val_in_memory stv v p mem ==> val_in_memory dtv v p mem) ==>
  frag_exec ctx sa sb (\u. u = s)
    (\t. val_in_memory dtv v (w2n dw) t.vs_memory /\
         return_copy_frame sa (w2n dw) (type_memory_size dtv) s t) (\r. F)
Proof
  strip_tac >>
  drule_all return_typed_bytestring_copy_extent_explicit >> strip_tac >>
  irule frag_exec_conseq >> first_assum (irule_at Any) >>
  simp[return_copy_frame_def, return_copy_memory_frame_def] >>
  rpt strip_tac >>
  qpat_x_assum `!p n. _ \/ _ ==> mem_bytes_at _ _ _ = _`
    (qspecl_then [`a`, `n`] mp_tac) >> simp[ADD_COMM]
QED

Theorem return_evaluate_base_inv[local]:
  evaluate_type tenv ty = SOME (BaseTV bt) ==> ty = BaseT bt
Proof
  Cases_on `ty` >> simp[Once evaluate_type_def] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem return_word_size_monotone[local]:
  m <= n ==> word_size m <= word_size n
Proof
  rw[vfmConstantsTheory.word_size_def] >> irule DIV_LE_MONOTONE >> simp[]
QED

Theorem return_bytes_widen_shape[local]:
  type_widens_to tenv (BaseT (BytesT (Dynamic n))) dty ==>
  ?m. dty = BaseT (BytesT (Dynamic m))
Proof
  Cases_on `dty` >> simp[type_widens_to_def, arg_type_fits_def] >>
  rename1 `BaseT b` >> Cases_on `b` >> simp[arg_type_fits_def] >>
  qmatch_goalsub_rename_tac `arg_type_fits _ (BaseT (BytesT bd))` >>
  Cases_on `bd` >> simp[arg_type_fits_def]
QED

Theorem return_string_widen_shape[local]:
  type_widens_to tenv (BaseT (StringT n)) dty ==>
  ?m. dty = BaseT (StringT m)
Proof
  Cases_on `dty` >> simp[type_widens_to_def, arg_type_fits_def] >>
  rename1 `BaseT b` >> Cases_on `b` >> simp[arg_type_fits_def]
QED

Theorem return_copy_dynamic_bytes:
  compile_store_memory_typed cenv dst (BaseT (BytesT (Dynamic dn)))
    src (BaseT (BytesT (Dynamic sn))) sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  val_in_memory (BaseTV (BytesT (Dynamic sn))) (BytesV bs)
    (w2n sw) s.vs_memory /\
  val_wf (BaseTV (BytesT (Dynamic sn))) (BytesV bs) /\
  LENGTH bs <= dn /\
  w2n dw + type_memory_size (BaseTV (BytesT (Dynamic dn))) < dimword (:256) ==>
  frag_exec ctx sa sb (\u. u = s)
    (\t. val_in_memory (BaseTV (BytesT (Dynamic dn))) (BytesV bs)
           (w2n dw) t.vs_memory /\
         return_copy_frame sa (w2n dw)
           (type_memory_size (BaseTV (BytesT (Dynamic dn)))) s t) (\r. F)
Proof
  strip_tac >> irule return_copy_bytes_extent_frame >>
  qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
  qexistsl_tac [`sw`, `BaseTV (BytesT (Dynamic sn))`, `LENGTH bs`] >>
  simp[is_word_type_def, is_bytestring_type_def, val_in_memory_def,
       val_footprint_def, type_memory_size_def] >>
  `word_size (LENGTH bs) <= word_size dn` by
    (irule return_word_size_monotone >> simp[]) >>
  gvs[val_in_memory_def, type_memory_size_def] >>
  simp[vfmConstantsTheory.word_size_def] >>
  `(LENGTH bs + 31) MOD 32 < 32` by simp[] >>
  qspec_then `32` mp_tac DIVISION >> simp[] >>
  disch_then (qspec_then `LENGTH bs + 31` strip_assume_tac) >> decide_tac
QED

Theorem return_copy_string:
  compile_store_memory_typed cenv dst (BaseT (StringT dn))
    src (BaseT (StringT sn)) sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  val_in_memory (BaseTV (StringT sn)) (StringV str) (w2n sw) s.vs_memory /\
  val_wf (BaseTV (StringT sn)) (StringV str) /\ LENGTH str <= dn /\
  w2n dw + type_memory_size (BaseTV (StringT dn)) < dimword (:256) ==>
  frag_exec ctx sa sb (\u. u = s)
    (\t. val_in_memory (BaseTV (StringT dn)) (StringV str) (w2n dw) t.vs_memory /\
         return_copy_frame sa (w2n dw) (type_memory_size (BaseTV (StringT dn))) s t)
    (\r. F)
Proof
  strip_tac >> irule return_copy_bytes_extent_frame >>
  qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
  qexistsl_tac [`sw`, `BaseTV (StringT sn)`, `LENGTH str`] >>
  simp[is_word_type_def, is_bytestring_type_def, val_in_memory_def,
       val_footprint_def, type_memory_size_def] >>
  `word_size (LENGTH str) <= word_size dn` by
    (irule return_word_size_monotone >> simp[]) >>
  gvs[val_in_memory_def, type_memory_size_def] >>
  simp[vfmConstantsTheory.word_size_def] >>
  `(LENGTH str + 31) MOD 32 < 32` by simp[] >>
  qspec_then `32` mp_tac DIVISION >> simp[] >>
  disch_then (qspec_then `LENGTH str + 31` strip_assume_tac) >> decide_tac
QED

Theorem return_adapter_footprint_cases[local]:
  !tv v.
    (?bs n. v = BytesV bs /\ tv = BaseTV (BytesT (Dynamic n))) \/
    (?str n. v = StringV str /\ tv = BaseTV (StringT n)) \/
    val_footprint tv v = type_memory_size tv
Proof
  rpt gen_tac >> Cases_on `v` >> simp[val_footprint_def] >>
  Cases_on `tv` >> simp[] >>
  rename1 `BaseTV bt` >> Cases_on `bt` >> simp[] >>
  rename1 `BytesT sz` >> Cases_on `sz` >> simp[]
QED

Theorem return_copy_entry_actual_footprint:
  return_copy_entry cenv ctx tenv dty sty dtv stv v /\
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  evaluate_type tenv dty = SOME dtv /\ evaluate_type tenv sty = SOME stv /\
  type_widens_to tenv sty dty /\ value_has_type stv v /\ value_has_type dtv v /\
  val_wf stv v /\ val_wf dtv v /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (0 < val_footprint stv v ==>
    w2n sw + val_footprint stv v < dimword (:256) /\
    (w2n sw + val_footprint stv v <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw)) ==>
  frag_exec ctx sa sb (\u. u = s)
    (\t. val_in_memory dtv v (w2n dw) t.vs_memory /\
         return_copy_frame sa (w2n dw) (type_memory_size dtv) s t) (\r. F)
Proof
  strip_tac >>
  qspecl_then [`stv`, `v`] strip_assume_tac return_adapter_footprint_cases
  >- (gvs[] >> drule return_evaluate_base_inv >> strip_tac >> gvs[] >>
      drule return_bytes_widen_shape >> strip_tac >> gvs[] >>
      gvs[Once evaluate_type_def, AllCaseEqs()] >>
      irule return_copy_dynamic_bytes >>
      qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
      simp[] >> gvs[value_has_type_def])
  >- (gvs[] >> drule return_evaluate_base_inv >> strip_tac >> gvs[] >>
      drule return_string_widen_shape >> strip_tac >> gvs[] >>
      gvs[Once evaluate_type_def, AllCaseEqs()] >>
      irule return_copy_string >>
      qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _` (irule_at Any) >>
      simp[] >> gvs[value_has_type_def]) >>
  irule return_copy_entry_layout_footprint >>
  qpat_assum `return_copy_entry _ _ _ _ _ _ _ _` (irule_at Any) >>
  qexistsl_tac [`sw`, `src`, `dst`] >> simp[]
QED
