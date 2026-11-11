(* Bytestring return stores retain both typed views and the declared write frame. *)
Theory bodyIntCallFamStmtReturnBytesEffect
Ancestors
  bodyIntCallFamStmtReturnStoreEffect valueCopyBytes context
  placeMemoryCopyEffect compileEnv venomState venomExecSemantics

Theorem bytestring_store_effect:
  compile_store_memory ce src dst declared physical sa = ((),sm) /\
  is_bytestring_type declared /\ is_bytestring_type a /\
  evaluate_type tenv a = SOME av /\
  evaluate_type tenv declared = SOME dv /\
  value_has_type av v /\ value_has_type dv v /\
  val_in_memory av v (w2n sw) s.vs_memory /\
  type_memory_bytes ce a = type_memory_size av /\
  type_memory_size av + 64 < dimword (:256) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME bw /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory dv v (w2n bw) t.vs_memory /\
    typed_copy_effect ctx func sa sm s t (w2n bw) (type_memory_size dv)
Proof
  strip_tac >>
  `~is_word_type declared /\ ~is_word_type a` by
    metis_tac[is_bytestring_word_type] >>
  `compile_store_memory ce src dst a declared sa = ((),sm)` by
    gvs[compile_store_memory_def] >>
  `val_in_memory dv v (w2n sw) s.vs_memory` by
    (irule bytestring_val_in_memory_transfer >> metis_tac[]) >>
  qpat_x_assum `compile_store_memory ce src dst declared physical sa = _` kall_tac >>
  SUBGOAL_THEN ``a = declared \/
    is_bytestring_type a /\ is_bytestring_type declared`` assume_tac
  >- simp[] >>
  `(if is_word_type declared then sw = typed_val_to_w256 dv v
    else val_in_memory dv v (w2n sw) s.vs_memory)` by simp[] >>
  drule_all compatible_store_effect >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> conj_tac
  >- (irule bytestring_val_in_memory_transfer >> metis_tac[]) >>
  irule typed_copy_effect_enlarge >> goal_assum (drule_at Any) >> simp[]
QED
