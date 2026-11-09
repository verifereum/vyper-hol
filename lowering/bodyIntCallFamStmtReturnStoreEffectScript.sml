(* Compatible stores retain the static frame as well as their counted path. *)
Theory bodyIntCallFamStmtReturnStoreEffect
Ancestors
  bodyIntCallAggregateStoreLanding bodyIntCallWidenCopy
  placeMemoryCopyEffect localMemoryStorePath entrySinkExtraction
  instIdxIndep exprSimStorageCopy fragGasMode compileEnv
  venomState venomExecSemantics list rich_list
  exprLoweringProps placeMemoryPrimitiveForward

Theorem compatible_store_effect:
  compile_store_memory ce src dst dty sty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  evaluate_type tenv dty = SOME dtv /\ evaluate_type tenv sty = SOME stv /\
  (dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty) /\
  value_has_type dtv v /\ value_has_type stv v /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  (if is_word_type sty then sw = typed_val_to_w256 stv v
   else val_in_memory stv v (w2n sw) s.vs_memory) /\
  type_memory_size dtv + 64 < dimword (:256) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
    typed_copy_effect ctx func sa sb s t (w2n dw)
      (MIN (type_memory_size stv) (type_memory_size dtv))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (SRULE [] o Q.INST [`P` |-> `\b n. regions_disjoint b n (w2n dw)
      (MIN (type_memory_size stv) (type_memory_size dtv))`,
    `reserved` |-> `\op. F`] $ SPEC_ALL protected_compatible_store_run) >>
  strip_tac >>
  drule_all compatible_store_no_gas >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  `gas_marked_path F ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path >> simp[] >> metis_tac[]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[typed_copy_effect_def, lookup_var_def,
     venom_state_component_equality, regions_disjoint_def] >>
  metis_tac[]
QED
