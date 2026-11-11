(* TOP-LEVEL: complete typed copy frames retain disjoint source values,
   and allocation frames retain any live source operand's pointer. *)
Theory typedStoreFrames
Ancestors
  typedSArrayDynInvariant memoryValueDefs memoryValueTyping valueEncoding
  venomState venomInst list words arithmetic

Theorem array_copy_frame_source:
  !ftv atv v copy_count dst_off src_off before_mem after_mem.
    value_has_type atv v /\ memory_value_rel atv v src_off before_mem /\
    array_copy_frame ftv copy_count dst_off before_mem after_mem /\
    (src_off + type_memory_size atv <= dst_off \/
      dst_off + copy_count * type_memory_size ftv <= src_off) ==>
    memory_value_rel atv v src_off after_mem
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule value_has_type_val_wf >> DISCH_TAC >>
  qpat_x_assum `array_copy_frame _ _ _ _ _` (mp_tac o REWRITE_RULE [array_copy_frame_def]) >>
  disch_then (qspecl_then [`atv`, `v`, `src_off`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED

Theorem compiler_operand_frame_value:
  !names src before after ptr_addr.
    EVERY (\name. src <> Var name) names /\ eval_operand src before = SOME ptr_addr /\
    (!arg_op. EVERY (\name. arg_op <> Var name) names ==>
      eval_operand arg_op after = eval_operand arg_op before) ==>
    eval_operand src after = SOME ptr_addr
Proof
  rpt gen_tac >> strip_tac >> first_x_assum (qspec_then `src` mp_tac) >> simp[]
QED
