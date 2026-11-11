(* Compatible copies retain the source-footprint bound, including short literals. *)
Theory bodyIntCallWidenCopy
Ancestors
  bodyIntCallProtectedReturn valueCopySource exprLoweringProps compileEnv loweringStateRelDefs
  valueEncoding venomState venomExecSemantics venomInst words list

Theorem protected_compatible_store_run:
  !ce src dst dty sty sa sb s tenv dtv stv v sw dw P reserved.
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
    (!b n. P b n ==> regions_disjoint b n (w2n dw)
       (MIN (type_memory_size stv) (type_memory_size dtv))) /\
    (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
      val_in_memory dtv v (w2n dw) u.vs_memory /\
      (!b n. P b n ==> mem_bytes_at b n u.vs_memory = mem_bytes_at b n s.vs_memory) /\
      (!op. reserved op ==> eval_operand op u = eval_operand op s) /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      LENGTH s.vs_memory <= LENGTH u.vs_memory
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_store_memory_run_source_bound_with_capacity >> strip_tac >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> metis_tac[regions_disjoint_def]) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `op` >>
      gvs[eval_operand_def, venom_state_component_equality]) >>
  gvs[venom_state_component_equality]
QED
