(* Counted compatible stores preserve resources at the same encoding endpoint. *)
Theory bodyIntCallAggregateStoreLanding
Ancestors
  bodyIntCallWidenCopy bodyIntCallLiteralLanding localMemoryStorePath
  placeMemoryPrimitiveForward entrySinkExtraction valueCopyBytes valueEncoding
  exprLoweringProps compileEnv loweringStateRelDefs loweringPosts venomState venomExecSemantics
  venomInst words list rich_list fragGasMode instIdxIndep finite_map

Theorem compatible_store_no_gas:
  compile_store_memory ce src dst dty sty sa = ((),sb) /\
  (dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty) ==>
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  strip_tac
  >- metis_tac[compile_store_memory_same_type_no_gas] >>
  `~is_word_type dty` by metis_tac[is_bytestring_word_type] >>
  drule compile_store_memory_no_gas >> simp[FILTER_EQ_NIL, EVERY_MEM]
QED

Theorem protected_compatible_store_landing:
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
  (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    val_in_memory dtv v (w2n dw) u.vs_memory /\
    (!b n. P b n ==> mem_bytes_at b n u.vs_memory = mem_bytes_at b n s.vs_memory) /\
    (!op. reserved op ==> eval_operand op u = eval_operand op s) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory /\
    (local_ptrs_reserved ce sa ==>
      !name b sz. local_region ce scopes u name b sz <=> local_region ce scopes s name b sz) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all protected_compatible_store_run >> strip_tac >>
  drule_all compatible_store_no_gas >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  `gas_marked_path F ctx func s 0
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path >> simp[] >> metis_tac[]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[eval_op_inst_idx, lookup_var_def, venom_state_component_equality] >>
  strip_tac >>
  irule local_region_reserved_operands >>
  qexists_tac `\op. ?x. op = Var x /\ not_fresh_at sa x` >>
  fs[local_ptrs_reserved_def] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> gvs[eval_operand_def, lookup_var_def] >> metis_tac[]
QED
