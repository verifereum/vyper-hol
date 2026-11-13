Theory exprSimPopNestedLocalRun
Ancestors
  exprSimHashBoundary
  exprSimPopNestedBase exprSimPop emitHelperProps emitHelper exprLowering
  exprLoweringProps compileEnv loweringStateRelDefs venomState venomExecSemantics venomInst
  exprSimHash fragGasSeqAbort gasSummaryCompose gasExemptCert gasSummary
  exprSimPopNestedLocalProps vyperState
  list rich_list finite_map arithmetic words

Theorem nested_pop_compile_memory_eq:
  compile_get_target_ptr compile_expr cenv bt sa =
    ((hdr,SOME LocMemory,SOME (ValPT (ArrayT et (Dynamic n)))),sm) ==>
  compile_expr cenv ty (Pop ann bt) sa =
    (let (elem,sb) = compile_dynarray_pop hdr 32
       (type_memory_bytes cenv et) cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory sm
     in (LocatedValue ann (mk_ptr elem LocMemory),sb))
Proof
  strip_tac >> rewrite_tac[nested_pop_compile_eq] >>
  simp[word_scale_def, elem_size_in_location_def, is_slot_addressed_def]
QED

Definition memory_pop_insts_def:
  memory_pop_insts hdr id esz x0 x1 x2 x3 x4 x5 x6 =
    [mk_inst id MLOAD [hdr] [x0];
     mk_inst (id+1) ISZERO [Var x0] [x1];
     mk_inst (id+2) ISZERO [Var x1] [x2];
     mk_inst (id+3) ASSERT [Var x2] [];
     mk_inst (id+4) SUB [Var x0; Lit 1w] [x3];
     mk_inst (id+5) MSTORE [hdr; Var x3] [];
     mk_inst (id+6) ADD [hdr; Lit 32w] [x4];
     mk_inst (id+7) MUL [Var x3; Lit (n2w esz)] [x5];
     mk_inst (id+8) ADD [Var x4; Var x5] [x6]]
End

Theorem memory_pop_shape:
  compile_dynarray_pop hdr 32 esz is_ctor imm LocMemory sa = (r,sb) ==>
  ?x0 x1 x2 x3 x4 x5 x6.
    ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6] /\
    EVERY (\x. ~not_fresh_at sa x) [x0;x1;x2;x3;x4;x5;x6] /\
    r = Var x6 /\
    sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
    sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
    sb.cs_current_insts = sa.cs_current_insts ++
      memory_pop_insts hdr sa.cs_next_id esz x0 x1 x2 x3 x4 x5 x6
Proof
  simp[compile_dynarray_pop_def, contextTheory.compile_ptr_load_def,
       contextTheory.compile_ptr_store_def,
       emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >>
  rpt strip_tac >> gvs[APPEND_ASSOC] >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`,
                `STRING #"%" (toString (sa.cs_next_var + 1))`,
                `STRING #"%" (toString (sa.cs_next_var + 2))`,
                `STRING #"%" (toString (sa.cs_next_var + 3))`,
                `STRING #"%" (toString (sa.cs_next_var + 4))`,
                `STRING #"%" (toString (sa.cs_next_var + 5))`] >>
  simp[ASCIInumbersTheory.toString_11, not_fresh_at_def, APPEND_ASSOC,
       memory_pop_insts_def]
QED

Theorem memory_pop_load[local]:
  IS_SOME (eval_operand hdr s) ==>
  step_inst_base (mk_inst id MLOAD [hdr] [out]) s =
    OK (update_var out (mload (w2n (THE (eval_operand hdr s))) s) s)
Proof
  Cases_on `eval_operand hdr s` >> simp[] >>
  irule step_MLOAD >> simp[]
QED

Theorem memory_pop_store[local]:
  IS_SOME (eval_operand hdr s) /\ IS_SOME (lookup_var x s) ==>
  step_inst_base (mk_inst id MSTORE [hdr; Var x] []) s =
    OK (mstore (w2n (THE (eval_operand hdr s))) (THE (lookup_var x s)) s)
Proof
  Cases_on `eval_operand hdr s` >> Cases_on `lookup_var x s` >> simp[] >>
  irule step_MSTORE >> simp[eval_operand_def]
QED

Theorem memory_pop_add[local]:
  IS_SOME (eval_operand hdr s) ==>
  step_inst_base (mk_inst id ADD [hdr; Lit 32w] [out]) s =
    OK (update_var out (THE (eval_operand hdr s) + 32w) s)
Proof
  Cases_on `eval_operand hdr s` >> simp[] >>
  irule step_ADD >> simp[eval_operand_def]
QED

Theorem memory_pop_run:
  ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\
  EVERY (\x. hdr <> Var x) [x0;x1;x2;x3;x4;x5;x6] /\
  eval_operand hdr s = SOME w /\ mload (w2n w) s <> 0w ==>
  ?u. run_inst_seq (memory_pop_insts hdr id esz x0 x1 x2 x3 x4 x5 x6) s = OK u /\
    u.vs_memory = (mstore (w2n w) (mload (w2n w) s - 1w) s).vs_memory /\
    u = s with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory|> /\
    (!x. ~MEM x [x0;x1;x2;x3;x4;x5;x6] ==> lookup_var x u = lookup_var x s) /\
    lookup_var x6 u = SOME (w + 32w + (mload (w2n w) s - 1w) * n2w esz)
Proof
  Cases_on `hdr` >> simp[eval_operand_def] >> rpt strip_tac >>
  fs[memory_pop_insts_def, run_inst_seq_def, memory_pop_load, memory_pop_store,
     memory_pop_add, pop_step_ISZERO, pop_step_ASSERT, pop_step_SUB_lit,
     pop_step_MUL_lit, pop_step_ADD_var, eval_operand_def,
     lookup_var_def, update_var_def, FLOOKUP_UPDATE, mstore_def,
     bool_to_word_def] >>
  simp[venom_state_component_equality, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[]
QED

Theorem memory_pop_run_empty:
  ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\
  eval_operand hdr s = SOME w /\ mload (w2n w) s = 0w ==>
  ?a t. run_inst_seq (memory_pop_insts hdr id esz x0 x1 x2 x3 x4 x5 x6) s = Abort a t
Proof
  strip_tac >>
  fs[memory_pop_insts_def, run_inst_seq_def, memory_pop_load,
     pop_step_ISZERO, pop_step_ASSERT, lookup_var_def, update_var_def,
     FLOOKUP_UPDATE, bool_to_word_def]
QED

Theorem memory_pop_gas_path:
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    memory_pop_insts hdr id esz x0 x1 x2 x3 x4 x5 x6 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (memory_pop_insts hdr id esz x0 x1 x2 x3 x4 x5 x6) s = OK t ==>
  gas_marked_path F ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (memory_pop_insts hdr id esz x0 x1 x2 x3 x4 x5 x6)` by
    simp[memory_pop_insts_def, mk_inst_def, is_terminator_def] >>
  drule_all hash_run_path >>
  simp[memory_pop_insts_def, mk_inst_def]
QED

Theorem memory_pop_abort_path:
  fn_has_code sa sb func /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_blocks = sa.cs_blocks /\
  sb.cs_current_insts = sa.cs_current_insts ++
    memory_pop_insts hdr id esz x0 x1 x2 x3 x4 x5 x6 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (memory_pop_insts hdr id esz x0 x1 x2 x3 x4 x5 x6) s = Abort a t ==>
  ?j. gas_marked_path F ctx func s 0 (Abort a (t with vs_inst_idx := j))
Proof
  strip_tac >>
  `same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    simp[same_blocks_def, IS_PREFIX_APPEND] >>
  drule_all storageCopyGasPathTheory.storage_copy_code_prefix >> strip_tac >>
  `isPREFIX (memory_pop_insts hdr id esz x0 x1 x2 x3 x4 x5 x6)
     (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode)
     (memory_pop_insts hdr id esz x0 x1 x2 x3 x4 x5 x6)` by
    simp[memory_pop_insts_def, mk_inst_def, is_terminator_def] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  drule_all run_inst_seq_abort_zero_path >> simp[]
QED

Theorem memory_pop_live_exec:
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  entry.assignable /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
  vs <> [] /\
  assign_subscripts entry.type entry.value path
    (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated /\
  gas_marked_path F ctx func s 0 r ==>
  gas_marked_exec F (ctx,func) (pop_place cx (MemoryPlace id path)) (es,s) []
    (INL (PlaceR (MemoryPlace id
      (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]))))
    (es with scopes := pre ++ sc |+ (id,entry with
      <|value := updated;
        popped := record_pop path (ArrayV (DynArrayV vs)) (LAST vs) entry.popped|>) :: rest) r
Proof
  strip_tac >> simp[gas_marked_exec_def, gas_explicit_def] >> gen_tac >>
  qspecl_then [`cx`, `es with gas_obs := tail`] mp_tac pop_memory_place_live >>
  simp[] >> disch_then drule_all >> simp[]
QED

Theorem memory_pop_empty_exec:
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  entry.assignable /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV [])) /\
  gas_marked_path F ctx func s 0 r ==>
  gas_marked_exec F (ctx,func) (pop_place cx (MemoryPlace id path)) (es,s) []
    (INR (Error (RuntimeError "pop empty memory array"))) es r
Proof
  strip_tac >> simp[gas_marked_exec_def, gas_explicit_def] >> gen_tac >>
  qspecl_then [`cx`, `es with gas_obs := tail`] mp_tac pop_memory_place_live_empty >>
  simp[] >> disch_then drule_all >> simp[]
QED
