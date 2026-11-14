(* Memory reads for the bytestring mapping-key hash. *)
Theory bodyMappingKeyMemory
Ancestors
  exprSimMapKey bodyMemBiKeccakBounds bodyMemBiKeccakSuffix
  allocaFootprint builtinHashing emitHelper emitHelperProps fragExecMem
  instMemFrontier compileEnv context venomState venomInst venomExecSemantics
  finite_map words exprLowering exprLoweringProps fragExec rich_list
  freshWrites valueEncodingProps exprSimHash loweringStateRelDefs
  vyperTyping vyperValue vyperTypeSystem exprSimMemDefs

Theorem compile_keccak256_key_mem_ok:
  compile_keccak256_key key F sa = (op,sb) /\
  (!v. key = Var v ==> not_fresh_at sa v) /\
  eval_operand key s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w n /\
  b + 32 < dimword (:256) /\ n < dimword (:256) /\
  b + 32 <= s.vs_alloca_next /\
  (n = 0 \/ b + 32 + n <= s.vs_alloca_next) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[compile_keccak256_key_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!k. LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + k) = 0`
    by decide_tac >>
  qpat_x_assum `_ with <| cs_next_var := _; cs_next_id := _;
      cs_current_insts := _ |> = sb` (SUBST1_TAC o SYM) >>
  simp[emitted_insts_def, DROP_APPEND] >>
  rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  drule step_ADD >> disch_then (qspec_then `Lit 32w` mp_tac) >>
  simp[eval_operand_def] >>
  disch_then (qspecl_then [`sa.cs_next_id`,
    `STRING #"%" (toString sa.cs_next_var)`] assume_tac) >>
  simp[] >>
  `eval_operand key (update_var (STRING #"%" (toString sa.cs_next_var))
      (n2w b + 32w) s) = SOME (n2w b)` by
    (irule eval_operand_update_other_local >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[not_fresh_at_def]) >>
  conj_tac >- simp[below_frontier_MLOAD, update_var_def] >>
  drule step_MLOAD_local >>
  disch_then (qspecl_then [`STRING #"%" (toString (sa.cs_next_var + 1))`,
                          `sa.cs_next_id + 1`] assume_tac) >>
  simp[run_inst_seq_mem_ok_last, below_frontier_SHA3] >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, ASCIInumbersTheory.toString_inj,
       GSYM mem_word_at_eq_mload, GSYM word_add_n2w] >>
  Cases_on `n = 0` >> simp[] >>
  `n2w b + 32w = (n2w (b + 32):256 word)` by simp[word_add_n2w] >>
  simp[] >> decide_tac
QED

Theorem compile_mapping_bytestring_key_mem_ok:
  expr_post ctx func cenv cx e es sa sm s0 es' kv key s /\
  expr_store_bound cx (expr_type e) kv key s /\
  is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv kv /\
  compile_keccak256_key key F sm = (op,sb) /\
  (!v. key = Var v ==> not_fresh_at sm v) ==>
  run_inst_seq_mem_ok (emitted_insts sm sb) s
Proof
  strip_tac >> Cases_on `expr_type e` >> gvs[is_bytestring_type_def] >>
  rename1 `expr_type e = BaseT bt` >> Cases_on `bt` >>
  gvs[is_bytestring_type_def, evaluate_type_def]
  >~ [`expr_type e = BaseT (BytesT bd)`]
  >- (Cases_on `bd` >> gvs[is_bytestring_type_def] >>
      Cases_on `kv` >> gvs[value_has_type_def] >>
      drule_at (Pos hd) keccak_dynamic_post_bounds >> simp[evaluate_type_def] >> strip_tac >>
      irule compile_keccak256_key_mem_ok >>
      qexistsl_tac [`b`, `key`, `LENGTH l`, `op`] >> simp[]) >>
  Cases_on `kv` >> gvs[value_has_type_def] >>
  drule_at (Pos hd) keccak_string_post_bounds >> simp[evaluate_type_def] >> strip_tac >>
  irule compile_keccak256_key_mem_ok >>
  qexistsl_tac [`b`, `key`, `LENGTH s'`, `op`] >> simp[]
QED
