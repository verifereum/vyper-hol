(* Source mapping extension boundary for write-side subscripts. *)
Theory targetSubscriptMapping
Ancestors
  targetPlaceSimCasesBase loweringPosts vyperState exprSimHash fragGasMode
  emitHelperProps venomInst exprSimAlloc exprSimPrecompiles compileEnv
  exprLowering exprLoweringProps emitHelper fragExec venomState words finite_map list arithmetic valueEncodingProps

Theorem target_mapping_extend_place:
  extend_place cx (HashMapRef tr slot kt vt) (ValueSubscript kv) es =
    (INL pv, es') ==>
  es' = es /\
  place_ptr_rel cenv cx s pv (hashmap_slot slot (encode_hashmap_key kt kv))
    (SOME (slot_loc tr)) vt /\
  place_readable cx es' pv
Proof
  Cases_on `vt`
  >- (rename1 `Type typ` >>
      Cases_on `evaluate_type (get_tenv cx) typ` >>
      simp[extend_place_def, lift_option_type_def, bind_def,
           return_def, raise_def, place_ptr_rel_def, place_readable_def] >>
      rpt strip_tac >> gvs[place_ptr_rel_def, place_readable_def]) >>
  simp[extend_place_nested_mapping] >> rpt strip_tac >>
  gvs[place_ptr_rel_def, place_readable_def]
QED

Theorem target_SHA3_bytes_path:
  emit_op SHA3 [ptr_op; len] sa = (op,sb) /\ fn_has_code sa sb func /\
  eval_operand ptr_op s = SOME p /\ eval_operand len s = SOME n /\
  mem_bytes_at (w2n p) (w2n n) s.vs_memory = bs /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_marked_path F ctx func s 0
    (OK ((update_var (STRING #"%" (toString sa.cs_next_var))
       (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) s)
       with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> pure_rewrite_tac[gas_marked_path_def, COND_CLAUSES] >>
  irule emit_op_zero_path >> simp[] >>
  qexistsl_tac [`[ptr_op; len]`, `op`, `SHA3`, `sb`] >>
  simp[is_terminator_def] >> rpt strip_tac >>
  irule step_SHA3_bytes >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem target_scratch_store_frame:
  stmt_state_rel ctx func cenv cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  b <= a /\ a + 32 <= b + sz /\
  (!aid off len. aid < sa.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
     regions_disjoint b sz off len) /\
  (!name off len. local_region cenv es.scopes s name off len ==>
     regions_disjoint b sz off len) ==>
  stmt_state_rel ctx func cenv cx es (mstore a w s) /\
  wb_frame cenv es sa s (mstore a w s)
Proof
  strip_tac >> conj_tac
  >- (irule literal_mstore_state_rel >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`b`, `inst`, `sz`] >> simp[] >>
      rpt strip_tac >> first_x_assum drule >>
      simp[regions_disjoint_def]) >>
  irule scratch_mstore_frame >> conj_tac >> rpt strip_tac >>
  first_x_assum drule >> simp[regions_disjoint_def] >> decide_tac
QED

Theorem target_keccak_key_run:
  compile_keccak256_key key F sa = (op,sb) /\
  (!x. key = Var x ==> not_fresh_at sa x) /\
  eval_operand key s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
  b+32 < dimword(:256) /\ LENGTH bs < dimword(:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) /\
      (t with vs_vars := s.vs_vars) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  simp[compile_keccak256_key_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_op ADD _ sa = (dp,sm)` >>
  rename1 `emit_op MLOAD _ sm = (len,sh)` >>
  `!n. sa.cs_next_var <= n ==>
     key <> Var (STRING #"%" (toString n))` by
    (rpt strip_tac >> first_x_assum drule >>
     simp[not_fresh_at_def]) >>
  qpat_assum `emit_op ADD _ _ = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  qpat_x_assum `emit_op MLOAD _ _ = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  qpat_x_assum `emit_op SHA3 _ _ = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sh ++ emitted_insts sh sb` by
    simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, APPEND_ASSOC] >>
  qabbrev_tac `v0 = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `v1 = STRING #"%" (toString (sa.cs_next_var + 1))` >>
  qabbrev_tac `v2 = STRING #"%" (toString (sa.cs_next_var + 2))` >>
  `v0 <> v1 /\ v0 <> v2 /\ v1 <> v2` by
    simp[Abbr `v0`, Abbr `v1`, Abbr `v2`] >>
  qabbrev_tac `s1 = update_var v0 (n2w (b+32)) s` >>
  qabbrev_tac `s2 = update_var v1 (n2w (LENGTH bs)) s1` >>
  `eval_operand key s1 = SOME (n2w b)` by
    (Cases_on `key` >> gvs[Abbr `s1`, eval_operand_def, lookup_var_update_var] >>
     metis_tac[LESS_EQ_REFL, Abbr `v0`]) >>
  `step_inst_base (mk_inst sa.cs_next_id ADD [key; Lit 32w] [v0]) s = OK s1` by
    (simp[Abbr `s1`, GSYM word_add_n2w] >> irule step_ADD >> simp[eval_operand_def]) >>
  `step_inst_base (mk_inst (sa.cs_next_id+1) MLOAD [key] [v1]) s1 = OK s2` by
    (simp[Abbr `s2`] >> irule EQ_TRANS >>
     irule_at Any step_MLOAD >> simp[] >>
     simp[GSYM mem_word_at_eq_mload, Abbr `s1`, update_var_def, w2n_n2w, LESS_MOD]) >>
  `step_inst_base (mk_inst (sa.cs_next_id+2) SHA3 [Var v0; Var v1] [v2]) s2 =
     OK (update_var v2 (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) s2)` by
    (irule step_SHA3_bytes >>
     simp[Abbr `s2`, Abbr `s1`, eval_operand_def, lookup_var_update_var,
          update_var_def, w2n_n2w, LESS_MOD]) >>
  qexists_tac `update_var v2 (word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) s2` >>
  conj_tac
  >- (simp[Abbr `v1`, Abbr `v2`, run_inst_seq_def, ADD_ASSOC]) >>
  conj_tac
  >- simp[Abbr `v2`, eval_operand_def, lookup_var_update_var, ADD_ASSOC] >>
  conj_tac
  >- simp[Abbr `s2`, Abbr `s1`, update_var_def] >>
  rpt strip_tac >>
  `x <> v0 /\ x <> v1 /\ x <> v2` by
    (gvs[not_fresh_at_def, Abbr `v0`, Abbr `v1`, Abbr `v2`] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  simp[Abbr `s2`, Abbr `s1`, lookup_var_update_var]
QED
