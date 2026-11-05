(* Source mapping extension boundary for write-side subscripts. *)
Theory targetSubscriptMapping
Ancestors
  targetPlaceSimCasesBase loweringPosts vyperState exprSimHash fragGasMode
  emitHelperProps venomInst exprSimAlloc exprSimPrecompiles compileEnv

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
