(* Stronger suffix boundaries: execution starts at the operand end index,
   so compiler-block openness is not required. *)
Theory bodyMemBiKeccakOpenFree
Ancestors
  bodyMemBiKeccakCompose bodyMemBiKeccakScratch bodyMemBiKeccakSuffix bodyMemBiKeccakBounds
  allocaFootprint abiBuiltinAllocation venomMemDefs venomInst finite_map words exprSimHash exprOperandVar
  exprSimMemDefs exprSimProps fragGasSeqMem allocaHistoryFragment
  vyperTyping vyperValue builtinHashing vyperTypeSystem compileEnv
  loweringPosts exprLoweringProps exprSimAlloc context emitHelper list rich_list exprSimVVFrame fragExec entrySinkExtraction

Theorem keccak_typed_suffix_mem_ok_open_free:
  expr_post ctx func cenv cx e es sa sm s0 es' v x s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  (if is_bytestring_type (expr_type e) then compile_keccak256_bytes x sm
   else case expr_type e of
     BaseT (BytesT (Fixed m)) => compile_keccak256_bytesm x m sm
   | _ => compile_keccak256_word x sm) = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  expr_store_bound cx (expr_type e) v x s ==>
  run_inst_seq_mem_ok (emitted_insts sm sb) s
Proof
  strip_tac >>
  `!a. x = Var a ==> not_fresh_at sm a` by
    (metis_tac[compile_lower_value_var]) >>
  Cases_on `bty` >> gvs[is_bytes_or_string_type_def] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  gvs[is_bytestring_type_def]
  >~ [`expr_type e = BaseT (BytesT bd)`]
  >- (Cases_on `bd` >> gvs[is_bytestring_type_def]
      >- (gvs[evaluate_type_def, value_has_type_def] >>
          drule_at (Pos hd) hash_fixed_post_view >>
          simp[value_has_type_def] >> strip_tac >>
          `stmt_state_rel ctx func cenv cx es' s` by
            fs[expr_post_def] >>
          `MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
            [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func)` by
            (irule (SRULE [] (Q.INST [`sha` |-> `F`] hash_fixed_alloca_code)) >>
             metis_tac[]) >>
          `alloca_next_valid s` by fs[stmt_state_rel_def, alloca_inv_def] >>
          `?p. FLOOKUP (abi_builtin_allocate_state sm.cs_next_id 32 s).vs_allocas
            sm.cs_next_id = SOME (p,32) /\ p + 32 < dimword (:256)` by
            (reverse (Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id`)
             >- (PairCases_on `x'` >>
                 `x'1 = 32` by
                   (fs[stmt_state_rel_def] >>
                    qpat_x_assum `!inst n base sz. _` drule >> simp[mk_inst_def, dimword_def]) >>
                 qexists_tac `x'0` >>
                 fs[alloca_site_cases, alloca_next_valid_def,
                    stmt_state_rel_def, alloca_room_def] >>
                 qpat_x_assum `!aid base sz. _` drule >> simp[] >> decide_tac) >>
             qexists_tac `s.vs_alloca_next` >> simp[alloca_site_cases] >>
             `alloca_room ctx func s` by fs[stmt_state_rel_def] >>
             drule_at (Pos hd) alloca_room_fresh >>
             disch_then (qspec_then `mk_inst sm.cs_next_id ALLOCA [Lit 32w]
               [STRING #"%" (toString sm.cs_next_var)]` mp_tac) >>
             simp[mk_inst_def, FLOOKUP_DEF] >>
             `sm.cs_next_id NOTIN FDOM s.vs_allocas` by
               metis_tac[FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
             simp[dimword_def]) >>
          irule keccak_fixed_site_mem_ok >> goal_assum (drule_at Any) >>
          simp[] >> metis_tac[]) >>
      drule_at (Pos hd) keccak_dynamic_post_bounds >> simp[] >> strip_tac >>
      irule keccak_memory_suffix_mem_ok >>
      qexistsl_tac [`b`, `LENGTH l`, `op`, `x`] >> simp[]) >>
  drule_at (Pos hd) keccak_string_post_bounds >> simp[] >> strip_tac >>
  irule keccak_memory_suffix_mem_ok >>
  qexistsl_tac [`b`, `LENGTH s'`, `op`, `x`] >> simp[]
QED

Theorem keccak_typed_suffix_counted_open_free:
  expr_post ctx func cenv cx e es sa sm s0 es' v x s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  (if is_bytestring_type (expr_type e) then compile_keccak256_bytes x sm
   else case expr_type e of
     BaseT (BytesT (Fixed m)) => compile_keccak256_bytesm x m sm
   | _ => compile_keccak256_word x sm) = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  expr_store_bound cx (expr_type e) v x s /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t r. gas_path_mem ctx func s 0 (OK t) /\
    builtin_result cx es'.accounts (BaseT (BytesT (Fixed 32)))
      Keccak256 [expr_type e] [v] = INL r /\
    vv_post ctx func cenv cx (Builtin (BaseT (BytesT (Fixed 32))) Keccak256 [e])
      es sa sb s0 es' (Value r) (StackValue (BaseT (BytesT (Fixed 32))) op) t /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_current_bb = sb.cs_current_bb /\ ~t.vs_halted
Proof
  strip_tac >>
  drule_all keccak_typed_post_run >> strip_tac >>
  drule_all keccak_typed_suffix_mem_ok_open_free >> strip_tac >>
  drule_all keccak_typed_suffix_shape >> strip_tac >>
  drule_all keccak_typed_suffix_no_gas >> strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sm sb ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sm sb) = LENGTH sb.cs_current_insts` by
    (fs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND]) >>
  `isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  drule_all run_inst_seq_gas_path_mem >> simp[] >> strip_tac >>
  `alloca_inv s` by fs[expr_post_def, stmt_state_rel_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    fs[EVERY_MEM] >>
  drule_all alloca_history_run_inst_seq >> simp[] >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  fs[same_blocks_def] >>
  `!a. x = Var a ==> not_fresh_at sm a` by
    metis_tac[compile_lower_value_var] >>
  Cases_on `bty` >> gvs[is_bytes_or_string_type_def] >>
  Cases_on `v` >> gvs[value_has_type_def, is_bytestring_type_def]
  >~ [`expr_type e = BaseT (BytesT bd)`]
  >- (Cases_on `bd` >> gvs[is_bytestring_type_def]
      >- metis_tac[keccak_fixed_suffix_frontier] >>
      drule_at (Pos hd) keccak_dynamic_post_bounds >> simp[] >> strip_tac >>
      drule_all keccak_memory_suffix_frontier >> simp[]) >>
  drule_at (Pos hd) keccak_string_post_bounds >> simp[] >> strip_tac >>
  drule_at (Pos hd) (Q.INST [`bs` |-> `MAP (n2w o ORD) s'`] keccak_memory_suffix_frontier) >>
  simp[] >> disch_then drule_all >> simp[]
QED
