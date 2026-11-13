(* Memory endpoint for an empty immutable length-word store. *)
Theory immutableAssignEmptyEndpointMem
Ancestors
  immutableAssignStoreMem bodyImmutableAssignFacts immutableDeployAssignBytes
  placeStore memoryLocalRhsProps stmtLowering compileEnv context emitHelper
  venomExecSemantics loweringStateRelDefs venomState valueEncodingProps finite_map
  vyperTyping

Theorem immutable_assign_empty_mem_endpoint:
  compile_store_at_loc (SOME region) dst (Lit 0w) (SOME LocCode) sm = ((),sb) /\
  fn_has_code sm sb func /\
  eval_operand region s = SOME 0w /\ eval_operand dst s = SOME (n2w off) /\
  off + 32 <= s.vs_alloca_next /\ off + 32 < dimword (:256) /\
  has_length_word dty /\ evaluate_type tenv dty = SOME tv /\
  immutable_value_admissible tv (default_value tv) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. mem_cont_sim ctx func s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    val_in_memory tv (default_value tv) off t.vs_memory /\
    immutable_value_bytes_rel tv (default_value tv)
      (mem_bytes_at off (type_memory_size tv) t.vs_memory) /\
    (!q k. q+k <= off \/ off+32 <= q ==>
      mem_bytes_at q k t.vs_memory = mem_bytes_at q k s.vs_memory) /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
      vs_immutables := t.vs_immutables; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `compile_imm_store_word (SOME region) dst (Lit 0w) sm = ((),sb)` by
    gvs[compile_store_at_loc_def] >>
  `w2n (n2w off : bytes32) = off` by (simp[] >> decide_tac) >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  `!x. Lit (0w:bytes32) = Var x ==> not_fresh_at sm x` by simp[] >>
  `w2n (n2w off : bytes32) + 32 <= s.vs_alloca_next` by simp[] >>
  drule_all immutable_store_word_mem_cont >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    (qpat_x_assum `compile_imm_store_word _ _ _ _ = _` mp_tac >>
     simp[compile_imm_store_word_def, emit_op_def, emit_void_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[]) >>
  `val_in_memory tv (default_value tv) off (istore off 0w s).vs_memory` by
    (irule (cj 1 place_store_empty_representation) >>
     simp[istore_def, mstore_mem_word_at_same] >> metis_tac[]) >>
  `immutable_value_bytes_rel tv (default_value tv)
     (mem_bytes_at off (type_memory_size tv) (istore off 0w s).vs_memory)` by
    (irule immutable_memory_bytes >> simp[]) >>
  `!q k. q+k <= off \/ off+32 <= q ==>
     mem_bytes_at q k (mstore off 0w s).vs_memory = mem_bytes_at q k s.vs_memory` by
    metis_tac[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint] >>
  qexists_tac `(istore off 0w
    (update_var (STRING #"%" (toString sm.cs_next_var)) (n2w off) s))
    with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[istore_def, mstore_def, update_var_def,
      write_memory_with_expansion_def, lookup_var_def, FLOOKUP_UPDATE,
      not_fresh_at_def, venom_state_component_equality] >>
  first_assum ACCEPT_TAC
QED
