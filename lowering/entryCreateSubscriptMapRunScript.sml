(* Interpret the retained mapping run on its installed caller interval. *)
Theory entryCreateSubscriptMapRun
Ancestors
  bodyFullMappingSuffixExecution bodyFullMappingRunSeq entryCreateAdminSequence
  entryCreateFocusSpec entryCreateCompletedCut targetSubscriptMapping exprSimMapKey
  exprLoweringProps exprLowering context compileEnv emitHelper venomInst venomState
  abiEncoderProps fragExec list rich_list arithmetic pred_set
  bodyPtrDefs loweringPosts fragGasOriginPtr allocaHistory words finite_map

Definition mapping_admin_inst_def:
  mapping_admin_inst a b i <=>
    i.inst_id IN frag_ids a b /\ i.inst_opcode <> GAS /\
    ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2
End

Theorem mapping_key_admin[local]:
  compile_keccak256_key key F a = (op,b) ==>
  EVERY (mapping_admin_inst a b) (emitted_insts a b)
Proof
  simp[compile_keccak256_key_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mapping_admin_inst_def, frag_ids_def, mk_inst_def, is_terminator_def]
QED

Theorem mapping_slot_admin[local]:
  compile_mapping_subscript bop key a = (op,b) ==>
  EVERY (mapping_admin_inst a b) (emitted_insts a b)
Proof
  simp[compile_mapping_subscript_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mapping_admin_inst_def, frag_ids_def, mk_inst_def, is_terminator_def]
QED

Theorem mapping_admin_widen[local]:
  a.cs_next_id <= b.cs_next_id /\ b.cs_next_id <= c.cs_next_id /\
  EVERY (mapping_admin_inst a b) xs /\ EVERY (mapping_admin_inst b c) ys ==>
  EVERY (mapping_admin_inst a c) (xs ++ ys)
Proof
  simp[EVERY_MEM, mapping_admin_inst_def, frag_ids_def] >>
  metis_tac[LESS_TRANS, LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED

Theorem mapping_suffix_admin_geometry[local]:
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript bop hashed sp = (slot,sb) ==>
  sb.cs_current_bb = sn.cs_current_bb /\
  sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb /\
  EVERY (mapping_admin_inst sn sb) (emitted_insts sn sb)
Proof
  strip_tac >>
  drule target_mapping_suffix_shape >> strip_tac >>
  drule mapping_slot_admin >> strip_tac >>
  Cases_on `is_bytestring_type kt`
  >- (fs[] >> drule target_keccak_key_suffix_shape >> strip_tac >>
      drule mapping_key_admin >> strip_tac >>
      `sp.cs_next_id <= sb.cs_next_id` by
        metis_tac[mapping_suffix_next_id, arithmeticTheory.LESS_EQ_ADD] >>
      drule_all emitted_insts_append >> strip_tac >>
      conj_tac >- metis_tac[] >>
      conj_tac >- metis_tac[APPEND_ASSOC] >>
      qpat_assum `emitted_insts sn sb = _` (fn th => pure_rewrite_tac[th]) >>
      drule_all mapping_admin_widen >> simp[]) >>
  gvs[]
QED

Theorem mapping_suffix_visit_inventory:
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript bop hashed sp = (slot,sb) /\
  fn_has_code sn sb func /\ create_operand_at sn s ==>
  create_operand_cut sn sb explicit ctx func tops cx st0 source (es,s)
Proof
  strip_tac >> drule_all mapping_suffix_admin_geometry >> strip_tac >>
  irule create_admin_sequence_cut >>
  fs[EVERY_MEM, mapping_admin_inst_def]
QED

Theorem mapping_suffix_raw_scope[local]:
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript bop hashed sp = (slot,sb) /\
  fn_has_code sn sb func /\ create_operand_at sn s /\ ~s.vs_halted /\
  mapping_raw_endpoint sn sb s t ==>
  create_operand_full_scope sn sb explicit ctx func s [] (OK t)
Proof
  strip_tac >> drule_all mapping_suffix_admin_geometry >> strip_tac >>
  qpat_x_assum `mapping_raw_endpoint _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [mapping_raw_endpoint_def]) >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  irule create_admin_sequence_scope >>
  fs[EVERY_MEM, mapping_admin_inst_def]
QED

Theorem mapping_suffix_confined_run:
  (if is_bytestring_type kt then compile_keccak256_key key F sn
   else (key,sn)) = (hashed,sp) /\
  compile_mapping_subscript bop hashed sp = (slot,sb) /\
  (!x. key = Var x \/ bop = Var x ==> not_fresh_at sn x) /\
  (if is_bytestring_type kt then
     ?x b base cap bs.
       key = Var x /\ eval_operand key s = SOME (n2w b) /\
       FLOOKUP G x = SOME (base,cap) /\ base <= b /\
       b+32+LENGTH bs <= base+cap /\
       b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
       b+32+LENGTH bs <= s.vs_alloca_next /\
       op_taint tn key = {} /\
       (!i. b <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
       mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
       mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
       encode_hashmap_key kt v = word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)
   else eval_operand key s = SOME (encode_hashmap_key kt v) /\
        op_taint tn key = {} /\ op_prov G key = NONE) /\
  eval_operand bop s = SOME base_slot /\ op_taint tn bop = {} /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sn.cs_current_bb /\
  s.vs_inst_idx = LENGTH sn.cs_current_insts /\ P H0 /\
  (!H. P H ==> stmt_state_rel H ctx func cenv cx es s /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) ==>
  ?t HG tm.
    create_operand_full_scope sn sb explicit ctx func s [] (OK t) /\
    eval_operand slot t = SOME (hashmap_slot base_slot (encode_hashmap_key kt v)) /\
    op_taint tm slot = {} /\ op_prov HG slot = NONE /\
    (!x. slot = Var x ==> not_fresh_at sb x) /\
    (!x. not_fresh_at sn x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP HG x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv es es sn s t /\ pure_frame cenv func es sn s t /\
    ghost_kept_at lo cenv es sn G tn s HG tm /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!H. P H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,HG,tm) /\
      stmt_state_rel H ctx func cenv cx es t /\
      ghost_inv_at (DF H) lo d cenv cx es HG tm t)
Proof
  strip_tac >> drule_all mapping_suffix_full_run_with_execution >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `create_operand_at sn s` by simp[create_operand_at_def] >>
  drule_all mapping_suffix_raw_scope >> strip_tac >>
  qexistsl_tac [`t`, `HG`, `tm`] >> simp[]
QED
