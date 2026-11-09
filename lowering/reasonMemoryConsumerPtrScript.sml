(* Expression memory endpoints feed the shared checked reason encoder. *)
Theory reasonMemoryConsumerPtr
Ancestors
  reasonEndpointResourcesPtr revertReasonEntryPtr reasonRepresentationPtr
  loweringPosts bodyPtrDefs compileEnv context exprSimProps exprLoweringProps
  valueEncoding valueEncodingProps vyperValue vyperState venomState
  ptrDiscipline words arithmetic finite_map list contractABI vfmConstants

Theorem memory_string_endpoint:
  evaluate_type (get_tenv cx) (BaseT (StringT max)) = SOME (BaseTV (StringT max)) /\
  vv_holds cenv cx (BaseT (StringT max)) tv vv es s /\
  vv_at cenv cx (BaseT (StringT max)) sx sa es tv vv s /\
  ptr_vv_ok cx (BaseT (StringT max)) tv vv es G tn s /\
  read_result cx tv es = (INL (StringV str),es) /\
  (vv = StackValue ty op \/
   (vv = LocatedValue ty p /\ p.ptr_location = LocMemory /\ p.ptr_operand = op)) ==>
  ?src A. op = Var src /\ lookup_var src s = SOME A /\
    ptr_covers G tn src s (32+contractABI$ceil32 (LENGTH str)) /\
    mload (w2n A) s = n2w (LENGTH str) /\
    (!j. w2n A <= j /\ j < w2n A+32 ==> j NOTIN tn.t_mem) /\
    val_wf (BaseTV (StringT max)) (StringV str) /\
    ((?aid a sz. FLOOKUP s.vs_allocas aid = SOME (a,sz) /\ aid < sa.cs_next_id /\
        a <= w2n A /\ w2n A+32 <= a+sz) \/
     (?name a sz. local_region cenv es.scopes s name a sz /\
        a <= w2n A /\ w2n A+32 <= a+sz))
Proof
  strip_tac >>
  `?A. eval_operand op s = SOME A /\
       val_in_memory (BaseTV (StringT max)) (StringV str) (w2n A) s.vs_memory /\
       ptr_mem_ok cx (BaseT (StringT max)) (StringV str) op G tn s` by
    (gvs[vv_holds_def, ptr_vv_ok_def, ptr_val_ok_def, expr_val_rel_def,
         evaluate_type_def, is_word_type_def] >> metis_tac[]) >>
  drule_all ptr_mem_ok_string_region >> simp[evaluate_type_def] >> strip_tac >>
  qpat_x_assum `op = Var x` SUBST_ALL_TAC >>
  `eval_operand (Var x) s = SOME A` by simp[] >>
  `!j. w2n A <= j /\ j < w2n A+32 ==> j NOTIN tn.t_mem` by
    (gen_tac >> strip_tac >> drule_all ptr_mem_ok_string_head_clean >> simp[]) >>
  `val_wf (BaseTV (StringT max)) (StringV str)` by
    (gvs[vv_at_def, expr_val_at_def, evaluate_type_def, is_word_type_def] >> metis_tac[]) >>
  `(?aid a sz. FLOOKUP s.vs_allocas aid = SOME (a,sz) /\ aid < sa.cs_next_id /\
      a <= w2n A /\ w2n A+32 <= a+sz) \/
   (?name a sz. local_region cenv es.scopes s name a sz /\
      a <= w2n A /\ w2n A+32 <= a+sz)` by
    (irule vv_at_memory_region_prefix >> simp[] >>
     goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
     simp[is_word_type_def, val_footprint_def] >> metis_tac[]) >>
  qexistsl [`x`,`A`] >>
  gvs[eval_operand_def, ptr_covers_def, val_in_memory_def, mem_word_at_def,
      mload_def, contractABITheory.ceil32_def, word_size_def, ptr_mem_ok_def,
      ptr_vv_ok_def, ptr_val_ok_def] >> metis_tac[]
QED

Theorem compile_revert_memory_string_endpoint_ptr:
  compile_revert_with_reason cenv vv mt
    (type_memory_bytes cenv (BaseT (StringT max))) sa = ((),sb) /\
  evaluate_type (get_tenv cx) (BaseT (StringT max)) = SOME (BaseTV (StringT max)) /\
  type_alloc_ok cenv (BaseT (StringT max)) /\
  vv_holds cenv cx (BaseT (StringT max)) tv vv es s /\
  vv_at cenv cx (BaseT (StringT max)) sx sa es tv vv s /\
  ptr_vv_ok cx (BaseT (StringT max)) tv vv es G tn s /\
  read_result cx tv es = (INL (StringV str),es) /\
  (vv = StackValue ty op \/
   (vv = LocatedValue ty p /\ ~is_word_type ty /\
    p.ptr_location = LocMemory /\ p.ptr_operand = op)) /\
  copy_old_operand sa op /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes
    (STRING #"%" (toString (sa.cs_next_var+k)))) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z Gf tnf. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (Abort Revert_abort z)
Proof
  strip_tac >>
  `?src A. op = Var src /\ lookup_var src s = SOME A /\
    ptr_covers G tn src s (32+contractABI$ceil32 (LENGTH str)) /\
    mload (w2n A) s = n2w (LENGTH str) /\
    (!j. w2n A <= j /\ j < w2n A+32 ==> j NOTIN tn.t_mem) /\
    val_wf (BaseTV (StringT max)) (StringV str) /\
    ((?aid a sz. FLOOKUP s.vs_allocas aid = SOME (a,sz) /\ aid < sa.cs_next_id /\
        a <= w2n A /\ w2n A+32 <= a+sz) \/
     (?name a sz. local_region cenv es.scopes s name a sz /\
        a <= w2n A /\ w2n A+32 <= a+sz))` by
    (irule memory_string_endpoint >> goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  drule_all string_encoder_size_bounds >> strip_tac >>
  irule compile_revert_reason_memory_path_ptr >> simp[] >>
  goal_assum (drule_at (Pat `compile_revert_with_reason _ _ _ _ _ = _`)) >>
  gvs[] >> qexistsl [`LENGTH str`,`cx`,`es`] >> simp[] >>
  `LENGTH str < dimword(:256)` by decide_tac >> simp[] >> metis_tac[]
QED
