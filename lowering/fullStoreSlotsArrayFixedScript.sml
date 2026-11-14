(* Fixed sparse arrays use the common recursive element runner directly. *)
Theory fullStoreSlotsArrayFixed
Ancestors
  fullStoreSlotsElementRun bodyPtrSubscriptMemoryRebuild placeStoreSlots
  valueEncodingProps valueEncodingDefs valueEncoding vyperValueOperation
  vyperTypeValues vyperValue context emitHelper exprLoweringProps
  loweringStateRelDefs compileEnv venomState ptrDiscipline venomInst
  finite_map list rich_list arithmetic words bodyPtrDefs fragGasOriginPtr
  typedMemoryCopy fragExec stateFrame exprSimProps vyperTyping

Theorem store_slots_fixed_array_origin_ptr:
  (!v. value_has_type tv v ==> !root slot tr sa sb func s sw dw writes G tn.
    compile_store_slots cenv (Var root) slot ty tr sa = ((),sb) /\
    not_fresh_at sa root /\ (!x. slot = Var x ==> not_fresh_at sa x) /\
    lookup_var root s = SOME sw /\ eval_operand slot s = SOME dw /\
    op_prov G slot = NONE /\ op_taint tn slot = {} /\
    ptr_covers G tn root s (val_store_size tv v) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n sw) m) /\
    w2n sw + type_memory_size tv < dimword(:256) /\
    w2n dw + type_slot_size tv <= dimword(:256) /\
    encode_value tv v = SOME writes /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
    w2n sw + val_store_size tv v <= s.vs_alloca_next ==>
    ?Gf tf u ks.
      (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf)) /\
      store_copy_normalize s u = FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
        (mload (w2n sw+32*j) s) q) s ks /\
      u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
      (if tr then tf.t_trans else tf.t_stor) = FOLDL (\ta j. key_update ta (dw+n2w j)
        (mem_word_taint tn.t_mem (w2n sw+32*j))) (if tr then tn.t_trans else tn.t_stor) ks /\
      (if tr then tf.t_stor else tf.t_trans) = (if tr then tn.t_stor else tn.t_trans) /\
      (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
      u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
      u.vs_labels = s.vs_labels /\ u.vs_call_ctx = s.vs_call_ctx /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts) /\
  compile_store_slots cenv (Var root) dst (ArrayT ty (Fixed n)) tr sa = ((),sb) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  is_abi_dynamic cenv.ce_struct_fields (ArrayT ty (Fixed n)) /\
  type_memory_bytes cenv ty = type_memory_size tv /\ n < dimword(:256) /\
  well_formed_type_value tv /\
  value_has_type (ArrayTV tv (Fixed n)) (ArrayV (SArrayV sparse)) /\
  not_fresh_at sa root /\ (!x. dst = Var x ==> not_fresh_at sa x) /\
  lookup_var root s = SOME sw /\ eval_operand dst s = SOME dw /\
  op_prov G dst = NONE /\ op_taint tn dst = {} /\
  ptr_covers G tn root s (val_store_size (ArrayTV tv (Fixed n)) (ArrayV (SArrayV sparse))) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (ArrayTV tv (Fixed n)) (ArrayV (SArrayV sparse)) (w2n sw) m) /\
  w2n sw + type_memory_size (ArrayTV tv (Fixed n)) < dimword(:256) /\
  w2n dw + type_slot_size (ArrayTV tv (Fixed n)) <= dimword(:256) /\
  encode_value (ArrayTV tv (Fixed n)) (ArrayV (SArrayV sparse)) = SOME writes /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  w2n sw + val_store_size (ArrayTV tv (Fixed n)) (ArrayV (SArrayV sparse)) <= s.vs_alloca_next ==>
  ?Gf tf u ks.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf)) /\
    store_copy_normalize s u = FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
      (mload (w2n sw+32*j) s) q) s ks /\
    u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    (if tr then tf.t_trans else tf.t_stor) = FOLDL (\ta j. key_update ta (dw+n2w j)
      (mem_word_taint tn.t_mem (w2n sw+32*j))) (if tr then tn.t_trans else tn.t_stor) ks /\
    (if tr then tf.t_stor else tf.t_trans) = (if tr then tn.t_stor else tn.t_trans) /\
    (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_labels = s.vs_labels /\ u.vs_call_ctx = s.vs_call_ctx /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `all_have_type tv (array_elements (ArrayTV tv (Fixed n)) (SArrayV sparse))` by
    metis_tac[sarray_elements_have_type] >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    elems_in_memory (array_elements (ArrayTV tv (Fixed n)) (SArrayV sparse)) (w2n sw) tv m` by
    metis_tac[sarray_in_memory_elements] >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _`
    (strip_assume_tac o SRULE [Once compile_store_slots_def,is_bytestring_type_def]) >>
  `!k. MEM k (MAP FST writes) <=>
    ?i ew j. i < LENGTH (array_elements (ArrayTV tv (Fixed n)) (SArrayV sparse)) /\
      encode_value tv (EL i (array_elements (ArrayTV tv (Fixed n)) (SArrayV sparse))) = SOME ew /\
      MEM j (MAP FST ew) /\ k = i * type_slot_size tv + j` by
    (drule_all store_slots_sarray_support >>
     simp[array_elements_def,SF CONJ_ss]) >>
  pure_asm_rewrite_tac[] >>
  irule (Q.INST [`vs` |-> `array_elements (ArrayTV tv (Fixed n)) (SArrayV sparse)`]
    store_slots_elements_origin_ptr) >>
  `LENGTH (array_elements (ArrayTV tv (Fixed n)) (SArrayV sparse)) = n` by
    simp[array_elements_def] >>
  `w2n sw + n * type_memory_size tv < dimword(:256) /\
   w2n dw + n * type_slot_size tv <= dimword(:256) /\
   w2n sw + n * type_memory_size tv <= s.vs_alloca_next` by
    fs[type_memory_size_def,type_slot_size_def,val_store_size_def] >>
  asm_simp_tac bool_ss [] >>
  qexistsl [`cenv`,`Lit (n2w n)`,`dst`,`root`,`ty`] >>
  conj_tac >- (gen_tac >> disch_tac >>
    qpat_x_assum `!v. value_has_type tv v ==> _`
      (qspec_then `EL i (array_elements (ArrayTV tv (Fixed n)) (SArrayV sparse))` mp_tac) >>
    (impl_tac >- fs[all_have_type_EVERY,EVERY_EL]) >>
    asm_simp_tac bool_ss []) >>
  fs[eval_operand_def,op_prov_def,op_taint_def,
     val_store_size_def,type_memory_size_def,type_slot_size_def] >> gvs[]
QED
