(* Uniform recursive element loop assembly. *)
Theory fullStoreSlotsElementRun
Ancestors
  fullStoreSlotsElementControlTransfer fullStoreSlotsElementBodyTransfer
  fullStoreSlotsElementRunLayout placeStoreSlots valueEncodingProps
  fullStoreSlotsElements fullStoreSlotsElementStep fullStoreSlotsElementLayout
  fullStoreSlotsUniformLoop fullStoreSlotsMemberFrame
  fragGasOriginPtr context emitHelper exprLoweringProps loweringStateRelDefs
  compileEnv venomState ptrDiscipline venomInst finite_map list arithmetic words
  stateFrame stmtLoweringMono typedMemoryCopy fragExec pair

Theorem store_slots_elements_origin_ptr:
  (!i. i<LENGTH vs ==> !root slot tr sa sb func s sw dw writes G tn.
    compile_store_slots cenv (Var root) slot ty tr sa = ((),sb) /\
    not_fresh_at sa root /\ (!x. slot = Var x ==> not_fresh_at sa x) /\
    lookup_var root s = SOME sw /\ eval_operand slot s = SOME dw /\
    op_prov G slot = NONE /\ op_taint tn slot = {} /\ ptr_covers G tn root s (val_store_size tv (EL i vs)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv (EL i vs) (w2n sw) m) /\
    w2n sw + type_memory_size tv < dimword(:256) /\
    w2n dw + type_slot_size tv <= dimword(:256) /\
    encode_value tv (EL i vs) = SOME writes /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
    w2n sw + val_store_size tv (EL i vs) <= s.vs_alloca_next ==>
    ?Gf tf u ks.
      (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK u,Gf,tf)) /\
      store_copy_normalize s u =
        FOLDL (\q k. (if tr then tstore else sstore) (dw+n2w k)
          (mload (w2n sw+32*k) s) q) s ks /\
      u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
      (if tr then tf.t_trans else tf.t_stor) =
        FOLDL (\ta k. key_update ta (dw+n2w k)
          (mem_word_taint tn.t_mem (w2n sw+32*k)))
          (if tr then tn.t_trans else tn.t_stor) ks /\
      (if tr then tf.t_stor else tf.t_trans) = (if tr then tn.t_stor else tn.t_trans) /\
      (!k. MEM k ks <=> MEM k (MAP FST writes)) /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
      u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
      u.vs_labels = s.vs_labels /\ u.vs_call_ctx = s.vs_call_ctx /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts) /\
  compile_copy_elements_to_slots cenv (Var root) dst ty cnt tr sb = ((),sc) /\
  type_memory_bytes cenv ty = type_memory_size tv /\ all_have_type tv vs /\
  not_fresh_at sb root /\ (!p. dst=Var p \/ cnt=Var p ==> not_fresh_at sb p) /\
  lookup_var root s0=SOME sw /\ eval_operand dst s0=SOME dw /\
  eval_operand cnt s0=SOME(n2w (LENGTH vs)) /\
  op_prov G0 dst=NONE /\ op_prov G0 cnt=NONE /\
  op_taint t0 dst={} /\ op_taint t0 cnt={} /\
  ptr_covers G0 t0 root s0 (LENGTH vs*type_memory_size tv) /\
  (!m. mem_agree_outside t0.t_mem s0.vs_memory m ==>
    elems_in_memory vs (w2n sw) tv m) /\
  LENGTH vs < dimword(:256) /\
  w2n sw+LENGTH vs*type_memory_size tv <= s0.vs_alloca_next /\
  w2n sw+LENGTH vs*type_memory_size tv < dimword(:256) /\
  w2n dw+LENGTH vs*type_slot_size tv <= dimword(:256) /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s0 /\ ~s0.vs_call_ctx.cc_static /\
  ~s0.vs_halted /\ s0.vs_current_bb=sb.cs_current_bb /\
  s0.vs_inst_idx=LENGTH sb.cs_current_insts ==>
  ?Gf tf u ks.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s0,G0,t0) [] (OK u,Gf,tf)) /\
    store_copy_normalize s0 u =
      FOLDL (\q k. (if tr then tstore else sstore) (dw+n2w k)
        (mload (w2n sw+32*k) s0) q) s0 ks /\
    u.vs_memory=s0.vs_memory /\ tf.t_mem=t0.t_mem /\ tf.t_imm=t0.t_imm /\
    (if tr then tf.t_trans else tf.t_stor) =
      FOLDL (\ta k. key_update ta (dw+n2w k)
        (mem_word_taint t0.t_mem (w2n sw+32*k)))
        (if tr then t0.t_trans else t0.t_stor) ks /\
    (if tr then tf.t_stor else tf.t_trans)=(if tr then t0.t_stor else t0.t_trans) /\
    (!k. MEM k ks <=> ?i w r. i<LENGTH vs /\ encode_value tv (EL i vs)=SOME w /\
      MEM r (MAP FST w) /\ k=i*type_slot_size tv+r) /\
    (!p. not_fresh_at sb p ==> lookup_var p u=lookup_var p s0 /\
      FLOOKUP Gf p=FLOOKUP G0 p /\ op_taint tf (Var p)=op_taint t0 (Var p)) /\
    u.vs_allocas=s0.vs_allocas /\ u.vs_alloca_next=s0.vs_alloca_next /\
    u.vs_labels=s0.vs_labels /\ u.vs_call_ctx=s0.vs_call_ctx /\
    ~u.vs_halted /\ u.vs_current_bb=sc.cs_current_bb /\
    u.vs_inst_idx=LENGTH sc.cs_current_insts
Proof
  strip_tac >> drule store_slots_elements_layout >>
  disch_then (qspec_then `func` strip_assume_tac) >>
  `?lv. lt=Var lv` by metis_tac[emitted_insts_emit_op_local] >>
  `?dv. done=Var dv` by metis_tac[emitted_insts_emit_op_local] >>
  `?sv. so=Var sv` by metis_tac[emitted_insts_emit_op_local] >>
  `?spv. sp=Var spv` by metis_tac[emitted_insts_emit_op_local] >>
  `?ov. doff=Var ov` by metis_tac[emitted_insts_emit_op_local] >>
  `?dpv. dp=Var dpv` by metis_tac[emitted_insts_emit_op_local] >>
  `?iv. inc=Var iv` by metis_tac[emitted_insts_emit_op_local] >>
  gvs[] >>
  `type_memory_size tv DIV 32 = type_slot_size tv` by
    simp[cj 1 type_memory_size_slots] >>
  drule_all store_slots_elements_run_layout >> strip_tac >>
  suspend "iterate"
QED

Resume store_slots_elements_origin_ptr[iterate]:
  qabbrev_tac `Inv = (\j G t q. j<=LENGTH vs /\
    lookup_var cv q=SOME(n2w j) /\ FLOOKUP G cv=NONE /\ op_taint t (Var cv)={} /\
    lookup_var root q=SOME sw /\ eval_operand dst q=SOME dw /\
    eval_operand cnt q=SOME(n2w (LENGTH vs)) /\ op_prov G dst=NONE /\
    op_prov G cnt=NONE /\ op_taint t dst={} /\ op_taint t cnt={} /\
    ptr_covers G t root q (LENGTH vs*type_memory_size tv) /\
    q.vs_memory=s0.vs_memory /\ q.vs_allocas=s0.vs_allocas /\
    q.vs_alloca_next=s0.vs_alloca_next /\ q.vs_labels=s0.vs_labels /\
    q.vs_call_ctx=s0.vs_call_ctx /\ t.t_mem=t0.t_mem /\ t.t_imm=t0.t_imm /\
    (!p. not_fresh_at sb p ==> lookup_var p q=lookup_var p s0 /\
      FLOOKUP G p=FLOOKUP G0 p /\ op_taint t (Var p)=op_taint t0 (Var p)) /\
    (?K. store_copy_normalize s0 q =
       FOLDL (\r k. (if tr then tstore else sstore) (dw+n2w k)
         (mload (w2n sw+32*k) s0) r) s0 K /\
      (if tr then t.t_trans else t.t_stor) =
       FOLDL (\ta k. key_update ta (dw+n2w k)
         (mem_word_taint t0.t_mem (w2n sw+32*k)))
         (if tr then t0.t_trans else t0.t_stor) K /\
      (if tr then t.t_stor else t.t_trans)=(if tr then t0.t_stor else t0.t_trans) /\
      (!k. MEM k K <=> ?i w r. i<j /\ encode_value tv (EL i vs)=SOME w /\
        MEM r (MAP FST w) /\ k=i*type_slot_size tv+r)))` >>
  qpat_assum `Abbrev (Inv = _)`
    (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  `!p. not_fresh_at sb p ==> p<>cv` by metis_tac[] >>
  drule_at (Pat `Inv = _`) store_slots_elements_init_transfer >>
  disch_then (drule_at (Pat `emit_inst ASSIGN _ _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_inst JMP _ _ _ = _`)) >>
  disch_then (qspecl_then [`lo`,`func`,`ctx`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  suspend "transfers"
QED

Resume store_slots_elements_origin_ptr[transfers]:
  `!j G tn q. j<=LENGTH vs /\ Inv j G tn q /\ ~q.vs_halted /\
     q.vs_current_bb=hdr /\ q.vs_inst_idx=0 ==>
     ?r G1 t1. (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (q,G,tn) [] (OK r,G1,t1)) /\ Inv j G1 t1 r /\ ~r.vs_halted /\
       r.vs_inst_idx=0 /\ r.vs_current_bb=(if j=LENGTH vs then exit else body')` by
    (rpt gen_tac >> strip_tac >>
     drule_at (Pat `Inv = _`) store_slots_elements_header_transfer >>
     disch_then (drule_at (Pat `emit_op LT _ _ = _`)) >>
     disch_then (drule_at (Pat `emit_op ISZERO _ _ = _`)) >>
     disch_then (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
     disch_then (qspecl_then [`tn`,`q'`,`lo`,`j`,`func`,`ctx`,`G`] mp_tac) >>
     (impl_tac >- (simp[] >>
       `q'.vs_allocas = s0.vs_allocas` by fs[Abbr `Inv`] >>
       conj_tac >- (qpat_x_assum `allocas_from lo s0` mp_tac >>
         simp[allocas_from_def]) >> first_assum ACCEPT_TAC)) >>
     simp[]) >>
  suspend "body"
QED

Resume store_slots_elements_origin_ptr[body]:
  qpat_assum `type_memory_size tv DIV 32 = _` (fn th =>
    qpat_x_assum `emit_op MUL _ b2 = _` (assume_tac o REWRITE_RULE[th])) >>
  `!j G tn q. j<LENGTH vs /\ Inv j G tn q /\ ~q.vs_halted /\
     q.vs_current_bb=body' /\ q.vs_inst_idx=0 ==>
     ?r G1 t1. (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (q,G,tn) [] (OK r,G1,t1)) /\ Inv (j+1) G1 t1 r /\ ~r.vs_halted /\
       r.vs_inst_idx=0 /\ r.vs_current_bb=hdr` by
    (rpt gen_tac >> strip_tac >>
     drule_at (Pat `Inv = _`) store_slots_elements_body_transfer >>
     disch_then (drule_at (Pat `emit_op MUL [Var cv; _] body_start = _`)) >>
     disch_then (drule_at (Pat `emit_op ADD [Var _; Var _] _ = _`)) >>
     disch_then (drule_at (Pat `emit_op MUL _ b2 = _`)) >>
     disch_then (drule_at (Pat `emit_op ADD [_; Var _] _ = _`)) >>
     disch_then (drule_at (Pat `compile_store_slots _ _ _ _ _ _ = _`)) >>
     disch_then (drule_at (Pat `emit_op ADD [Var cv; _] sd = _`)) >>
     disch_then (drule_at (Pat `emit_inst ASSIGN [Var iv] _ _ = _`)) >>
     disch_then (drule_at (Pat `emit_inst JMP _ _ tail2 = _`)) >>
     disch_then (qspecl_then [`tn`,`q'`,`lo`,`j`,`func`,`ctx`,`G`] mp_tac) >>
     (impl_tac >- (conj_tac
       >- (qpat_x_assum `!i. i<LENGTH vs ==> _` mp_tac >>
           simp_tac bool_ss [ADD_COMM] >>
           disch_tac >> rpt gen_tac >> disch_tac >>
           first_x_assum drule >> disch_tac >>
           rpt gen_tac >> strip_tac >>
           first_x_assum irule >> asm_rewrite_tac[] >>
           qexistsl [`root'`,`slot`] >> asm_rewrite_tac[]) >>
       simp[] >> conj_tac >- metis_tac[] >>
       simp[type_memory_size_slots] >>
       `q'.vs_allocas=s0.vs_allocas /\ q'.vs_call_ctx=s0.vs_call_ctx` by
         fs[Abbr `Inv`] >>
       asm_rewrite_tac[] >>
       qpat_x_assum `allocas_from lo s0` mp_tac >>
       simp[allocas_from_def])) >> simp[]) >>
  suspend "join"
QED

Resume store_slots_elements_origin_ptr[join]:
  qpat_x_assum `Inv = _` kall_tac >>
  qpat_x_assum `!i. i<LENGTH vs ==> _` kall_tac >>
  drule store_slots_uniform_loop_iterate >>
  disch_then (qspecl_then [`LENGTH vs`,`0`,`Gf`,`tf`,`u`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qx_choosel_then [`sf`,`Gend`,`tend`] strip_assume_tac) >>
  qpat_x_assum `!j G tn q. j <= _ /\ _ ==> _` kall_tac >>
  qpat_x_assum `!j G tn q. j < _ /\ _ ==> _` kall_tac >>
  qpat_x_assum `Inv 0 _ _ _` kall_tac >>
  qpat_x_assum `Inv (LENGTH vs) _ _ _` mp_tac >>
  simp_tac bool_ss [Abbr `Inv`] >> strip_tac >>
  rename1 `store_copy_normalize s0 sf = FOLDL _ s0 ks` >>
  qexistsl [`Gend`,`tend`,`sf`,`ks`] >>
  conj_tac >- metis_tac[fragGasCopyLoopTheory.origin_ptr_path_then] >>
  rule_assum_tac (SIMP_RULE bool_ss [ADD_COMM]) >>
  simp_tac bool_ss [ADD_COMM] >>
  asm_simp_tac bool_ss [ADD_COMM, LENGTH]
QED

Finalise store_slots_elements_origin_ptr
