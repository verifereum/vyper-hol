(* Cumulative live-slot transfers for recursive element stores. *)
Theory fullStoreSlotsElementBodyTransfer
Ancestors
  fullStoreSlotsElementStep fullStoreSlotsElementLayout fullStoreSlotsMemberFrame
  stateFrame stmtSimStoreCopy venomState ptrDiscipline bodyPtrDefs
  valueEncoding valueEncodingDefs list arithmetic words finite_map

Theorem store_slots_frame_pure_suffix:
  execution_frame z=execution_frame u /\
  tz.t_mem=tu.t_mem /\ tz.t_imm=tu.t_imm /\
  tz.t_stor=tu.t_stor /\ tz.t_trans=tu.t_trans /\
  store_copy_normalize s u =
    FOLDL (\q k. (if tr then tstore else sstore) (dw+n2w k)
      (mload (w2n sw+32*k) s) q) s ks /\
  u.vs_memory=s.vs_memory /\ tu.t_mem=tn.t_mem /\ tu.t_imm=tn.t_imm /\
  (if tr then tu.t_trans else tu.t_stor) =
    FOLDL (\ta k. key_update ta (dw+n2w k)
      (mem_word_taint tn.t_mem (w2n sw+32*k)))
      (if tr then tn.t_trans else tn.t_stor) ks /\
  (if tr then tu.t_stor else tu.t_trans)=(if tr then tn.t_stor else tn.t_trans) ==>
  store_copy_normalize s z =
    FOLDL (\q k. (if tr then tstore else sstore) (dw+n2w k)
      (mload (w2n sw+32*k) s) q) s ks /\
  z.vs_memory=s.vs_memory /\ tz.t_mem=tn.t_mem /\ tz.t_imm=tn.t_imm /\
  (if tr then tz.t_trans else tz.t_stor) =
    FOLDL (\ta k. key_update ta (dw+n2w k)
      (mem_word_taint tn.t_mem (w2n sw+32*k)))
      (if tr then tn.t_trans else tn.t_stor) ks /\
  (if tr then tz.t_stor else tz.t_trans)=(if tr then tn.t_stor else tn.t_trans)
Proof
  strip_tac >>
  `store_copy_normalize s z = store_copy_normalize s u` by
    (qpat_x_assum `execution_frame z = execution_frame u` mp_tac >>
     simp_tac (srw_ss()) [execution_frame_def,store_copy_normalize_def,
       venom_state_component_equality] >> strip_tac >> simp[]) >>
  `z.vs_memory=u.vs_memory` by
    (qpat_x_assum `execution_frame z = execution_frame u` mp_tac >>
     simp[execution_frame_def,venom_state_component_equality]) >>
  asm_rewrite_tac[]
QED


Theorem store_slots_element_body_frame:
  ms=32*slots /\ w2n (sw:bytes32)+j*ms < dimword(:256) /\
  execution_frame p=execution_frame s /\
  tp.t_mem=tn.t_mem /\ tp.t_imm=tn.t_imm /\
  tp.t_stor=tn.t_stor /\ tp.t_trans=tn.t_trans /\
  store_copy_normalize p u =
    FOLDL (\q k. (if tr then tstore else sstore)
      (n2w (w2n dw+j*slots)+n2w k)
      (mload (w2n sw+j*ms+32*k) p) q) p child /\
  u.vs_memory=p.vs_memory /\ tu.t_mem=tp.t_mem /\ tu.t_imm=tp.t_imm /\
  (if tr then tu.t_trans else tu.t_stor) =
    FOLDL (\ta k. key_update ta (n2w (w2n dw+j*slots)+n2w k)
      (mem_word_taint tp.t_mem (w2n sw+j*ms+32*k)))
      (if tr then tp.t_trans else tp.t_stor) child /\
  (if tr then tu.t_stor else tu.t_trans)=(if tr then tp.t_stor else tp.t_trans) /\
  execution_frame z=execution_frame u /\
  tf.t_mem=tu.t_mem /\ tf.t_imm=tu.t_imm /\
  tf.t_stor=tu.t_stor /\ tf.t_trans=tu.t_trans ==>
  store_copy_normalize s z =
    FOLDL (\q k. (if tr then tstore else sstore) (dw+n2w k)
      (mload (w2n sw+32*k) s) q) s (MAP ((+) (j*slots)) child) /\
  z.vs_memory=s.vs_memory /\ tf.t_mem=tn.t_mem /\ tf.t_imm=tn.t_imm /\
  (if tr then tf.t_trans else tf.t_stor) =
    FOLDL (\ta k. key_update ta (dw+n2w k)
      (mem_word_taint tn.t_mem (w2n sw+32*k)))
      (if tr then tn.t_trans else tn.t_stor) (MAP ((+) (j*slots)) child) /\
  (if tr then tf.t_stor else tf.t_trans)=(if tr then tn.t_stor else tn.t_trans)
Proof
  strip_tac >>
  `w2n (sw+n2w (32*(j*slots)))=w2n sw+j*ms` by
    (`j*ms=32*(j*slots)` by
       (qpat_x_assum `ms=32*slots` SUBST1_TAC >>
        simp_tac bool_ss [AC MULT_ASSOC MULT_COMM]) >>
     `w2n sw+32*(j*slots) < dimword(:256)` by metis_tac[] >>
     simp[w2n_add_2]) >>
  `n2w (w2n dw+j*slots):bytes32 = dw+n2w (j*slots)` by
    simp[GSYM word_add_n2w] >>
  qpat_assum `w2n (sw+n2w (32*(j*slots))) = _`
    (fn th =>
      qpat_x_assum `store_copy_normalize p u = _`
        (assume_tac o PURE_ONCE_REWRITE_RULE [GSYM th]) >>
      qpat_x_assum `(if tr then tu.t_trans else tu.t_stor) = _`
        (assume_tac o PURE_ONCE_REWRITE_RULE [GSYM th])) >>
  drule_all store_slots_frame_pure_prefix >> strip_tac >>
  drule_all store_slots_frame_pure_suffix >> strip_tac >>
  irule store_slots_frame_shift >> asm_rewrite_tac[] >> gvs[] >> decide_tac
QED

Theorem store_slots_elements_body_transfer:
  Inv = (\j G t q. j<=n /\ lookup_var cv q=SOME(n2w j) /\
    FLOOKUP G cv=NONE /\ op_taint t (Var cv)={} /\
    lookup_var root q=SOME sw /\ eval_operand dst q=SOME dw /\
    eval_operand cnt q=SOME(n2w n) /\ op_prov G dst=NONE /\
    op_prov G cnt=NONE /\ op_taint t dst={} /\ op_taint t cnt={} /\
    ptr_covers G t root q (n*ms) /\
    q.vs_memory=s0.vs_memory /\ q.vs_allocas=s0.vs_allocas /\
    q.vs_alloca_next=s0.vs_alloca_next /\ q.vs_labels=s0.vs_labels /\
    q.vs_call_ctx=s0.vs_call_ctx /\ t.t_mem=t0.t_mem /\ t.t_imm=t0.t_imm /\
    (!p. not_fresh_at sa p ==> lookup_var p q=lookup_var p s0 /\
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
        MEM r (MAP FST w) /\ k=i*slots+r))) /\
  (!i. i<n ==> !root slot tr sa sb func s sw dw writes G tn.
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
  emit_op MUL [Var cv;Lit (n2w ms)] a = (Var so,b) /\
  emit_op ADD [Var root;Var so] b = (Var sp,c) /\
  emit_op MUL [Var cv;Lit (n2w slots)] c = (Var off,d) /\
  emit_op ADD [dst;Var off] d = (Var dp,ee) /\
  compile_store_slots cenv (Var sp) (Var dp) ty tr ee = ((),f) /\
  emit_op ADD [Var cv;Lit 1w] f = (Var inc,g) /\
  emit_inst ASSIGN [Var inc] [cv] g = ((),h) /\
  emit_inst JMP [Label hdr] [] h = ((),ii) /\
  fn_has_code a ii func /\ fn_inst_ids_distinct func /\
  not_fresh_at a cv /\ not_fresh_at a root /\
  (!p. dst=Var p ==> not_fresh_at a p) /\
  not_fresh_at sa root /\ root<>cv /\
  (!p. dst=Var p \/ cnt=Var p ==> not_fresh_at a p /\ p<>cv) /\
  (!p. not_fresh_at sa p ==> not_fresh_at a p /\ p<>cv) /\
  ms=type_memory_size tv /\ slots=type_slot_size tv /\ ms=32*slots /\
  n=LENGTH vs /\ all_have_type tv vs /\ n<dimword(:256) /\
  (!m. mem_agree_outside t0.t_mem s0.vs_memory m ==>
    elems_in_memory vs (w2n sw) tv m) /\
  w2n sw+n*ms <= s0.vs_alloca_next /\
  w2n sw+n*ms < dimword(:256) /\ w2n dw+n*slots <= dimword(:256) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_call_ctx.cc_static /\
  ~s.vs_halted /\ s.vs_current_bb=a.cs_current_bb /\
  s.vs_inst_idx=LENGTH a.cs_current_insts /\ j<n /\ Inv j G tn s ==>
  ?z Gf tf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK z,Gf,tf)) /\
    Inv (j+1) Gf tf z /\ ~z.vs_halted /\ z.vs_inst_idx=0 /\ z.vs_current_bb=hdr
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `Inv = _` SUBST_ALL_TAC >>
  qpat_x_assum `(\j G t q. _) j G tn s` (strip_assume_tac o BETA_RULE) >>
  `value_has_type tv (EL j vs) /\
   (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv (EL j vs) (w2n sw+j*ms) m) /\
   w2n sw+j*ms+val_store_size tv (EL j vs) <= s.vs_alloca_next /\
   w2n dw+j*slots+type_slot_size tv <= dimword(:256)` by
    (qpat_x_assum `store_copy_normalize s0 s = _` kall_tac >>
     qpat_x_assum `!i. i<n ==> _` kall_tac >>
     gvs[] >> drule_all store_slots_element_resources >>
     strip_tac >> simp[] >> decide_tac) >>
  `val_store_size tv (EL j vs) <= ms` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf,
      exprSimPropsTheory.val_store_size_le] >>
  `w2n sw+j*ms+type_memory_size tv < dimword(:256)` by
    (`j*ms+ms <= n*ms` by
      (`(j+1)*ms <= n*ms` by
         (irule LESS_MONO_MULT >> decide_tac) >>
       qpat_x_assum `(j+1)*ms <= n*ms` mp_tac >>
       simp_tac bool_ss [RIGHT_ADD_DISTRIB,MULT_LEFT_1]) >>
     `ms=type_memory_size tv` by metis_tac[] >> decide_tac) >>
  `?writes. encode_value tv (EL j vs)=SOME writes` by
    metis_tac[cj 1 vyperTypingTheory.value_has_type_equiv,optionTheory.IS_SOME_EXISTS] >>
  qpat_x_assum `!i. i<n ==> _` (qspec_then `j` mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> disch_tac >>
  drule_all store_slots_element_step_origin_ptr >>
  disch_then (qx_choosel_then [`p`,`tp`,`u`,`tu`,`z`,`Gf`,`tf`,`child`]
    strip_assume_tac) >>
  suspend "assembly"
QED

Resume store_slots_elements_body_transfer[assembly]:
  `w2n sw+j*ms < dimword(:256)` by decide_tac >>
  drule_all store_slots_element_body_frame >> strip_tac >>
  drule_all store_slots_frame_append >> strip_tac >>
  qexistsl_tac [`z`,`Gf`,`tf`] >>
  BETA_TAC >>
  `lookup_var root z = lookup_var root s /\ FLOOKUP Gf root=FLOOKUP G root /\
   op_taint tf (Var root)=op_taint tn (Var root)` by metis_tac[] >>
  `!op. (!p. op=Var p ==> not_fresh_at a p /\ p<>cv) ==>
    eval_operand op z=eval_operand op s /\ op_prov Gf op=op_prov G op /\
    op_taint tf op=op_taint tn op` by
    (Cases >> simp[eval_operand_def,op_prov_def,op_taint_def] >> metis_tac[]) >>
  `ptr_covers Gf tf root z (n*ms)` by
    (qpat_x_assum `ptr_covers G tn root s (n*ms)` mp_tac >>
     pure_rewrite_tac[ptr_covers_def] >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >>
  conj_tac >- decide_tac >>
  ntac 6 (conj_tac >- metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  qexists_tac `K' ++ MAP ((+) (j*slots)) child` >>
  asm_rewrite_tac[] >>
  rewrite_tac[GSYM ADD1] >>
  irule (PURE_REWRITE_RULE [ETA_THM] (BETA_RULE
    (Q.INST [`el` |-> `\i. EL i vs`]
      placeStoreSlotsTheory.store_slots_prefix_members_step))) >>
  asm_rewrite_tac[] >> qexists_tac `writes` >> rewrite_tac[]
QED

Finalise store_slots_elements_body_transfer
