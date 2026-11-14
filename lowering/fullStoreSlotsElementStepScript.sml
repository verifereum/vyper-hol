(* Uniform recursive element step and scalar backedge boundaries. *)
Theory fullStoreSlotsElementStep
Ancestors
  fullStoreSlotsElementAddress fullStoreSlotsElements fullStoreSlotsMemberFrame
  fullStoreSlotsMembers
  typedCopyOriginPtrBase fragGasOriginPtr context emitHelper exprLoweringProps
  loweringStateRelDefs compileEnv venomState ptrDiscipline venomInst
  finite_map list arithmetic words stateFrame stmtLoweringMono
  typedMemoryCopy fragExec pair

Theorem store_slots_element_backedge_origin_ptr:
  emit_op ADD [Var cv;Lit 1w] a = (Var inc,b) /\
  emit_inst ASSIGN [Var inc] [cv] b = ((),c) /\
  emit_inst JMP [Label hdr] [] c = ((),d) /\
  not_fresh_at a cv /\ lookup_var cv s = SOME (n2w j) /\
  FLOOKUP G cv = NONE /\ op_taint tn (Var cv) = {} /\
  j < n /\ n < dimword(:256) /\ fn_has_code a d func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s ==>
  inc <> cv /\ j+1 < dimword(:256) /\
  (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to hdr (update_var cv (n2w (j+1))
      (update_var inc (n2w (j+1)) s))),
     DRESTRICT (DRESTRICT G (COMPL {inc})) (COMPL {cv}),
     tn with t_var := (tn.t_var |+ (inc,{})) |+ (cv,{})))
Proof
  strip_tac >>
  drule_all typed_copy_origin_ptr_counter_backedge_path >>
  disch_then (fn th => assume_tac th >>
    qspecl_then [`ARB`,`ARB`,`ARB`] strip_assume_tac th) >>
  gvs[] >> rpt gen_tac >>
  first_x_assum (qspecl_then [`explicit`,`PG`,`D`] strip_assume_tac) >> gvs[]
QED

Theorem store_slots_element_body_code:
  emit_op MUL [Var cv;Lit (n2w ms)] sa = (Var so,sb) /\
  emit_op ADD [Var xs;Var so] sb = (Var sp,sc) /\
  emit_op MUL [Var cv;Lit (n2w slots)] sc = (Var off,sd) /\
  emit_op ADD [dst;Var off] sd = (Var dp,se) /\
  compile_store_slots cenv (Var sp) (Var dp) ty tr se = ((),sf) /\
  emit_op ADD [Var cv;Lit 1w] sf = (Var inc,sg) /\
  emit_inst ASSIGN [Var inc] [cv] sg = ((),sh) /\
  emit_inst JMP [Label hdr] [] sh = ((),si) /\
  fn_has_code sa si func ==>
  fn_has_code sa se func /\ fn_has_code se sf func /\
  fn_has_code sf si func /\
  (!p. not_fresh_at sa p ==> not_fresh_at se p /\
    not_fresh_at sf p /\ p <> inc)
Proof
  strip_tac >>
  `ci_mono sa sb /\ ci_mono sb sc /\ ci_mono sc sd /\
   ci_mono sd se /\ ci_mono se sf /\ ci_mono sf sg /\
   ci_mono sg sh /\ ci_mono sh si` by
    (metis_tac[typed_copy_emit_op_mono,ci_mono_emit_inst,
      cj 1 ci_mono_compile_store_slots,SND]) >>
  `cs_extends sa se /\ cs_extends se sf /\ cs_extends sf si` by
    metis_tac[ci_mono_def,cs_extends_trans] >>
  `fn_has_code sa se func /\ fn_has_code se sf func /\
   fn_has_code sf si func` by metis_tac[fn_has_code_split,cs_extends_trans] >>
  simp[] >> rpt strip_tac >>
  `not_fresh_at se p /\ not_fresh_at sf p` by
    metis_tac[ci_mono_def,freshWritesTheory.not_fresh_at_mono,LESS_EQ_TRANS] >>
  simp[] >> drule store_slots_add_code >> strip_tac >> gvs[]
QED

Theorem store_slots_element_step_origin_ptr:
  (!root slot tr sa sb func s sw dw writes G tn.
    compile_store_slots cenv (Var root) slot ty tr sa = ((),sb) /\
    not_fresh_at sa root /\ (!x. slot = Var x ==> not_fresh_at sa x) /\
    lookup_var root s = SOME sw /\ eval_operand slot s = SOME dw /\
    op_prov G slot = NONE /\ op_taint tn slot = {} /\ ptr_covers G tn root s (val_store_size tv v) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n sw) m) /\
    w2n sw + type_memory_size tv < dimword(:256) /\
    w2n dw + type_slot_size tv <= dimword(:256) /\
    encode_value tv v = SOME writes /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
    w2n sw + val_store_size tv v <= s.vs_alloca_next ==>
    ?Gf tf u ks.
      (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK u,Gf,tf)) /\
      store_copy_normalize s u =
        FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
          (mload (w2n sw+32*j) s) q) s ks /\
      u.vs_memory = s.vs_memory /\ tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
      (if tr then tf.t_trans else tf.t_stor) =
        FOLDL (\ta j. key_update ta (dw+n2w j)
          (mem_word_taint tn.t_mem (w2n sw+32*j)))
          (if tr then tn.t_trans else tn.t_stor) ks /\
      (if tr then tf.t_stor else tf.t_trans) =
        (if tr then tn.t_stor else tn.t_trans) /\
      (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
      u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
      u.vs_labels = s.vs_labels /\ u.vs_call_ctx = s.vs_call_ctx /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts) /\
  emit_op MUL [Var cv;Lit (n2w ms)] sa = (Var so,sb) /\
  emit_op ADD [Var xs;Var so] sb = (Var sp,sc) /\
  emit_op MUL [Var cv;Lit (n2w slots)] sc = (Var off,sd) /\
  emit_op ADD [dst;Var off] sd = (Var dp,se) /\
  compile_store_slots cenv (Var sp) (Var dp) ty tr se = ((),sf) /\
  emit_op ADD [Var cv;Lit 1w] sf = (Var inc,sg) /\
  emit_inst ASSIGN [Var inc] [cv] sg = ((),sh) /\
  emit_inst JMP [Label hdr] [] sh = ((),si) /\
  not_fresh_at sa cv /\ not_fresh_at sa xs /\
  (!p. dst = Var p ==> not_fresh_at sa p) /\
  lookup_var cv s = SOME (n2w j) /\ lookup_var xs s = SOME sw /\
  eval_operand dst s = SOME dw /\ op_prov G dst = NONE /\
  FLOOKUP G cv = NONE /\ op_taint tn (Var cv) = {} /\ op_taint tn dst = {} /\
  ptr_covers G tn xs s (n*ms) /\ j < n /\ n < dimword(:256) /\
  w2n sw+n*ms < dimword(:256) /\ w2n dw+n*slots <= dimword(:256) /\
  val_store_size tv v <= ms /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n sw+j*ms) m) /\
  w2n sw+j*ms+type_memory_size tv < dimword(:256) /\
  w2n dw+j*slots+type_slot_size tv <= dimword(:256) /\
  w2n sw+j*ms+val_store_size tv v <= s.vs_alloca_next /\
  encode_value tv v = SOME writes /\
  fn_has_code sa si func /\ fn_inst_ids_distinct func /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_call_ctx.cc_static /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?p tp u tu z Gf tf ks.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK z,Gf,tf)) /\
    execution_frame p = execution_frame s /\
    tp.t_mem = tn.t_mem /\ tp.t_imm = tn.t_imm /\
    tp.t_stor = tn.t_stor /\ tp.t_trans = tn.t_trans /\
    store_copy_normalize p u =
      FOLDL (\q k. (if tr then tstore else sstore)
        (n2w (w2n dw+j*slots)+n2w k)
        (mload (w2n sw+j*ms+32*k) p) q) p ks /\
    u.vs_memory = p.vs_memory /\ tu.t_mem = tp.t_mem /\ tu.t_imm = tp.t_imm /\
    (if tr then tu.t_trans else tu.t_stor) =
      FOLDL (\ta k. key_update ta (n2w (w2n dw+j*slots)+n2w k)
        (mem_word_taint tp.t_mem (w2n sw+j*ms+32*k)))
        (if tr then tp.t_trans else tp.t_stor) ks /\
    (if tr then tu.t_stor else tu.t_trans) =
      (if tr then tp.t_stor else tp.t_trans) /\
    (!k. MEM k ks <=> MEM k (MAP FST writes)) /\
    execution_frame z = execution_frame u /\
    tf.t_mem = tu.t_mem /\ tf.t_imm = tu.t_imm /\
    tf.t_stor = tu.t_stor /\ tf.t_trans = tu.t_trans /\
    lookup_var cv z = SOME (n2w (j+1)) /\ FLOOKUP Gf cv = NONE /\
    op_taint tf (Var cv) = {} /\ z.vs_current_bb = hdr /\ z.vs_inst_idx = 0 /\
    ~z.vs_halted /\ z.vs_allocas = s.vs_allocas /\
    z.vs_alloca_next = s.vs_alloca_next /\ z.vs_labels = s.vs_labels /\
    z.vs_call_ctx = s.vs_call_ctx /\
    (!x. not_fresh_at sa x /\ x <> cv ==>
      lookup_var x z = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all store_slots_element_body_code >> strip_tac >>
  drule_all store_slots_element_addresses_origin_ptr >>
  disch_then (qx_choose_then `p` (qx_choose_then `Gp`
    (qx_choose_then `tp` strip_assume_tac))) >>
  `p.vs_memory = s.vs_memory /\ p.vs_alloca_next = s.vs_alloca_next /\
   p.vs_allocas = s.vs_allocas /\ p.vs_labels = s.vs_labels /\
   p.vs_call_ctx = s.vs_call_ctx` by
    gvs[execution_frame_def,venom_state_component_equality] >>
  `w2n (n2w (w2n sw+j*ms):bytes32) = w2n sw+j*ms /\
   w2n (n2w (w2n dw+j*slots):bytes32) = w2n dw+j*slots` by
    (`w2n sw+j*ms < dimword(:256) /\
      w2n dw+j*slots < dimword(:256)` by
      (conj_tac >- decide_tac >>
       Cases_on `slots=0` >- simp[w2n_lt] >>
       `j*slots < n*slots` by simp[LT_MULT_RCANCEL] >> decide_tac) >> simp[]) >>
  `ptr_covers Gp tp sp p (val_store_size tv v)` by
    (gvs[bodyPtrDefsTheory.ptr_covers_def] >> decide_tac) >>
  `eval_operand (Var dp) p = SOME (n2w (w2n dw+j*slots))` by
    simp[eval_operand_def] >>
  `!m. mem_agree_outside tp.t_mem p.vs_memory m ==>
    val_in_memory tv v (w2n (n2w (w2n sw+j*ms):bytes32)) m` by simp[] >>
  qpat_x_assum `!root slot tr sa sb func s sw dw writes G tn. _` drule >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  simp[eval_operand_def,op_prov_def] >>
  disch_then drule_all >>
  disch_then (qx_choose_then `Gu` (qx_choose_then `tu`
    (qx_choose_then `u` (qx_choose_then `ks` strip_assume_tac)))) >>
  `not_fresh_at se cv /\ not_fresh_at sf cv` by metis_tac[] >>
  `lookup_var cv u = SOME (n2w j) /\ FLOOKUP Gu cv = NONE /\
   op_taint tu (Var cv) = {}` by metis_tac[] >>
  `allocas_from lo u` by metis_tac[allocas_from_def] >>
  drule_all store_slots_element_backedge_origin_ptr >> strip_tac >>
  qexistsl_tac [`p`,`tp`,`u`,`tu`,
    `jump_to hdr (update_var cv (n2w (j+1)) (update_var inc (n2w (j+1)) u))`,
    `DRESTRICT (DRESTRICT Gu (COMPL {inc})) (COMPL {cv})`,
    `tu with t_var := (tu.t_var |+ (inc,{})) |+ (cv,{})`,`ks`] >>
  conj_tac
  >- (rpt gen_tac >> metis_tac[gas_origin_ptr_path_append,APPEND_NIL]) >>
  simp[jump_to_def,update_var_def,lookup_var_def,FLOOKUP_DRESTRICT,
    FLOOKUP_UPDATE,op_taint_def,execution_frame_def] >>
  conj_tac
  >- (qpat_x_assum `execution_frame p = execution_frame s` mp_tac >>
      simp[execution_frame_def,venom_state_component_equality]) >>
  rpt strip_tac >> gvs[lookup_var_def,op_taint_def]
QED
