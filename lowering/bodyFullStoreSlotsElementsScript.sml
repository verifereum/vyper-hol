Theory bodyFullStoreSlotsElements
Ancestors
  bodyFullStoreSlotsTaintFold
  placeStoreSlots typedCopyOriginPtrBase typedMemoryCopy fragGasOriginPtrLoop
  emitHelperProps emitHelper compileEnv ptrDiscipline venomState
  venomExecSemantics venomInst codegenRel contextCodegenRel memSafeRun
  finite_map pred_set list words arithmetic decoderArraySetupPtr bodyPtrMakeArrayEmission

(* Control endpoints are chosen before the dead configuration. *)
Theorem store_slots_counter_init_uniform[local]:
  emit_inst ASSIGN [Lit 0w] [counter] a = ((),b) /\
  emit_inst JMP [Label hdr] [] b = ((),c) /\
  fn_has_code a c func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    t = jump_to hdr (update_var counter 0w s) /\
    Gf = DRESTRICT G (COMPL {counter}) /\
    tf = (tn with t_var := tn.t_var |+ (counter,{})) /\
    lookup_var counter t = SOME 0w /\ FLOOKUP Gf counter = NONE /\
    op_taint tf (Var counter) = {} /\
    store_copy_normalize s t = s /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    t.vs_call_ctx = s.vs_call_ctx /\ ~t.vs_halted /\
    t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    (!p. p <> counter ==> lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by simp[] >>
  drule_all typed_copy_origin_ptr_counter_init_path >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`,`ARB`] strip_assume_tac) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf)` by
    (gen_tac >> drule_all typed_copy_origin_ptr_counter_init_path >>
     disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`,`D`] strip_assume_tac) >>
     gvs[]) >>
  qexistsl [`t`,`Gf`,`tnf`] >>
  gvs[stmtSimStoreCopyTheory.store_copy_normalize_def, jump_to_def, update_var_def] >>
  simp[venom_state_component_equality]
QED

Theorem store_slots_header_entry_layout[local]:
  fresh_var c = (cv,init) /\
  emit_inst ASSIGN [Lit 0w] [cv] init = ((),p) /\
  emit_inst JMP [Label hdr] [] p = ((),q) /\
  new_block hdr q = (old,h) ==>
  not_fresh_at h cv /\ c.cs_next_var <= h.cs_next_var /\
  h.cs_current_bb = hdr /\ h.cs_current_insts = []
Proof
  strip_tac >>
  imp_res_tac emit_inst_extends >> imp_res_tac new_block_props >>
  qpat_x_assum `fresh_var c = _` mp_tac >>
  simp[fresh_var_def, LET_THM, pairTheory.PAIR_EQ] >> strip_tac >>
  gvs[loweringStateRelDefsTheory.not_fresh_at_def,
      ASCIInumbersTheory.toString_11]
QED

Theorem store_slots_header_uniform[local]:
  emit_op LT [Var counter; length] a = (lt,b) /\
  emit_op ISZERO [lt] b = (done,c) /\
  emit_inst JNZ [done; Label exit; Label blabel] [] c = ((),d) /\
  lookup_var counter s = SOME (n2w k) /\
  eval_operand length s = SOME (n2w N) /\ k <= N /\ N < dimword(:256) /\
  FLOOKUP G counter = NONE /\ op_prov G length = NONE /\
  op_taint tn (Var counter) = {} /\ op_taint tn length = {} /\
  fn_has_code a d func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?x y t Gf tf.
    lt = Var x /\ done = Var y /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    t = jump_to (if k = N then exit else blabel)
      (update_var y (if k = N then 1w else 0w)
        (update_var x (if k < N then 1w else 0w) s)) /\
    Gf = DRESTRICT (DRESTRICT G (COMPL {x})) (COMPL {y}) /\
    tf = (tn with t_var := (tn.t_var |+ (x,{})) |+ (y,{})) /\
    store_copy_normalize s t = s /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    t.vs_call_ctx = s.vs_call_ctx /\ ~t.vs_halted /\
    t.vs_current_bb = (if k = N then exit else blabel) /\ t.vs_inst_idx = 0 /\
    (!p. p <> x /\ p <> y ==> lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p)) /\
    (!p. not_fresh_at a p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by simp[] >>
  drule_all typed_copy_origin_ptr_header_branch_path >>
  disch_then (qspecl_then [`explicit`,`PG`,`ARB`] strip_assume_tac) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf)` by
    (gen_tac >> drule_all typed_copy_origin_ptr_header_branch_path >>
     disch_then (qspecl_then [`explicit`,`PG`,`D`] strip_assume_tac) >>
     gvs[]) >>
  `cs_extends a b /\ a.cs_next_var <= b.cs_next_var` by
    metis_tac[typed_copy_emit_op_mono, exprLoweringPropsTheory.ci_mono_def] >>
  `!p. not_fresh_at a p ==> p <> x /\ p <> y` by
    (gen_tac >> disch_tac >> conj_tac
     >- (irule emit_op_old_var_separate >>
         qexistsl [`[Var counter; length]`,`venomInst$LT`,`a`,`b`,`a`] >> simp[])
     >> irule emit_op_old_var_separate >>
     qexistsl [`[lt]`,`ISZERO`,`a`,`c`,`b`] >> simp[]) >>
  `!p. not_fresh_at a p ==> lookup_var p t = lookup_var p s /\
    FLOOKUP Gf p = FLOOKUP G p /\
    op_taint tnf (Var p) = op_taint tn (Var p)` by metis_tac[] >>
  qexistsl [`x`,`y`,`t`,`Gf`,`tnf`] >>
  gvs[stmtSimStoreCopyTheory.store_copy_normalize_def, jump_to_def, update_var_def] >>
  simp[venom_state_component_equality]
QED

Theorem store_slots_backedge_uniform[local]:
  emit_op ADD [Var counter;Lit 1w] a = (inc,b) /\
  emit_inst ASSIGN [inc] [counter] b = ((),c) /\
  emit_inst JMP [Label hdr] [] c = ((),d) /\
  not_fresh_at a counter /\
  lookup_var counter s = SOME (n2w k) /\ FLOOKUP G counter = NONE /\
  op_taint tn (Var counter) = {} /\ k < N /\ N < dimword(:256) /\
  fn_has_code a d func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s ==>
  ?out t Gf tf.
    inc = Var out /\ out <> counter /\ k+1 < dimword(:256) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    t = jump_to hdr (update_var counter (n2w (k+1))
      (update_var out (n2w (k+1)) s)) /\
    Gf = DRESTRICT (DRESTRICT G (COMPL {out})) (COMPL {counter}) /\
    tf = (tn with t_var := (tn.t_var |+ (out,{})) |+ (counter,{})) /\
    lookup_var counter t = SOME (n2w (k+1)) /\ FLOOKUP Gf counter = NONE /\
    op_taint tf (Var counter) = {} /\
    store_copy_normalize s t = s /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    t.vs_call_ctx = s.vs_call_ctx /\ ~t.vs_halted /\
    t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    (!p. p <> counter /\ p <> out ==> lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p)) /\
    (!p. not_fresh_at a p /\ p <> counter ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by simp[] >>
  drule_all typed_copy_origin_ptr_counter_backedge_path >> disch_tac >>
  qpat_assum `!explicit PG D. _`
    (qspecl_then [`explicit`,`PG`,`ARB`] strip_assume_tac) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf)` by
    (gen_tac >> qpat_assum `!explicit PG D. _`
       (qspecl_then [`explicit`,`PG`,`D`] strip_assume_tac) >> gvs[]) >>
  `!p. not_fresh_at a p ==> p <> out` by
    (gen_tac >> disch_tac >> irule emit_op_old_var_separate >>
     qexistsl [`[Var counter;Lit 1w]`,`ADD`,`a`,`b`,`a`] >> simp[]) >>
  `!p. not_fresh_at a p /\ p <> counter ==>
    lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
    op_taint tnf (Var p) = op_taint tn (Var p)` by metis_tac[] >>
  qexistsl [`out`,`t`,`Gf`,`tnf`] >>
  gvs[stmtSimStoreCopyTheory.store_copy_normalize_def, jump_to_def, update_var_def] >>
  simp[venom_state_component_equality] >> metis_tac[]
QED

(* Shift child-relative sparse keys into the enclosing prefix. *)
Theorem store_slots_taint_shift:
  !js X dw base off M.
    FOLDL (\Z j. key_update Z ((dw:bytes32)+n2w off+n2w j)
      (mem_word_taint M (base+32*off+32*j))) X js =
    FOLDL (\Z j. key_update Z (dw+n2w j)
      (mem_word_taint M (base+32*j))) X (MAP (\j. off+j) js)
Proof
  Induct >- simp[] >> rpt gen_tac >>
  pure_rewrite_tac[MAP, FOLDL] >> BETA_TAC >>
  first_x_assum (fn th => pure_once_rewrite_tac[th]) >>
  AP_THM_TAC >> AP_TERM_TAC >>
  simp_tac pure_ss [GSYM word_add_n2w, WORD_ADD_ASSOC, LEFT_ADD_DISTRIB, ADD_ASSOC] >>
  REFL_TAC
QED

(* Runtime/support part of one conditional child application. *)
Theorem store_slots_prefix_child_step[local]:
  store_slots_prefix sa tv el tr sw dw s i ks a /\
  store_copy_normalize a t =
    FOLDL (\q j. (if tr then tstore else sstore)
      ((dw + n2w (i * type_slot_size tv)) + n2w j)
      (mload (w2n (sw + n2w (i * type_memory_size tv)) + 32*j) a) q) a js /\
  w2n sw + i * type_memory_size tv < dimword (:256) /\
  encode_value tv (el i) = SOME writes /\
  (!j. MEM j js <=> MEM j (MAP FST writes)) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x a) /\
  t.vs_allocas = a.vs_allocas /\ t.vs_memory = a.vs_memory /\
  t.vs_labels = a.vs_labels /\ t.vs_call_ctx = a.vs_call_ctx /\
  ~t.vs_halted ==>
  store_slots_prefix sa tv el tr sw dw s (SUC i)
    (ks ++ MAP (\j. i * type_slot_size tv + j) js) t
Proof
  strip_tac >>
  qpat_x_assum `store_slots_prefix _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [store_slots_prefix_def]) >>
  pure_rewrite_tac[store_slots_prefix_def] >>
  conj_tac
  >- (irule store_slots_compose_fold >> conj_tac >- asm_rewrite_tac[] >>
      qexists_tac `a` >>
      asm_rewrite_tac[GSYM word_add_n2w, n2w_w2n]) >>
  conj_tac
  >- (irule store_slots_prefix_members_step >> metis_tac[]) >>
  simp[]
QED

Theorem store_slots_child_bank_bound:
  (!ks X Y (k:bytes32) (b:num) M. X SUBSET Y ==>
    FOLDL (\Z i. key_update Z (k+n2w i) (mem_word_taint M (b+32*i))) X ks
    SUBSET
    FOLDL (\Z i. key_update Z (k+n2w i) (mem_word_taint M (b+32*i))) Y ks) /\
  X SUBSET FOLDL (\Z j. key_update Z ((dw:bytes32)+n2w j)
    (mem_word_taint M ((off0:num)+32*j))) X0 ks /\
  Y SUBSET FOLDL (\Z j. key_update Z (dw+n2w off+n2w j)
    (mem_word_taint M (off0+32*off+32*j))) X js ==>
  Y SUBSET FOLDL (\Z j. key_update Z (dw+n2w j)
    (mem_word_taint M (off0+32*j))) X0 (ks ++ MAP (\j. off+j) js)
Proof
  strip_tac >>
  qpat_x_assum `Y SUBSET _` mp_tac >>
  rewrite_tac[store_slots_taint_shift, rich_listTheory.FOLDL_APPEND] >>
  strip_tac >> irule SUBSET_TRANS >>
  goal_assum (drule_at Any) >>
  first_x_assum irule >> asm_rewrite_tac[]
QED

(* Source-level sharing of the unchanged conditional proposition. *)
val elements_contract = ``
  ((!counter ss ds src dst sa sp dp sb s sw dw i tn N G func ctx lo explicit PG.
    (do so <- emit_op MUL [Var counter; Lit (n2w ss)];
        sp <- emit_op ADD [src; so];
        doff <- emit_op MUL [Var counter; Lit (n2w ds)];
        dp <- emit_op ADD [dst; doff]; comp_return (sp,dp)
     od) sa = ((sp,dp),sb) /\
    not_fresh_at sa counter /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    lookup_var counter s = SOME (n2w i) /\
    op_taint tn (Var counter) = {} /\ op_taint tn src = {} /\
    op_taint tn dst = {} /\ i < N /\
    w2n sw + N*ss < dimword(:256) /\
    w2n dw + N*ds <= dimword(:256) /\
    (ss <> 0 ==> ?x. src = Var x /\ ptr_covers G tn x s (N*ss)) /\
    fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
    allocas_from lo s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?vsp vdp t Gf tf.
      sp = Var vsp /\ dp = Var vdp /\
      not_fresh_at sb vsp /\ not_fresh_at sb vdp /\
      eval_operand sp t = SOME (sw+n2w (i*ss)) /\
      eval_operand dp t = SOME (dw+n2w (i*ds)) /\
      op_taint tf sp = {} /\ op_taint tf dp = {} /\
      (ss <> 0 ==> ptr_covers Gf tf vsp t ss) /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,Gf,tf)) /\
      store_copy_normalize s t = s /\
      tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
      tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x)) /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
      t.vs_call_ctx = s.vs_call_ctx /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts) /\
   (!ks X Y k b M. X SUBSET Y ==>
     FOLDL (\Z i. key_update Z (k+n2w i) (mem_word_taint M (b+32*i))) X ks SUBSET
     FOLDL (\Z i. key_update Z (k+n2w i) (mem_word_taint M (b+32*i))) Y ks)) ==>
  !cenv tenv elem etv.
  (!v src dst tr sa sb s sw dw tn G writes func ctx lo explicit PG.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !rt. evaluate_type tenv fty = SOME rt ==>
        sz = type_memory_size rt) fields) /\
    evaluate_type tenv elem = SOME etv /\ value_has_type etv v /\
    compile_store_slots cenv src dst elem tr sa = ((),sb) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    op_taint tn src = {} /\ op_taint tn dst = {} /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory etv v (w2n sw) mem) /\
    (type_memory_size etv <> 0 ==>
      ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size etv)) /\
    w2n sw + type_memory_size etv < dimword(:256) /\
    w2n dw + type_slot_size etv <= dimword(:256) /\
    (type_memory_size etv = 0 \/
      w2n sw + type_memory_size etv <= s.vs_alloca_next) /\
    encode_value etv v = SOME writes /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
    ~s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t ks Gf tnf.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,Gf,tnf)) /\
      store_copy_normalize s t =
        FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
          (mload (w2n sw+32*j) s) q) s ks /\
      (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
      (!x. not_fresh_at sa x ==>
        lookup_var x t = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\
        op_taint tnf (Var x) = op_taint tn (Var x)) /\
      tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
      (if tr then tnf.t_stor = tn.t_stor else tnf.t_trans = tn.t_trans) /\
      (if tr then tnf.t_trans else tnf.t_stor) SUBSET
        FOLDL (\X j. key_update X (dw+n2w j)
          (mem_word_taint tn.t_mem (w2n sw+32*j)))
          (if tr then tn.t_trans else tn.t_stor) ks /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts) ==>
  !el N src slot cnt tr sa sb func s sw dw tn G ctx lo explicit PG.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !rt. evaluate_type tenv fty = SOME rt ==>
        sz = type_memory_size rt) fields) /\
    evaluate_type tenv elem = SOME etv /\
    type_memory_bytes cenv elem = type_memory_size etv /\
    compile_copy_elements_to_slots cenv src slot elem cnt tr sa = ((),sb) /\
    (!i. i < N ==> value_has_type etv (el i) /\
      IS_SOME (encode_value etv (el i)) /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory etv (el i) (w2n sw+i*type_memory_size etv) mem)) /\
    (!x. src = Var x \/ slot = Var x \/ cnt = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
    eval_operand cnt s = SOME (n2w N) /\
    op_taint tn src = {} /\ op_taint tn slot = {} /\ op_taint tn cnt = {} /\
    op_prov G cnt = NONE /\ N < dimword(:256) /\
    w2n sw + N*type_memory_size etv < dimword(:256) /\
    w2n dw + N*type_slot_size etv <= dimword(:256) /\
    (type_memory_size etv <> 0 ==>
      ?x. src = Var x /\ ptr_covers G tn x s (N*type_memory_size etv)) /\
    (type_memory_size etv = 0 \/
      w2n sw + N*type_memory_size etv <= s.vs_alloca_next) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
    ~s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t ks Gf tnf.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,Gf,tnf)) /\
      store_copy_normalize s t =
        FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
          (mload (w2n sw+32*j) s) q) s ks /\
      (!k. MEM k ks <=> ?i writes j. i < N /\
        encode_value etv (el i) = SOME writes /\ MEM j (MAP FST writes) /\
        k = i*type_slot_size etv+j) /\
      (!x. not_fresh_at sa x ==>
        lookup_var x t = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\
        op_taint tnf (Var x) = op_taint tn (Var x)) /\
      tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
      (if tr then tnf.t_stor = tn.t_stor else tnf.t_trans = tn.t_trans) /\
      (if tr then tnf.t_trans else tnf.t_stor) SUBSET
        FOLDL (\X j. key_update X (dw+n2w j)
          (mem_word_taint tn.t_mem (w2n sw+32*j)))
          (if tr then tn.t_trans else tn.t_stor) ks /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts``;
val (elements_AM, elements_rest) = boolSyntax.dest_imp elements_contract;
val (elements_A, elements_M) = boolSyntax.dest_conj elements_AM;
val (_, elements_inner) = boolSyntax.strip_forall elements_rest;
val (elements_H, elements_goal) = boolSyntax.dest_imp elements_inner;

(* Compiler-only projection: package the four emitted address operations in
   the exact shape consumed by the conditional address interface. *)
Theorem store_slots_element_address_layout[local]:
  emit_op MUL [Var cv; Lit (n2w ss)] a = (so,b1) /\
  emit_op ADD [src; so] b1 = (sp,b2) /\
  emit_op MUL [Var cv; Lit (n2w ds)] b2 = (doff,b3) /\
  emit_op ADD [dst; doff] b3 = (dp,b) ==>
  (do so <- emit_op MUL [Var cv; Lit (n2w ss)];
      sp <- emit_op ADD [src; so];
      doff <- emit_op MUL [Var cv; Lit (n2w ds)];
      dp <- emit_op ADD [dst; doff]; comp_return (sp,dp)
   od) a = ((sp,dp),b)
Proof
  simp[comp_bind_def, comp_return_def]
QED

Theorem store_slots_element_body_conditional[local]:
  ^elements_A ==> ^elements_H ==>
  (do so <- emit_op MUL [Var cv; Lit (n2w (type_memory_size etv))];
      sp <- emit_op ADD [src; so];
      doff <- emit_op MUL [Var cv; Lit (n2w (type_slot_size etv))];
      dp <- emit_op ADD [slot; doff]; comp_return (sp,dp)
   od) body_start = ((sp,dp),child_start) /\
  compile_store_slots cenv sp dp elem tr child_start = ((),child_end) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !rt. evaluate_type tenv fty = SOME rt ==>
      sz = type_memory_size rt) fields) /\
  evaluate_type tenv elem = SOME etv /\
  value_has_type etv (el i) /\ encode_value etv (el i) = SOME writes /\
  not_fresh_at body_start cv /\
  (!x. src = Var x \/ slot = Var x ==> not_fresh_at body_start x) /\
  eval_operand src a = SOME sw /\ eval_operand slot a = SOME dw /\
  lookup_var cv a = SOME (n2w i) /\
  op_taint ta src = {} /\ op_taint ta slot = {} /\
  op_taint ta (Var cv) = {} /\ i < N /\
  w2n sw + N * type_memory_size etv < dimword (:256) /\
  w2n dw + N * type_slot_size etv <= dimword (:256) /\
  (type_memory_size etv <> 0 ==>
    ?x. src = Var x /\ ptr_covers Ga ta x a (N * type_memory_size etv)) /\
  (!mem. mem_agree_outside ta.t_mem a.vs_memory mem ==>
    val_in_memory etv (el i) (w2n sw + i * type_memory_size etv) mem) /\
  (type_memory_size etv = 0 \/
    w2n sw + N * type_memory_size etv <= a.vs_alloca_next) /\
  fn_has_code body_start child_start func /\
  fn_has_code child_start child_end func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ allocas_from lo a /\ lo <= a.vs_alloca_next /\
  ~a.vs_call_ctx.cc_static /\ ~a.vs_halted /\
  a.vs_current_bb = body_start.cs_current_bb /\
  a.vs_inst_idx = LENGTH body_start.cs_current_insts ==>
  ?b js Gb tb.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (a,Ga,ta) [] (OK b,Gb,tb)) /\
    store_copy_normalize a b =
      FOLDL (\q j. (if tr then tstore else sstore)
        (dw+n2w (i*type_slot_size etv)+n2w j)
        (mload (w2n sw+i*type_memory_size etv+32*j) a) q) a js /\
    (!j. MEM j js <=> MEM j (MAP FST writes)) /\
    (!x. not_fresh_at body_start x ==>
      lookup_var x b = lookup_var x a /\ FLOOKUP Gb x = FLOOKUP Ga x /\
      op_taint tb (Var x) = op_taint ta (Var x)) /\
    tb.t_mem = ta.t_mem /\ tb.t_imm = ta.t_imm /\
    (if tr then tb.t_stor = ta.t_stor else tb.t_trans = ta.t_trans) /\
    (if tr then tb.t_trans else tb.t_stor) SUBSET
      FOLDL (\X j. key_update X (dw+n2w (i*type_slot_size etv)+n2w j)
        (mem_word_taint ta.t_mem (w2n sw+i*type_memory_size etv+32*j)))
        (if tr then ta.t_trans else ta.t_stor) js /\
    b.vs_memory = a.vs_memory /\ b.vs_allocas = a.vs_allocas /\
    b.vs_alloca_next = a.vs_alloca_next /\ b.vs_labels = a.vs_labels /\
    b.vs_call_ctx = a.vs_call_ctx /\ ~b.vs_halted /\
    b.vs_current_bb = child_end.cs_current_bb /\
    b.vs_inst_idx = LENGTH child_end.cs_current_insts
Proof
  disch_then (fn address => disch_then (mk_asm "child") >> strip_tac >>
    `(!x. src = Var x ==> not_fresh_at body_start x) /\
     (!x. slot = Var x ==> not_fresh_at body_start x)` by metis_tac[] >>
    drule_at (Pos hd) address) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  drule_all store_slots_element_bounds >> strip_tac >>
  `w2n (sw+n2w (i*type_memory_size etv)) =
     w2n sw+i*type_memory_size etv` by
    metis_tac[GSYM word_add_n2w, n2w_w2n] >>
  `i+1 <= N` by decide_tac >>
  `type_memory_size etv + i*type_memory_size etv <= N*type_memory_size etv` by
    (qspecl_then [`i+1`,`N`,`type_memory_size etv`] mp_tac LESS_MONO_MULT >>
     pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac) >>
  `(!x. sp = Var x \/ dp = Var x ==> not_fresh_at child_start x)` by
    (gvs[] >> metis_tac[]) >>
  asm_x "child" (drule_at (Pat `compile_store_slots _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `encode_value _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand sp _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand dp _ = _`)) >>
  disch_then (qspecl_then [`tf`,`Gf`,`func`,`ctx`,`lo`,`explicit`,`PG`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC,
      gvs[allocas_from_def, WORD_ADD_0] >> metis_tac[]])) >>
  strip_tac >> (
  `!x. not_fresh_at body_start x ==> not_fresh_at child_start x` by
    (qpat_x_assum `do _ od body_start = _` mp_tac >>
     simp[comp_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >>
     imp_res_tac typed_copy_emit_op_mono >>
     metis_tac[loweringShapeDefsTheory.not_fresh_at_mono,
       exprLoweringPropsTheory.ci_mono_def]) >>
  qexistsl [`t'`,`ks`,`Gf'`,`tnf`] >>
  conj_tac >- (gen_tac >> irule gas_origin_ptr_path_trans >>
    qexistsl [`Gf`,`t`,`tf`] >> simp[]) >>
  conj_tac >- (
    qpat_x_assum `store_copy_normalize t t' = _` mp_tac >>
    disch_then (mp_tac o AP_TERM ``store_copy_normalize a``) >>
    simp[store_slots_normalize_compose, store_slots_normalize_fold,
      mload_def]) >>
  gvs[WORD_ADD_0] >> metis_tac[])
QED

(* Shared syntax only: these fragments introduce no logical constants. *)
val elements_I = fn i => fn u => fn ks => fn Gu => fn tu => ``
  store_slots_prefix sa etv el tr sw dw s ^i ^ks ^u /\
  (!x. not_fresh_at sa x ==> FLOOKUP ^Gu x = FLOOKUP G x /\
    op_taint ^tu (Var x) = op_taint tn (Var x)) /\
  (^tu).t_mem = tn.t_mem /\ (^tu).t_imm = tn.t_imm /\
  (if tr then (^tu).t_stor = tn.t_stor else (^tu).t_trans = tn.t_trans) /\
  (if tr then (^tu).t_trans else (^tu).t_stor) SUBSET
    FOLDL (\X j. key_update X (dw+n2w j)
      (mem_word_taint tn.t_mem (w2n sw+32*j)))
      (if tr then tn.t_trans else tn.t_stor) ^ks /\
  (^u).vs_alloca_next = s.vs_alloca_next /\
  lookup_var cv ^u = SOME (n2w ^i) /\ FLOOKUP ^Gu cv = NONE /\
  op_taint ^tu (Var cv) = {} /\
  (^u).vs_current_bb = hdr /\ (^u).vs_inst_idx = 0``;

val elements_layout_syntax = fn child_start => fn child_end => fn body_label => ``
  emit_op LT [Var cv; cnt] h = (lt,h1) /\
  emit_op ISZERO [lt] h1 = (done,h2) /\
  emit_inst JNZ [done; Label exit; Label ^body_label] [] h2 = ((),hj) /\
  (do so <- emit_op MUL [Var cv; Lit (n2w (type_memory_size etv))];
      sp <- emit_op ADD [src; so];
      doff <- emit_op MUL [Var cv; Lit (n2w (type_slot_size etv))];
      dp <- emit_op ADD [slot; doff]; comp_return (sp,dp)
   od) body_start = ((sp,dp),^child_start) /\
  compile_store_slots cenv sp dp elem tr ^child_start = ((),^child_end) /\
  emit_op ADD [Var cv; Lit 1w] ^child_end = (inc,tail1) /\
  emit_inst ASSIGN [inc] [cv] tail1 = ((),tail2) /\
  emit_inst JMP [Label hdr] [] tail2 = ((),tail3) /\
  h.cs_current_bb = hdr /\ h.cs_current_insts = [] /\
  body_start.cs_current_bb = ^body_label /\ body_start.cs_current_insts = [] /\
  not_fresh_at h cv /\ not_fresh_at body_start cv /\
  not_fresh_at ^child_end cv /\ ~not_fresh_at sa cv /\
  (!x. not_fresh_at sa x ==> not_fresh_at h x /\
    not_fresh_at body_start x /\ not_fresh_at ^child_end x) /\
  fn_has_code h hj func /\ fn_has_code body_start ^child_start func /\
  fn_has_code ^child_start ^child_end func /\ fn_has_code ^child_end tail3 func``;

val elements_round_layout = elements_layout_syntax
  ``child_start:compile_state`` ``child_end:compile_state`` ``body_label:string``;
val elements_actual_layout = elements_layout_syntax
  ``sc:compile_state`` ``sd:compile_state`` ``body':string``;

Theorem store_slots_elements_round_conditional[local]:
  ^elements_A ==> ^elements_M ==> ^elements_H ==>
  ^elements_round_layout ==>
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !rt. evaluate_type tenv fty = SOME rt ==>
      sz = type_memory_size rt) fields) /\
  evaluate_type tenv elem = SOME etv /\
  (!j. j < N ==> value_has_type etv (el j) /\
    IS_SOME (encode_value etv (el j)) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory etv (el j) (w2n sw+j*type_memory_size etv) mem)) /\
  (!x. src = Var x \/ slot = Var x \/ cnt = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
  eval_operand cnt s = SOME (n2w N) /\
  op_taint tn src = {} /\ op_taint tn slot = {} /\ op_taint tn cnt = {} /\
  op_prov G cnt = NONE /\ N < dimword(:256) /\
  w2n sw+N*type_memory_size etv < dimword(:256) /\
  w2n dw+N*type_slot_size etv <= dimword(:256) /\
  (type_memory_size etv <> 0 ==>
    ?x. src = Var x /\ ptr_covers G tn x s (N*type_memory_size etv)) /\
  (type_memory_size etv = 0 \/
    w2n sw+N*type_memory_size etv <= s.vs_alloca_next) /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_call_ctx.cc_static ==>
  !i u ks Gu tu.
  ^(elements_I ``i:num`` ``u:venom_state`` ``ks:num list``
    ``Gu:string |-> num # num`` ``tu:taint``) ==> i < N ==>
  ?v js Gv tv.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (u,Gu,tu) [] (OK v,Gv,tv)) /\
    ^(elements_I ``SUC i`` ``v:venom_state`` ``js:num list``
      ``Gv:string |-> num # num`` ``tv:taint``)
Proof
  disch_then (mk_asm "address") >> disch_then (mk_asm "mono") >>
  disch_then (mk_asm "child") >> strip_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> disch_tac >> suspend "header"
QED

Resume store_slots_elements_round_conditional[header]:
  markerLib.RESUME_TAC >> (
  qpat_assum `store_slots_prefix _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [store_slots_prefix_def]) >>
  `eval_operand cnt u = SOME (n2w N) /\
   op_taint tu cnt = {} /\ op_prov Gu cnt = NONE` by
    (`eval_operand cnt u = eval_operand cnt s /\
      op_taint tu cnt = op_taint tn cnt /\ op_prov Gu cnt = op_prov G cnt` by
      (irule old_operand_ghost_frame >> conj_tac >-
       (qexists_tac `sa` >> simp[] >> metis_tac[]) >> simp[] >> metis_tac[]) >>
     simp[]) >>
  `allocas_from lo u` by (fs[allocas_from_def] >> metis_tac[]) >>
  `u.vs_current_bb = h.cs_current_bb /\
   u.vs_inst_idx = LENGTH h.cs_current_insts /\ i <= N` by simp[] >>
  drule_all store_slots_header_uniform >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `store_slots_prefix sa etv el tr sw dw s i ks t` by
    (irule store_slots_prefix_transfer >> conj_tac >- simp[] >>
     qexists_tac `u` >> simp[] >>
     metis_tac[GSYM store_slots_normalize_compose]) >>
  `(!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
   lookup_var cv t = SOME (n2w i) /\ FLOOKUP Gf cv = NONE /\
   op_taint tf (Var cv) = {}` by
    (conj_tac >-
      (gen_tac >> strip_tac >>
       qpat_x_assum `!p. not_fresh_at h p ==> _`
         (qspec_then `x'` mp_tac) >> simp[] >> metis_tac[]) >>
     qpat_x_assum `!p. not_fresh_at h p ==> _`
       (qspec_then `cv` mp_tac) >> simp[]) >>
  suspend "child_entry")
QED

Resume store_slots_elements_round_conditional[child_entry]:
  markerLib.RESUME_TAC >> (
  `eval_operand src t = SOME sw /\ eval_operand slot t = SOME dw /\
   op_taint tf src = {} /\ op_taint tf slot = {}` by
    (`eval_operand src t = eval_operand src s /\
      op_taint tf src = op_taint tn src /\ op_prov Gf src = op_prov G src` by
       (irule old_operand_ghost_frame >> conj_tac >-
        (qexists_tac `sa` >> simp[] >> metis_tac[]) >> simp[] >> metis_tac[]) >>
     `eval_operand slot t = eval_operand slot s /\
      op_taint tf slot = op_taint tn slot /\ op_prov Gf slot = op_prov G slot` by
       (irule old_operand_ghost_frame >> conj_tac >-
        (qexists_tac `sa` >> simp[] >> metis_tac[]) >> simp[] >> metis_tac[]) >>
     simp[]) >>
  `!vsrc. src = Var vsrc /\ ptr_covers G tn vsrc s (N*type_memory_size etv) ==>
     ptr_covers Gf tf vsrc t (N*type_memory_size etv)` by
    (rpt strip_tac >>
     irule appendStorageGhostPtrTheory.ptr_covers_old_transport >>
     qexistsl [`G`,`s`,`sa`,`tn`] >> simp[] >> gvs[]) >>
  `type_memory_size etv <> 0 ==>
    ?x. src = Var x /\ ptr_covers Gf tf x t (N*type_memory_size etv)` by metis_tac[] >>
  qpat_assum `!j. j < N ==> _` (qspec_then `i` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `allocas_from lo t` by
    (fs[allocas_from_def] >> metis_tac[]) >>
  Cases_on `encode_value etv (el i)` >- fs[] >>
  asm "address" (fn ath => asm "child" (fn hth =>
    drule_at (Pos hd) (MATCH_MP (MATCH_MP store_slots_element_body_conditional ath) hth))) >>
  disch_then (drule_at (Pat `encode_value _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand src _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand slot _ = _`)) >>
  disch_then (drule_at (Pat `compile_store_slots _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `op_taint _ src = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (qspecl_then [`lo`,`func`,`explicit`,`ctx`,`PG`] mp_tac) >>
  (impl_tac >-
    (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       simp[] >> metis_tac[], fs[allocas_from_def] >> metis_tac[]])) >>
  strip_tac >> suspend "child_exit")
QED

Resume store_slots_elements_round_conditional[child_exit]:
  markerLib.RESUME_TAC >> (
  `w2n sw + i * type_memory_size etv < dimword(:256)` by
    (irule LESS_EQ_LESS_TRANS >> qexists_tac `w2n sw + N*type_memory_size etv` >>
     simp[] >> irule LESS_MONO_MULT >> simp[]) >>
  `w2n (sw + n2w (i * type_memory_size etv)) =
     w2n sw + i * type_memory_size etv` by
    (`i * type_memory_size etv < dimword(:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w]) >>
  `!p. not_fresh_at sa p ==> lookup_var p b = lookup_var p t /\
     FLOOKUP Gb p = FLOOKUP Gf p /\ op_taint tb (Var p) = op_taint tf (Var p)` by
    (rpt strip_tac >> qpat_x_assum `!x. not_fresh_at body_start x ==> _`
       (qspec_then `p` mp_tac) >> simp[] >> metis_tac[]) >>
  `store_slots_prefix sa etv el tr sw dw s (SUC i)
     (ks ++ MAP (\j. i*type_slot_size etv+j) js) b` by
    (irule store_slots_prefix_child_step >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexists_tac `x'` >> simp[]) >>
     qexists_tac `t` >>
     simp[wordsTheory.w2n_add, wordsTheory.w2n_n2w] >> metis_tac[]) >>
  `(if tr then tb.t_trans else tb.t_stor) SUBSET
     FOLDL (\X j. key_update X (dw+n2w j)
       (mem_word_taint tn.t_mem (w2n sw+32*j)))
       (if tr then tn.t_trans else tn.t_stor)
       (ks ++ MAP (\j. i*type_slot_size etv+j) js)` by
    suspend "bank_bound" >>
  `lookup_var cv b = SOME (n2w i) /\ FLOOKUP Gb cv = NONE /\
     op_taint tb (Var cv) = {}` by
    (qpat_assum `!x. not_fresh_at body_start x ==> _`
       (qspec_then `cv` mp_tac) >> simp[]) >>
  `allocas_from lo b` by
    (qpat_assum `allocas_from lo t` mp_tac >>
     pure_rewrite_tac[allocas_from_def] >>
     qpat_assum `b.vs_allocas = t.vs_allocas` (fn th => rewrite_tac[th]) >> simp[]) >>
  drule_all store_slots_backedge_uniform >> strip_tac >>
  suspend "backedge_exit")
QED

Resume store_slots_elements_round_conditional[bank_bound]:
  markerLib.RESUME_TAC >> (irule store_slots_child_bank_bound >> conj_tac >-
  (MATCH_ACCEPT_TAC store_slots_taint_fold_mono) >>
  qexists_tac `if tr then tf.t_trans else tf.t_stor` >>
  conj_tac >- (pure_asm_rewrite_tac[] >> first_assum ACCEPT_TAC) >>
  qpat_assum `(if tr then tb.t_trans else tb.t_stor) SUBSET _` mp_tac >>
  qpat_assum `tf.t_mem = tu.t_mem` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `tu.t_mem = tn.t_mem` (fn th => pure_rewrite_tac[th]) >>
  pure_rewrite_tac[valueEncodingPropsTheory.type_memory_size_slots, MULT_ASSOC] >>
  simp_tac bool_ss [AC MULT_ASSOC MULT_COMM])
QED

Resume store_slots_elements_round_conditional[backedge_exit]:
  markerLib.RESUME_TAC >> (
  qpat_x_assum `!explicit PG. ?out t Gf tf. _`
    (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `!p. not_fresh_at sa p ==> lookup_var p t' = lookup_var p b /\
     FLOOKUP Gf' p = FLOOKUP Gb p /\
     op_taint tf' (Var p) = op_taint tb (Var p)` by
    (gen_tac >> disch_tac >>
     `p <> cv` by (strip_tac >> gvs[]) >>
     `not_fresh_at child_end p` by
       (qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at h x /\ _`
          (qspec_then `p` mp_tac) >> simp_tac bool_ss [] >>
        disch_then drule >> simp_tac bool_ss []) >>
     qpat_x_assum `!p. not_fresh_at child_end p /\ p <> cv ==> _`
       (qspec_then `p` mp_tac) >> asm_rewrite_tac[]) >>
  qexistsl [`t'`,`ks ++ MAP (\j. i*type_slot_size etv+j) js`,`Gf'`,`tf'`] >>
  conj_tac >-
    (gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl [`Gb`,`b`,`tb`] >> conj_tac >-
       (irule gas_origin_ptr_path_trans >> qexistsl [`Gf`,`t`,`tf`] >>
        conj_tac >> first_assum (irule o SPEC_ALL)) >>
     first_assum (irule o SPEC_ALL)) >>
  conj_tac >-
    (irule store_slots_prefix_transfer >> conj_tac >- simp[] >>
     qexists_tac `b` >> simp[] >>
     metis_tac[GSYM store_slots_normalize_compose]) >>
  conj_tac >-
    (gen_tac >> disch_tac >>
     qpat_assum `!p. not_fresh_at sa p ==> lookup_var p t' = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!p. not_fresh_at sa p ==> lookup_var p b = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`
       (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  asm_simp_tac bool_ss [ADD1] >>
  Cases_on `tr` >> fs[])
QED

Finalise store_slots_elements_round_conditional

Theorem compile_copy_elements_to_slots_origin_ptr_path_conditional:
  ^elements_contract
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "address") (mk_asm "mono")) >>
  rpt gen_tac >> disch_then (mk_asm "child") >> rpt gen_tac >> strip_tac >>
  drule store_slots_elements_layout >>
  disch_then (qspec_then `func` strip_assume_tac) >>
  suspend "finite_loop"
QED

Resume compile_copy_elements_to_slots_origin_ptr_path_conditional[finite_loop]:
  markerLib.RESUME_TAC >>
  imp_res_tac typed_copy_emit_op_mono >>
  imp_res_tac fragExecTheory.cs_extends_emit_inst >>
  imp_res_tac cs_extends_new_block >>
  imp_res_tac cs_extends_fresh_label >>
  imp_res_tac cs_extends_fresh_var >>
  fs[exprLoweringPropsTheory.ci_mono_def] >>
  drule_all store_slots_header_entry_layout >> strip_tac >>
  (SUBGOAL_THEN elements_actual_layout
    (fn th => mk_asm "layout" th >> strip_assume_tac th)
    >- suspend "compiler_layout") >>
  `cs_extends sa init /\ cs_extends init q /\ cs_extends q sb` by
    (rpt (qpat_x_assum `cs_extends _ _` mp_tac) >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     metis_tac[cs_extends_trans]) >>
  `fn_has_code init q func` by
    (irule fragExecTheory.fn_has_code_mid >> metis_tac[]) >>
  `init.cs_current_bb = sa.cs_current_bb /\
   init.cs_current_insts = sa.cs_current_insts` by
    (imp_res_tac fresh_label_props >>
     qpat_x_assum `fresh_var c = _` mp_tac >>
     simp[fresh_var_def] >> strip_tac >> gvs[]) >>
  `s.vs_current_bb = init.cs_current_bb /\
   s.vs_inst_idx = LENGTH init.cs_current_insts` by simp[] >>
  drule_all store_slots_counter_init_uniform >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`] strip_assume_tac) >>
  `!i. i <= N ==> ?u ks Gu tu.
     (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK u,Gu,tu)) /\
     store_slots_prefix sa etv el tr sw dw s i ks u /\
     (!x. not_fresh_at sa x ==> FLOOKUP Gu x = FLOOKUP G x /\
       op_taint tu (Var x) = op_taint tn (Var x)) /\
     tu.t_mem = tn.t_mem /\ tu.t_imm = tn.t_imm /\
     (if tr then tu.t_stor = tn.t_stor else tu.t_trans = tn.t_trans) /\
     (if tr then tu.t_trans else tu.t_stor) SUBSET
       FOLDL (\X j. key_update X (dw+n2w j)
         (mem_word_taint tn.t_mem (w2n sw+32*j)))
         (if tr then tn.t_trans else tn.t_stor) ks /\
     u.vs_alloca_next = s.vs_alloca_next /\
     lookup_var cv u = SOME (n2w i) /\ FLOOKUP Gu cv = NONE /\
     op_taint tu (Var cv) = {} /\
     u.vs_current_bb = hdr /\ u.vs_inst_idx = 0` by
    (Induct
     >- (strip_tac >> qexistsl [`t`,`[]`,`Gf`,`tf`] >>
         suspend "invariant_init") >>
     strip_tac >> suspend "invariant_round") >>
  suspend "invariant_exit"
QED

Resume compile_copy_elements_to_slots_origin_ptr_path_conditional[invariant_init]:
  markerLib.RESUME_TAC >>
  `!x. not_fresh_at sa x ==> x <> cv` by metis_tac[] >>
  simp[store_slots_prefix_def] >> metis_tac[]
QED

Resume compile_copy_elements_to_slots_origin_ptr_path_conditional[invariant_exit]:
  markerLib.RESUME_TAC >> (
  ntac 3 (pop_last_assum kall_tac) >>
  qpat_x_assum `!i. i <= N ==> _` (qspec_then `N` mp_tac) >>
  simp_tac bool_ss [LESS_EQ_REFL] >>
  disch_then (qx_choose_then `u` (qx_choose_then `ks`
    (qx_choose_then `Gu` (qx_choose_then `tu` strip_assume_tac)))) >>
  qpat_assum `store_slots_prefix _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [store_slots_prefix_def]) >>
  `eval_operand cnt u = SOME (n2w N) /\
   op_taint tu cnt = {} /\ op_prov Gu cnt = NONE` by
    (`eval_operand cnt u = eval_operand cnt s /\
      op_taint tu cnt = op_taint tn cnt /\ op_prov Gu cnt = op_prov G cnt` by
       (irule old_operand_ghost_frame >> conj_tac >- (qexists_tac `sa` >> simp[] >>
        metis_tac[]) >> simp[] >> metis_tac[]) >> simp[]) >>
  `cs_extends sa h /\ cs_extends h hj /\ cs_extends hj sb` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code h hj func` by
    (irule fragExecTheory.fn_has_code_mid >> metis_tac[]) >>
  `u.vs_current_bb = h.cs_current_bb /\
   u.vs_inst_idx = LENGTH h.cs_current_insts` by simp[] >>
  `allocas_from lo u` by
    (fs[allocas_from_def] >> rpt strip_tac >>
     first_x_assum irule >> metis_tac[]) >>
  `N <= N` by simp[] >>
  drule_all store_slots_header_uniform >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl [`t'`,`ks`,`Gf'`,`tf'`] >>
  conj_tac >- (gen_tac >> irule gas_origin_ptr_path_trans >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at h x` by
    (imp_res_tac fresh_label_props >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  qpat_assum `new_block exit tail3 = _`
    (strip_assume_tac o MATCH_MP new_block_props) >>
  `store_copy_normalize s t' = store_copy_normalize s u` by
    (qpat_x_assum `t' = _` (fn th => rewrite_tac[th]) >>
     rewrite_tac[stmtSimStoreCopyTheory.store_copy_normalize_jump,
       stmtSimStoreCopyTheory.store_copy_normalize_update]) >>
  qpat_x_assum `t' = _` kall_tac >>
  qpat_x_assum `Gf' = _` kall_tac >>
  qpat_x_assum `tf' = _` kall_tac >>

  conj_tac >- (asm_rewrite_tac[] >> simp_tac bool_ss [ADD_COMM]) >>
  conj_tac >- (qpat_x_assum `!k. MEM k ks <=> _` mp_tac >>
    simp_tac bool_ss [ADD_COMM]) >>
  conj_tac >- simp[] >>
  asm_rewrite_tac[] >>
  qpat_x_assum `_ SUBSET FOLDL _ _ ks` mp_tac >>
  simp_tac bool_ss [ADD_COMM, listTheory.LENGTH])
QED

Resume compile_copy_elements_to_slots_origin_ptr_path_conditional[invariant_round]:
  markerLib.RESUME_TAC >> (
  `i <= N /\ i < N` by decide_tac >>
  qpat_x_assum `i <= N ==> _` (fn th =>
    mp_tac th >> (impl_tac >- simp[]) >>
    disch_then (qx_choose_then `u` (qx_choose_then `ks`
      (qx_choose_then `Gu` (qx_choose_then `tu` strip_assume_tac))))) >>
  `?v js Gv tv.
     (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (u,Gu,tu) [] (OK v,Gv,tv)) /\
     ^(elements_I ``SUC i`` ``v:venom_state`` ``js:num list``
       ``Gv:string |-> num # num`` ``tv:taint``)` by
    (asm "address" (fn ath => asm "child" (fn hth =>
       asm "layout" (fn lth => irule (MATCH_MP
         (MATCH_MP (MATCH_MP (MATCH_MP
           store_slots_elements_round_conditional ath)
           store_slots_taint_fold_mono) hth) lth)))) >>
     suspend "round_static") >>
  qexistsl [`v`,`js`,`Gv`,`tv`] >>
  conj_tac >- (gen_tac >> irule gas_origin_ptr_path_trans >>
    qexistsl [`Gu`,`u`,`tu`] >> conj_tac >> first_assum (irule o SPEC_ALL)) >>
  asm_rewrite_tac[])
QED

Resume compile_copy_elements_to_slots_origin_ptr_path_conditional[compiler_layout]:
  markerLib.RESUME_TAC >>
  `type_memory_bytes cenv elem DIV 32 = type_slot_size etv` by
    (fs[valueEncodingPropsTheory.type_memory_size_slots]) >>
  imp_res_tac new_block_props >>
  imp_res_tac fresh_label_props >>
  imp_res_tac emit_inst_extends >>
  qpat_assum `fresh_var c = _` (strip_assume_tac o REWRITE_RULE [fresh_var_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at h x /\
     not_fresh_at body_start x /\ not_fresh_at sd x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[] >> metis_tac[cs_extends_trans]) >>
  `not_fresh_at body_start cv /\ not_fresh_at sd cv` by
    (conj_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `h` >> simp[] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code h hj func /\ fn_has_code body_start sc func /\
   fn_has_code sc sd func /\ fn_has_code sd tail3 func` by
    (rpt (qpat_x_assum `cs_extends _ _` mp_tac) >>
     qpat_x_assum `fn_has_code sa sb func` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     rpt conj_tac >> irule fragExecTheory.fn_has_code_mid >>
     metis_tac[cs_extends_trans]) >>
  qpat_assum `type_memory_bytes cenv elem DIV 32 = _`
    (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
  qpat_assum `type_memory_bytes cenv elem = _`
    (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
  simp[comp_bind_def, comp_return_def]
QED

Resume compile_copy_elements_to_slots_origin_ptr_path_conditional[round_static]:
  markerLib.RESUME_TAC >> (
  asm_simp_tac bool_ss [] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexists_tac `N` >> simp[]) >>
  qexists_tac `ks` >> asm_rewrite_tac[])
QED

Finalise compile_copy_elements_to_slots_origin_ptr_path_conditional
