(* Initialization and header transfers for the recursive element loop. *)
Theory fullStoreSlotsElementControlTransfer
Ancestors
  fullStoreSlotsElements fullStoreSlotsMemberFrame typedCopyOriginPtrBase
  fragGasOriginPtr context emitHelper exprLoweringProps loweringStateRelDefs
  compileEnv venomState ptrDiscipline venomInst finite_map list arithmetic words
  stateFrame stmtLoweringMono typedMemoryCopy fragExec pair bodyPtrDefs stmtSimStoreCopy

Theorem store_slots_elements_header_frame:
  emit_op LT [Var cv;cnt] a = (Var x,b) /\
  emit_op ISZERO [Var x] b = (Var y,c) /\
  emit_inst JNZ [Var y;Label exit;Label blabel] [] c = ((),d) /\
  lookup_var cv s = SOME (n2w j) /\
  eval_operand cnt s = SOME (n2w n) /\ j <= n /\ n < dimword(:256) /\
  FLOOKUP G cv = NONE /\ op_prov G cnt = NONE /\
  op_taint tn (Var cv) = {} /\ op_taint tn cnt = {} /\
  cv <> x /\ cv <> y /\ (!p. old p ==> p <> x /\ p <> y) /\
  fn_has_code a d func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?u Gf tf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tf)) /\
    execution_frame u = execution_frame s /\
    tf.t_mem = tn.t_mem /\ tf.t_imm = tn.t_imm /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    lookup_var cv u = SOME (n2w j) /\ FLOOKUP Gf cv = NONE /\
    op_taint tf (Var cv) = {} /\
    ~u.vs_halted /\ u.vs_inst_idx = 0 /\
    u.vs_current_bb = (if j=n then exit else blabel) /\
    (!p. old p ==> lookup_var p u = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all store_slots_elements_header_origin_ptr >> strip_tac >>
  qexistsl_tac [`jump_to (if j=n then exit else blabel)
      (update_var y (if j=n then 1w else 0w)
        (update_var x (if j<n then 1w else 0w) s))`,
    `DRESTRICT (DRESTRICT G (COMPL {x})) (COMPL {y})`,
    `tn with t_var := (tn.t_var |+ (x,{})) |+ (y,{})`] >>
  simp[jump_to_def,update_var_def,lookup_var_def,FLOOKUP_UPDATE,
    FLOOKUP_DRESTRICT,op_taint_def,execution_frame_def] >>
  rpt strip_tac >> gvs[op_taint_def,lookup_var_def] >>
  `p <> x /\ p <> y` by metis_tac[] >> simp[]
QED

Theorem store_slots_elements_init_transfer:
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
  emit_inst ASSIGN [Lit 0w] [cv] a = ((),b) /\
  emit_inst JMP [Label hdr] [] b = ((),c) /\ fn_has_code a c func /\
  ~s0.vs_halted /\ s0.vs_current_bb=a.cs_current_bb /\
  s0.vs_inst_idx=LENGTH a.cs_current_insts /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s0 /\
  not_fresh_at sa root /\
  (!p. dst=Var p \/ cnt=Var p ==> not_fresh_at sa p) /\
  (!p. not_fresh_at sa p ==> p<>cv) /\
  lookup_var root s0=SOME sw /\ eval_operand dst s0=SOME dw /\
  eval_operand cnt s0=SOME(n2w n) /\ op_prov G0 dst=NONE /\
  op_prov G0 cnt=NONE /\ op_taint t0 dst={} /\ op_taint t0 cnt={} /\
  ptr_covers G0 t0 root s0 (n*ms) ==>
  ?u Gf tf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s0,G0,t0) [] (OK u,Gf,tf)) /\
    Inv 0 Gf tf u /\ ~u.vs_halted /\ u.vs_inst_idx=0 /\ u.vs_current_bb=hdr
Proof
  strip_tac >> gvs[] >>
  qexistsl_tac [`jump_to hdr (update_var cv 0w s0)`,
    `DRESTRICT G0 (COMPL {cv})`, `t0 with t_var := t0.t_var |+ (cv,{})`] >>
  conj_tac >- (rpt gen_tac >>
    drule_all typed_copy_origin_ptr_counter_init_path >> simp[] >> metis_tac[]) >>
  simp[jump_to_def,update_var_def,lookup_var_def,FLOOKUP_DRESTRICT,
    op_taint_def,FLOOKUP_UPDATE] >>
  `root <> cv` by metis_tac[] >>
  `!p. dst=Var p \/ cnt=Var p ==> p<>cv` by metis_tac[] >>
  Cases_on `dst` >> Cases_on `cnt` >>
  gvs[eval_operand_def,lookup_var_def,op_prov_def,op_taint_def,
    FLOOKUP_DRESTRICT,FLOOKUP_UPDATE,ptr_covers_def] >>
  (conj_tac >- (rpt strip_tac >> `p <> cv` by metis_tac[] >> simp[])) >>
  qexists_tac `[]` >> simp[store_copy_normalize_def,venom_state_component_equality]
QED

Theorem store_slots_elements_header_transfer:
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
  emit_op LT [Var cv;cnt] a = (Var x,b) /\
  emit_op ISZERO [Var x] b = (Var y,c) /\
  emit_inst JNZ [Var y;Label exit;Label blabel] [] c = ((),d) /\
  fn_has_code a d func /\ ~s.vs_halted /\
  s.vs_current_bb=a.cs_current_bb /\ s.vs_inst_idx=LENGTH a.cs_current_insts /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ n < dimword(:256) /\
  cv<>x /\ cv<>y /\ not_fresh_at sa root /\
  (!p. dst=Var p \/ cnt=Var p ==> not_fresh_at sa p) /\
  (!p. not_fresh_at sa p ==> p<>x /\ p<>y) /\ Inv j G tn s ==>
  ?u Gf tf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tf)) /\
    Inv j Gf tf u /\ ~u.vs_halted /\ u.vs_inst_idx=0 /\
    u.vs_current_bb=(if j=n then exit else blabel)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `Inv = _` SUBST_ALL_TAC >>
  qpat_x_assum `(\j G t q. _) j G tn s` (strip_assume_tac o BETA_RULE) >>
  drule_all (Q.INST [`old` |-> `not_fresh_at sa`] store_slots_elements_header_frame) >>
  disch_then (qx_choosel_then [`u`,`Gf`,`tf`] strip_assume_tac) >>
  qexistsl_tac [`u`,`Gf`,`tf`] >>
  conj_tac >- simp[] >>
  `store_copy_normalize s0 u = store_copy_normalize s0 s` by
    (qpat_x_assum `execution_frame u = execution_frame s` mp_tac >>
     simp_tac (srw_ss()) [execution_frame_def,store_copy_normalize_def,
       venom_state_component_equality] >> strip_tac >> simp[]) >>
  qpat_x_assum `execution_frame u = execution_frame s` mp_tac >>
  simp[execution_frame_def,venom_state_component_equality] >> strip_tac >>
  `lookup_var root u = lookup_var root s /\ FLOOKUP Gf root=FLOOKUP G root /\
   op_taint tf (Var root)=op_taint tn (Var root)` by metis_tac[] >>
  `!op. (!p. op=Var p ==> not_fresh_at sa p) ==>
    eval_operand op u=eval_operand op s /\ op_prov Gf op=op_prov G op /\
    op_taint tf op=op_taint tn op` by
    (Cases >> simp[eval_operand_def,op_prov_def,op_taint_def] >> metis_tac[]) >>
  BETA_TAC >> asm_rewrite_tac[] >>
  ntac 6 (conj_tac >- metis_tac[]) >>
  conj_tac >- (fs[ptr_covers_def] >> metis_tac[]) >>
  qexists_tac `K'` >> simp[]
QED
