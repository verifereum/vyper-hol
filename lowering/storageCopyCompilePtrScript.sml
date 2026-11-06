(* Compiler/code registration boundary for checked storage-copy loops. *)
Theory storageCopyCompilePtr
Ancestors
  storageCopyLoopPtr storageCopyBodyLayout exprSimCopy exprSimStorageCopy
  fragExec exprLowering exprLoweringProps emitHelper emitHelperProps context
  compileEnv localPtrsProps moduleLoweringProps venomInst venomState
  list rich_list finite_map words arithmetic

Theorem storage_copy_registered_layout:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop src dst n loc LocMemory F sa = (u,sb) /\
  fn_has_code sa sb fn ==>
  ?hdr body exit cv tv sv vv mv dv nv ebb hbb bbb.
    lookup_block sa.cs_current_bb fn.fn_blocks = SOME ebb /\
    ebb.bb_instructions = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv];
       mk_inst (sa.cs_next_id+1) JMP [Label hdr] []] /\
    lookup_block hdr fn.fn_blocks = SOME hbb /\
    hbb.bb_instructions =
      [mk_inst (sa.cs_next_id+2) EQ [Var cv;Lit (n2w n)] [tv];
       mk_inst (sa.cs_next_id+3) JNZ [Var tv;Label exit;Label body] []] /\
    lookup_block body fn.fn_blocks = SOME bbb /\
    bbb.bb_instructions =
      [mk_inst (sa.cs_next_id+4) ADD [src;Var cv] [sv];
       mk_inst (sa.cs_next_id+5) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
       mk_inst (sa.cs_next_id+6) MUL [Var cv;Lit 32w] [mv];
       mk_inst (sa.cs_next_id+7) ADD [dst;Var mv] [dv];
       mk_inst (sa.cs_next_id+8) MSTORE [Var dv;Var vv] [];
       mk_inst (sa.cs_next_id+9) ADD [Var cv;Lit 1w] [nv];
       mk_inst (sa.cs_next_id+10) ASSIGN [Var nv] [cv];
       mk_inst (sa.cs_next_id+11) JMP [Label hdr] []] /\
    ALL_DISTINCT [tv;cv;sv;vv;mv;dv;nv] /\
    (!x. not_fresh_at sa x ==> ~MEM x [tv;cv;sv;vv;mv;dv;nv]) /\
    sb.cs_current_bb = exit /\ sb.cs_current_insts = []
Proof
  strip_tac >>
  qpat_x_assum `compile_word_copy_loop _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `loc = LocStorage` >> gvs[] >>
  simp[compile_word_copy_loop_def, word_scale_def, compile_ptr_load_def,
       compile_ptr_store_def, emit_op_def, emit_void_def, emit_inst_def,
       fresh_label_def, fresh_var_def, fresh_id_def, emit_def, new_block_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  qmatch_goalsub_abbrev_tac `fn_has_code sa sc fn` >>
  pure_rewrite_tac[fn_has_code_def, emitted_blocks_def] >>
  simp[Abbr `sc`, LENGTH, TAKE, MEM, DISJ_IMP_THM, FORALL_AND_THM] >> strip_tac >>
  qexistsl [`fresh_label_output "wcopy_cond" sa.cs_next_label`,
    `fresh_label_output "wcopy_body" (sa.cs_next_label+1)`,
    `STRING #"%" (toString sa.cs_next_var)`,
    `STRING #"%" (toString (sa.cs_next_var+1))`,
    `STRING #"%" (toString (sa.cs_next_var+2))`,
    `STRING #"%" (toString (sa.cs_next_var+3))`,
    `STRING #"%" (toString (sa.cs_next_var+4))`,
    `STRING #"%" (toString (sa.cs_next_var+5))`,
    `STRING #"%" (toString (sa.cs_next_var+6))`] >>
  goal_assum (drule_at Any) >> simp[GSYM APPEND_ASSOC, fresh_var_distinct] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >>
  first_x_assum irule >> simp[]
QED

Theorem compile_storage_copy_path_ptr:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop src (Var root) n loc LocMemory F sa = (u,sb) /\
  fn_has_code sa sb fn /\ copy_old_operand sa src /\ not_fresh_at sa root /\
  eval_operand src s = SOME a /\ lookup_var root s = SOME b /\
  op_taint tn src = {} /\ ptr_covers G tn root s span /\ 32*n <= span /\
  w2n b+32*n < dimword(:256) /\ n < dimword(:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~ctx_has_dalloca ctx /\
  alloca_inv s /\ alloca_room ctx fn s /\
  (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w) ==>
  ?t Gf tf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand src t = SOME a /\ op_taint tf src = {} /\
    lookup_var root t = SOME b /\ ptr_covers Gf tf root t span /\
    copy_prefix loc a (w2n b) n s n t /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i h. i < n /\ h < 32 ==>
      (w2n b+32*i+h IN tf.t_mem <=>
       (a+n2w i,h) IN (if loc = LocTransient then tf.t_trans else tf.t_stor))) /\
    (!i. i < w2n b \/ w2n b+32*n <= i ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    (t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) /\
    alloca_inv t /\ alloca_room ctx fn t /\
    (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
      i.inst_operands = [Lit w] /\
      FLOOKUP t.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all storage_copy_registered_layout >> strip_tac >>
  Cases_on `loc = LocStorage`
  >- (gvs[] >> drule_at (Pat `_ = [mk_inst _ ADD _ _; _; _; _; _; _; _; _]`)
        (SRULE [GSYM arithmeticTheory.ADD_ASSOC] (Q.INST [`tr` |-> `F`, `id` |-> `sa.cs_next_id+4`,
          `hid` |-> `sa.cs_next_id+2`, `eid` |-> `sa.cs_next_id`]
          storage_copy_entry_loop_path_ptr)) >> suspend "storage_inputs") >>
  gvs[] >> drule_at (Pat `_ = [mk_inst _ ADD _ _; _; _; _; _; _; _; _]`)
    (SRULE [GSYM arithmeticTheory.ADD_ASSOC]
      (Q.INST [`tr` |-> `T`, `id` |-> `sa.cs_next_id+4`,
      `hid` |-> `sa.cs_next_id+2`, `eid` |-> `sa.cs_next_id`]
      storage_copy_entry_loop_path_ptr)) >> suspend "transient_inputs"
QED
Resume compile_storage_copy_path_ptr[storage_inputs]:
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_room _ _ _`)) >>
  disch_then (drule_at (Pat `_ = [mk_inst _ EQ _ _; _]`)) >>
  disch_then (drule_at (Pat `_ = _ ++ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >>
  (impl_tac >- (simp[] >> conj_tac
    >- (gvs[copy_old_operand_def] >> metis_tac[]) >> metis_tac[])) >>
  strip_tac >> qexistsl [`t`,`G'`,`tn'`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `h + (32*i+w2n b) = w2n b+(32*i+h)` by decide_tac >>
      metis_tac[]) >>
  conj_tac >- metis_tac[ADD_COMM] >> metis_tac[]
QED
Resume compile_storage_copy_path_ptr[transient_inputs]:
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_room _ _ _`)) >>
  disch_then (drule_at (Pat `_ = [mk_inst _ EQ _ _; _]`)) >>
  disch_then (drule_at (Pat `_ = _ ++ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >>
  (impl_tac >- (simp[] >> conj_tac
    >- (gvs[copy_old_operand_def] >> metis_tac[]) >> metis_tac[])) >>
  strip_tac >> qexistsl [`t`,`G'`,`tn'`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `h + (32*i+w2n b) = w2n b+(32*i+h)` by decide_tac >>
      metis_tac[]) >>
  conj_tac >- metis_tac[ADD_COMM] >> metis_tac[]
QED
Finalise compile_storage_copy_path_ptr
