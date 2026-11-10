Theory bodyPtrPopLocalRootFrame
Ancestors
  bodyPtrPopLocalRootPath bodyPtrPopInteriorPointer bodyPtrAttributeAdd
  typedCopyLoopHeaderPtr emitHelperProps emitHelper compileEnv loweringStateRelDefs venomState
  ptrDiscipline finite_map words list fragGasPathPtr storageCopyBodyPtr
  bodyPtrBopCompareCompile

(* Exact frames retain fields deliberately hidden by the earlier path interfaces. *)
Theorem pop_local_header_exact:
  emit_op MLOAD [Var src] sa = (op,sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn src s bytes /\ 32 <= bytes /\
  lookup_var src s = SOME a /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
      (w2n a) mem) ==>
  ?out t G' tn'. op = Var out /\ not_fresh_at sb out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    eval_operand op t = SOME (mem_word_at (w2n a) s.vs_memory) /\
    op_taint tn' op = {} /\ op_prov G' op = NONE /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_labels = s.vs_labels /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP G' v = FLOOKUP G v /\ op_taint tn' (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> drule_all bodyPtrPopMemoryHeaderTheory.pop_memory_header_load >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`out`, `(update_var out (mload (w2n a) s) s) with
    vs_inst_idx := SUC s.vs_inst_idx`, `G'`, `tn'`] >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
   not_fresh_at sb out` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def]) >>
  simp[update_var_def, lookup_var_def, eval_operand_def, FLOOKUP_UPDATE,
       GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >> metis_tac[]
QED

Theorem pop_local_mul_exact:
  emit_op MUL [left;right] sa = (dst,sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  ?out t G' tn'. dst = Var out /\ not_fresh_at sb out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    eval_operand dst t = SOME (a*b) /\
    op_taint tn' dst = {} /\ op_prov G' dst = NONE /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_labels = s.vs_labels /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP G' v = FLOOKUP G v /\ op_taint tn' (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> drule_all bop_compare_emit_placement >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  `dst = Var out /\ sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
   not_fresh_at sb out /\ (!v. not_fresh_at sa v ==> v <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def, Abbr `out`]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {out})) (tn with t_var := tn.t_var |+ (out,{}))
    (OK ((update_var out (a*b) s) with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule storage_copy_mul_path_ptr >> metis_tac[]) >>
  qexistsl_tac [`out`, `(update_var out (a*b) s) with
      vs_inst_idx := SUC s.vs_inst_idx`,
    `DRESTRICT G (COMPL {out})`, `tn with t_var := tn.t_var |+ (out,{})`] >>
  simp[eval_operand_def, update_var_def, lookup_var_def, op_taint_def,
       op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem pop_local_interior_exact:
  !sa sb dst root offset fn ctx s a off tn G total n D PG.
  emit_op ADD [Var root; offset] sa = (dst,sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa root /\ lookup_var root s = SOME a /\
  eval_operand offset s = SOME (n2w off) /\ op_taint tn offset = {} /\
  ptr_covers G tn root s total /\ off < total /\ off+n <= total /\
  w2n a + off < dimword(:256) ==>
  ?out t G' tn'. dst = Var out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    lookup_var out t = SOME (n2w (w2n a + off)) /\
    ptr_covers G' tn' out t n /\ not_fresh_at sb out /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_labels = s.vs_labels /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==> lookup_var v t = lookup_var v s /\
      FLOOKUP G' v = FLOOKUP G v /\ op_taint tn' (Var v) = op_taint tn (Var v))
Proof
  rpt gen_tac >> strip_tac >>
  `op_taint tn (Var root) = {}` by gvs[bodyPtrDefsTheory.ptr_covers_def] >>
  `?out G' tn' t.
    dst = Var out /\ gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t = (update_var out (a + n2w off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    G' = step_prov PG G (mk_inst sa.cs_next_id ADD [Var root;offset] [out])
      (update_var out (a + n2w off) s) /\
    tn' = step_taint (mk_inst sa.cs_next_id ADD [Var root;offset] [out]) s
      (update_var out (a + n2w off) s) tn /\
    tn'.t_imm = tn.t_imm /\ op_taint tn' (Var out) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!v. v <> out ==> FLOOKUP G' v = FLOOKUP G v /\
      op_taint tn' (Var v) = op_taint tn (Var v))` by
    (irule attribute_emit_binop_path_ptr >>
     simp[eval_operand_def] >> qexistsl_tac [`Var root`, `offset`, `sb`] >> simp[]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
   not_fresh_at sb out /\ (!v. not_fresh_at sa v ==> v <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `ptr_covers G' tn' out (update_var out (a + n2w off) s) n` by
    (simp[] >> irule typed_copy_loop_dynamic_offset_covers >> metis_tac[]) >>
  `a + n2w off = n2w (w2n a + off)` by simp[GSYM word_add_n2w] >>
  `ptr_covers G' tn' out t n` by
    gvs[bodyPtrDefsTheory.ptr_covers_def, update_var_def, lookup_var_def] >>
  qexistsl_tac [`out`, `t`, `G'`, `tn'`] >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  `v <> out` by metis_tac[] >> gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED
