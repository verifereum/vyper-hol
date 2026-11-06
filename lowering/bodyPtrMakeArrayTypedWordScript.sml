Theory bodyPtrMakeArrayTypedWord
Ancestors
  bodyPtrMakeArrayPrimitiveInstall bodyPtrMakeArrayMemoryWord
  bodyPtrMakeArrayWordStore bodyPtrDefs fragGasPathPtr exprSimProps
  compileEnv context venomState venomInst finite_map ptrDiscipline entryDecodeProps

Theorem typed_word_copy_counted:
  is_word_type dt /\
  compile_store_memory_typed ce (Var dst) dt (Var src) st sa = ((),sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa dst /\ not_fresh_at sa src /\
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  ptr_mem_ok cx st v (Var src) G tn s /\ is_word_type st /\
  evaluate_type (get_tenv cx) st = SOME sty /\ value_has_type sty v /\
  evaluate_type (get_tenv cx) dt = SOME dty /\ value_has_type dty v /\
  typed_val_to_w256 sty v = typed_val_to_w256 dty v /\
  lookup_var dst s = SOME a /\ eval_operand (Var src) s = SOME p /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!x n. not_fresh_at sa x /\ ptr_covers G tn x s n ==>
      ptr_covers Gf tnf x sf n) /\
    mem_agree_outside {i | w2n a <= i /\ i < w2n a + 32}
      sf.vs_memory s.vs_memory /\
    (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
      mem_word_at (w2n a) m = typed_val_to_w256 sty v) /\
    (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
      val_in_memory dty v (w2n a) m) /\
    (!ty u off. val_wf ty u /\
      (!i. off <= i /\ i < off + val_footprint ty u ==>
        ~(w2n a <= i /\ i < w2n a + 32)) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory ty u off m) ==>
      !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory ty u off m)
Proof
  strip_tac >>
  `!off mem. val_in_memory dty v off mem <=>
     mem_word_at off mem = typed_val_to_w256 dty v` by
    (rpt gen_tac >> irule val_in_memory_word >>
     reverse conj_tac >- simp[] >>
     qexistsl_tac [`get_tenv cx`, `dt`] >> simp[]) >>
  drule_all typed_word_copy_fetch >> strip_tac >>
  `dst <> tmp /\ src <> tmp` by metis_tac[] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id MLOAD [Var src] [tmp])` by simp[] >>
  drule_all memory_word_materialize_endpoint >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `ptr_covers Gf tnf dst sf 32` by metis_tac[] >>
  `lookup_var dst sf = SOME a` by metis_tac[] >>
  `~sf.vs_halted /\
   lookup_block sf.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb sf.vs_inst_idx =
     SOME (mk_inst (sa.cs_next_id + 1) MSTORE [Var dst; Var tmp] [])` by
    gvs[update_var_def] >>
  drule_all make_array_word_store_endpoint >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf'`, `tnf'`, `sf'`] >>
  conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
  `sf'.vs_current_bb = sb.cs_current_bb /\
   sf'.vs_inst_idx = LENGTH sb.cs_current_insts` by
    gvs[mstore_def, update_var_def] >>
  `!x. not_fresh_at sa x ==>
     lookup_var x sf' = lookup_var x s /\
     FLOOKUP Gf' x = FLOOKUP G x /\
     op_taint tnf' (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `x <> tmp` by metis_tac[] >>
     first_x_assum (drule_then strip_assume_tac) >>
     gvs[mstore_def, lookup_var_def, op_taint_def]) >>
  gvs[] >> metis_tac[]
QED
