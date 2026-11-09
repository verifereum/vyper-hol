(* The actual unsigned memory selector: length, bounds, then address tail. *)
Theory bodyPtrSubscriptDynamicSelector
Ancestors
  bodyPtrSubscriptDynamicAddress bodyPtrSubscriptBoundsRun bodyPtrSubscriptLengthRead
  bodyPtrSubscriptReadOnly bodyPtrSubscriptBounds appendStorageGhostPtr
  exprLowering exprLoweringProps emitHelperProps emitHelper compileEnv fragExec
  freshWrites fragGasPathPtr ptrDiscipline bodyPtrDefs venomState finite_map words loweringPosts

Theorem dynamic_selector_emissions:
  compile_array_subscript (Var p) idx T 0 32 elem_size F
    (\op. emit_op MLOAD [op]) sa = (op,sb) ==>
  ?len lt not_oob invalid valid data offset out s1 s2 s3 s4 s5 s6 s7 s8.
    op = Var out /\
    emit_op MLOAD [Var p] sa = (Var len,s1) /\
    emit_op LT [idx;Var len] s1 = (Var lt,s2) /\
    emit_op ISZERO [Var lt] s2 = (Var not_oob,s3) /\
    emit_op OR [Lit 0w;Var not_oob] s3 = (Var invalid,s4) /\
    emit_op ISZERO [Var invalid] s4 = (Var valid,s5) /\
    emit_void ASSERT [Var valid] s5 = ((),s6) /\
    emit_op ADD [Var p;Lit 32w] s6 = (Var data,s7) /\
    emit_op MUL [idx;Lit (n2w elem_size)] s7 = (Var offset,s8) /\
    emit_op ADD [Var data;Var offset] s8 = (Var out,sb)
Proof
  simp[compile_array_subscript_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> rpt (pairarg_tac >> simp[]) >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> gvs[] >> metis_tac[]
QED

Theorem dynamic_length_bounds_counted:
  emit_op MLOAD [Var p] sa = (Var len,s1) /\
  emit_op LT [idx;Var len] s1 = (Var lt,s2) /\
  emit_op ISZERO [Var lt] s2 = (Var not_oob,s3) /\
  emit_op OR [Lit 0w;Var not_oob] s3 = (Var invalid,s4) /\
  emit_op ISZERO [Var invalid] s4 = (Var valid,s5) /\
  emit_void ASSERT [Var valid] s5 = ((),sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!q. idx = Var q ==> not_fresh_at sa q) /\ (!l. idx <> Label l) /\
  ptr_covers G tn p s parent_sz /\ 32 <= parent_sz /\ lookup_var p s = SOME a /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) mem) /\
  eval_operand idx s = SOME (n2w i) /\ op_taint tn idx = {} /\ op_prov G idx = NONE /\
  i < LENGTH vs /\ LENGTH vs < dimword (:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!cenv cx es. stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
      stmt_state_rel ctx func cenv cx es sf)
Proof
  strip_tac >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\ ci_mono s4 s5` by
    metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono s5 sb` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends s1 sb` by metis_tac[ci_mono_def, cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  drule_all emit_dynarray_length_counted >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `t1`] strip_assume_tac) >>
  `eval_operand idx t1 = SOME (n2w i) /\ op_taint tn1 idx = {} /\
   op_prov G1 idx = NONE` by (drule_all reserved_operand_read_only >> simp[]) >>
  `eval_operand (Var len) t1 = SOME (n2w (LENGTH vs))` by simp[eval_operand_def] >>
  `w2n (n2w i:bytes32) < w2n (n2w (LENGTH vs):bytes32)` by
    (simp[w2n_n2w, arithmeticTheory.LESS_MOD] >> decide_tac) >>
  drule_all unsigned_bounds_counted_read_only >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `t2`] strip_assume_tac) >>
  qexistsl_tac [`G2`, `tn2`, `t2`] >> simp[] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at s1 q` by metis_tac[ci_mono_def, freshWritesTheory.not_fresh_at_mono] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `local_ptrs_reserved cenv s1` by metis_tac[ci_mono_def, local_ptrs_reserved_next_var] >>
  metis_tac[]
QED

Theorem dynamic_child_at_selected_address:
  i < LENGTH vs /\ w2n (a:bytes32) + 32 + i * type_memory_size tv < dimword (:256) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) mem) ==>
  val_in_memory tv (EL i vs)
    (w2n (a + n2w (32 + i * type_memory_size tv))) s.vs_memory /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv (EL i vs) (w2n (a + n2w (32 + i * type_memory_size tv))) mem)
Proof
  strip_tac >>
  `32 + i * type_memory_size tv < dimword (:256)` by decide_tac >>
  `w2n (a + n2w (32 + i * type_memory_size tv)) =
   w2n a + 32 + i * type_memory_size tv` by
    (simp[w2n_add_2, w2n_n2w, arithmeticTheory.LESS_MOD] >> decide_tac) >>
  pure_asm_rewrite_tac[] >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory tv (EL i vs) (w2n a + 32 + i * type_memory_size tv) mem` by
    (rpt strip_tac >>
     metis_tac[typedCopyLayoutPtrTheory.dynarray_in_memory_robust_element]) >>
  conj_tac >- (first_x_assum irule >> simp[mem_agree_outside_def]) >> simp[]
QED

Theorem dynamic_selector_counted:
  compile_array_subscript (Var p) idx T 0 32 elem_size F
    (\op. emit_op MLOAD [op]) sa = (op,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa p /\ (!q. idx = Var q ==> not_fresh_at sa q) /\ (!l. idx <> Label l) /\
  ptr_covers G tn p s parent_sz /\ lookup_var p s = SOME a /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) mem) /\
  eval_operand idx s = SOME (n2w i) /\ op_taint tn idx = {} /\ op_prov G idx = NONE /\
  i < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  32 + i * elem_size + child_sz <= parent_sz /\
  w2n a + 32 + i * elem_size < dimword (:256) ==>
  ?out Gf tnf sf.
    op = Var out /\ gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (a + n2w (32 + i * elem_size)) /\
    ptr_covers Gf tnf out sf child_sz /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!cenv cx es. stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
      stmt_state_rel ctx func cenv cx es sf) /\
    (elem_size = type_memory_size tv ==>
      val_in_memory tv (EL i vs) (w2n (a + n2w (32 + i * elem_size))) sf.vs_memory /\
      (!mem. mem_agree_outside tnf.t_mem sf.vs_memory mem ==>
        val_in_memory tv (EL i vs) (w2n (a + n2w (32 + i * elem_size))) mem))
Proof
  strip_tac >>
  `elem_size = type_memory_size tv ==>
   val_in_memory tv (EL i vs) (w2n (a + n2w (32 + i * elem_size))) s.vs_memory /\
   (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory tv (EL i vs) (w2n (a + n2w (32 + i * elem_size))) mem)` by
    (disch_then SUBST_ALL_TAC >> irule dynamic_child_at_selected_address >>
     simp[] >> qexists_tac `cap` >> simp[]) >>
  drule dynamic_selector_emissions >> strip_tac >> gvs[] >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\
   ci_mono s4 s5 /\ ci_mono s6 s7 /\ ci_mono s7 s8 /\ ci_mono s8 sb` by
    metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono s5 s6` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends sa s6 /\ cs_extends s6 sb /\ sa.cs_next_var <= s6.cs_next_var` by
    (fs[ci_mono_def] >> conj_tac
     >- (irule cs_extends_trans >> qexists_tac `s3` >> conj_tac >>
         metis_tac[cs_extends_trans]) >>
     metis_tac[cs_extends_trans]) >>
  `fn_has_code sa s6 func /\ fn_has_code s6 sb func` by metis_tac[fn_has_code_split] >>
  `32 <= parent_sz` by decide_tac >>
  drule_all dynamic_length_bounds_counted >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `t1`] strip_assume_tac) >>
  `ptr_covers G1 tn1 p t1 parent_sz` by
    (irule ptr_covers_old_transport >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `lookup_var p t1 = SOME a /\ not_fresh_at s6 p /\
   (!q. idx = Var q ==> not_fresh_at s6 q)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand idx t1 = SOME (n2w i) /\ op_taint tn1 idx = {} /\
   op_prov G1 idx = NONE` by (drule_all reserved_operand_read_only >> simp[]) >>
  `32 + i * elem_size + child_sz <= parent_sz /\
   w2n a + 32 + i * elem_size < dimword (:256)` by decide_tac >>
  drule_all dynamic_address_counted_read_only >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (qx_choosel_then [`G2`, `tn2`, `t2`] strip_assume_tac) >>
  qexistsl_tac [`G2`, `tn2`, `t2`] >> simp[] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at s6 q` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `local_ptrs_reserved cenv s6` by metis_tac[local_ptrs_reserved_next_var] >>
  metis_tac[]
QED
