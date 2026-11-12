(* The equal-layout dynamic-array tail copies only its live payload. *)
Theory typedCopyDynamicFastPathPtr
Ancestors
 annAssignPtrBytestring typedCopyLoopHeaderPathPtr liveArrayTransportPtr
 typedCopyFlatPathPtr exprSimPtrProps emitHelperProps freshWrites fragExec
 exprSimAggregateEncoding exprSimProps
 valueEncodingProofs valueEncodingDefs venomMemProofs
 compileEnv emitHelper context bodyPtrDefs ptrDiscipline venomInst
 venomExecSemantics venomState finite_map words arithmetic list

Theorem typed_copy_emit_mul_path_ptr:
 !D ctx fn PG G tn s sa sb left right out a b.
 emit_op MUL [left;right] sa = (Var out,sb) /\ fn_has_code sa sb fn /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
 op_taint tn left = {} /\ op_taint tn right = {} ==>
 ?sf.
 gas_path_ptr D 0 ctx fn PG G tn s 0 (DRESTRICT G (COMPL {out}))
   (tn with t_var := tn.t_var |+ (out,{})) (OK sf) /\
 sf = (update_var out (a*b) s with vs_inst_idx := SUC s.vs_inst_idx) /\
 sf.vs_current_bb = sb.cs_current_bb /\
 sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
 (sf with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
 (!p. not_fresh_at sa p ==> lookup_var p sf = lookup_var p s /\
   FLOOKUP (DRESTRICT G (COMPL {out})) p = FLOOKUP G p /\
   op_taint (tn with t_var := tn.t_var |+ (out,{})) (Var p) = op_taint tn (Var p))
Proof
 rpt gen_tac >> strip_tac >>
 drule_all annAssignPtrLengthTheory.annassign_emit_op_instruction_ptr >> strip_tac >>
 qexists_tac `update_var out (a*b) s with vs_inst_idx := SUC s.vs_inst_idx` >>
 conj_tac
 >- (irule typed_copy_header_arith_path_ptr >> simp[] >>
     qexistsl [`sa.cs_next_id`, `MUL`, `[left;right]`, `out`, `update_var out (a*b) s`] >>
     simp[update_var_def, DISJ_IMP_THM, FORALL_AND_THM,
       step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def]) >>
 simp[update_var_def, venom_state_component_equality] >> rpt strip_tac >>
 `p <> out` by metis_tac[] >>
 simp[lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def]
QED

Theorem typed_copy_dynamic_window_path_ptr:
 !D ctx fn PG G tn s dst src count_op a b k sa sb.
 compile_copy_memory_dynamic (Var dst) (Var src) count_op sa = ((),sb) /\
 fn_has_code sa sb fn /\
 s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ k < dimword(:256) /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 eval_operand count_op s = SOME (n2w k) /\ op_taint tn count_op = {} /\
 ptr_covers G tn src s k /\ ptr_covers G tn dst s k ==>
 ?sf tnf.
 gas_path_ptr D 0 ctx fn PG G tn s 0 G tnf (OK sf) /\
 sf.vs_current_bb = sb.cs_current_bb /\
 sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
 (sf with <|vs_memory := s.vs_memory; vs_inst_idx := s.vs_inst_idx|>) = s /\
 (tnf with t_mem := tn.t_mem) = tn /\
 (!p. lookup_var p sf = lookup_var p s) /\
 mem_bytes_at (w2n b) k sf.vs_memory = mem_bytes_at (w2n a) k s.vs_memory /\
 (!i. i < k ==> (w2n b+i IN tnf.t_mem <=> w2n a+i IN tn.t_mem)) /\
 (!i. ~(w2n b <= i /\ i < w2n b+k) ==>
   mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
   (i IN tnf.t_mem <=> i IN tn.t_mem))
Proof
 rpt gen_tac >> strip_tac >>
 `emit_inst MCOPY [Var dst;Var src;count_op] [] sa = ((),sb)` by
   gvs[compile_copy_memory_dynamic_def, emit_void_def, emit_inst_def] >>
 `w2n (n2w k : bytes32) = k` by simp[w2n_n2w] >>
 drule_all annassign_emit_mcopy_path_ptr >>
 disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
 `!i. ~(w2n b <= i /\ i < w2n b+k) ==>
    mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tnf.t_mem <=> i IN tn.t_mem)` by
  (gen_tac >> disch_tac >> conj_tac
   >- (simp[] >> irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
   simp[] >> eq_tac >> strip_tac >> gvs[] >> decide_tac) >>
 qexistsl [`sf`,`tnf`] >> simp[mcopy_mem_bytes_at_same]
QED

Theorem typed_copy_dynarray_fast_tail_path_ptr:
 !D ctx fn PG G tn s sa sm sb dst src len kreg a b sc dc stride tv vs.
 emit_op MUL [Var len;Lit (n2w stride)] sa = (Var kreg,sm) /\
 compile_copy_memory_dynamic (Var dst) (Var src) (Var kreg) sm = ((),sb) /\
 fn_has_code sa sb fn /\
 not_fresh_at sa dst /\ not_fresh_at sa src /\ not_fresh_at sa len /\
 s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 lookup_var len s = SOME (n2w (LENGTH vs)) /\
 op_taint tn (Var len) = {} /\ op_prov G (Var len) = NONE /\
 LENGTH vs < dimword(:256) /\ LENGTH vs <= sc /\ LENGTH vs <= dc /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 ptr_covers G tn src s (sc*stride) /\ ptr_covers G tn dst s (dc*stride) /\
 w2n a + sc*stride < dimword(:256) /\
 w2n b + dc*stride < dimword(:256) /\
 (w2n a+sc*stride <= w2n b \/ w2n b+dc*stride <= w2n a) /\
 type_memory_size tv = stride /\ EVERY (val_wf tv) vs /\
 (!j. j < LENGTH vs ==> !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
   val_in_memory tv (EL j vs) (w2n a+j*stride) m) ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = sb.cs_current_bb /\
 sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
 (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
   vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
   vs_inst_idx := s.vs_inst_idx|>) = s /\
 tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!p. not_fresh_at sa p ==>
   lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
   op_taint tnf (Var p) = op_taint tn (Var p)) /\
 (!i. ~(w2n b <= i /\ i < w2n b+dc*stride) ==>
   mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
   (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
 (!j. j < LENGTH vs ==> !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
   val_in_memory tv (EL j vs) (w2n b+j*stride) m)
Proof
 rpt gen_tac >> strip_tac >>
 rename1 `emit_op MUL _ sa = (Var kreg,sm)` >>
 `cs_extends sa sm /\ cs_extends sm sb` by
  (conj_tac
   >- gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def, cs_extends_def] >>
   gvs[compile_copy_memory_dynamic_def, emit_void_def, emit_inst_def,
     comp_bind_def, fresh_id_def, emit_def, cs_extends_def]) >>
 `fn_has_code sa sm fn /\ fn_has_code sm sb fn` by
   metis_tac[fn_has_code_split] >>
 `eval_operand (Var len) s = SOME (n2w (LENGTH vs)) /\
  eval_operand (Lit (n2w stride)) s = SOME (n2w stride) /\
  op_taint tn (Lit (n2w stride)) = {}` by simp[eval_operand_def, op_taint_def] >>
 drule_all typed_copy_emit_mul_path_ptr >>
 disch_then (qspecl_then [`D`,`PG`,`G`] strip_assume_tac) >>
 rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 _ _ (OK u)` >>
 qabbrev_tac `g1 = DRESTRICT G (COMPL {kreg})` >>
 qabbrev_tac `t1 = tn with t_var := tn.t_var |+ (kreg,{})` >>
 `LENGTH vs*stride <= sc*stride /\ LENGTH vs*stride <= dc*stride` by
   simp[LE_MULT_RCANCEL] >>
 `LENGTH vs*stride < dimword(:256)` by decide_tac >>
 `!p. not_fresh_at sa p ==> p <> kreg` by
   metis_tac[annAssignPtrLengthTheory.annassign_emit_op_instruction_ptr] >>
 `src <> kreg /\ dst <> kreg` by metis_tac[] >>
 `eval_operand (Var kreg) u = SOME (n2w (LENGTH vs*stride)) /\
  op_taint t1 (Var kreg) = {} /\
  lookup_var src u = SOME a /\ lookup_var dst u = SOME b /\
  u.vs_memory = s.vs_memory /\ t1.t_mem = tn.t_mem` by
  gvs[Abbr `t1`, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
    op_taint_def, eval_operand_def, word_mul_n2w] >>
 `ptr_covers g1 t1 src u (LENGTH vs*stride) /\
  ptr_covers g1 t1 dst u (LENGTH vs*stride)` by
  (gvs[ptr_covers_def, Abbr `g1`, Abbr `t1`, FLOOKUP_DRESTRICT,
     op_taint_def, FLOOKUP_UPDATE] >>
   `LENGTH vs * type_memory_size tv <= sc * type_memory_size tv /\
    LENGTH vs * type_memory_size tv <= dc * type_memory_size tv` by
     simp[LE_MULT_RCANCEL] >> decide_tac) >>
 drule_all typed_copy_dynamic_window_path_ptr >>
 disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
 rename1 `gas_path_ptr D 0 ctx fn PG g1 t1 u 0 g1 tf (OK v)` >>
 qexistsl [`g1`,`tf`,`v`] >>
 (conj_tac
 >- (irule (fragGasPathPtrTheory.gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl [`g1`,`u`,`t1`] >> conj_tac >> first_assum ACCEPT_TAC)) >>
 all_tac >>
 `!m. mem_agree_outside tf.t_mem v.vs_memory m ==>
   elems_in_memory vs (w2n b) tv m` by
  (rpt strip_tac >> irule robust_elems_in_memory_copy_transport >>
   conj_tac
   >- (gvs[EVERY_MEM] >> metis_tac[val_footprint_le]) >>
   qexistsl [`s.vs_memory`, `v.vs_memory`, `LENGTH vs*stride`,
     `w2n a`, `tn.t_mem`, `tf.t_mem`] >>
   simp[] >> rpt strip_tac >> irule elems_in_memory_intro >> simp[]) >>
 `tf.t_var = t1.t_var /\ tf.t_stor = tn.t_stor /\
  tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm` by
  (qpat_x_assum `tf with t_mem := _ = _` mp_tac >>
   simp[taint_component_equality, Abbr `t1`]) >>
 `!i. ~(w2n b <= i /\ i < w2n b+dc*stride) ==>
   mem_bytes_at i 1 v.vs_memory = mem_bytes_at i 1 s.vs_memory /\
   (i IN tf.t_mem <=> i IN tn.t_mem)` by
  (gen_tac >> disch_tac >>
   `~(w2n b <= i /\ i < w2n b+LENGTH vs*stride)` by decide_tac >> simp[]) >>
 `v with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
   vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
   vs_inst_idx := s.vs_inst_idx|> = s` by
  (qpat_x_assum `v with <|vs_memory := _; vs_inst_idx := _|> = u` mp_tac >>
   simp[venom_state_component_equality, update_var_def] >> rpt strip_tac >> simp[]) >>
 `!p. not_fresh_at sa p ==> op_taint tf (Var p) = op_taint tn (Var p)` by
  (rpt strip_tac >> simp[op_taint_def, Abbr `t1`, FLOOKUP_UPDATE] >>
   metis_tac[]) >>
 simp[] >> rpt strip_tac >>
 qpat_x_assum `type_memory_size tv = stride` (SUBST_ALL_TAC o SYM) >>
 simp[elems_in_memory_EL]
QED

