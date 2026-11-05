(* Restricted destination copy: only the reachable same-layout and bytestring
   branches.  The source representation is robust, including tainted padding. *)
Theory annAssignPtrDestination
Ancestors
 annAssignPtrBytestring annAssignPtrScratch context bodyPtrDefs
 ptrDiscipline venomState venomInst venomMemDefs valueEncoding
 finite_map compileEnv fragGasPathPtr

Theorem annassign_store_memory_path_ptr:
 !D ctx func PG G tn s sa sb cenv ty sty src dst a b len k tv v.
 compile_store_memory cenv (Var src) (Var dst) ty sty sa = ((),sb) /\
 fn_has_code sa sb func /\ ~is_word_type ty /\
 (sty = ty \/ is_bytestring_type ty) /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 not_fresh_at sa src /\ not_fresh_at sa dst /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 k < dimword (:256) /\ ptr_covers G tn src s k /\ ptr_covers G tn dst s k /\
 (if is_bytestring_type ty then
    k = 32 + 32 * ((len + 31) DIV 32) /\ mload (w2n a) s = n2w len /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem)
  else k = type_memory_bytes cenv ty) /\
 val_wf tv v /\ val_footprint tv v <= k /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n a) m) ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = sb.cs_current_bb /\ sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
 ~sf.vs_halted /\
 (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
            vs_inst_idx := s.vs_inst_idx|>) = s /\
 tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!p. not_fresh_at sa p ==> lookup_var p sf = lookup_var p s /\
   FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
 (!i. ~(w2n b <= i /\ i < w2n b+k) ==>
   mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
   (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
 (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==> val_in_memory tv v (w2n b) m)
Proof
 rpt gen_tac >> strip_tac >> (Cases_on `is_bytestring_type ty`
 >- (qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
     asm_rewrite_tac[compile_store_memory_def] >> strip_tac >>
     qpat_x_assum `if _ then _ else _` mp_tac >>
     asm_rewrite_tac[] >> strip_tac >>
     drule_all annassign_bytestring_copy_robust_ptr >>
     disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
     qexistsl [`Gf`,`tnf`,`sf`] >> asm_rewrite_tac[] >>
     fs[venom_state_component_equality]) >>
 gvs[compile_store_memory_def] >>
 drule_all annassign_counted_copy_robust_ptr >>
 disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
 `tn'.t_imm = tn.t_imm` by
   (qpat_x_assum `(tn' with t_mem := _) = _` mp_tac >>
    simp[taint_component_equality]) >>
 qexistsl [`G`,`tn'`,`s'`] >> simp[op_taint_def] >>
 fs[venom_state_component_equality])
QED
