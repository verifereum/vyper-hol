(* Actual counted execution of the atomic typed word copy. *)
Theory typedCopyWordPathPtr
Ancestors
 typedCopyPtr annAssignPtrLength annAssignPtrStore representationCleanPtr
 fragGasPathPtr fragGasSeqPtr exprSimProps valueEncodingProofs valueEncodingProps
 bodyPtrDefs ptrDiscipline context emitHelper emitHelperProps
 exprLoweringProps fragExec compileEnv loweringStateRelDefs
 venomState venomMemProofs finite_map pred_set arithmetic

Theorem compile_store_word_robust_path_ptr:
 !D ctx func PG cenv dst dty src sty sa sb G tn s a b tenv tv v.
  is_word_type dty /\ evaluate_type tenv dty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  compile_store_memory_typed cenv (Var dst) dty (Var src) sty sa = ((),sb) /\
  not_fresh_at sa dst /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory tv v (w2n a) m) ==>
  ?Gf tnf sf.
   gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
   sf.vs_current_bb = sb.cs_current_bb /\
   sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
   (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
   tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
   (!p. not_fresh_at sa p ==>
     lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
     op_taint tnf (Var p) = op_taint tn (Var p)) /\
   (!i. ~(w2n b <= i /\ i < w2n b+32) ==>
      mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
   (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory tv v (w2n b) m)
Proof
 rpt gen_tac >> strip_tac >>
 `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      mem_word_at (w2n a) m = typed_val_to_w256 tv v` by
   metis_tac[val_in_memory_word_type] >>
 `!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem` by
   (drule robust_mem_word_at_clean >> simp[]) >>
 drule_all compile_store_word_code >> strip_tac >>
 `tmp <> dst` by metis_tac[] >>
 `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb (LENGTH sa.cs_current_insts) =
     SOME (mk_inst id MLOAD [Var src] [tmp]) /\
   get_instruction bb (SUC (LENGTH sa.cs_current_insts)) =
     SOME (mk_inst (id+1) MSTORE [Var dst;Var tmp] [])` by
  (`sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst id MLOAD [Var src] [tmp];
       mk_inst (id+1) MSTORE [Var dst;Var tmp] []]` by simp[] >>
   drule_all fn_has_code_same_block >> strip_tac >>
   qexists `bb` >> simp[] >>
   first_x_assum (fn th => map_every (fn q => qspec_then q mp_tac th) [`0`,`1`]) >> simp[ADD1]) >>
 qabbrev_tac `s1 = update_var tmp (mload (w2n a) s) s` >>
 qabbrev_tac `G1 = step_prov PG G (mk_inst id MLOAD [Var src] [tmp]) s1` >>
 qabbrev_tac `tn1 = step_taint (mk_inst id MLOAD [Var src] [tmp]) s s1 tn` >>
 qabbrev_tac `v1 = s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
 `ptr_covers G1 tn1 dst s1 32` by
  (simp[Abbr `G1`, Abbr `tn1`, Abbr `s1`] >>
   metis_tac[mload_preserves_ptr_covers]) >>
 `ptr_covers G1 tn1 dst v1 32` by
  gvs[Abbr `v1`, ptr_covers_def, lookup_var_def] >>
 `op_taint tn1 (Var tmp) = {} /\ tn1.t_mem = tn.t_mem /\
   tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans` by
  (simp[Abbr `tn1`, Abbr `s1`] >> irule mload_ghost_clean >> simp[eval_operand_def]) >>
 `lookup_var dst v1 = SOME b /\
   eval_operand (Var tmp) v1 = SOME (mload (w2n a) s)` by
  (simp[Abbr `v1`, Abbr `s1`, update_var_def, lookup_var_def,
        eval_operand_def, FLOOKUP_UPDATE] >> gvs[lookup_var_def]) >>
 qabbrev_tac `s2 = mstore (w2n b) (mload (w2n a) s) v1` >>
 qabbrev_tac `G2 = step_prov PG G1 (mk_inst (id+1) MSTORE [Var dst;Var tmp] []) s2` >>
 qabbrev_tac `tn2 = step_taint (mk_inst (id+1) MSTORE [Var dst;Var tmp] []) v1 s2 tn1` >>
 qexistsl [`G2`,`tn2`,`s2 with vs_inst_idx := SUC v1.vs_inst_idx`] >>
 conj_tac >- suspend "path" >>
 suspend "frame"
QED

Resume compile_store_word_robust_path_ptr[path]:
 `gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1 (OK v1)` by
  (simp[Abbr `G1`, Abbr `tn1`, Abbr `v1`, Abbr `s1`] >>
   metis_tac[annassign_mload_path_ptr]) >>
 `gas_path_ptr D 0 ctx func PG G1 tn1 v1 0 G2 tn2
    (OK (s2 with vs_inst_idx := SUC v1.vs_inst_idx))` by
  (simp[Abbr `G2`, Abbr `tn2`, Abbr `s2`] >>
   irule annassign_mstore_path_ptr >> simp[] >>
   simp[Abbr `v1`, Abbr `s1`, update_var_def] >> metis_tac[]) >>
 drule_all gas_path_ptr_then >> simp[]
QED

Resume compile_store_word_robust_path_ptr[frame]:
 `G2 = G1 /\ tn2.t_var = tn1.t_var /\
  tn2.t_stor = tn1.t_stor /\ tn2.t_trans = tn1.t_trans /\
  tn2.t_mem = tn1.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32}` by
  (simp[Abbr `G2`, Abbr `tn2`, Abbr `s2`] >>
   metis_tac[mstore_ghost_frame]) >>
 `s2.vs_memory = (mstore (w2n b) (mload (w2n a) s) s).vs_memory` by
  simp[Abbr `s2`, Abbr `v1`, Abbr `s1`, mstore_def, update_var_def] >>
 conj_tac >- simp[Abbr `s2`, Abbr `v1`, Abbr `s1`, mstore_def, update_var_def] >>
 conj_tac >- simp[Abbr `s2`, Abbr `v1`, Abbr `s1`, mstore_def, update_var_def] >>
 conj_tac >- simp[Abbr `s2`, Abbr `v1`, Abbr `s1`, mstore_def, update_var_def] >>
 conj_tac >- (qpat_x_assum `s.vs_inst_idx = _` (SUBST1_TAC o SYM) >>
  simp[Abbr `s2`, Abbr `v1`, Abbr `s1`, mstore_def, update_var_def]) >>
 simp[] >>
 conj_tac >-
  simp[Abbr `tn2`, Abbr `tn1`, step_taint_def, imm_taint_def,
       adopt_reset_def, venomInstTheory.mk_inst_def, Abbr `s2`, Abbr `v1`, Abbr `s1`,
       mstore_def, update_var_def] >>
 conj_tac >-
  (rpt strip_tac >> `tmp <> p` by metis_tac[] >>
   simp[Abbr `G1`, Abbr `tn1`, Abbr `s2`, Abbr `v1`, Abbr `s1`,
        step_prov_def, set_prov_def, out_prov_def, step_taint_def,
        set_var_taint_def, op_taint_def, venomInstTheory.mk_inst_def, update_var_def,
        lookup_var_def, mstore_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
 conj_tac >-
  (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
 `mload (w2n a) s = typed_val_to_w256 tv v` by
  (qpat_x_assum `!m. _ ==> mem_word_at _ _ = _`
     (qspec_then `s.vs_memory` mp_tac) >>
   simp[mem_agree_outside_def, valueEncodingDefsTheory.mem_word_at_def, valueEncodingDefsTheory.mem_bytes_at_def, mload_def]) >>
 rpt strip_tac >> irule annassign_clean_store_layout_ptr >>
 simp[] >> qexistsl [`s`, `tn.t_mem`, `typed_val_to_w256 tv v`] >>
 reverse conj_tac >- metis_tac[] >> qx_gen_tac `u` >>
 `val_in_memory tv v (w2n b) (mstore (w2n b) (typed_val_to_w256 tv v) u).vs_memory <=>
  mem_word_at (w2n b) (mstore (w2n b) (typed_val_to_w256 tv v) u).vs_memory =
    typed_val_to_w256 tv v` by metis_tac[val_in_memory_word] >>
 simp[valueEncodingDefsTheory.mem_word_at_def,
      GSYM valueEncodingDefsTheory.mem_bytes_at_def, mem_bytes_at_mstore_same,
      byteTheory.word_of_bytes_word_to_bytes]
QED

Finalise compile_store_word_robust_path_ptr
