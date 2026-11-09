(* Robust layouts are transported pointwise, not by assuming taint is empty. *)
Theory annAssignPtrMemorySource
Ancestors
 annAssignPtrMemoryLayout annAssignPtrStage valueCopyBytes
 representationCleanPtr exprOperandVar exprSimProps exprSimDefs
 loweringPosts bodyPtrDefs valueTypingMemoryProps valueEncoding compileEnv
 ptrDiscipline venomState venomMemDefs finite_map exprSimHyps
 venomMemProofs vyperValue vyperTypeSystem vyperTyping valueEncodingProps vfmConstants

Theorem annassign_robust_layout_transfer_ptr:
 !tenv src dst stv dtv v a tn mem.
 (src = dst \/ is_bytestring_type src /\ is_bytestring_type dst) /\
 evaluate_type tenv src = SOME stv /\ evaluate_type tenv dst = SOME dtv /\
 value_has_type dtv v /\
 (!m. mem_agree_outside tn mem m ==> val_in_memory stv v a m) ==>
 !m. mem_agree_outside tn mem m ==> val_in_memory dtv v a m
Proof
 rpt gen_tac >> strip_tac >> Cases_on `src = dst` >- gvs[] >>
 rpt strip_tac >> irule bytestring_val_in_memory_transfer >>
 metis_tac[]
QED

Theorem annassign_memory_rhs_layout_ptr:
 !ctx func c cx e es ea eb s0 es1 v op s G tn etv typ tyv.
 expr_post ctx func c cx e es ea eb s0 es1 v op s /\
 lower_value compile_expr c (expr_type e) e ea = (op,eb) /\
 local_ptrs_reserved c ea /\
 evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
 evaluate_type (get_tenv cx) typ = SOME tyv /\
 ~is_word_type (expr_type e) /\
 (expr_type e = typ \/ is_bytestring_type (expr_type e) /\ is_bytestring_type typ) /\
 value_has_type tyv v /\
 ptr_val_ok cx (expr_type e) v op G tn s /\ ptr_buf_ok c e op G s /\
 0 < type_memory_bytes c (lowered_value_type c e) ==>
 ?src a. op = Var src /\ lookup_var src s = SOME a /\
 ptr_covers G tn src s (type_memory_bytes c (lowered_value_type c e)) /\
 val_wf tyv v /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tyv v (w2n a) m)
Proof
 rpt gen_tac >> strip_tac >>
 drule compile_lower_value_var >> disch_then drule >> disch_tac >>
 `?w. eval_operand op s = SOME w` by
   (fs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
 `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory etv v (w2n w) m` by
   (fs[ptr_val_ok_def, ptr_mem_ok_def] >> metis_tac[]) >>
 `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory tyv v (w2n w) m` by
   metis_tac[annassign_robust_layout_transfer_ptr] >>
 fs[ptr_buf_ok_def] >> qexists `w` >>
 gvs[ptr_covers_def, ptr_val_ok_def, eval_operand_def,
     value_has_type_memory_wf] >> metis_tac[]
QED

Theorem annassign_bytestring_window_ptr:
 !tenv sty dty stv dtv v a s tn.
 is_bytestring_type sty /\ is_bytestring_type dty /\
 evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
 value_has_type stv v /\ value_has_type dtv v /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory dtv v a m) ==>
 ?len. mload a s = n2w len /\
 (!i. a <= i /\ i < a+32 ==> i NOTIN tn.t_mem) /\
 val_footprint dtv v <= 32 + 32 * ((len+31) DIV 32) /\
 32 + 32 * ((len+31) DIV 32) <= type_memory_size stv /\
 32 + 32 * ((len+31) DIV 32) <= type_memory_size dtv
Proof
 rpt gen_tac >> strip_tac >>
 `(?n. stv = BaseTV (BytesT (Dynamic n))) \/
  (?n. stv = BaseTV (StringT n))` by metis_tac[bytestring_type_value] >>
 `(?n. dtv = BaseTV (BytesT (Dynamic n))) \/
  (?n. dtv = BaseTV (StringT n))` by metis_tac[bytestring_type_value] >>
 Cases_on `v` >>
 gvs[value_has_type_def] >>
 rename1 `LENGTH payload <= n` >>
 `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       mem_word_at a m = n2w (LENGTH payload)` by
   (rpt strip_tac >> first_x_assum drule >> simp[val_in_memory_def]) >>
 `!i. a <= i /\ i < a+32 ==> i NOTIN tn.t_mem` by
   (drule robust_mem_word_at_clean >> simp[]) >>
 `mload a s = n2w (LENGTH payload)` by
   (qpat_x_assum `!m. _ ==> mem_word_at _ _ = _`
      (qspec_then `s.vs_memory` mp_tac) >>
    simp[mem_agree_outside_def, mem_word_at_eq_mload]) >>
 qexists `LENGTH payload` >>
 simp[val_footprint_def, type_memory_size_def,
      GSYM word_size_def, word_size_capacity] >>
 metis_tac[word_size_monotone]
QED
