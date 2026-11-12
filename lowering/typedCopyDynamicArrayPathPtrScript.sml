(* Dynamic-array length extraction for counted typed-copy execution. *)
Theory typedCopyDynamicArrayPathPtr
Ancestors
 typedCopyLayoutPtr representationCleanPtr exprSimPtrProps
 annAssignPtrLength valueEncodingProofs valueEncodingProps venomMemProofs
 bodyPtrDefs ptrDiscipline venomState finite_map words list arithmetic

Theorem typed_copy_dynarray_length_path_ptr:
 !D ctx fn PG G tn s sa sb src out a tv cap vs.
 emit_op MLOAD [Var src] sa = (Var out,sb) /\ fn_has_code sa sb fn /\
 ~ctx_has_dalloca ctx /\ ptr_covers G tn src s 32 /\
 lookup_var src s = SOME a /\ ~s.vs_halted /\
 s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
   val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) m) ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
 sf = (update_var out (n2w (LENGTH vs)) s with vs_inst_idx := SUC s.vs_inst_idx) /\
 sf.vs_current_bb = sb.cs_current_bb /\
 sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
 lookup_var out sf = SOME (n2w (LENGTH vs)) /\
 op_taint tnf (Var out) = {} /\ op_prov Gf (Var out) = NONE /\
 (sf with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
 tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
 tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!p. not_fresh_at sa p ==>
   lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
   op_taint tnf (Var p) = op_taint tn (Var p))
Proof
 rpt gen_tac >> strip_tac >>
 drule dynarray_in_memory_robust_length >> strip_tac >>
 `!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem` by
   metis_tac[robust_mem_word_at_clean] >>
 `mload (w2n a) s = n2w (LENGTH vs)` by
   (simp[GSYM mem_word_at_eq_mload] >>
    first_x_assum irule >> simp[mem_agree_outside_def]) >>
 drule_all emit_mload_ptr_path >>
 disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >> gvs[] >>
 drule_all annassign_emit_op_instruction_ptr >> strip_tac >>
 qexistsl [`G'`,`tn'`] >>
 simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE, venom_state_component_equality] >>
 rpt strip_tac >> metis_tac[]
QED
