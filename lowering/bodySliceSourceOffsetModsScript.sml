(* Raw ADD at the copy-source cut of an ordinary Slice. *)
Theory bodySliceSourceOffsetMods
Ancestors
  bodyPtrBytestringBuiltinsAllocation bodyPtrBytestringBuiltinsExternalSlice
  appendStorageGhostPtr reasonCopySourcePtr typedCopyPtr allocasBelowFmpUpdatesProps
  emitHelperProps exprLoweringProps loweringStateRelDefs bodyPtrDefs ptrDiscipline
  venomExecSemantics venomState venomInst words finite_map

Theorem slice_source_offset_mods:
  emit_op ADD [Var src;start] sd = (copy_src,se) /\
  not_fresh_at sd root /\ not_fresh_at sd dst /\
  (!x. cnt = Var x ==> not_fresh_at sd x) /\
  lookup_var src v = SOME p /\ ptr_covers G2 tn2 src v (LENGTH bs) /\
  lookup_var root v = SOME w /\ lookup_var dst v = SOME (w+32w) /\
  ptr_covers G2 tn2 root v N /\ ptr_covers G2 tn2 dst v (N-32) /\
  eval_operand start v = SOME (n2w i) /\ op_taint tn2 start = {} /\
  eval_operand cnt v = SOME (n2w k) /\ op_taint tn2 cnt = {} /\
  i+k <= LENGTH bs /\ 32+k <= N /\
  w2n p + LENGTH bs < dimword (:256) /\ w2n w + N < dimword (:256) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp v) ==>
  ?copy_var offset_inst za G3 tn3.
    copy_var = STRING #"%" (toString sd.cs_next_var) /\ copy_src = Var copy_var /\
    offset_inst = mk_inst sd.cs_next_id ADD [Var src;start] [copy_var] /\
    se.cs_current_bb = sd.cs_current_bb /\
    se.cs_current_insts = sd.cs_current_insts ++ [offset_inst] /\
    emitted_insts sd se = [offset_inst] /\
    (!x. not_fresh_at sd x ==> x <> copy_var) /\
    za = update_var copy_var (p+n2w i) v /\
    step_inst_base offset_inst v = OK za /\
    G3 = step_prov PG G2 offset_inst za /\ tn3 = step_taint offset_inst v za tn2 /\
    (!D fuel. ptr_inst_ok D 0 fuel ctx func G2 tn2 offset_inst v) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp za) /\
    lookup_var copy_var za = SOME (p+n2w i) /\
    lookup_var root za = SOME w /\ lookup_var dst za = SOME (w+32w) /\
    eval_operand cnt za = SOME (n2w k) /\ op_taint tn3 cnt = {} /\
    ptr_covers G3 tn3 copy_var za k /\
    ptr_covers G3 tn3 root za N /\ ptr_covers G3 tn3 dst za (N-32) /\
    ptr_covers G3 tn3 dst za k /\
    w2n (p+n2w i) = w2n p+i /\ w2n (w+32w) = w2n w+32 /\
    tn3.t_mem = tn2.t_mem /\ tn3.t_stor = tn2.t_stor /\
    tn3.t_trans = tn2.t_trans /\ tn3.t_imm = tn2.t_imm /\
    (!x. not_fresh_at sd x ==>
       lookup_var x za = lookup_var x v /\ FLOOKUP G3 x = FLOOKUP G2 x /\
       op_taint tn3 (Var x) = op_taint tn2 (Var x))
Proof
  strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> simp[same_blocks_def] >> strip_tac >>
  qabbrev_tac `copy_var = STRING #"%" (toString sd.cs_next_var)` >>
  qabbrev_tac `offset_inst = mk_inst sd.cs_next_id ADD [Var src;start] [copy_var]` >>
  qabbrev_tac `za = update_var copy_var (p+n2w i) v` >>
  qabbrev_tac `G3 = step_prov PG G2 offset_inst za` >>
  qabbrev_tac `tn3 = step_taint offset_inst v za tn2` >>
  `!x. not_fresh_at sd x ==> x <> copy_var` by
    (simp[not_fresh_at_def, Abbr `copy_var`] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `op_taint tn2 (Var src) = {}` by fs[ptr_covers_def] >>
  `step_inst_base offset_inst v = OK za` by
    simp[Abbr `offset_inst`, Abbr `za`, step_inst_base_opcode_eqs,
         mk_inst_def, exec_pure2_def, eval_operand_def] >>
  `!D fuel. ptr_inst_ok D 0 fuel ctx func G2 tn2 offset_inst v` by
    (simp[Abbr `offset_inst`] >> rpt gen_tac >> irule ptr_inst_ok_copy_len_binop >> simp[]) >>
  `w2n p+i < dimword (:256) /\ i < dimword (:256) /\
   w2n w+32 < dimword (:256)` by decide_tac >>
  `ptr_covers G3 tn3 copy_var za k` by
    (drule_all pointer_offset_covers >>
     disch_then (qspecl_then [`PG`,`sd.cs_next_id`,`copy_var`] mp_tac) >>
     simp[Abbr `G3`, Abbr `tn3`, Abbr `offset_inst`, Abbr `za`,
          ptr_covers_def, lookup_var_def]) >>
  `tn3.t_mem = tn2.t_mem /\ tn3.t_stor = tn2.t_stor /\ tn3.t_trans = tn2.t_trans /\
   (!x. x <> copy_var ==> FLOOKUP G3 x = FLOOKUP G2 x /\
                        op_taint tn3 (Var x) = op_taint tn2 (Var x))` by
    simp[Abbr `G3`, Abbr `tn3`, Abbr `offset_inst`, Abbr `za`,
         copy_len_binop_ghost_frame] >>
  `tn3.t_imm = tn2.t_imm` by
    simp[Abbr `tn3`, Abbr `offset_inst`, step_taint_def, imm_taint_def, mk_inst_def] >>
  `!x. not_fresh_at sd x ==>
      lookup_var x za = lookup_var x v /\ FLOOKUP G3 x = FLOOKUP G2 x /\
      op_taint tn3 (Var x) = op_taint tn2 (Var x)` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sd x ==> x <> copy_var` drule >>
     simp[Abbr `za`, lookup_var_update_var]) >>
  `za.vs_labels = v.vs_labels` by simp[Abbr `za`, update_var_def] >>
  `eval_operand cnt za = SOME (n2w k) /\ op_taint tn3 cnt = {}` by
    (drule_all reserved_operand_ghost_frame >> simp[]) >>
  `ptr_covers G3 tn3 root za N /\ ptr_covers G3 tn3 dst za (N-32)` by
    (rpt conj_tac >> irule ptr_covers_old_transport >>
     qexistsl_tac [`G2`,`v`,`sd`,`tn2`] >> rpt strip_tac >> simp[]) >>
  `ptr_covers G3 tn3 dst za k` by
    (irule ptr_covers_mono >> qexists_tac `N-32` >> simp[] >> decide_tac) >>
  `w2n (p+n2w i) = w2n p+i /\ w2n (w+32w) = w2n w+32` by
    (simp[w2n_add_2,w2n_n2w,arithmeticTheory.LESS_MOD]) >>
  `~not_fresh_at sd copy_var` by metis_tac[] >>
  `lookup_var copy_var za = SOME (p+n2w i) /\
   lookup_var root za = SOME w /\ lookup_var dst za = SOME (w+32w)` by
    (simp[Abbr `za`, lookup_var_update_var]) >>
  simp[]
QED
