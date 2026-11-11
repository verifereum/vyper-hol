(* Exterior transport permits fresh temporary variable writes. *)
Theory annAssignPtrExterior
Ancestors
 annAssignPtrScratch annAssignPtrBytestring bodyPtrDefs ptrDiscipline
 venomState stmtSimProps exprSimProps finite_map pred_set

Theorem annassign_ghost_vars_exterior_ptr:
 !ctx func cenv cx es d G tn s Gf tnf sf writes.
 stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
 (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
            vs_inst_idx := s.vs_inst_idx|>) = s /\
 tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!name b sz. local_region cenv es.scopes s name b sz ==>
    !i. b <= i /\ i < b+sz ==> i NOTIN writes) /\
 (!i. i NOTIN writes ==> mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
 (!i. i NOTIN writes ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
 (!name entry p sz.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
    op_taint tnf (Var p) = op_taint tn (Var p)) /\
 (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==>
    lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
    op_taint tnf (Var p) = op_taint tn (Var p)) /\
 (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==>
    op_taint tnf (Var p) = op_taint tn (Var p)) ==>
 ghost_inv d cenv cx es Gf tnf sf
Proof
 rpt gen_tac >> strip_tac >>
 `ghost_inv d cenv cx es G (tn with t_mem := tnf.t_mem)
   (s with <|vs_memory := sf.vs_memory; vs_inst_idx := sf.vs_inst_idx|>)` by
   (irule annassign_ghost_exterior_ptr >> simp[] >>
    conj_tac >- (qexists `writes` >> asm_rewrite_tac[]) >>
    qexistsl [`ctx`,`func`] >> simp[]) >>
 qpat_x_assum `ghost_inv _ _ _ _ G tn s` kall_tac >>
 fs[ghost_inv_def] >> conj_tac
 >- (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!name entry p sz. _ ==> ptr_covers _ _ _ _ _ /\ _` drule_all >>
     strip_tac >>
     qpat_x_assum `!name entry p sz. _ ==> lookup_var _ _ = _ /\ _` drule_all >>
     strip_tac >> fs[ptr_covers_def, lookup_var_def, op_taint_def]) >>
 conj_tac
 >- (Cases_on `d` >> fs[return_buf_ptr_def] >>
     PairCases_on `x` >> gvs[return_buf_ptr_def] >>
     gvs[ptr_covers_def, lookup_var_def, op_taint_def]) >>
 conj_tac >- fs[op_taint_def] >>
 fs[stor_taint_ok_def, venom_state_component_equality]
QED

Theorem annassign_ghost_kept_vars_exterior_ptr:
 !cenv es sa G0 tn0 s0 G tn Gf tnf writes.
 ghost_kept cenv es sa G0 tn0 s0 G tn /\
 (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
     op_taint tnf (Var p) = op_taint tn (Var p)) /\
 (!i. i NOTIN writes ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
 (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    aid < sa.cs_next_id /\ off <= i /\ i < off+sz ==> i NOTIN writes) /\
 (!n b sz i. local_region cenv es.scopes s0 n b sz /\
    b <= i /\ i < b+sz ==> i NOTIN writes) ==>
 ghost_kept cenv es sa G0 tn0 s0 Gf tnf
Proof
 rw[ghost_kept_def] >> metis_tac[]
QED
