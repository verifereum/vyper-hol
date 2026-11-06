Theory forPtrCheckedFrame
Ancestors
  forPtrRangeChecked forPtrRangePrepare exprSimProps bodyPtrDefs
  forPtrControl venomState venomExecSemantics ptrDiscipline ptrSafeRun
  compileEnv exprLoweringProps finite_map list pred_set

(* The entry path exposes an arbitrary final variable map with an untouched
   variable frame.  Preserve invariants directly at that abstraction boundary. *)

Theorem for_checked_outputs_taint:
  !outputs tn x.
  op_taint (tn with t_var := tn.t_var |++ MAP (\v. (v,{})) outputs) (Var x) =
    if MEM x outputs then {} else op_taint tn (Var x)
Proof
  Induct >- simp[FUPDATE_LIST_THM] >> rpt gen_tac >>
  simp[FUPDATE_LIST_THM] >>
  first_x_assum (qspec_then `tn with t_var := tn.t_var |+ (h,{})` mp_tac) >>
  simp[op_taint_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  Cases_on `MEM x outputs` >> Cases_on `x = h` >> gvs[]
QED

Theorem for_checked_outputs_ptr_covers:
  ptr_covers G tn p s sz /\ ~MEM p outputs /\
  lookup_var p (s with vs_vars := vs) = lookup_var p s ==>
  ptr_covers (DRESTRICT G (COMPL (set outputs)))
    (tn with t_var := tn.t_var |++ MAP (\v. (v,{})) outputs)
    p (jump_to lbl (s with vs_vars := vs)) sz
Proof
  simp[ptr_covers_def, FLOOKUP_DRESTRICT, for_checked_outputs_taint,
       jump_to_def, lookup_var_def]
QED

Theorem for_checked_outputs_ghost_frame:
  ghost_inv d cenv cx es G tn s /\
  (!x. MEM x outputs ==> not_local_ptr cenv es.scopes x /\
     (!sz. cenv.ce_return_buf <> SOME (PtrVar (Var x) sz))) /\
  (!x. ~MEM x outputs ==> lookup_var x (s with vs_vars := vs) = lookup_var x s) ==>
  ghost_inv d cenv cx es (DRESTRICT G (COMPL (set outputs)))
    (tn with t_var := tn.t_var |++ MAP (\v. (v,{})) outputs)
    (jump_to lbl (s with vs_vars := vs))
Proof
  strip_tac >> fs[ghost_inv_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `~MEM p outputs` by metis_tac[not_local_ptr_def] >>
      qpat_x_assum `!name entry p sz. _` drule_all >> strip_tac >>
      conj_tac >- (irule for_checked_outputs_ptr_covers >> simp[]) >>
      qpat_x_assum `!x. ~MEM x outputs ==> _` (qspec_then `p` mp_tac) >>
      simp[jump_to_def, lookup_var_def] >> metis_tac[])
  >- (Cases_on `d` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
      fs[return_buf_ptr_def] >>
      rename1 `cenv.ce_return_buf = SOME (PtrVar (Var rp) slot_size)` >>
      `~MEM rp outputs` by metis_tac[] >>
      reverse conj_tac >- (irule for_checked_outputs_ptr_covers >> simp[]) >>
      qpat_x_assum `!x. ~MEM x outputs ==> _` (qspec_then `rp` mp_tac) >>
      simp[jump_to_def, lookup_var_def])
  >- (rpt strip_tac >> simp[for_checked_outputs_taint] >> metis_tac[]) >>
  fs[stor_taint_ok_def, jump_to_def]
QED

Theorem for_checked_outputs_state_frame:
  stmt_state_rel ctx fn cenv cx es s /\
  (!x. MEM x outputs ==> not_local_ptr cenv es.scopes x /\
    cenv.ce_imm_alloca <> SOME (Var x)) /\
  (!x. ~MEM x outputs ==> lookup_var x (s with vs_vars := vs) = lookup_var x s) ==>
  stmt_state_rel ctx fn cenv cx es (jump_to lbl (s with vs_vars := vs))
Proof
  strip_tac >> simp[stmt_state_rel_jump_to] >>
  irule stmt_state_rel_vars_frame >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `~MEM p outputs` by metis_tac[not_local_ptr_def] >> simp[]) >>
  rpt strip_tac >> `~MEM p outputs` by metis_tac[] >> simp[]
QED

Theorem for_checked_outputs_frame:
  (!x. ~MEM x outputs ==> lookup_var x (s with vs_vars := vs) = lookup_var x s) ==>
  !x. ~MEM x outputs ==>
    lookup_var x (jump_to lbl (s with vs_vars := vs)) = lookup_var x s /\
    FLOOKUP (DRESTRICT G (COMPL (set outputs))) x = FLOOKUP G x /\
    op_taint (tn with t_var := tn.t_var |++ MAP (\v. (v,{})) outputs) (Var x) =
      op_taint tn (Var x)
Proof
  simp[FLOOKUP_DRESTRICT, for_checked_outputs_taint, jump_to_def, lookup_var_def]
QED

Theorem for_checked_outputs_clean:
  MEM x outputs ==>
  FLOOKUP (DRESTRICT G (COMPL (set outputs))) x = NONE /\
  op_taint (tn with t_var := tn.t_var |++ MAP (\v. (v,{})) outputs) (Var x) = {}
Proof
  simp[FLOOKUP_DRESTRICT, for_checked_outputs_taint]
QED

(* Consumer package: the successful checked-entry theorem supplies vs and its
   frame; outputs is [cv;rv;g1;z1;g2;z2;ev].  No property of its instructions
   is reopened here, and the allocated pointer p must not be overwritten. *)
Theorem for_checked_entry_setup:
  ghost_inv d cenv cx es G tn s /\ stmt_state_rel ctx fn cenv cx es s /\
  ptr_covers G tn p s sz /\ ~MEM p outputs /\
  (!x. MEM x outputs ==> not_local_ptr cenv es.scopes x /\
     cenv.ce_imm_alloca <> SOME (Var x) /\
     (!q. cenv.ce_return_buf <> SOME (PtrVar (Var x) q))) /\
  (!x. ~MEM x outputs ==> lookup_var x (s with vs_vars := vs) = lookup_var x s) /\
  sf = jump_to lbl (s with vs_vars := vs) /\
  Gf = DRESTRICT G (COMPL (set outputs)) /\
  tf = tn with t_var := tn.t_var |++ MAP (\v. (v,{})) outputs ==>
  ghost_inv d cenv cx es Gf tf sf /\
  stmt_state_rel ctx fn cenv cx es sf /\ ptr_covers Gf tf p sf sz /\
  sf.vs_current_bb = lbl /\ sf.vs_inst_idx = 0 /\
  sf.vs_allocas = s.vs_allocas /\ sf.vs_halted = s.vs_halted /\
  (!x. ~MEM x outputs ==> lookup_var x sf = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!x. MEM x outputs ==> FLOOKUP Gf x = NONE /\ op_taint tf (Var x) = {})
Proof
  strip_tac >> gvs[] >>
  (conj_tac >- (irule for_checked_outputs_ghost_frame >> simp[] >> metis_tac[])) >>
  (conj_tac >- (irule for_checked_outputs_state_frame >> simp[] >> metis_tac[])) >>
  (conj_tac >- (irule for_checked_outputs_ptr_covers >> simp[])) >>
  simp[jump_to_def, lookup_var_def, FLOOKUP_DRESTRICT,
       for_checked_outputs_taint] >>
  qpat_x_assum `!x. ~MEM x outputs ==> _` mp_tac >> simp[lookup_var_def]
QED
