(* The internal return's guard release with the pointer ghost: the
   pointer twin of internalReturnUnlockMem's compile_return_unlock_frag_mem.
   Every runtime and deploy package uses transient locks, so the release
   is at most one TSTORE of zero.  Zeroing a slot only grows the dead
   storage bytes (storage_dead_update_zero), so storage taint stays
   confined to dead bytes whatever the key.
   TOP-LEVEL: return_unlock_path_ptr. *)
Theory internalReturnUnlockPtr
Ancestors
  stmtSimReturn stmtLowering context emitHelper assignTuplePtrPrefix
  assignBasePtrWordStore transientLockProps accountsRelProps bodyPtrDefs
  fragGasPathPtr ptrDiscipline ptrSafeRun venomState venomInst
  loweringStateRelDefs pred_set

Theorem return_unlock_path_ptr:
  compile_return_unlock ce sa = ((),su) /\ fn_has_code sa su func /\
  (!nr nkey ut iv. ce.ce_nonreentrant = (nr,nkey,ut,iv) ==> ut) /\
  ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~s.vs_call_ctx.cc_static /\ stor_taint_ok cx tn s ==>
  ?tm. gas_path_ptr D 0 ctx func PG G tn s 0 G tm
         (OK (return_unlock_state ce s)) /\
       stor_taint_ok cx tm (return_unlock_state ce s) /\
       tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\ tm.t_imm = tn.t_imm /\
       (!p. op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `?nr nkey ut iv. ce.ce_nonreentrant = (nr,nkey,ut,iv)` by
    metis_tac[pairTheory.ABS_PAIR_THM] >>
  `ut` by metis_tac[] >>
  reverse (Cases_on `nr /\ ~iv`)
  >- (`return_unlock_state ce s = s` by gvs[return_unlock_state_def, LET_THM] >>
      qexists_tac `tn` >> simp[] >>
      irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  gvs[] >>
  `emit_inst TSTORE [Lit (n2w nkey); Lit 0w] [] sa = ((),su)` by
    (qpat_x_assum `compile_return_unlock _ _ = _` mp_tac >>
      asm_simp_tac (srw_ss()) [compile_return_unlock_def, LET_THM,
       compile_nonreentrant_unlock_def, emit_void_def, emit_inst_def]) >>
  `return_unlock_state ce s =
     tstore (n2w nkey) 0w s with vs_inst_idx := SUC s.vs_inst_idx` by
    asm_simp_tac (srw_ss()) [return_unlock_state_def, LET_THM] >>
  `step_inst_base (mk_inst sa.cs_next_id TSTORE [Lit (n2w nkey); Lit 0w] [])
     s = OK (tstore (n2w nkey) 0w s)` by simp[step_TSTORE_lit] >>
  `ptr_inst_ok D 0 0 ctx func G tn
     (mk_inst sa.cs_next_id TSTORE [Lit (n2w nkey); Lit 0w] []) s` by
    (irule assign_base_ptr_inst_ok_storage_word >> simp[op_taint_def]) >>
  `TSTORE <> INVOKE /\ TSTORE <> GAS /\ ~is_terminator TSTORE` by
    simp[is_terminator_def] >>
  drule_all emit_inst_zero_path_ptr >>
  disch_then (qspec_then `PG` assume_tac) >>
  `eval_operand (Lit (n2w nkey)) s = SOME (n2w nkey) /\
   (tstore (n2w nkey) 0w s).vs_allocas = s.vs_allocas /\
   (tstore (n2w nkey) 0w s).vs_fmp = s.vs_fmp` by
    simp[eval_operand_def, tstore_def] >>
  qspecl_then [`TSTORE`, `sa.cs_next_id`, `Lit (n2w nkey)`, `Lit 0w`, `s`,
    `tstore (n2w nkey) 0w s`, `PG`, `G`, `tn`, `n2w nkey`] mp_tac
    assign_base_storage_word_ghost >>
  impl_tac >- simp[] >> strip_tac >>
  gvs[] >>
  qexists_tac `tn with t_trans := key_update tn.t_trans (n2w nkey) {}` >>
  gvs[op_taint_def] >>
  qpat_x_assum `stor_taint_ok _ _ _` mp_tac >>
  simp[stor_taint_ok_def, tstore_def, cx_dead_def, SUBSET_DEF,
       key_update_def, combinTheory.APPLY_UPDATE_THM,
       pairTheory.FORALL_PROD] >>
  rpt strip_tac >> first_x_assum drule >> rw[] >>
  irule storage_dead_update_zero >> simp[]
QED

(* A state reached after the release is the release of a state that still
   has the transient storage from before it; intret_q asks for that form. *)
Theorem return_unlock_state_from_final:
  (!nr nkey ut iv. ce.ce_nonreentrant = (nr,nkey,ut,iv) ==> ut) /\
  t.vs_transient = (return_unlock_state ce t0).vs_transient /\
  t.vs_call_ctx = t0.vs_call_ctx /\ 0 < t.vs_inst_idx ==>
  ?i. t = return_unlock_state ce
            (t with <| vs_transient := t0.vs_transient; vs_inst_idx := i |>)
Proof
  strip_tac >>
  `?nr nkey ut iv. ce.ce_nonreentrant = (nr,nkey,ut,iv)` by
    metis_tac[pairTheory.ABS_PAIR_THM] >>
  `ut` by metis_tac[] >>
  Cases_on `nr /\ ~iv`
  >- (qexists_tac `PRE t.vs_inst_idx` >>
      gvs[return_unlock_state_def, LET_THM, tstore_def,
          venom_state_component_equality] >>
      decide_tac) >>
  qexists_tac `t.vs_inst_idx` >>
  gvs[return_unlock_state_def, LET_THM, venom_state_component_equality]
QED
