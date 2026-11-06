(* Scalar external materialization exports no buffer claim for the loaded word. *)
Theory bodyPtrMakeArrayExternalWord
Ancestors
  bodyPtrMakeArrayCopyStep bodyPtrMakeArrayExternalFrame bodyPtrDefs
  venomState venomInst finite_map

Theorem external_word_materialize_endpoint:
  (opc = SLOAD \/ opc = TLOAD \/ opc = DLOAD) /\
  op_taint tn src = {} /\ allocas_from 0 s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc [src] [tmp]) /\
  eval_operand src s = SOME a /\
  step_inst_base (mk_inst id opc [src] [tmp]) s = OK (update_var tmp w s) /\
  (opc = SLOAD ==> key_taint tn.t_stor a = {}) /\
  (opc = TLOAD ==> key_taint tn.t_trans a = {}) /\
  ghost_inv d cenv cx es' G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. not_fresh_at sa x ==> x <> tmp) /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> p <> tmp) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> tmp) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> tmp) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf = ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx) /\
    eval_operand (Var tmp) sf = SOME w /\ op_taint tnf (Var tmp) = {} /\
    op_prov Gf (Var tmp) = NONE /\
    ghost_inv d cenv cx es' Gf tnf sf /\
    ghost_kept cenv es sa G0 tn0 s0 Gf tnf /\
    sf.vs_memory = s.vs_memory /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\
    (!dst. tmp <> dst ==> lookup_var dst sf = lookup_var dst s) /\
    (!dst n. tmp <> dst /\ ptr_covers G tn dst s n ==>
       ptr_covers Gf tnf dst sf n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexistsl_tac [
    `step_prov PG G (mk_inst id opc [src] [tmp]) (update_var tmp w s)`,
    `step_taint (mk_inst id opc [src] [tmp]) s (update_var tmp w s) tn`,
    `(update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >- (irule external_load_ptr_path >> simp[]) >>
  simp[] >>
  conj_tac >- simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- (drule_all external_load_output_ghost >> gvs[]) >>
  conj_tac >- (drule_all external_load_output_ghost >> simp[ptrDisciplineTheory.op_prov_def]) >>
  conj_tac >- (irule external_load_ghost_inv >> simp[] >> metis_tac[]) >>
  conj_tac >- (irule external_load_ghost_kept >> simp[] >> metis_tac[]) >>
  conj_tac >- simp[update_var_def] >>
  conj_tac >- metis_tac[external_load_ghost_frame] >>
  conj_tac >- metis_tac[external_load_ghost_frame] >>
  conj_tac >- metis_tac[external_load_ghost_frame] >>
  conj_tac >- simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> irule external_load_old_coverage >> simp[]
QED
