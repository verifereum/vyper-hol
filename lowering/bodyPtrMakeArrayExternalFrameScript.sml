(* Fresh external loads preserve ambient ghost judgments even with tainted outputs. *)
Theory bodyPtrMakeArrayExternalFrame
Ancestors
  bodyPtrMakeArrayCopyStep bodyPtrMakeArrayAddFrame bodyPtrDefs ptrDiscipline
  venomState venomInst finite_map compileEnv context

Theorem external_load_ghost_kept:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (opc = SLOAD \/ opc = TLOAD \/ opc = DLOAD) /\
  eval_operand src s = SOME a /\
  (!x. not_fresh_at sa x ==> x <> tmp) ==>
  ghost_kept cenv es sa G0 tn0 s0
    (step_prov PG G (mk_inst id opc [src] [tmp]) (update_var tmp w s))
    (step_taint (mk_inst id opc [src] [tmp]) s (update_var tmp w s) tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all external_load_ghost_frame >> strip_tac >>
  irule ghost_kept_frame >> qexistsl_tac [`G`, `tn`] >>
  simp[op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem external_load_ghost_inv:
  ghost_inv d cenv cx es G tn s /\
  (opc = SLOAD \/ opc = TLOAD \/ opc = DLOAD) /\
  eval_operand src s = SOME a /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> p <> tmp) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> tmp) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> tmp) ==>
  ghost_inv d cenv cx es
    (step_prov PG G (mk_inst id opc [src] [tmp]) (update_var tmp w s))
    (step_taint (mk_inst id opc [src] [tmp]) s (update_var tmp w s) tn)
    ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all external_load_ghost_frame >> strip_tac >>
  gvs[ghost_inv_def] >> (
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `p <> tmp` by metis_tac[] >>
      simp[ptr_covers_def, op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
      gvs[ptr_covers_def, op_taint_def, update_var_def, lookup_var_def,
          FLOOKUP_UPDATE] >> metis_tac[]) >>
  conj_tac
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >> PairCases_on `x` >>
      gvs[return_buf_ptr_def] >>
      simp[ptr_covers_def, op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
      gvs[ptr_covers_def, op_taint_def, update_var_def, lookup_var_def,
          FLOOKUP_UPDATE] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> `x <> tmp` by metis_tac[] >>
      qpat_x_assum `!x sz. cenv.ce_return_pc = _ ==> _` drule >>
      simp[op_taint_def, FLOOKUP_UPDATE]) >>
  gvs[stor_taint_ok_def, update_var_def])
QED
