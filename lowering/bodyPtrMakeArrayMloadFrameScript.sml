(* Fresh MLOAD preserves ambient ghosts independently of loaded taint. *)
Theory bodyPtrMakeArrayMloadFrame
Ancestors
  bodyPtrMakeArrayAddFrame bodyPtrDefs ptrDiscipline venomState venomInst
  finite_map compileEnv context codegenRel

Theorem mload_ghost_frame:
  (step_taint (mk_inst id MLOAD [src] [tmp]) s (update_var tmp w s) tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id MLOAD [src] [tmp]) s (update_var tmp w s) tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id MLOAD [src] [tmp]) s (update_var tmp w s) tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id MLOAD [src] [tmp]) s (update_var tmp w s) tn).t_imm = tn.t_imm /\
  (!x. x <> tmp ==>
    FLOOKUP (step_prov PG G (mk_inst id MLOAD [src] [tmp]) (update_var tmp w s)) x = FLOOKUP G x /\
    op_taint (step_taint (mk_inst id MLOAD [src] [tmp]) s (update_var tmp w s) tn) (Var x) = op_taint tn (Var x))
Proof
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       mk_inst_def, set_var_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, fixed_source_write_range_def,
       written_taint_def, range_bytes_def, new_site_bytes_def,
       op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, update_var_def,
       pred_setTheory.EXTENSION] >>
  simp[FLOOKUP_DEF] >> metis_tac[]
QED

Theorem mload_ghost_kept:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. not_fresh_at sa x ==> x <> tmp) ==>
  ghost_kept cenv es sa G0 tn0 s0
    (step_prov PG G (mk_inst id MLOAD [src] [tmp]) (update_var tmp w s))
    (step_taint (mk_inst id MLOAD [src] [tmp]) s (update_var tmp w s) tn)
Proof
  strip_tac >>
  irule ghost_kept_frame >> qexistsl_tac [`G`, `tn`] >>
  simp[mload_ghost_frame]
QED

Theorem mload_ghost_inv:
  ghost_inv d cenv cx es G tn s /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> p <> tmp) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> tmp) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> tmp) ==>
  ghost_inv d cenv cx es
    (step_prov PG G (mk_inst id MLOAD [src] [tmp]) (update_var tmp w s))
    (step_taint (mk_inst id MLOAD [src] [tmp]) s (update_var tmp w s) tn)
    ((update_var tmp w s) with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gvs[ghost_inv_def] >> (
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `p <> tmp` by metis_tac[] >>
      simp[ptr_covers_def, mload_ghost_frame] >>
      gvs[ptr_covers_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  conj_tac
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >> PairCases_on `x` >>
      gvs[return_buf_ptr_def] >>
      simp[ptr_covers_def, mload_ghost_frame] >>
      gvs[ptr_covers_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> `x <> tmp` by metis_tac[] >>
      qpat_x_assum `!x sz. cenv.ce_return_pc = _ ==> _` drule >>
      simp[mload_ghost_frame]) >>
  gvs[stor_taint_ok_def, update_var_def, mload_ghost_frame])
QED
