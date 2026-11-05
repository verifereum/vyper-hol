(* Concrete range-header layout adapter. No synthetic compiler transition is
   assumed by the consumer: the witness states below only describe prefixes. *)
Theory forPtrRangePrepare
Ancestors forPtrControl forPtrScalarStore forPtrRangeCallback fragExec
  emitHelperProps venomState venomInst finite_map list ptrDiscipline
  fragGasPathPtr bodyPtrDefs compileEnv

Theorem for_header_test_path_ptr:
  lookup_block cond_lbl fn.fn_blocks =
    SOME <| bb_label := cond_lbl;
      bb_instructions := [mk_inst j1 EQ [Var cv; Var ev] [dv];
        mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []] |> /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\
  lookup_var cv s = SOME w /\ lookup_var ev s = SOME z /\
  op_taint tn (Var cv) = {} /\ op_taint tn (Var ev) = {} /\
  op_prov G (Var cv) = NONE /\ op_prov G (Var ev) = NONE ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {dv}))
    (tn with t_var := tn.t_var |+ (dv,{}))
    (OK (jump_to (if w = z then exit_lbl else body_lbl)
      (update_var dv (if w = z then 1w else 0w) s)))
Proof
  strip_tac >> irule for_counter_test_path_ptr >> simp[] >>
  qexistsl_tac [`Var ev`, `cv`, `j1`,

    `(ARB:compile_state) with <| cs_blocks := []; cs_current_bb := cond_lbl;
       cs_current_insts := []; cs_next_id := j1 |>`,
    `(ARB:compile_state) with <| cs_blocks := []; cs_current_bb := cond_lbl;
       cs_current_insts := [mk_inst j1 EQ [Var cv; Var ev] [dv];
         mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []] |>`,
    `(ARB:compile_state) with <| cs_blocks := []; cs_current_bb := cond_lbl;
       cs_current_insts := [mk_inst j1 EQ [Var cv; Var ev] [dv]];
       cs_next_id := j2 |>`] >>
  simp[fn_has_code_def, emitted_blocks_def, eval_operand_def]
QED

Theorem for_header_store_path_ptr:
  lookup_block cond_lbl fn.fn_blocks =
    SOME <| bb_label := cond_lbl;
      bb_instructions := [mk_inst j1 EQ [Var cv; Var ev] [dv];
        mk_inst j2 JNZ [Var dv; Label exit_lbl; Label body_lbl] []] |> /\
  lookup_block body_lbl fn.fn_blocks = SOME bbb /\
  get_instruction bbb 0 = SOME (mk_inst j3 MSTORE [Var p; Var cv] []) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = cond_lbl /\ s.vs_inst_idx = 0 /\
  lookup_var cv s = SOME w /\ lookup_var ev s = SOME z /\
  lookup_var p s = SOME a /\ w <> z /\ dv <> p /\ dv <> cv /\
  ptr_covers G tn p s 32 /\
  op_taint tn (Var cv) = {} /\ op_taint tn (Var ev) = {} /\
  op_prov G (Var cv) = NONE /\ op_prov G (Var ev) = NONE ==>
  ?tf. gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {dv})) tf
    (OK ((mstore (w2n a) w (jump_to body_lbl (update_var dv 0w s)))
      with vs_inst_idx := 1)) /\
    tf.t_var = (tn.t_var |+ (dv,{})) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    tf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32}
Proof
  strip_tac >> drule_all for_header_test_path_ptr >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `OK s1` >>
  `ptr_covers (DRESTRICT G (COMPL {dv}))
     (tn with t_var := tn.t_var |+ (dv,{})) p s1 32` by
    gvs[Abbr `s1`, ptr_covers_def, jump_to_def, update_var_def,
        lookup_var_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def] >>
  `?tf. gas_path_ptr D 0 ctx fn PG (DRESTRICT G (COMPL {dv}))
     (tn with t_var := tn.t_var |+ (dv,{})) s1 0
     (DRESTRICT G (COMPL {dv})) tf
     (OK ((mstore (w2n a) w s1) with vs_inst_idx := SUC s1.vs_inst_idx)) /\
     tf.t_var = tn.t_var |+ (dv,{}) /\ tf.t_stor = tn.t_stor /\
     tf.t_trans = tn.t_trans /\
     tf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32}` by
    (irule (SRULE [] (Q.INST
       [`tn` |-> `tn with t_var := tn.t_var |+ (dv,{})`]
       scalar_mstore_path_ptr)) >> simp[] >>
     conj_tac >- simp[Abbr `s1`, jump_to_def, update_var_def] >>
     qexistsl_tac [`bbb`, `p`, `j3`, `Var cv`] >>
     gvs[Abbr `s1`, jump_to_def, update_var_def, eval_operand_def,
          lookup_var_def, FLOOKUP_UPDATE, op_taint_def]) >>
  qexists_tac `tf` >> simp[Abbr `s1`] >>
  qpat_x_assum `!PG D. _` (qspecl_then [`PG`, `D`] mp_tac) >>
  disch_then (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >>
  simp[jump_to_def]
QED

(* Scalar control results may replace no live local or return-buffer pointer.
   Return-PC taint is safe even if the result replaces that scalar. *)
Theorem for_scalar_overwrite_ghost:
  ghost_inv d cenv cx es G tn s /\
  not_local_ptr cenv es.scopes out /\
  (!sz. cenv.ce_return_buf <> SOME (PtrVar (Var out) sz)) ==>
  ghost_inv d cenv cx es (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{})) (update_var out w s)
Proof
  strip_tac >> fs[ghost_inv_def, not_local_ptr_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `p <> out` by metis_tac[] >>
      qpat_x_assum `!name entry p sz. _` drule_all >>
      simp[ptr_covers_def, lookup_var_def, update_var_def,
           op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE])
  >- (Cases_on `d` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
      fs[return_buf_ptr_def] >>
      rename1 `cenv.ce_return_buf = SOME (PtrVar (Var rp) slot_size)` >>
      `rp <> out` by metis_tac[] >>
      simp[ptr_covers_def, lookup_var_def, update_var_def,
           op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
      gvs[ptr_covers_def, lookup_var_def, op_taint_def])
  >- (rpt strip_tac >> Cases_on `out = x`
      >- simp[op_taint_def, FLOOKUP_UPDATE] >>
      qpat_x_assum `!x sz. _` drule >>
      simp[op_taint_def, FLOOKUP_UPDATE]) >>
  fs[stor_taint_ok_def, update_var_def]
QED
