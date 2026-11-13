(* Exhaustion drops the array resources: only the checked equal header and
   caller frame are required by the shared Done post. *)
Theory forPtrArrayTerminal
Ancestors forPtrArrayInvariant forPtrArrayPrepare forPtrRangeTerminal
  bodyPtrDefs venomState ptrDiscipline finite_map

Theorem for_array_terminal_ptr:
  lookup_block cond_lbl func.fn_blocks =
    SOME <|bb_label := cond_lbl; bb_instructions :=
      [mk_inst j1 EQ [Var idx; Lit (n2w n)] [dv];
       mk_inst j2 JNZ [Var dv; Label exit_lbl; Label stmts_lbl] []]|> /\
  n = LENGTH vs /\
  for_array_inv_ptr ctx func cenv cx st0 vs tv id idx bp arr_base p dst sz ainst
    cond_lbl st s0 G0 tn0 d name snapshot (LENGTH vs) es G tn s /\
  ~ctx_has_dalloca ctx /\ not_local_ptr cenv es.scopes dv /\
  (!x. not_fresh_at st x ==> x <> dv) /\
  (!x q. cenv.ce_return_buf = SOME (PtrVar (Var x) q) ==> not_fresh_at st x) ==>
  ?t gf tf.
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_path_ptr (cx_dead H cx) 0 ctx func PG G tn s 0 gf tf (OK t)) /\
    for_array_done_ptr ctx func cenv cx st0 exit_lbl st s0 G0 tn0 d
      (es with gas_obs := []) gf tf t
Proof
  strip_tac >> drule for_array_inv_header_ptr >> strip_tac >>
  `!q. cenv.ce_return_buf <> SOME (PtrVar (Var dv) q)` by metis_tac[] >>
  `!D. gas_path_ptr D 0 ctx func PG G tn s 0
    (DRESTRICT G (COMPL {dv})) (tn with t_var := tn.t_var |+ (dv,{}))
    (OK (jump_to exit_lbl (update_var dv 1w s)))` by
    (gen_tac >>
     drule_all (SRULE [op_prov_def] for_array_header_test_path_ptr) >> simp[]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx (es with gas_obs := [])
      (jump_to exit_lbl (update_var dv 1w s)) /\
    ghost_inv H d cenv cx (es with gas_obs := [])
      (DRESTRICT G (COMPL {dv})) (tn with t_var := tn.t_var |+ (dv,{}))
      (jump_to exit_lbl (update_var dv 1w s))` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `H` (strip_assume_tac o UNDISCH)) >>
     drule_all for_header_exit_transport_ptr >>
     disch_then (qspec_then `exit_lbl` strip_assume_tac) >> simp[]) >>
  drule_all for_header_exit_old_frame >>
  disch_then (qspec_then `exit_lbl` strip_assume_tac) >>
  qexistsl_tac [`jump_to exit_lbl (update_var dv 1w s)`,
    `DRESTRICT G (COMPL {dv})`, `tn with t_var := tn.t_var |+ (dv,{})`] >>
  simp[for_array_done_ptr_def, jump_to_def, update_var_def] >>
  rpt strip_tac >>
  `(es with gas_obs := []).accounts = es.accounts /\
   (es with gas_obs := []).tStorage = es.tStorage` by simp[] >>
  metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_backends]
QED
