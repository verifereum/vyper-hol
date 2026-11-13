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
  for_array_inv_ptr ctx func cenv cx vs tv id idx bp arr_base p dst sz ainst
    cond_lbl st s0 G0 tn0 d name snapshot (LENGTH vs) es G tn s /\
  ~ctx_has_dalloca ctx /\ not_local_ptr cenv es.scopes dv /\
  (!x. not_fresh_at st x ==> x <> dv) /\
  (!x q. cenv.ce_return_buf = SOME (PtrVar (Var x) q) ==> not_fresh_at st x) ==>
  ?t gf tf.
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 gf tf (OK t) /\
    for_array_done_ptr ctx func cenv cx exit_lbl st s0 G0 tn0 d
      (es with gas_obs := []) gf tf t
Proof
  strip_tac >> drule for_array_inv_header_ptr >> strip_tac >>
  `!q. cenv.ce_return_buf <> SOME (PtrVar (Var dv) q)` by metis_tac[] >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0
    (DRESTRICT G (COMPL {dv})) (tn with t_var := tn.t_var |+ (dv,{}))
    (OK (jump_to exit_lbl (update_var dv 1w s)))` by
    (drule_all (SRULE [op_prov_def] for_array_header_test_path_ptr) >> simp[]) >>
  drule_all for_header_exit_transport_ptr >>
  disch_then (qspec_then `exit_lbl` strip_assume_tac) >>
  drule_all for_header_exit_old_frame >>
  disch_then (qspec_then `exit_lbl` strip_assume_tac) >>
  qexistsl_tac [`jump_to exit_lbl (update_var dv 1w s)`,
    `DRESTRICT G (COMPL {dv})`, `tn with t_var := tn.t_var |+ (dv,{})`] >>
  simp[for_array_done_ptr_def, jump_to_def, update_var_def]
QED
