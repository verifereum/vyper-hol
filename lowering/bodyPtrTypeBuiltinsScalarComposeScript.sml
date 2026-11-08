Theory bodyPtrTypeBuiltinsScalarCompose
Ancestors
  bodyPtrBopHashSuffix bodyPtrTypeBuiltinsSeq instSeqComposePtr fragGasSeqPtr exprLoweringProps
  instIdxIndep fragExec arithmetic venomExecSemantics venomState venomInst ptrDiscipline list

Theorem scalar_seq_append_abort_iff:
  run_inst_seq (xs ++ ys) s = Abort err t <=>
  run_inst_seq xs s = Abort err t \/
  ?u. run_inst_seq xs s = OK u /\ run_inst_seq ys u = Abort err t
Proof
  Cases_on `run_inst_seq xs s` >>
  qspecl_then [`xs`,`ys`,`s`] mp_tac run_inst_seq_append_err >> simp[] >>
  imp_res_tac run_inst_seq_append >> gvs[]
QED

(* The suffix witness may depend on the actual advanced cursor. *)
Theorem scalar_seq_ptr_append_at:
  !xs s u G tn H th ys J tk.
    EVERY (\i. ~is_terminator i.inst_opcode) xs /\
    run_inst_seq xs s = OK u /\
    inst_seq_ptr D lo ctx fn PG G tn xs s H th /\
    inst_seq_ptr D lo ctx fn PG H th ys
      (u with vs_inst_idx := s.vs_inst_idx + LENGTH xs) J tk ==>
    inst_seq_ptr D lo ctx fn PG G tn (xs ++ ys) s J tk
Proof
  Induct >- simp[run_inst_seq_def, inst_seq_ptr_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, Once inst_seq_ptr_def] >>
  rename1 `step_inst_base h s = OK v` >>
  simp[Once inst_seq_ptr_def] >> first_x_assum irule >>
  qexistsl_tac [`H`,`th`,`u with vs_inst_idx := SUC s.vs_inst_idx`] >>
  gvs[run_inst_seq_inst_idx, exec_result_map_def, ADD_CLAUSES]
QED

Theorem scalar_seq_clean_trans:
  (!op. op_prov G op = NONE /\ op_taint tn op = {} ==>
     op_prov H op = NONE /\ op_taint th op = {}) /\
  (!op. op_prov H op = NONE /\ op_taint th op = {} ==>
     op_prov J op = NONE /\ op_taint tk op = {}) ==>
  !op. op_prov G op = NONE /\ op_taint tn op = {} ==>
     op_prov J op = NONE /\ op_taint tk op = {}
Proof
  metis_tac[]
QED

Theorem scalar_seq_ghost_frame_trans:
  (!p. protected p ==> FLOOKUP H p = FLOOKUP G p /\
     op_taint th (Var p) = op_taint tn (Var p)) /\
  (!p. protected p ==> FLOOKUP J p = FLOOKUP H p /\
     op_taint tk (Var p) = op_taint th (Var p)) /\
  th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
  th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
  tk.t_mem = th.t_mem /\ tk.t_stor = th.t_stor /\
  tk.t_trans = th.t_trans /\ tk.t_imm = th.t_imm ==>
  (!p. protected p ==> FLOOKUP J p = FLOOKUP G p /\
     op_taint tk (Var p) = op_taint tn (Var p)) /\
  tk.t_mem = tn.t_mem /\ tk.t_stor = tn.t_stor /\
  tk.t_trans = tn.t_trans /\ tk.t_imm = tn.t_imm
Proof
  strip_tac >> simp[] >> metis_tac[]
QED

Theorem scalar_seq_runtime_frame_trans:
  (u with vs_vars := s.vs_vars) = s /\
  (t with vs_vars := u.vs_vars) = u /\
  (!p. protected p ==> lookup_var p u = lookup_var p s) /\
  (!p. protected p ==> lookup_var p t = lookup_var p u) ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. protected p ==> lookup_var p t = lookup_var p s)
Proof
  strip_tac >> conj_tac
  >- (`(t with vs_vars := s.vs_vars) =
         ((t with vs_vars := u.vs_vars) with vs_vars := s.vs_vars)` by simp[] >>
      metis_tac[]) >> metis_tac[]
QED

Theorem scalar_seq_ptr_append_post:
  EVERY (\i. ~is_terminator i.inst_opcode) xs /\
  run_inst_seq xs s = OK u /\
  inst_seq_ptr D lo ctx fn PG G tn xs s H th /\
  (!k. ?J tk. inst_seq_ptr D lo ctx fn PG H th ys
     (u with vs_inst_idx := k) J tk /\ post J tk) ==>
  ?J tk. inst_seq_ptr D lo ctx fn PG G tn (xs ++ ys) s J tk /\ post J tk
Proof
  strip_tac >> first_x_assum
    (qspec_then `s.vs_inst_idx + LENGTH xs` strip_assume_tac) >>
  qexistsl_tac [`J`,`tk`] >> simp[] >>
  irule scalar_seq_ptr_append_at >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> gvs[ADD_COMM]
QED

Theorem scalar_seq_ptr_abort_post:
  EVERY (\i. ~is_terminator i.inst_opcode) xs /\
  run_inst_seq xs s = Abort err t /\
  (?H th. inst_seq_ptr D lo ctx fn PG G tn xs s H th /\ post H th) ==>
  ?H th. inst_seq_ptr D lo ctx fn PG G tn (xs ++ ys) s H th /\ post H th
Proof
  strip_tac >> qexistsl_tac [`H`,`th`] >> simp[] >>
  irule inst_seq_ptr_abort_append >> goal_assum (drule_at Any) >> simp[]
QED
