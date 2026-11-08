Theory bodyPtrTypeBuiltinsEmptyUniform
Ancestors
  wordLoadStorePtr
  bodyPtrTypeBuiltinsEmptyZero typedCopyPtr fragGasSeqPtr ghostPcTransportPtr
  bodyPtrDefs fragExecPtr
  ptrDiscipline ptrSafeRun venomExecSemantics venomState venomInst finite_map words emitHelperProps

Theorem empty_zero_pair_cursor_frame:
  !D ctx func PG G tn s id p out w off sz H th.
    lookup_var p s = SOME w /\ ptr_covers G tn p s sz /\ p <> out /\
    off+32 <= sz /\ w2n w+sz < dimword (:256) /\ ~ctx_has_dalloca ctx /\
    inst_seq_ptr D 0 ctx func PG G tn
      [mk_inst id ADD [Var p; Lit (n2w off)] [out];
       mk_inst (id+1) MSTORE [Var out; Lit 0w] []] s H th ==>
    (!k. inst_seq_ptr D 0 ctx func PG G tn
      [mk_inst id ADD [Var p; Lit (n2w off)] [out];
       mk_inst (id+1) MSTORE [Var out; Lit 0w] []]
      (s with vs_inst_idx := k) H th) /\
    th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `u = update_var out (w+n2w off) s` >>
  qabbrev_tac `v = mstore (w2n (w+n2w off)) 0w u` >>
  `step_inst_base (mk_inst id ADD [Var p; Lit (n2w off)] [out]) s = OK u` by
    (simp[Abbr `u`] >> irule step_ADD >> simp[eval_operand_def]) >>
  `lookup_var out u = SOME (w+n2w off)` by
    simp[Abbr `u`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `!k. step_inst_base (mk_inst (id+1) MSTORE [Var out; Lit 0w] [])
      (u with vs_inst_idx := k) = OK (v with vs_inst_idx := k)` by
    (gvs[Abbr `v`, step_inst_base_def, mk_inst_def, exec_write2_def,
         eval_operand_def, lookup_var_def, mstore_def]) >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[inst_seq_ptr_def] >> strip_tac >>
  conj_tac >- suspend "cursor" >>
  simp[copy_len_binop_ghost_frame, Abbr `u`, Abbr `v`,
       mstore_ghost_frame, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       eval_operand_def, op_taint_def] >>
  simp[step_taint_def, imm_taint_def, mk_inst_def]
QED

Resume empty_zero_pair_cursor_frame[cursor]:
  gen_tac >>
  `step_inst_base (mk_inst id ADD [Var p; Lit (n2w off)] [out])
      (s with vs_inst_idx := k) = OK (u with vs_inst_idx := k)` by
    (`step_inst_base (mk_inst id ADD [Var p; Lit (n2w off)] [out])
        (s with vs_inst_idx := k) =
        OK (update_var out (w+n2w off) (s with vs_inst_idx := k))` by
       (irule step_ADD >> gvs[eval_operand_def, lookup_var_def]) >>
     gvs[Abbr `u`, update_var_def]) >>
  simp[] >>
  conj_tac >- (irule ptr_inst_ok_copy_len_binop >>
    gvs[ptr_covers_def, op_taint_def]) >>
  irule ptr_inst_ok_mstore >> simp[op_taint_def] >>
  `ptr_covers (step_prov PG G (mk_inst id ADD [Var p; Lit (n2w off)] [out]) u)
      (step_taint (mk_inst id ADD [Var p; Lit (n2w off)] [out]) s u tn)
      out u 32` by
    (simp[Abbr `u`] >> irule empty_zero_offset_coverage >> metis_tac[]) >>
  simp[]
QED
Finalise empty_zero_pair_cursor_frame

Theorem empty_zero_pair_uniform_certificate:
  !D ctx func PG G tn s id p out w off sz.
    lookup_var p s = SOME w /\ ptr_covers G tn p s sz /\ p <> out /\
    off+32 <= sz /\ w2n w+sz < dimword (:256) /\ ~ctx_has_dalloca ctx ==>
    ?G' tn'. inst_seq_ptr D 0 ctx func PG G tn
      [mk_inst id ADD [Var p; Lit (n2w off)] [out];
       mk_inst (id+1) MSTORE [Var out; Lit 0w] []] s G' tn' /\
      ptr_covers G' tn' p
        (mstore (w2n (w+n2w off)) 0w (update_var out (w+n2w off) s)) sz /\
      tn'.t_mem = tn.t_mem DIFF
        {i | w2n w+off <= i /\ i < w2n w+off+32} /\
      (!q. q <> out ==> FLOOKUP G' q = FLOOKUP G q /\
        op_taint tn' (Var q) = op_taint tn (Var q)) /\
      (!k. inst_seq_ptr D 0 ctx func PG G tn
        [mk_inst id ADD [Var p; Lit (n2w off)] [out];
         mk_inst (id+1) MSTORE [Var out; Lit 0w] []]
        (s with vs_inst_idx := k) G' tn') /\
      tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  rpt gen_tac >> strip_tac >>
  drule_all empty_zero_pair_certificate >>
  disch_then (qspecl_then [`D`, `func`, `PG`, `id`] strip_assume_tac) >>
  drule_all empty_zero_pair_cursor_frame >> strip_tac >>
  qexistsl_tac [`G'`, `tn'`] >> simp[]
QED
