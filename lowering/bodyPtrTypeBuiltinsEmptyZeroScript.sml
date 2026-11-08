Theory bodyPtrTypeBuiltinsEmptyZero
Ancestors
  wordLoadStorePtr
  bodyPtrTypeBuiltinsEmptyAlloc fragGasSeqPtr fragExecPtr typedCopyPtr
  bodyPtrDefs ptrDiscipline venomExecSemantics venomState venomInst finite_map words
  ghostPcTransportPtr emitHelperProps

(* Header zeroing, with no fresh-site or initial-memory cleanliness premise. *)
Theorem empty_zero_store_certificate:
  !D ctx func PG G tn s id p w sz.
    lookup_var p s = SOME w /\ ptr_covers G tn p s sz /\
    32 <= sz /\ ~ctx_has_dalloca ctx ==>
    ?tn'. inst_seq_ptr D 0 ctx func PG G tn
      [mk_inst id MSTORE [Var p; Lit 0w] []] s G tn' /\
      ptr_covers G tn' p (mstore (w2n w) 0w s) sz /\
      (!q k. ptr_covers G tn q s k ==>
        ptr_covers G tn' q (mstore (w2n w) 0w s) k) /\
      tn'.t_mem = tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w+32} /\
      tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  rpt gen_tac >> strip_tac >>
  `ptr_covers G tn p s 32` by
    (gvs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
      arithmeticTheory.LESS_EQ_LESS_EQ_MONO]) >>
  `step_inst_base (mk_inst id MSTORE [Var p; Lit 0w] []) s =
    OK (mstore (w2n w) 0w s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx func G tn
     (mk_inst id MSTORE [Var p; Lit 0w] []) s` by
    (irule ptr_inst_ok_mstore >> simp[op_taint_def]) >>
  qexists_tac `step_taint (mk_inst id MSTORE [Var p; Lit 0w] []) s
     (mstore (w2n w) 0w s) tn` >>
  drule mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `tn`, `id`, `Lit 0w`, `0w`] mp_tac) >>
  simp[eval_operand_def, op_taint_def] >> strip_tac >>
  simp[inst_seq_ptr_def, ptr_inst_ok_mstore] >>
  gvs[ptr_covers_def, op_taint_def, lookup_var_def, mstore_def] >>
  simp[step_taint_def, imm_taint_def, mk_inst_def]
QED

Theorem empty_zero_offset_coverage:
  !PG G tn s id p out w off sz n.
    lookup_var p s = SOME w /\ ptr_covers G tn p s sz /\
    off+n <= sz /\ w2n w + sz < dimword (:256) ==>
    ptr_covers
      (step_prov PG G (mk_inst id ADD [Var p; Lit (n2w off)] [out])
        (update_var out (w+n2w off) s))
      (step_taint (mk_inst id ADD [Var p; Lit (n2w off)] [out]) s
        (update_var out (w+n2w off) s) tn)
      out (update_var out (w+n2w off) s) n
Proof
  rpt gen_tac >> strip_tac >>
  `op_taint (step_taint (mk_inst id ADD [Var p; Lit (n2w off)] [out]) s
     (update_var out (w+n2w off) s) tn) (Var out) = {}` by
    simp[copy_len_binop_ghost_frame] >>
  gvs[ptr_covers_def] >>
  `off < dimword (:256)` by decide_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_UPDATE, lookup_var_def,
       update_var_def, w2n_add_2, w2n_n2w, arithmeticTheory.LESS_MOD] >>
  decide_tac
QED

Theorem empty_zero_pair_certificate:
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
        op_taint tn' (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `u = update_var out (w+n2w off) s` >>
  qabbrev_tac `G1 = step_prov PG G
    (mk_inst id ADD [Var p; Lit (n2w off)] [out]) u` >>
  qabbrev_tac `tn1 = step_taint
    (mk_inst id ADD [Var p; Lit (n2w off)] [out]) s u tn` >>
  `lookup_var out u = SOME (w+n2w off)` by
    simp[Abbr `u`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `ptr_covers G1 tn1 out u 32` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `u`] >>
     irule empty_zero_offset_coverage >> metis_tac[]) >>
  `ptr_covers G1 tn1 p u sz` by suspend "base" >>
  drule_all (SRULE [] (Q.INST [`sz` |-> `32`] (SPEC_ALL empty_zero_store_certificate))) >>
  disch_then (qspecl_then [`id+1`, `func`, `PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G1`, `tn'`] >>
  conj_tac >- suspend "sequence" >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "memory" >>
  rpt strip_tac >>
  `op_taint tn' (Var q) = op_taint tn1 (Var q)` by simp[op_taint_def] >>
  simp[Abbr `G1`, Abbr `tn1`, Abbr `u`, copy_len_binop_ghost_frame]
QED

Resume empty_zero_pair_certificate[base]:
  simp[ptr_covers_def, Abbr `G1`, Abbr `tn1`, Abbr `u`,
       copy_len_binop_ghost_frame, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  gvs[ptr_covers_def, lookup_var_def]
QED

Resume empty_zero_pair_certificate[memory]:
  `off < dimword (:256)` by decide_tac >>
  `w2n (w+n2w off) = w2n w+off` by
    (simp[w2n_add_2, w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  simp[Abbr `tn1`, Abbr `u`, copy_len_binop_ghost_frame]
QED

Resume empty_zero_pair_certificate[sequence]:
  `ptr_inst_ok D 0 0 ctx func G tn
     (mk_inst id ADD [Var p; Lit (n2w off)] [out]) s` by
    (irule ptr_inst_ok_copy_len_binop >>
     gvs[ptr_covers_def, op_taint_def]) >>
  `step_inst_base (mk_inst id ADD [Var p; Lit (n2w off)] [out]) s = OK u` by
    (simp[Abbr `u`] >> irule step_ADD >> simp[eval_operand_def]) >>
  simp[Once inst_seq_ptr_def, GSYM (markerTheory.Abbrev_def)] >>
  `!a v k. mstore a v (u with vs_inst_idx := k) =
     (mstore a v u) with vs_inst_idx := k` by simp[mstore_def] >>
  `!k. lookup_var out (u with vs_inst_idx := k) = SOME (w+n2w off)` by
    (gvs[lookup_var_def]) >>
  `ptr_inst_ok D 0 0 ctx func G1 tn1
     (mk_inst (id+1) MSTORE [Var out; Lit 0w] [])
     (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule ptr_inst_ok_mstore >> simp[op_taint_def]) >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ u _ _` mp_tac >>
  simp[inst_seq_ptr_def, step_inst_base_opcode_eqs,
       mk_inst_def, exec_write2_def, eval_operand_def]
QED

Finalise empty_zero_pair_certificate
