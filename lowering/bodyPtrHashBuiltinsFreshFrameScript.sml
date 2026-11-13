(* Fresh clean scalar outputs preserve the protected expression frame. *)
Theory bodyPtrHashBuiltinsFreshFrame
Ancestors bodyPtrHashBuiltinsGhostFrame bodyPtrHashBuiltinsAllocFrame
  bodyPtrHashBuiltinsKeccak
  bodyPtrDefs venomState finite_map pred_set ptrDiscipline

Theorem hash_fresh_output_ghost_inv:
  !d cenv cx es G tn s ctx fn sa out v.
    ghost_inv d cenv cx es G tn s /\
    stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    ~not_fresh_at sa out ==>
    ghost_inv d cenv cx es (DRESTRICT G (COMPL {out}))
      (tn with t_var := tn.t_var |+ (out,{})) (update_var out v s)
Proof
  rpt gen_tac >> strip_tac >>
  `stor_taint_ok cx tn s` by metis_tac[ghost_inv_def] >>
  irule hash_ghost_inv_exterior_frame >>
  conj_tac >- gvs[stor_taint_ok_def, update_var_def] >>
  qexistsl_tac [`G`, `ctx`, `fn`, `s`, `sa`, `tn`, `{}`] >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
    FLOOKUP_DRESTRICT, op_taint_def, stor_taint_ok_def] >>
  metis_tac[]
QED

Theorem hash_fresh_output_ghost_kept:
  !cenv es sa G tn s out.
    ~not_fresh_at sa out ==>
    ghost_kept cenv es sa G tn s (DRESTRICT G (COMPL {out}))
      (tn with t_var := tn.t_var |+ (out,{}))
Proof
  rpt gen_tac >> strip_tac >> irule hash_ghost_kept_frame >>
  simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def] >> metis_tac[]
QED

Theorem hash_fresh_output_kept_tail:
  !cenv es sa G tn s G1 tn1 out.
    ghost_kept cenv es sa G tn s G1 tn1 /\ ~not_fresh_at sa out ==>
    ghost_kept cenv es sa G tn s (DRESTRICT G1 (COMPL {out}))
      (tn1 with t_var := tn1.t_var |+ (out,{}))
Proof
  rpt gen_tac >> strip_tac >> irule hash_ghost_kept_clean_tail >>
  qexistsl_tac [`G1`, `tn1`] >>
  simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def] >> metis_tac[]
QED

Theorem hash_sha3_fresh_frame:
  !d cenv cx es G tn s ctx fn sa out v PG id src len G0 tn0 s0.
    ghost_inv d cenv cx es G tn s /\
    stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    ~not_fresh_at sa out /\ ghost_kept cenv es sa G0 tn0 s0 G tn ==>
    ghost_inv d cenv cx es
      (step_prov PG G (mk_inst id SHA3 [src;len] [out]) (update_var out v s))
      (step_taint (mk_inst id SHA3 [src;len] [out]) s (update_var out v s) tn)
      (update_var out v s) /\
    ghost_kept cenv es sa G0 tn0 s0
      (step_prov PG G (mk_inst id SHA3 [src;len] [out]) (update_var out v s))
      (step_taint (mk_inst id SHA3 [src;len] [out]) s (update_var out v s) tn) /\
    op_taint (step_taint (mk_inst id SHA3 [src;len] [out]) s
      (update_var out v s) tn) (Var out) = {} /\
    op_prov (step_prov PG G (mk_inst id SHA3 [src;len] [out])
      (update_var out v s)) (Var out) = NONE
Proof
  rpt gen_tac >> strip_tac >> simp[hash_sha3_ghost] >>
  conj_tac >- (irule hash_fresh_output_ghost_inv >> metis_tac[]) >>
  conj_tac >- (irule hash_fresh_output_kept_tail >> simp[]) >>
  simp[op_taint_def, op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED
