(* A shrinking memory taint set preserves both the ghost and kept bytes. *)
Theory bodyPtrHashBuiltinsShaTailFrame
Ancestors bodyPtrHashBuiltinsGhostFrame bodyPtrDefs pred_set
  bodyPtrHashBuiltinsShaTail exprSimHash valueCopy valueEncoding
  venomExecSemantics venomState ptrDiscipline finite_map words

Theorem hash_shrinking_ghost_frame:
  !d cenv cx es G tn s ctx fn sa t G' tn' writes.
    ghost_inv d cenv cx es G tn s /\
    stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!name b k i. local_region cenv es.scopes s name b k /\
      b <= i /\ i < b+k ==> i NOTIN writes) /\
    (!i. i NOTIN writes ==> mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    tn'.t_mem = tn.t_mem DIFF writes /\ stor_taint_ok cx tn' t ==>
    ghost_inv d cenv cx es G' tn' t /\ ghost_kept cenv es sa G tn s G' tn'
Proof
  rpt gen_tac >> strip_tac >>
  `!i. i NOTIN writes ==> (i IN tn'.t_mem <=> i IN tn.t_mem)` by simp[] >>
  conj_tac >-
    (drule_all hash_ghost_inv_exterior_frame >> simp[]) >>
  irule hash_ghost_kept_frame >> simp[] >> metis_tac[]
QED

Theorem hash_ghost_inv_outcomes[local]:
  !d cenv cx es G tn s os.
    ghost_inv d cenv cx (es with outcomes := os) G tn s =
    ghost_inv d cenv cx es G tn s
Proof
  simp[ghost_inv_def]
QED

Theorem hash_sha256_tail_success_frame:
  !d cenv cx es G tn s ctx fn sa t i0 i1 i2 i3 gv p len q sv out w n r bs outcome rest Gf tf.
    eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
    eval_operand (Var q) s = SOME r /\
    p <> gv /\ q <> gv /\ (!x. len = Var x ==> x <> gv) /\ q <> sv /\
    mem_bytes_at (w2n w) (w2n n) s.vs_memory = bs /\
    s.vs_outcomes = outcome::rest /\ outcome.co_success /\
    run_inst_seq [mk_inst i0 GAS [] [gv];
      mk_inst i1 STATICCALL [Var gv;Lit 2w;Var p;len;Var q;Lit 32w] [sv];
      mk_inst i2 ASSERT [Var sv] []; mk_inst i3 MLOAD [Var q] [out]] s = OK t /\
    ghost_inv d cenv cx es G tn s /\ stmt_state_rel ctx fn cenv cx es s /\
    local_ptrs_reserved cenv sa /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x. not_fresh_at sa x ==> x <> gv /\ x <> sv /\ x <> out) /\
    (!name b k. local_region cenv es.scopes s name b k ==>
      b+k <= w2n r \/ w2n r+32 <= b) /\
    Gf = DRESTRICT G (COMPL {gv;sv;out}) /\
    tf = tn with <|t_var := tn.t_var |+ (gv,{}) |+ (sv,{}) |+ (out,{});
      t_mem := tn.t_mem DIFF range_bytes [(w2n r,32)]|> ==>
    ghost_inv d cenv cx (es with outcomes := SOME rest) Gf tf
      (t with vs_inst_idx := s.vs_inst_idx+4) /\
    ghost_kept cenv es sa G tn s Gf tf /\ op_taint tf (Var out) = {} /\
    op_prov Gf (Var out) = NONE
Proof
  rpt gen_tac >> strip_tac >>
  `run_inst_seq [mk_inst i0 GAS [] [gv];
    mk_inst i1 STATICCALL [Var gv;Lit 2w;Var p;len;Var q;Lit 32w] [sv];
    mk_inst i2 ASSERT [Var sv] []; mk_inst i3 MLOAD [Var q] [out]] s =
    OK (update_var out (SHA_256_bytes bs) (update_var sv 1w
      ((write_memory_with_expansion (w2n r) (word_to_bytes (SHA_256_bytes bs) T)
        (update_var gv (HD (s.vs_gas_readings ++ [0w]))
          (s with vs_gas_readings := DROP 1 s.vs_gas_readings))) with
        <|vs_returndata := word_to_bytes (SHA_256_bytes bs) T; vs_outcomes := rest|>)))` by
    (irule sha256_tail_run >> simp[] >> metis_tac[]) >>
  `ghost_inv d cenv cx es Gf tf t /\ ghost_kept cenv es sa G tn s Gf tf` by
    suspend "frame" >>
  simp[hash_ghost_inv_inst_idx, hash_ghost_inv_outcomes] >>
  gvs[op_taint_def, FLOOKUP_UPDATE, op_prov_def, FLOOKUP_DRESTRICT]
QED

Resume hash_sha256_tail_success_frame[frame]:
  irule hash_shrinking_ghost_frame >> simp[] >>
  conj_tac >- suspend "vars" >>
  conj_tac >- (qexists `range_bytes [(w2n r,32)]` >> suspend "memory") >>
  suspend "storage"
QED

Resume hash_sha256_tail_success_frame[vars]:
  rpt strip_tac >>
  `x <> gv /\ x <> sv /\ x <> out` by metis_tac[] >>
  gvs[lookup_var_def, update_var_def, write_memory_with_expansion_def,
    FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def]
QED

Resume hash_sha256_tail_success_frame[memory]:
  simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[range_bytes_def] >>
      first_x_assum drule >> decide_tac) >>
  rpt strip_tac >>
  gvs[update_var_def] >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion (w2n r) bytes ss` >>
  `mem_bytes_at i 1 (write_memory_with_expansion (w2n r) bytes ss).vs_memory =
   mem_bytes_at i 1 ss.vs_memory` by
    (irule mem_bytes_at_write_disjoint >>
     gvs[Abbr `bytes`, range_bytes_def] >> decide_tac) >>
  gvs[Abbr `ss`]
QED

Resume hash_sha256_tail_success_frame[storage]:
  conj_tac >-
    (gvs[ghost_inv_def, stor_taint_ok_def, update_var_def,
      write_memory_with_expansion_def]) >> metis_tac[]
QED

Finalise hash_sha256_tail_success_frame
