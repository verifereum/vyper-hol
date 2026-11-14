(* The generated SHA256 call's complete ghost frame at an arbitrary bound. *)
Theory bodyFullHashShaTail
Ancestors
  bodyFullHashShaFrame bodyFullHashKeccakBytes bodyPtrHashBuiltinsShaTailFrame bodyPtrHashBuiltinsShaTail
  bodyPtrDefs exprSimHash valueCopy valueEncoding venomExecSemantics
  venomState ptrDiscipline finite_map pred_set words

Theorem sha_ghost_inv_at_outcomes[local]:
  ghost_inv_at D lo d cenv cx (es with outcomes := os) G tn s <=>
  ghost_inv_at D lo d cenv cx es G tn s
Proof
  simp[ghost_inv_at_def]
QED

Theorem sha_tail_success_frame_at:
  !D lo d cenv cx es G tn s ctx fn sa t i0 i1 i2 i3 gv p len q sv out w n r bs outcome rest Gf tf.
    eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
    eval_operand (Var q) s = SOME r /\
    p <> gv /\ q <> gv /\ (!x. len = Var x ==> x <> gv) /\ q <> sv /\
    mem_bytes_at (w2n w) (w2n n) s.vs_memory = bs /\
    s.vs_outcomes = outcome::rest /\ outcome.co_success /\
    run_inst_seq [mk_inst i0 GAS [] [gv];
      mk_inst i1 STATICCALL [Var gv;Lit 2w;Var p;len;Var q;Lit 32w] [sv];
      mk_inst i2 ASSERT [Var sv] []; mk_inst i3 MLOAD [Var q] [out]] s = OK t /\
    ghost_inv_at D lo d cenv cx es G tn s /\
    stmt_state_rel H ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x. not_fresh_at sa x ==> x <> gv /\ x <> sv /\ x <> out) /\
    (!name b k. local_region cenv es.scopes s name b k ==>
      b+k <= w2n r \/ w2n r+32 <= b) /\ lo <= w2n r /\
    Gf = DRESTRICT G (COMPL {gv;sv;out}) /\
    tf = tn with <|t_var := tn.t_var |+ (gv,{}) |+ (sv,{}) |+ (out,{});
      t_mem := tn.t_mem DIFF range_bytes [(w2n r,32)]|> ==>
    ghost_inv_at D lo d cenv cx (es with outcomes := SOME rest) Gf tf
      (t with vs_inst_idx := s.vs_inst_idx+4) /\
    ghost_kept_at lo cenv es sa G tn s Gf tf /\ op_taint tf (Var out) = {} /\
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
  `ghost_inv_at D lo d cenv cx es Gf tf t /\
   ghost_kept_at lo cenv es sa G tn s Gf tf` by suspend "frame" >>
  simp[bytes_ghost_cursor, sha_ghost_inv_at_outcomes] >>
  gvs[op_taint_def, FLOOKUP_UPDATE, op_prov_def, FLOOKUP_DRESTRICT]
QED

Resume sha_tail_success_frame_at[frame]:
  gvs[] >>
  irule sha_shrinking_ghost_frame_at >> simp[] >>
  conj_tac >- suspend "vars" >>
  conj_tac >- suspend "memory" >>
  suspend "tail"
QED

Resume sha_tail_success_frame_at[vars]:
  rpt strip_tac >>
  `x <> gv /\ x <> sv /\ x <> out` by metis_tac[] >>
  gvs[lookup_var_def, update_var_def, write_memory_with_expansion_def,
    FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def]
QED

Resume sha_tail_success_frame_at[memory]:
  qexists_tac `range_bytes [(w2n r,32)]` >> simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[range_bytes_def] >>
      first_x_assum drule >> decide_tac) >>
  rpt strip_tac >> gvs[update_var_def] >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion (w2n r) bytes ss` >>
  `mem_bytes_at i 1 (write_memory_with_expansion (w2n r) bytes ss).vs_memory =
   mem_bytes_at i 1 ss.vs_memory` by
    (irule mem_bytes_at_write_disjoint >>
     gvs[Abbr `bytes`, range_bytes_def] >> decide_tac) >>
  gvs[Abbr `ss`]
QED

Resume sha_tail_success_frame_at[tail]:
  `mem_bytes_at 0 lo
    (write_memory_with_expansion (w2n r)
      (word_to_bytes (SHA_256_bytes (mem_bytes_at (w2n w) (w2n n) s.vs_memory)) T)
      (update_var gv (HD (s.vs_gas_readings ++ [0w])) s)).vs_memory =
    mem_bytes_at 0 lo (update_var gv (HD (s.vs_gas_readings ++ [0w])) s).vs_memory` by
    (irule mem_bytes_at_write_disjoint >> simp[]) >>
  gvs[ghost_inv_at_def, stor_taint_ok_at_def, update_var_def,
    write_memory_with_expansion_def] >>
  qexistsl_tac [`H`, `ctx`, `fn`] >> simp[]
QED

Finalise sha_tail_success_frame_at
