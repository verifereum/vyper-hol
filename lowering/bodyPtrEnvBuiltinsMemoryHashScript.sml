(* Memory-input hashing boundaries; offsets retain the allocation even for
   an empty payload. No padding cleanliness is required. *)
Theory bodyPtrEnvBuiltinsMemoryHash
Ancestors bodyPtrEnvBuiltinsHashStep bodyPtrEnvBuiltinsLen typedCopyPtr
  bodyPtrEnvBuiltinsEdges bodyPtrDefs ptrDiscipline venomInst venomState
  words finite_map pred_set decoderGhostFramePtr

Theorem hash_payload_add_covers:
  FLOOKUP G root = SOME (b,sz) /\ lookup_var root s = SOME a /\
  op_taint tn (Var root) = {} /\
  b <= w2n a + 32 /\ w2n a + 32 + n <= b + sz /\
  w2n a + 32 < dimword(:256) ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var root; Lit 32w] [out])
      (update_var out (a + 32w) s))
    (step_taint (mk_inst id ADD [Var root; Lit 32w] [out]) s
      (update_var out (a + 32w) s) tn)
    out (update_var out (a + 32w) s) n
Proof
  strip_tac >>
  `op_taint (step_taint (mk_inst id ADD [Var root; Lit 32w] [out]) s
     (update_var out (a + 32w) s) tn) (Var out) = {}` by
    (irule scalar_builtin_output_clean >> simp[] >>
     rpt strip_tac >> gvs[] >> simp[op_taint_def]) >>
  simp[ptr_covers_def, step_prov_def, set_prov_def, out_prov_def,
       first_prov_def, op_prov_def, mk_inst_def, FLOOKUP_UPDATE,
       lookup_var_def, update_var_def, wordsTheory.w2n_add_2] >>
  metis_tac[]
QED

Theorem hash_covered_payload_ok:
  ptr_covers G tn p s (w2n n) /\
  eval_operand (Var p) s = SOME a /\ eval_operand len s = SOME n /\
  op_taint tn len = {} /\
  (!i. w2n a <= i /\ i < w2n a + w2n n ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id SHA3 [Var p; len] [out]) s
Proof
  strip_tac >> irule ptr_inst_ok_hash >>
  gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]
QED

Theorem hash_after_payload_add_ok:
  FLOOKUP G root = SOME (b,sz) /\ lookup_var root s = SOME a /\
  op_taint tn (Var root) = {} /\
  b <= w2n a + 32 /\ w2n a + 32 + w2n n <= b + sz /\
  w2n a + 32 < dimword(:256) /\
  lookup_var len s = SOME n /\ op_taint tn (Var len) = {} /\ len <> dst /\
  (!i. w2n a + 32 <= i /\ i < w2n a + 32 + w2n n ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn
    (step_prov PG G (mk_inst aid ADD [Var root; Lit 32w] [dst])
      (update_var dst (a + 32w) s))
    (step_taint (mk_inst aid ADD [Var root; Lit 32w] [dst]) s
      (update_var dst (a + 32w) s) tn)
    (mk_inst hid SHA3 [Var dst; Var len] [out])
    (update_var dst (a + 32w) s)
Proof
  strip_tac >> irule hash_covered_payload_ok >>
  simp[copy_len_binop_ghost_frame] >>
  qexistsl_tac [`a + 32w`, `n`] >>
  simp[copy_len_binop_ghost_frame, wordsTheory.w2n_add_2] >>
  conj_tac >- (simp[eval_operand_def, lookup_var_def, update_var_def,
                    FLOOKUP_UPDATE] >> gvs[lookup_var_def]) >>
  conj_tac >- simp[eval_operand_def, lookup_var_def, update_var_def,
                   FLOOKUP_UPDATE] >>
  irule hash_payload_add_covers >> metis_tac[]
QED

Theorem hash_header_load_frame:
  root <> len /\ lookup_var root s = SOME a /\
  FLOOKUP G root = SOME (b,sz) /\ op_taint tn (Var root) = {} /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  lookup_var root (update_var len (mload (w2n a) s) s) = SOME a /\
  FLOOKUP (step_prov PG G (mk_inst id MLOAD [Var root] [len])
    (update_var len (mload (w2n a) s) s)) root = SOME (b,sz) /\
  op_taint (step_taint (mk_inst id MLOAD [Var root] [len]) s
    (update_var len (mload (w2n a) s) s) tn) (Var root) = {} /\
  op_taint (step_taint (mk_inst id MLOAD [Var root] [len]) s
    (update_var len (mload (w2n a) s) s) tn) (Var len) = {} /\
  (step_taint (mk_inst id MLOAD [Var root] [len]) s
    (update_var len (mload (w2n a) s) s) tn).t_mem = tn.t_mem
Proof
  strip_tac >>
  `eval_operand (Var root) s = SOME a` by simp[eval_operand_def] >>
  drule_all mload_ghost_clean >> strip_tac >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
       FLOOKUP_DRESTRICT] >>
  simp[step_taint_other_output, mk_inst_def] >> gvs[lookup_var_def]
QED

Theorem memory_hash_instruction_checks:
  ptr_covers G tn root s 32 /\ lookup_var root s = SOME a /\
  FLOOKUP G root = SOME (b,sz) /\
  b <= w2n a + 32 /\ w2n a + 32 + w2n n <= b + sz /\
  w2n a + 32 < dimword(:256) /\ mload (w2n a) s = n /\
  root <> len /\ len <> dst /\ ~ctx_has_dalloca ctx /\
  (!i. w2n a <= i /\ i < w2n a + 32 + w2n n ==> i NOTIN tn.t_mem) /\
  u = update_var len n s /\
  G1 = step_prov PG G (mk_inst lid MLOAD [Var root] [len]) u /\
  tn1 = step_taint (mk_inst lid MLOAD [Var root] [len]) s u tn /\
  v = update_var dst (a + 32w) u /\
  G2 = step_prov PG G1 (mk_inst aid ADD [Var root; Lit 32w] [dst]) v /\
  tn2 = step_taint (mk_inst aid ADD [Var root; Lit 32w] [dst]) u v tn1 ==>
  ptr_inst_ok D 0 0 ctx fn G tn (mk_inst lid MLOAD [Var root] [len]) s /\
  ptr_inst_ok D 0 0 ctx fn G1 tn1 (mk_inst aid ADD [Var root; Lit 32w] [dst]) u /\
  ptr_inst_ok D 0 0 ctx fn G2 tn2 (mk_inst hid SHA3 [Var dst; Var len] [out]) v
Proof
  strip_tac >>
  `op_taint tn (Var root) = {}` by gvs[ptr_covers_def] >>
  `(!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem)` by
    (rpt gen_tac >> disch_tac >>
     qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` irule >> decide_tac) >>
  drule_all hash_header_load_frame >> strip_tac >>
  `lookup_var root u = SOME a /\ FLOOKUP G1 root = SOME (b,sz) /\
   op_taint tn1 (Var root) = {} /\ op_taint tn1 (Var len) = {} /\
   tn1.t_mem = tn.t_mem` by gvs[] >>
  conj_tac >- (irule ptr_inst_ok_mload >> simp[]) >>
  conj_tac
  >- (irule ptr_inst_ok_scalar_builtin >> simp[] >>
      rpt strip_tac >> gvs[] >> simp[op_taint_def]) >>
  gvs[] >> irule hash_after_payload_add_ok >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  qexistsl_tac [`b`, `sz`] >> simp[] >>
  rpt strip_tac >> qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` irule >> decide_tac
QED
