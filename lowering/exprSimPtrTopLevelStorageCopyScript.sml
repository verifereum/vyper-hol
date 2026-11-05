(* Ghost interface probes for the concrete storage-copy loop. *)
Theory exprSimPtrTopLevelStorageCopy
Ancestors
  exprSimPtrProps fragGasSeqAbort codegenRel contextCodegenRel
  exprSimStorageCopy exprSimPtrTopLevelCopy typedCopyPtr decoderGhostFramePtr bodyPtrDefs
  fragGasPathPtr ptrDiscipline ptrSafeRun gasCount venomExecSemantics venomState venomInst
  words finite_map pred_set list

Theorem toplevel_counter_increment_ghost:
  FLOOKUP G cv = NONE /\ op_taint tn (Var cv) = {} ==>
  FLOOKUP (step_prov PG G (mk_inst id ADD [Var cv; Lit 1w] [nv]) t) nv = NONE /\
  op_taint (step_taint (mk_inst id ADD [Var cv; Lit 1w] [nv]) s t tn)
    (Var nv) = {}
Proof
  strip_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_DRESTRICT,
       step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
       FLOOKUP_UPDATE] >>
  Cases_on `eval_operand (Var cv) s` >> simp[]
QED

Theorem toplevel_counter_assign_ghost:
  FLOOKUP G nv = NONE /\ op_taint tn (Var nv) = {} ==>
  FLOOKUP (step_prov PG G (mk_inst id ASSIGN [Var nv] [cv]) t) cv = NONE /\
  op_taint (step_taint (mk_inst id ASSIGN [Var nv] [cv]) s t tn)
    (Var cv) = {}
Proof
  strip_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_DRESTRICT,
       step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
       FLOOKUP_UPDATE] >>
  Cases_on `eval_operand (Var nv) s` >> gvs[op_taint_def]
QED

Theorem toplevel_counter_offset_ghost:
  FLOOKUP (step_prov PG G (mk_inst id MUL [Var cv; Lit 32w] [mv]) t) mv = NONE /\
  op_taint (step_taint (mk_inst id MUL [Var cv; Lit 32w] [mv]) s t tn)
    (Var mv) = {}
Proof
  simp[step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
       FLOOKUP_DRESTRICT, step_taint_def, set_var_taint_def,
       out_taint_def, op_taint_def, FLOOKUP_UPDATE] >>
  Cases_on `eval_operand (Var cv) s` >> simp[]
QED

Theorem toplevel_entry_non_phi_ghost:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = i::rest /\ i.inst_opcode <> PHI ==>
  entry_prov fn s G = G /\ entry_taint_vars fn s tn = tn
Proof
  simp[entry_prov_def, entry_taint_vars_def, phis_prov_def, phis_taint_def]
QED

(* Both arithmetic inputs have their actual pre-step values here. *)
Theorem toplevel_destination_offset_covers:
  ptr_covers G tn dst s (32*n) /\ lookup_var dst s = SOME w /\
  k < n /\ w2n w + 32*n < dimword (:256) ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var dst; Var mv] [dv])
      (update_var dv (w + n2w (32*k)) s))
    (step_taint (mk_inst id ADD [Var dst; Var mv] [dv]) s
      (update_var dv (w + n2w (32*k)) s) tn)
    dv (update_var dv (w + n2w (32*k)) s) 32
Proof
  strip_tac >> gvs[ptr_covers_def] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_UPDATE,
       lookup_var_def, update_var_def] >>
  conj_tac
  >- (simp[step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
           mk_inst_def, FLOOKUP_UPDATE] >>
      Cases_on `eval_operand (Var dst) s` >> simp[]) >>
  `w2n (w + n2w (32*k)) = w2n w + 32*k` by
    (`w2n w + 32*k < dimword (:256)` by decide_tac >>
     Cases_on `w` >> gvs[wordsTheory.word_add_n2w] >> decide_tac) >>
  simp[] >> decide_tac
QED

(* The counted fragment relation also has a raw-jump edge: no entry
   transformation is needed when stopping at a block's index-zero frontier. *)
Theorem toplevel_copy_raw_jump_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  MEM inst.inst_opcode [JMP;JNZ] /\
  ptr_inst_ok D 0 0 ctx fn G tn inst s /\
  step_inst_base inst s = OK (jump_to lbl s) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK (jump_to lbl s))
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  `step_inst 0 ctx inst s = OK (jump_to lbl s)` by
    (simp[step_inst_non_invoke] >> gvs[]) >>
  `ptr_safe_step D 0 0 ctx fn PG G tn inst s` by
    (simp[ptr_safe_step_def] >> gvs[]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G tn (OK (jump_to lbl s))` by
    (pure_rewrite_tac[gas_path_ptr_edge_def] >> conj_tac >- simp[] >>
     qexists_tac `0` >>
     simp[] >> gvs[gas_count_step_def, is_terminator_def] >> metis_tac[]) >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

(* Proof-only shared interface; no clean-padding assumption. *)
Definition toplevel_copy_region_def:
  toplevel_copy_region b k = {q | b <= q /\ q < b + 32*k}
End

Definition toplevel_copy_source_taint_def:
  toplevel_copy_source_taint loc tn =
    if loc = LocStorage then tn.t_stor else tn.t_trans
End

Definition toplevel_copy_translated_taint_def:
  toplevel_copy_translated_taint loc a b tn k =
    {q | ?i j. i < k /\ j < 32 /\
       (a + n2w i,j) IN toplevel_copy_source_taint loc tn /\
       q = b + 32*i + j}
End

Definition toplevel_copy_taint_bound_def:
  toplevel_copy_taint_bound loc a b tn k =
    (tn.t_mem DIFF toplevel_copy_region b k) UNION
    toplevel_copy_translated_taint loc a b tn k
End

Definition toplevel_copy_inv_def:
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s <=>
    storage_copy_inv cv ds loc a b n s0 k s /\
    k <= n /\ n < 2**256 /\ b + 32*n < 2**256 /\
    b + 32*n <= s.vs_alloca_next /\
    lookup_var dst s = SOME (n2w b) /\ ptr_covers G tn dst s (32*n) /\
    eval_operand src s = SOME a /\ op_taint tn src = {} /\
    op_taint tn (Var cv) = {} /\ FLOOKUP G cv = NONE /\
    (!x. ~MEM x ds ==> FLOOKUP G x = FLOOKUP G0 x /\
          op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    tn.t_stor = tn0.t_stor /\ tn.t_trans = tn0.t_trans /\
    tn.t_imm = tn0.t_imm /\
    tn.t_mem SUBSET toplevel_copy_taint_bound loc a b tn0 k
End

Theorem toplevel_copy_inv_jump[simp]:
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn (jump_to lbl s) <=>
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s
Proof
  simp[toplevel_copy_inv_def, storage_copy_inv_def, copy_prefix_def, copy_static_def,
       storage_copy_frame_def, ptr_covers_def, jump_to_def,
       eval_operand_def, lookup_var_def]
QED

Theorem toplevel_copy_inv_idx[simp]:
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn
    (s with vs_inst_idx := idx) <=>
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s
Proof
  simp[toplevel_copy_inv_def, storage_copy_inv_def, copy_prefix_def, copy_static_def,
       storage_copy_frame_def, ptr_covers_def, eval_operand_def, lookup_var_def]
QED

Theorem toplevel_copy_jump_inv_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  MEM inst.inst_opcode [JMP;JNZ] /\
  ptr_inst_ok D 0 0 ctx fn G tn inst s /\
  step_inst_base inst s = OK (jump_to lbl s) /\
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK (jump_to lbl s)) /\
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn (jump_to lbl s)
Proof
  strip_tac >> conj_tac
  >- (irule toplevel_copy_raw_jump_path >> gvs[]) >>
  simp[]
QED

Theorem toplevel_copy_init_inv:
  MEM cv ds /\ dst <> cv /\ (!x. src = Var x ==> x <> cv) /\
  n < 2**256 /\ b + 32*n < 2**256 /\ b + 32*n <= s.vs_alloca_next /\
  lookup_var dst s = SOME (n2w b) /\ ptr_covers G tn dst s (32*n) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} ==>
  toplevel_copy_inv cv ds dst src loc a b n s G tn 0
    (step_prov PG G (mk_inst id ASSIGN [Lit 0w] [cv]) (update_var cv 0w s))
    (step_taint (mk_inst id ASSIGN [Lit 0w] [cv]) s (update_var cv 0w s) tn)
    (update_var cv 0w s)
Proof
  strip_tac >>
  `!x. ~MEM x ds ==> x <> cv /\ cv <> x` by metis_tac[] >>
  simp[toplevel_copy_inv_def, storage_copy_inv_def, storage_copy_frame_def,
       copy_prefix_def, copy_static_def, ptr_covers_def,
       eval_operand_def, lookup_var_def, update_var_def,
       step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
       step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
       toplevel_copy_taint_bound_def, toplevel_copy_region_def,
       toplevel_copy_translated_taint_def, first_prov_def, op_prov_def,
       adopt_reset_def, store_taint_def, imm_taint_def,
       mem_taint_def, new_site_bytes_def, written_taint_def, step_writes_def,
       range_bytes_def] >>
  gvs[ptr_covers_def, lookup_var_def] >>
  Cases_on `src` >>
  gvs[eval_operand_def, op_taint_def, lookup_var_def, FLOOKUP_UPDATE] >>
  simp[FLOOKUP_DEF, EMPTY_DEF] >> SET_TAC[]
QED

Theorem toplevel_copy_init_path:
  MEM cv ds /\ dst <> cv /\ (!x. src = Var x ==> x <> cv) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  n < 2**256 /\ b + 32*n < 2**256 /\ b + 32*n <= s.vs_alloca_next /\
  lookup_var dst s = SOME (n2w b) /\ ptr_covers G tn dst s (32*n) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ASSIGN [Lit 0w] [cv]]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G1 tn1. gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK t) /\
    toplevel_copy_inv cv ds dst src loc a b n s G tn 0 G1 tn1 t /\
    ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx + 1
Proof
  strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSIGN [Lit 0w] [cv])` by
    metis_tac[instruction_prefix_cursor] >>
  `step_inst_base (mk_inst id ASSIGN [Lit 0w] [cv]) s = OK (update_var cv 0w s)` by
    simp[step_inst_base_def, mk_inst_def, eval_operands_def, eval_operand_def] >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ASSIGN [Lit 0w] [cv]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
          mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def]) >>
  qexistsl [`(update_var cv 0w s) with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_prov PG G (mk_inst id ASSIGN [Lit 0w] [cv]) (update_var cv 0w s)`,
    `step_taint (mk_inst id ASSIGN [Lit 0w] [cv]) s (update_var cv 0w s) tn`] >>
  conj_tac
  >- (irule gas_path_ptr_one_step >>
      simp[mk_inst_def, is_terminator_def, update_var_def] >> metis_tac[]) >>
  simp[update_var_def] >>
  pure_rewrite_tac[GSYM update_var_def] >>
  irule toplevel_copy_init_inv >> simp[] >> metis_tac[]
QED

Definition toplevel_copy_word_region_def:
  toplevel_copy_word_region b k = {q | b + 32*k <= q /\ q < b + 32*(k+1)}
End

Definition toplevel_copy_word_taint_def:
  toplevel_copy_word_taint loc a b tn k =
    {q | ?j. j < 32 /\ (a + n2w k,j) IN toplevel_copy_source_taint loc tn /\
             q = b + 32*k + j}
End

Theorem toplevel_copy_taint_bound_zero[simp]:
  toplevel_copy_taint_bound loc a b tn 0 = tn.t_mem
Proof
  simp[toplevel_copy_taint_bound_def, toplevel_copy_region_def,
       toplevel_copy_translated_taint_def]
QED

Theorem toplevel_copy_region_step:
  toplevel_copy_region b (k+1) =
    toplevel_copy_region b k UNION toplevel_copy_word_region b k
Proof
  simp[EXTENSION, toplevel_copy_region_def, toplevel_copy_word_region_def] >>
  decide_tac
QED

Theorem toplevel_copy_translated_step:
  toplevel_copy_translated_taint loc a b tn (k+1) =
    toplevel_copy_translated_taint loc a b tn k UNION
    toplevel_copy_word_taint loc a b tn k
Proof
  simp[EXTENSION, toplevel_copy_translated_taint_def, toplevel_copy_word_taint_def] >>
  gen_tac >> eq_tac
  >- (strip_tac >> Cases_on `i = k`
      >- (gvs[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
      disj1_tac >> qexistsl [`i`,`j`] >> simp[] >> decide_tac) >>
  strip_tac
  >- (qexistsl [`i`,`j`] >> simp[] >> decide_tac) >>
  qexistsl [`k`,`j`] >> simp[arithmeticTheory.ADD_COMM]
QED

Theorem toplevel_copy_taint_bound_step:
  M SUBSET toplevel_copy_taint_bound loc a b tn k ==>
  (M DIFF toplevel_copy_word_region b k) UNION
    toplevel_copy_word_taint loc a b tn k SUBSET
    toplevel_copy_taint_bound loc a b tn (k+1)
Proof
  simp[toplevel_copy_taint_bound_def, toplevel_copy_region_step,
       toplevel_copy_translated_step] >> SET_TAC[]
QED

Theorem toplevel_copy_store_taint_bound:
  tn.t_mem SUBSET toplevel_copy_taint_bound loc a b tn0 k /\
  tnf.t_mem = (tn.t_mem DIFF toplevel_copy_word_region b k) UNION
    toplevel_copy_word_taint loc a b tn0 k ==>
  tnf.t_mem SUBSET toplevel_copy_taint_bound loc a b tn0 (k+1)
Proof
  metis_tac[toplevel_copy_taint_bound_step]
QED

Theorem toplevel_copy_mstore_taint:
  eval_operand p s = SOME off /\ new_site_bytes s t = {} /\
  range_bytes (step_writes (mk_inst id MSTORE [p;v] []) s t) =
    toplevel_copy_word_region b k /\ w2n off = b + 32*k ==>
  (step_taint (mk_inst id MSTORE [p;v] []) s t tn).t_mem =
    (tn.t_mem DIFF toplevel_copy_word_region b k) UNION
    {b + 32*k + j | j IN op_taint tn v}
Proof
  simp[step_taint_def, mem_taint_def, written_taint_def, mk_inst_def] >>
  strip_tac >> AP_TERM_TAC >>
  simp[EXTENSION] >> metis_tac[arithmeticTheory.ADD_COMM]
QED
