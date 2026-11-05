(* Ghost interface probes for the concrete storage-copy loop. *)
Theory exprSimPtrTopLevelStorageCopy
Ancestors
  exprSimPtrProps fragGasSeqAbort fragGasSeqPtr codegenRel contextCodegenRel
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

Theorem toplevel_copy_inv_content:
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s ==>
  storage_copy_inv cv ds loc a b n s0 k s
Proof
  simp[toplevel_copy_inv_def]
QED

Theorem toplevel_copy_inv_bounds:
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s ==>
  k <= n /\ n < 2**256 /\ b + 32*n < 2**256 /\ b + 32*n <= s.vs_alloca_next
Proof
  simp[toplevel_copy_inv_def]
QED

Theorem toplevel_copy_inv_destination:
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s ==>
  lookup_var dst s = SOME (n2w b) /\ ptr_covers G tn dst s (32*n)
Proof
  simp[toplevel_copy_inv_def]
QED

Theorem toplevel_copy_inv_source:
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s ==>
  eval_operand src s = SOME a /\ op_taint tn src = {}
Proof
  simp[toplevel_copy_inv_def]
QED

Theorem toplevel_copy_inv_counter:
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s ==>
  op_taint tn (Var cv) = {} /\ FLOOKUP G cv = NONE
Proof
  simp[toplevel_copy_inv_def]
QED

Theorem toplevel_copy_inv_counter_value:
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s ==>
  lookup_var cv s = SOME (n2w k)
Proof
  simp[toplevel_copy_inv_def, storage_copy_inv_def, eval_operand_def]
QED

Theorem toplevel_copy_inv_ghost_frame:
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s /\ ~MEM x ds ==>
  FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)
Proof
  simp[toplevel_copy_inv_def]
QED

Theorem toplevel_copy_inv_storage_taint:
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s ==>
  tn.t_stor = tn0.t_stor
Proof
  simp[toplevel_copy_inv_def]
QED

Theorem toplevel_copy_inv_transient_taint:
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s ==>
  tn.t_trans = tn0.t_trans
Proof
  simp[toplevel_copy_inv_def]
QED

Theorem toplevel_copy_inv_immutable_taint:
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s ==>
  tn.t_imm = tn0.t_imm
Proof
  simp[toplevel_copy_inv_def]
QED

Theorem toplevel_copy_inv_memory_taint:
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s ==>
  tn.t_mem SUBSET toplevel_copy_taint_bound loc a b tn0 k
Proof
  simp[toplevel_copy_inv_def]
QED

(* Source-address arithmetic is clean even if the source has provenance. *)
Theorem toplevel_copy_source_add_clean:
  op_taint tn src = {} /\ op_taint tn (Var cv) = {} ==>
  op_taint (step_taint (mk_inst id ADD [src; Var cv] [sv]) s t tn)
    (Var sv) = {}
Proof
  strip_tac >>
  simp[step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
       mk_inst_def, FLOOKUP_UPDATE] >>
  Cases_on `eval_operand src s` >> simp[] >>
  Cases_on `eval_operand (Var cv) s` >> gvs[op_taint_def]
QED

Theorem toplevel_copy_source_load_taint:
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_operand (Var sv) s = SOME w ==>
  op_taint (step_taint
    (mk_inst id (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv])
    s t tn) (Var vv) = key_taint (toplevel_copy_source_taint loc tn) w
Proof
  strip_tac >> gvs[toplevel_copy_source_taint_def] >>
  simp[step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
       mk_inst_def, FLOOKUP_UPDATE]
QED

Theorem toplevel_copy_source_seq_ptr:
  op_taint tn src = {} /\ op_taint tn (Var cv) = {} /\
  ~ctx_has_dalloca ctx /\
  i = mk_inst id ADD [src; Var cv] [sv] /\
  j = mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv] /\
  (loc = LocStorage \/ loc = LocTransient) /\
  step_inst_base i s = OK u /\
  G1 = step_prov PG G i u /\ tn1 = step_taint i s u tn /\
  u1 = u with vs_inst_idx := SUC s.vs_inst_idx /\
  step_inst_base j u1 = OK t /\
  Gf = step_prov PG G1 j t /\ tnf = step_taint j u1 t tn1 ==>
  inst_seq_ptr D 0 ctx fn PG G tn [i;j] s Gf tnf
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    (gvs[] >> irule ptr_inst_ok_copy_len_binop >> simp[]) >>
  `op_taint tn1 (Var sv) = {}` by
    (gvs[] >> irule toplevel_copy_source_add_clean >> simp[]) >>
  `ptr_inst_ok D 0 0 ctx fn G1 tn1 j u1` by
    (gvs[] >> irule toplevel_ptr_inst_ok_load >> simp[]) >>
  gvs[] >> simp[fragGasSeqPtrTheory.inst_seq_ptr_def]
QED

(* Register-only instructions cannot alter any memory taint component. *)
Theorem toplevel_copy_register_taint_frame:
  MEM inst.inst_opcode [ADD; MUL; ASSIGN; SLOAD; TLOAD] /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp ==>
  (step_taint inst s t tn).t_mem = tn.t_mem /\
  (step_taint inst s t tn).t_stor = tn.t_stor /\
  (step_taint inst s t tn).t_trans = tn.t_trans /\
  (step_taint inst s t tn).t_imm = tn.t_imm
Proof
  strip_tac >>
  `new_site_bytes s t = {}` by
    (simp[new_site_bytes_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  gvs[] >>
  simp[step_taint_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, range_bytes_def,
       store_taint_def, adopt_reset_def, imm_taint_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  rename1 `inst.inst_operands = h::ops` >>
  Cases_on `ops` >> simp[] >>
  rename1 `inst.inst_operands = h::h1::ops1` >>
  Cases_on `ops1` >> simp[] >>
  rename1 `inst.inst_operands = h::h1::h2::ops2` >>
  Cases_on `ops2` >> simp[]
QED

Theorem toplevel_copy_source_destination_frame:
  sv <> dst /\ vv <> dst /\ ptr_covers G tn dst s C /\
  u = update_var sv w s /\
  i = mk_inst id ADD [src; Var cv] [sv] /\
  G1 = step_prov PG G i u /\ tn1 = step_taint i s u tn /\
  u1 = u with vs_inst_idx := SUC s.vs_inst_idx /\
  j = mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv] /\
  t = update_var vv v u1 ==>
  ptr_covers (step_prov PG G1 j t) (step_taint j u1 t tn1) dst t C
Proof
  strip_tac >>
  `ptr_covers G1 tn1 dst u C` by
    (gvs[] >> irule ptr_covers_step_frame >>
     simp[mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `ptr_covers G1 tn1 dst u1 C` by
    gvs[ptr_covers_def, lookup_var_def] >>
  irule ptr_covers_step_frame >>
  gvs[mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem toplevel_copy_source_taint_frame:
  (loc = LocStorage \/ loc = LocTransient) /\
  i = mk_inst id ADD [src; Var cv] [sv] /\
  u = update_var sv w s /\ tn1 = step_taint i s u tn /\
  u1 = u with vs_inst_idx := SUC s.vs_inst_idx /\
  j = mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv] /\
  t = update_var vv v u1 /\ tnf = step_taint j u1 t tn1 ==>
  tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
  tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm
Proof
  strip_tac >>
  `(step_taint i s u tn).t_mem = tn.t_mem /\
   (step_taint i s u tn).t_stor = tn.t_stor /\
   (step_taint i s u tn).t_trans = tn.t_trans /\
   (step_taint i s u tn).t_imm = tn.t_imm` by
    (irule toplevel_copy_register_taint_frame >>
     gvs[mk_inst_def, update_var_def]) >>
  `tnf.t_mem = tn1.t_mem /\ tnf.t_stor = tn1.t_stor /\
   tnf.t_trans = tn1.t_trans /\ tnf.t_imm = tn1.t_imm` by
    (qpat_x_assum `tnf = _` SUBST1_TAC >>
     irule toplevel_copy_register_taint_frame >>
     gvs[mk_inst_def, update_var_def]) >>
  gvs[]
QED

Theorem toplevel_copy_ptr_inst_ok_mul:
  op_taint tn (Var cv) = {} /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id MUL [Var cv; Lit 32w] [mv]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, op_taint_def] >>
  conj_tac >- (gen_tac >> Cases_on `op = Var cv` >>
    gvs[op_taint_def] >> Cases_on `op = Lit 32w` >> gvs[op_taint_def]) >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem toplevel_copy_destination_seq_ptr:
  op_taint tn (Var cv) = {} /\ ~ctx_has_dalloca ctx /\
  i = mk_inst id MUL [Var cv; Lit 32w] [mv] /\
  j = mk_inst (id+1) ADD [Var dst; Var mv] [dv] /\
  z = mk_inst (id+2) MSTORE [Var dv; Var vv] [] /\
  step_inst_base i s = OK u /\
  G1 = step_prov PG G i u /\ tn1 = step_taint i s u tn /\
  u1 = u with vs_inst_idx := SUC s.vs_inst_idx /\
  ptr_covers G1 tn1 dst u1 (32*n) /\
  lookup_var dst u1 = SOME w /\ k < n /\
  w2n w + 32*n < dimword (:256) /\
  step_inst_base j u1 = OK v /\ v = update_var dv (w + n2w (32*k)) u1 /\
  G2 = step_prov PG G1 j v /\ tn2 = step_taint j u1 v tn1 /\
  v1 = v with vs_inst_idx := SUC u1.vs_inst_idx /\
  step_inst_base z v1 = OK t /\
  Gf = step_prov PG G2 z t /\ tnf = step_taint z v1 t tn2 ==>
  inst_seq_ptr D 0 ctx fn PG G tn [i;j;z] s Gf tnf
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    (gvs[] >> irule toplevel_copy_ptr_inst_ok_mul >> simp[]) >>
  `op_taint tn1 (Var mv) = {}` by
    gvs[toplevel_counter_offset_ghost] >>
  `op_taint tn1 (Var dst) = {}` by gvs[ptr_covers_def] >>
  `ptr_inst_ok D 0 0 ctx fn G1 tn1 j u1` by
    (gvs[] >> irule ptr_inst_ok_copy_len_binop >> simp[]) >>
  `ptr_covers G2 tn2 dv v 32` by
    (qpat_x_assum `G2 = _` SUBST1_TAC >>
     qpat_x_assum `tn2 = _` SUBST1_TAC >>
     qpat_x_assum `j = _` SUBST1_TAC >>
     qpat_x_assum `v = _` SUBST1_TAC >>
     irule toplevel_destination_offset_covers >>
     simp[] >> qexists_tac `n` >> gvs[] >> decide_tac) >>
  `ptr_covers G2 tn2 dv v1 32` by gvs[ptr_covers_def, lookup_var_def] >>
  `ptr_inst_ok D 0 0 ctx fn G2 tn2 z v1` by
    (gvs[] >> irule toplevel_ptr_inst_ok_mstore >> simp[]) >>
  gvs[] >> simp[fragGasSeqPtrTheory.inst_seq_ptr_def]
QED

Theorem toplevel_copy_ptr_inst_ok_assign:
  op_taint tn (Var nv) = {} /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id ASSIGN [Var nv] [cv]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_read1_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem toplevel_copy_increment_seq_ptr:
  op_taint tn (Var cv) = {} /\ ~ctx_has_dalloca ctx /\
  i = mk_inst id ADD [Var cv; Lit 1w] [nv] /\
  j = mk_inst (id+1) ASSIGN [Var nv] [cv] /\
  step_inst_base i s = OK u /\
  G1 = step_prov PG G i u /\ tn1 = step_taint i s u tn /\
  u1 = u with vs_inst_idx := SUC s.vs_inst_idx /\
  step_inst_base j u1 = OK t /\
  Gf = step_prov PG G1 j t /\ tnf = step_taint j u1 t tn1 ==>
  inst_seq_ptr D 0 ctx fn PG G tn [i;j] s Gf tnf
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    (gvs[] >> irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  `op_taint tn1 (Var nv) = {}` by
    (gvs[] >> simp[step_taint_def, set_var_taint_def, out_taint_def,
      op_taint_def, mk_inst_def, FLOOKUP_UPDATE] >>
     Cases_on `eval_operand (Var cv) s` >> gvs[op_taint_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G1 tn1 j u1` by
    (gvs[] >> irule toplevel_copy_ptr_inst_ok_assign >> simp[]) >>
  gvs[] >> simp[fragGasSeqPtrTheory.inst_seq_ptr_def]
QED

Theorem toplevel_copy_source_counted_ptr:
  op_taint tn src = {} /\ op_taint tn (Var cv) = {} /\
  ~ctx_has_dalloca ctx /\
  i = mk_inst id ADD [src; Var cv] [sv] /\
  j = mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv] /\
  (loc = LocStorage \/ loc = LocTransient) /\
  step_inst_base i s = OK u /\
  G1 = step_prov PG G i u /\ tn1 = step_taint i s u tn /\
  u1 = u with vs_inst_idx := SUC s.vs_inst_idx /\
  step_inst_base j u1 = OK t /\
  Gf = step_prov PG G1 j t /\ tnf = step_taint j u1 t tn1 /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [i;j] (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq [i;j] s = OK r ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
    (OK (r with vs_inst_idx := s.vs_inst_idx + 2))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `inst_seq_ptr D 0 ctx fn PG G tn [i;j] s Gf tnf` by
    (irule toplevel_copy_source_seq_ptr >> metis_tac[]) >>
  `EVERY (\k. k.inst_opcode <> INVOKE /\ ~is_terminator k.inst_opcode)
     [i;j] /\ LENGTH (FILTER (\k. k.inst_opcode = GAS) [i;j]) = 0` by
    (gvs[mk_inst_def, is_terminator_def] >> rpt strip_tac >> gvs[]) >>
  drule_all fragGasSeqPtrTheory.run_inst_seq_gas_path_ptr >> simp[]
QED



Theorem toplevel_copy_body_safe:
  (loc = LocStorage \/ loc = LocTransient) /\ ~ctx_has_dalloca ctx /\
  ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
  EVERY (\x. MEM x ds) [cv;sv;vv;mv;dv;nv] /\
  ~MEM dst [cv;sv;vv;mv;dv;nv] /\
  (!x. src = Var x ==> ~MEM x [cv;sv;vv;mv;dv;nv]) /\
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s /\ k < n /\
  code = [mk_inst id ADD [src;Var cv] [sv];
    mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
    mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
    mk_inst (id+3) ADD [Var dst;Var mv] [dv];
    mk_inst (id+4) MSTORE [Var dv;Var vv] [];
    mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
    mk_inst (id+6) ASSIGN [Var nv] [cv]] /\
  run_inst_seq code s = OK r ==>
  ?Gf tnf. inst_seq_ptr D 0 ctx fn PG G tn code s Gf tnf
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule toplevel_copy_inv_source >> strip_tac >>
  drule toplevel_copy_inv_counter >> strip_tac >>
  drule toplevel_copy_inv_counter_value >> strip_tac >>
  qabbrev_tac `i = mk_inst id ADD [src;Var cv] [sv]` >>
  qabbrev_tac `u = update_var sv (a + n2w k) s` >>
  `step_inst_base i s = OK u` by
    (simp[Abbr `i`, Abbr `u`, step_inst_base_def, mk_inst_def,
          exec_pure2_def, eval_operands_def, eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_copy_len_binop >> simp[]) >>
  qabbrev_tac `G1 = step_prov PG G i u` >>
  qabbrev_tac `tn1 = step_taint i s u tn` >>
  `op_taint tn1 (Var sv) = {}` by
    (simp[Abbr `tn1`, Abbr `i`] >>
     irule toplevel_copy_source_add_clean >> simp[]) >>
  qabbrev_tac `j = mk_inst (id+1)
    (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv]` >>
  qabbrev_tac `u1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `v = update_var vv (copy_runtime_word loc s (a+n2w k)) u1` >>
  `step_inst_base j u1 = OK v` by
    (simp[Abbr `j`, Abbr `v`, Abbr `u1`, Abbr `u`,
      step_inst_base_def, mk_inst_def, exec_read1_def, eval_operand_def,
      lookup_var_def, update_var_def, FLOOKUP_UPDATE, copy_runtime_word_def,
      sload_def, tload_def, contract_storage_def, contract_transient_def] >>
     Cases_on `loc = LocStorage` >> simp[]) >>
  `ptr_inst_ok D 0 0 ctx fn G1 tn1 j u1` by
    (simp[Abbr `j`] >> irule toplevel_ptr_inst_ok_load >>
     Cases_on `loc = LocStorage` >> simp[]) >>
  qabbrev_tac `G2 = step_prov PG G1 j v` >>
  qabbrev_tac `tn2 = step_taint j u1 v tn1` >>
  drule toplevel_copy_inv_destination >> strip_tac >>
  `sv <> dst /\ vv <> dst` by gvs[] >>
  `ptr_covers G1 tn1 dst u (32*n)` by
    (simp[Abbr `G1`, Abbr `tn1`] >> irule ptr_covers_step_frame >>
     simp[Abbr `i`, Abbr `u`, mk_inst_def, lookup_var_def,
          update_var_def, FLOOKUP_UPDATE] >> gvs[lookup_var_def]) >>
  `ptr_covers G1 tn1 dst u1 (32*n)` by
    gvs[Abbr `u1`, ptr_covers_def, lookup_var_def] >>
  `ptr_covers G2 tn2 dst v (32*n)` by
    (simp[Abbr `G2`, Abbr `tn2`] >> irule ptr_covers_step_frame >>
     simp[Abbr `j`, Abbr `v`, mk_inst_def, lookup_var_def,
          update_var_def, FLOOKUP_UPDATE] >> gvs[lookup_var_def]) >>
  `cv <> sv /\ cv <> vv /\ cv <> mv /\ mv <> dst` by gvs[] >>
  `op_taint tn2 (Var cv) = {}` by
    (simp[Abbr `tn2`, Abbr `tn1`, Abbr `i`, Abbr `j`,
          step_taint_other_output, mk_inst_def]) >>
  qabbrev_tac `v1 = v with vs_inst_idx := SUC u1.vs_inst_idx` >>
  qabbrev_tac `l = mk_inst (id+2) MUL [Var cv;Lit 32w] [mv]` >>
  qabbrev_tac `w = update_var mv (n2w (32*k)) v1` >>
  `eval_operand (Var cv) v1 = SOME (n2w k)` by
    (simp[Abbr `v1`, Abbr `v`, Abbr `u1`, Abbr `u`, eval_operand_def,
      lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> gvs[lookup_var_def]) >>
  `step_inst_base l v1 = OK w` by
    (simp[Abbr `l`, Abbr `w`, step_inst_base_def, mk_inst_def,
      exec_pure2_def, eval_operands_def] >>
     simp[NoAsms, eval_operand_def, word_mul_n2w]) >>
  `ptr_inst_ok D 0 0 ctx fn G2 tn2 l v1` by
    (simp[Abbr `l`] >> irule toplevel_copy_ptr_inst_ok_mul >> simp[]) >>
  qabbrev_tac `G3 = step_prov PG G2 l w` >>
  qabbrev_tac `tn3 = step_taint l v1 w tn2` >>
  `ptr_covers G2 tn2 dst v1 (32*n)` by
    gvs[Abbr `v1`, ptr_covers_def, lookup_var_def] >>
  `ptr_covers G3 tn3 dst w (32*n)` by
    (simp[Abbr `G3`, Abbr `tn3`] >> irule ptr_covers_step_frame >>
     simp[Abbr `l`, Abbr `w`, mk_inst_def, lookup_var_def,
          update_var_def, FLOOKUP_UPDATE]) >>
  `op_taint tn3 (Var mv) = {}` by
    simp[Abbr `tn3`, Abbr `l`, toplevel_counter_offset_ghost] >>
  qabbrev_tac `w1 = w with vs_inst_idx := SUC v1.vs_inst_idx` >>
  qabbrev_tac `p = mk_inst (id+3) ADD [Var dst;Var mv] [dv]` >>
  qabbrev_tac `x = update_var dv (n2w b + n2w (32*k)) w1` >>
  `lookup_var dst w1 = SOME (n2w b)` by
    (simp[Abbr `w1`, Abbr `w`, Abbr `v1`, Abbr `v`, Abbr `u1`, Abbr `u`,
      lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> gvs[lookup_var_def]) >>
  `eval_operand (Var dst) w1 = SOME (n2w b)` by simp[eval_operand_def] >>
  `eval_operand (Var mv) w1 = SOME (n2w (32*k))` by
    simp[Abbr `w1`, Abbr `w`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base p w1 = OK x` by
    simp[Abbr `p`, Abbr `x`, step_inst_base_def, mk_inst_def,
      exec_pure2_def, eval_operands_def] >>
  `ptr_covers G3 tn3 dst w1 (32*n)` by
    gvs[Abbr `w1`, ptr_covers_def, lookup_var_def] >>
  `ptr_inst_ok D 0 0 ctx fn G3 tn3 p w1` by
    (simp[Abbr `p`] >> irule ptr_inst_ok_copy_len_binop >>
     gvs[ptr_covers_def]) >>
  qabbrev_tac `G4 = step_prov PG G3 p x` >>
  qabbrev_tac `tn4 = step_taint p w1 x tn3` >>
  `ptr_covers G4 tn4 dv x 32` by
    (simp[Abbr `G4`, Abbr `tn4`, Abbr `p`, Abbr `x`] >>
     irule toplevel_destination_offset_covers >>
     drule toplevel_copy_inv_bounds >> strip_tac >> simp[] >>
     qexists_tac `n` >> simp[] >>
     `b < dimword (:256)` by gvs[dimword_def] >>
     gvs[dimword_def]) >>
  `dv <> vv /\ dv <> cv /\ vv <> mv` by gvs[] >>
  qabbrev_tac `x1 = x with vs_inst_idx := SUC w1.vs_inst_idx` >>
  qabbrev_tac `q = mk_inst (id+4) MSTORE [Var dv;Var vv] []` >>
  qabbrev_tac `y = mstore (w2n ((n2w b:256 word) + n2w (32*k)))
    (copy_runtime_word loc s (a+n2w k)) x1` >>
  `eval_operand (Var dv) x1 = SOME (n2w b+n2w (32*k))` by
    simp[Abbr `x1`, Abbr `x`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  `eval_operand (Var vv) x1 = SOME (copy_runtime_word loc s (a+n2w k))` by
    simp[Abbr `x1`, Abbr `x`, Abbr `w1`, Abbr `w`, Abbr `v1`, Abbr `v`,
         eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base q x1 = OK y` by
    (simp[Abbr `q`, Abbr `y`, step_inst_base_def, mk_inst_def,
         eval_operands_def, exec_write2_def] >> REFL_TAC) >>
  `ptr_covers G4 tn4 dv x1 32` by
    gvs[Abbr `x1`, ptr_covers_def, lookup_var_def] >>
  `ptr_inst_ok D 0 0 ctx fn G4 tn4 q x1` by
    (simp[Abbr `q`] >> irule toplevel_ptr_inst_ok_mstore >> simp[]) >>
  qabbrev_tac `G5 = step_prov PG G4 q y` >>
  qabbrev_tac `tn5 = step_taint q x1 y tn4` >>
  `op_taint tn5 (Var cv) = {}` by
    simp[Abbr `tn5`, Abbr `tn4`, Abbr `tn3`, Abbr `q`, Abbr `p`, Abbr `l`,
         step_taint_other_output, mk_inst_def] >>
  qabbrev_tac `y1 = y with vs_inst_idx := SUC x1.vs_inst_idx` >>
  qabbrev_tac `h = mk_inst (id+5) ADD [Var cv;Lit 1w] [nv]` >>
  qabbrev_tac `z = update_var nv (n2w k + 1w) y1` >>
  `eval_operand (Var cv) y1 = SOME (n2w k)` by
    (simp[Abbr `y1`, Abbr `y`, mstore_def, Abbr `x1`, Abbr `x`,
      Abbr `w1`, Abbr `w`, Abbr `v1`, Abbr `v`, Abbr `u1`, Abbr `u`,
      eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     gvs[lookup_var_def]) >>
  `step_inst_base h y1 = OK z` by
    (simp[Abbr `h`, Abbr `z`, step_inst_base_def, mk_inst_def,
          exec_pure2_def, eval_operands_def] >> simp[NoAsms, eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G5 tn5 h y1` by
    (simp[Abbr `h`] >> irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  qabbrev_tac `G6 = step_prov PG G5 h z` >>
  qabbrev_tac `tn6 = step_taint h y1 z tn5` >>
  `op_taint tn6 (Var nv) = {}` by
    (simp[Abbr `tn6`, Abbr `h`] >>
     simp[toplevel_counter_increment_ghost, step_taint_def, out_taint_def,
          set_var_taint_def, mk_inst_def, op_taint_def, FLOOKUP_UPDATE,
          eval_operand_def]) >>
  qabbrev_tac `z1 = z with vs_inst_idx := SUC y1.vs_inst_idx` >>
  qabbrev_tac `f = mk_inst (id+6) ASSIGN [Var nv] [cv]` >>
  qabbrev_tac `t = update_var cv (n2w k + 1w) z1` >>
  `step_inst_base f z1 = OK t` by
    simp[Abbr `f`, Abbr `t`, Abbr `z1`, Abbr `z`, step_inst_base_def,
         mk_inst_def, exec_read1_def, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE] >>
  `ptr_inst_ok D 0 0 ctx fn G6 tn6 f z1` by
    (simp[Abbr `f`] >> irule toplevel_copy_ptr_inst_ok_assign >> simp[]) >>
  qabbrev_tac `G7 = step_prov PG G6 f t` >>
  qabbrev_tac `tn7 = step_taint f z1 t tn6` >>
  qexistsl_tac [`G7`, `tn7`] >>
  qpat_x_assum `code = _` SUBST1_TAC >>
      fs[Abbr `G7`, Abbr `tn7`, Abbr `G6`, Abbr `tn6`,
           Abbr `G5`, Abbr `tn5`, Abbr `G4`, Abbr `tn4`,
           Abbr `G3`, Abbr `tn3`, Abbr `G2`, Abbr `tn2`, Abbr `G1`, Abbr `tn1`,
           Abbr `z1`, Abbr `y1`, Abbr `x1`, Abbr `w1`, Abbr `v1`, Abbr `u1`,
           fragGasSeqPtrTheory.inst_seq_ptr_def]
QED

(* C1.4.3.2: restore toplevel_copy_body_ptr with the exact body_safe
   premises and conclusion
     ?Gf tnf. inst_seq_ptr D 0 ctx fn PG G tn code s Gf tnf /\
       toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 (k+1) Gf tnf r
   after the whole-body ghost and ordinary observation boundaries. *)

Theorem toplevel_copy_body_ordinary:
  (loc = LocStorage \/ loc = LocTransient) /\ ~ctx_has_dalloca ctx /\
  ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
  EVERY (\x. MEM x ds) [cv;sv;vv;mv;dv;nv] /\
  ~MEM dst [cv;sv;vv;mv;dv;nv] /\
  (!x. src = Var x ==> ~MEM x [cv;sv;vv;mv;dv;nv]) /\
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s /\ k < n /\
  code = [mk_inst id ADD [src;Var cv] [sv];
    mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
    mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
    mk_inst (id+3) ADD [Var dst;Var mv] [dv];
    mk_inst (id+4) MSTORE [Var dv;Var vv] [];
    mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
    mk_inst (id+6) ASSIGN [Var nv] [cv]] /\
  run_inst_seq code s = OK r ==>
  storage_copy_inv cv ds loc a b n s0 (k+1) r /\
  eval_operand src r = SOME a /\ lookup_var dst r = SOME (n2w b) /\
  b + 32*n <= r.vs_alloca_next
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule toplevel_copy_inv_source >> strip_tac >>
  drule toplevel_copy_inv_counter_value >> strip_tac >>
  drule toplevel_copy_inv_destination >> strip_tac >>
  `eval_operand (Var cv) s = SOME (n2w k) /\
   eval_operand (Var dst) s = SOME (n2w b)` by simp[eval_operand_def] >>
  `!x. src = Var x \/ Var dst = Var x ==>
       ~MEM x [cv;sv;vv;mv;dv;nv]` by metis_tac[operand_11] >>
  `?t. run_inst_seq code s = OK t /\
       eval_operand (Var cv) t = SOME (n2w k + 1w) /\
       eval_operand src t = SOME a /\ eval_operand (Var dst) t = SOME (n2w b) /\
       (!x. ~MEM x [cv;sv;vv;mv;dv;nv] ==> lookup_var x t = lookup_var x s) /\
       t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx /\
       t.vs_halted = s.vs_halted /\ t.vs_labels = s.vs_labels` by
    (qpat_assum `code = _` (fn th => rewrite_tac[th]) >>
     irule storage_copy_body_run >>
     Cases_on `loc = LocStorage` >> simp[] >>
     rpt strip_tac >> gvs[] >> metis_tac[MEM]) >>
  `t = r` by metis_tac[exec_result_11] >>
  qpat_x_assum `t = r` SUBST_ALL_TAC >>
  qpat_x_assum `code = _` SUBST_ALL_TAC >>
  drule_at (Pat `run_inst_seq _ _ = _`) storage_copy_body_run_effect >>
  disch_then (qspecl_then [`n2w k`, `n2w b`, `a`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  drule toplevel_copy_inv_bounds >> strip_tac >>
  drule toplevel_copy_inv_content >> strip_tac >>
  `copy_prefix loc a b n s0 k s` by gvs[storage_copy_inv_def] >>
  drule_all storage_copy_body_prefix >> strip_tac >>
  `r.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `copy_static r = copy_static s` mp_tac >>
     simp[copy_static_def, venom_state_component_equality]) >>
  simp[storage_copy_inv_def, eval_operand_def, GSYM word_add_n2w] >>
  conj_tac
  >- (gvs[storage_copy_inv_def, storage_copy_frame_def, EVERY_MEM] >>
      metis_tac[]) >>
  gvs[storage_copy_inv_def, venomMemPropsTheory.LENGTH_mstore_eq] >>
  decide_tac
QED

Theorem toplevel_copy_body_content:
  (loc = LocStorage \/ loc = LocTransient) /\ ~ctx_has_dalloca ctx /\
  ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
  EVERY (\x. MEM x ds) [cv;sv;vv;mv;dv;nv] /\
  ~MEM dst [cv;sv;vv;mv;dv;nv] /\
  (!x. src = Var x ==> ~MEM x [cv;sv;vv;mv;dv;nv]) /\
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s /\ k < n /\
  code = [mk_inst id ADD [src;Var cv] [sv];
    mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
    mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
    mk_inst (id+3) ADD [Var dst;Var mv] [dv];
    mk_inst (id+4) MSTORE [Var dv;Var vv] [];
    mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
    mk_inst (id+6) ASSIGN [Var nv] [cv]] /\
  run_inst_seq code s = OK r ==>
  storage_copy_inv cv ds loc a b n s0 (k+1) r
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all toplevel_copy_body_ordinary >> simp[]
QED

Theorem toplevel_copy_body_source:
  (loc = LocStorage \/ loc = LocTransient) /\ ~ctx_has_dalloca ctx /\
  ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
  EVERY (\x. MEM x ds) [cv;sv;vv;mv;dv;nv] /\
  ~MEM dst [cv;sv;vv;mv;dv;nv] /\
  (!x. src = Var x ==> ~MEM x [cv;sv;vv;mv;dv;nv]) /\
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s /\ k < n /\
  code = [mk_inst id ADD [src;Var cv] [sv];
    mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
    mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
    mk_inst (id+3) ADD [Var dst;Var mv] [dv];
    mk_inst (id+4) MSTORE [Var dv;Var vv] [];
    mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
    mk_inst (id+6) ASSIGN [Var nv] [cv]] /\
  run_inst_seq code s = OK r ==>
  eval_operand src r = SOME a
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all toplevel_copy_body_ordinary >> simp[]
QED

Theorem toplevel_copy_body_destination:
  (loc = LocStorage \/ loc = LocTransient) /\ ~ctx_has_dalloca ctx /\
  ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
  EVERY (\x. MEM x ds) [cv;sv;vv;mv;dv;nv] /\
  ~MEM dst [cv;sv;vv;mv;dv;nv] /\
  (!x. src = Var x ==> ~MEM x [cv;sv;vv;mv;dv;nv]) /\
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s /\ k < n /\
  code = [mk_inst id ADD [src;Var cv] [sv];
    mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
    mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
    mk_inst (id+3) ADD [Var dst;Var mv] [dv];
    mk_inst (id+4) MSTORE [Var dv;Var vv] [];
    mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
    mk_inst (id+6) ASSIGN [Var nv] [cv]] /\
  run_inst_seq code s = OK r ==>
  lookup_var dst r = SOME (n2w b)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all toplevel_copy_body_ordinary >> simp[]
QED

Theorem toplevel_copy_body_allocation_bound:
  (loc = LocStorage \/ loc = LocTransient) /\ ~ctx_has_dalloca ctx /\
  ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
  EVERY (\x. MEM x ds) [cv;sv;vv;mv;dv;nv] /\
  ~MEM dst [cv;sv;vv;mv;dv;nv] /\
  (!x. src = Var x ==> ~MEM x [cv;sv;vv;mv;dv;nv]) /\
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s /\ k < n /\
  code = [mk_inst id ADD [src;Var cv] [sv];
    mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
    mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
    mk_inst (id+3) ADD [Var dst;Var mv] [dv];
    mk_inst (id+4) MSTORE [Var dv;Var vv] [];
    mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
    mk_inst (id+6) ASSIGN [Var nv] [cv]] /\
  run_inst_seq code s = OK r ==>
  b + 32*n <= r.vs_alloca_next
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all toplevel_copy_body_ordinary >> simp[]
QED

Theorem toplevel_copy_backedge_path:
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label hdr] []) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK (jump_to hdr s)) /\
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn (jump_to hdr s)
Proof
  strip_tac >> irule toplevel_copy_jump_inv_path >>
  simp[] >>
  simp[step_inst_base_def, mk_inst_def, ptr_inst_ok_def, access_ok_def,
       taint_ok_def, allocas_from_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke, step_inst_base_def,
       mk_inst_def, jump_to_def, op_taint_def]
QED

Theorem toplevel_copy_test_inv:
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s /\
  cv <> tv /\ dst <> tv /\ (!x. src = Var x ==> x <> tv) /\ MEM tv ds ==>
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k
    (step_prov PG G (mk_inst id EQ [Var cv; Lit (n2w n)] [tv])
      (update_var tv (bool_to_word (k=n)) s))
    (step_taint (mk_inst id EQ [Var cv; Lit (n2w n)] [tv]) s
      (update_var tv (bool_to_word (k=n)) s) tn)
    (update_var tv (bool_to_word (k=n)) s)
Proof
  strip_tac >>
  `!x. ~MEM x ds ==> x <> tv /\ tv <> x` by metis_tac[] >>
  gvs[toplevel_copy_inv_def, storage_copy_inv_def, storage_copy_frame_def,
       copy_prefix_def, copy_static_def, ptr_covers_def,
       eval_operand_def, lookup_var_def, update_var_def,
       step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
       step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, first_prov_def, op_prov_def,
       adopt_reset_def, store_taint_def, imm_taint_def,
       mem_taint_def, new_site_bytes_def, written_taint_def, step_writes_def,
       range_bytes_def] >>
  Cases_on `src` >>
  gvs[eval_operand_def, op_taint_def, lookup_var_def, FLOOKUP_UPDATE,
      source_memory_write_ranges_def] >>
  `{i | ?aid b' sz. aid NOTIN FDOM s.vs_allocas /\
      FLOOKUP s.vs_allocas aid = SOME (b',sz) /\ b' <= i /\ i < b'+sz} = {}` by
    (simp[EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  gvs[] >> metis_tac[]
QED

Theorem toplevel_copy_header_path:
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  cv <> tv /\ dst <> tv /\ (!x. src = Var x ==> x <> tv) /\ MEM tv ds /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id EQ [Var cv;Lit (n2w n)] [tv];
    mk_inst (id+1) JNZ [Var tv;Label exit_lbl;Label body_lbl] []]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?r G1 tn1. gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK r) /\
    toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G1 tn1 r /\
    ~r.vs_halted /\ r.vs_current_bb = (if k=n then exit_lbl else body_lbl) /\
    r.vs_inst_idx = 0
Proof
  strip_tac >>
  drule toplevel_copy_inv_bounds >> strip_tac >>
  drule toplevel_copy_inv_counter_value >> strip_tac >>
  drule toplevel_copy_inv_counter >> strip_tac >>
  `((n2w k):256 word = n2w n) <=> k=n` by
    (`k < 2**256` by decide_tac >>
     pure_rewrite_tac[n2w_11, dimword_def] >>
     gvs[arithmeticTheory.LESS_MOD]) >>
  `step_inst_base (mk_inst id EQ [Var cv;Lit (n2w n)] [tv]) s =
     OK (update_var tv (bool_to_word (k=n)) s)` by
    simp[step_inst_base_def, exec_pure2_def, mk_inst_def,
         eval_operands_def, eval_operand_def] >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id EQ [Var cv;Lit (n2w n)] [tv]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
          mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def] >>
     rpt strip_tac >> Cases_on `op` >> gvs[op_taint_def]) >>
  drule instruction_prefix_cursor >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  qabbrev_tac `u = update_var tv (bool_to_word (k=n)) s` >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst id EQ [Var cv;Lit (n2w n)] [tv]) u` >>
  qabbrev_tac `tn1 = step_taint (mk_inst id EQ [Var cv;Lit (n2w n)] [tv]) s u tn` >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G1 tn1 t` by
    (simp[Abbr `t`, Abbr `G1`, Abbr `tn1`, Abbr `u`] >>
     irule toplevel_copy_test_inv >> simp[] >> metis_tac[]) >>
  `op_taint tn1 (Var tv) = {}` by
    simp[Abbr `tn1`, step_taint_def, set_var_taint_def, out_taint_def,
         mk_inst_def, op_taint_def, FLOOKUP_UPDATE, eval_operand_def] >>
  `~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = SUC s.vs_inst_idx /\
    lookup_var tv t = SOME (bool_to_word (k=n))` by
    simp[Abbr `t`, Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst (id+1) JNZ [Var tv;Label exit_lbl;Label body_lbl] []) t =
    OK (jump_to (if k=n then exit_lbl else body_lbl) t)` by
    (Cases_on `k=n` >>
     simp[step_inst_base_def, mk_inst_def, eval_operand_def, bool_to_word_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G1 tn1
    (mk_inst (id+1) JNZ [Var tv;Label exit_lbl;Label body_lbl] []) t` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
          mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, jump_to_def] >>
     rpt strip_tac >> Cases_on `op` >> gvs[op_taint_def]) >>
  `gas_path_ptr D 0 ctx fn PG G1 tn1 t 0 G1 tn1
    (OK (jump_to (if k=n then exit_lbl else body_lbl) t))` by
    (irule toplevel_copy_raw_jump_path >> conj_tac >- simp[] >>
     qexistsl [`bb`, `mk_inst (id+1) JNZ [Var tv;Label exit_lbl;Label body_lbl] []`] >>
     simp[mk_inst_def] >> simp[GSYM mk_inst_def]) >>
  qexistsl [`jump_to (if k=n then exit_lbl else body_lbl) t`, `G1`, `tn1`] >>
  conj_tac
  >- (irule (gas_path_ptr_step |> Q.INST
        [`i` |-> `mk_inst id EQ [Var cv;Lit (n2w n)] [tv]`, `n` |-> `0`]
        |> SRULE [mk_inst_def, is_terminator_def]) >>
      simp[GSYM mk_inst_def] >>
      qexistsl [`cv`, `id`, `n`, `tv`, `u`] >>
      simp[] >> gvs[Abbr `G1`, Abbr `tn1`, Abbr `t`]) >>
  simp[jump_to_def]

QED

Theorem toplevel_copy_seq_register_frame:
  !code G tn s Gf tnf.
    EVERY (\i. ~MEM x i.inst_outputs) code /\
    inst_seq_ptr D 0 ctx fn PG G tn code s Gf tnf ==>
    FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)
Proof
  Induct_on `code` >> simp[inst_seq_ptr_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  first_x_assum drule >>
  simp[step_prov_other_output, step_taint_other_output]
QED

Theorem toplevel_copy_body_register_frame:
  code = [mk_inst id ADD [src;Var cv] [sv];
    mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
    mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
    mk_inst (id+3) ADD [Var dst;Var mv] [dv];
    mk_inst (id+4) MSTORE [Var dv;Var vv] [];
    mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
    mk_inst (id+6) ASSIGN [Var nv] [cv]] /\
  inst_seq_ptr D 0 ctx fn PG G tn code s Gf tnf ==>
  !x. ~MEM x [cv;sv;vv;mv;dv;nv] ==>
    FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)
Proof
  strip_tac >> gen_tac >> disch_tac >>
  `EVERY (\i. ~MEM x i.inst_outputs) code` by gvs[mk_inst_def] >>
  drule_all toplevel_copy_seq_register_frame >> simp[]
QED

Theorem toplevel_copy_body_source_clean:
  code = [mk_inst id ADD [src;Var cv] [sv];
    mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
    mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
    mk_inst (id+3) ADD [Var dst;Var mv] [dv];
    mk_inst (id+4) MSTORE [Var dv;Var vv] [];
    mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
    mk_inst (id+6) ASSIGN [Var nv] [cv]] /\
  (!x. src = Var x ==> ~MEM x [cv;sv;vv;mv;dv;nv]) /\
  op_taint tn src = {} /\
  inst_seq_ptr D 0 ctx fn PG G tn code s Gf tnf ==>
  op_taint tnf src = {}
Proof
  strip_tac >> drule toplevel_copy_body_register_frame >>
  disch_then drule >> strip_tac >>
  Cases_on `src` >> gvs[op_taint_def] >> metis_tac[]
QED

Theorem toplevel_copy_body_destination_covers:
  (loc = LocStorage \/ loc = LocTransient) /\ ~ctx_has_dalloca ctx /\
  ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
  EVERY (\x. MEM x ds) [cv;sv;vv;mv;dv;nv] /\
  ~MEM dst [cv;sv;vv;mv;dv;nv] /\
  (!x. src = Var x ==> ~MEM x [cv;sv;vv;mv;dv;nv]) /\
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s /\ k < n /\
  code = [mk_inst id ADD [src;Var cv] [sv];
    mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
    mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
    mk_inst (id+3) ADD [Var dst;Var mv] [dv];
    mk_inst (id+4) MSTORE [Var dv;Var vv] [];
    mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
    mk_inst (id+6) ASSIGN [Var nv] [cv]] /\
  run_inst_seq code s = OK r /\
  inst_seq_ptr D 0 ctx fn PG G tn code s Gf tnf ==>
  ptr_covers Gf tnf dst r (32*n)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all toplevel_copy_body_destination >> strip_tac >>
  drule toplevel_copy_inv_destination >> strip_tac >>
  drule_all toplevel_copy_body_register_frame >> strip_tac >>
  gvs[ptr_covers_def]
QED

Theorem toplevel_copy_seq_storage_frame:
  !code G tn s Gf tnf.
    EVERY (\i. MEM i.inst_opcode [ADD;MUL;ASSIGN;SLOAD;TLOAD;MSTORE]) code /\
    inst_seq_ptr D 0 ctx fn PG G tn code s Gf tnf ==>
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm
Proof
  Induct_on `code` >> simp[inst_seq_ptr_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  first_x_assum drule >>
  simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def] >>
  gvs[]
QED

Theorem toplevel_copy_body_storage_frame:
  (loc = LocStorage \/ loc = LocTransient) /\
  code = [mk_inst id ADD [src;Var cv] [sv];
    mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
    mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
    mk_inst (id+3) ADD [Var dst;Var mv] [dv];
    mk_inst (id+4) MSTORE [Var dv;Var vv] [];
    mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
    mk_inst (id+6) ASSIGN [Var nv] [cv]] /\
  inst_seq_ptr D 0 ctx fn PG G tn code s Gf tnf ==>
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm
Proof
  strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [ADD;MUL;ASSIGN;SLOAD;TLOAD;MSTORE]) code` by
    gvs[mk_inst_def] >>
  drule_all toplevel_copy_seq_storage_frame >> simp[]
QED

Theorem toplevel_copy_counter_suffix_ghost:
  FLOOKUP G cv = NONE /\ op_taint tn (Var cv) = {} /\ cv <> nv /\
  run_inst_seq [mk_inst id ADD [Var cv;Lit 1w] [nv];
    mk_inst (id+1) ASSIGN [Var nv] [cv]] s = OK r /\
  inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id ADD [Var cv;Lit 1w] [nv];
     mk_inst (id+1) ASSIGN [Var nv] [cv]] s Gf tnf ==>
  FLOOKUP Gf cv = NONE /\ op_taint tnf (Var cv) = {}
Proof
  strip_tac >>
  Cases_on `lookup_var cv s`
  >- gvs[exprLoweringPropsTheory.run_inst_seq_def, step_inst_base_def,
         exec_pure2_def, mk_inst_def, eval_operands_def, eval_operand_def] >>
  rename1 `lookup_var cv s = SOME w` >>
  qabbrev_tac `i = mk_inst id ADD [Var cv;Lit 1w] [nv]` >>
  qabbrev_tac `j = mk_inst (id+1) ASSIGN [Var nv] [cv]` >>
  qabbrev_tac `u = update_var nv (w+1w) s` >>
  `step_inst_base i s = OK u` by
    simp[Abbr `i`, Abbr `u`, step_inst_base_def, exec_pure2_def,
         mk_inst_def, eval_operands_def, eval_operand_def] >>
  qabbrev_tac `u1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `step_inst_base j u1 = OK (update_var cv (w+1w) u1)` by
    simp[Abbr `j`, Abbr `u1`, Abbr `u`, step_inst_base_def, exec_read1_def,
         mk_inst_def, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[inst_seq_ptr_def] >> strip_tac >>
  gvs[] >> simp[Abbr `i`, Abbr `j`] >>
  irule toplevel_counter_assign_ghost >>
  drule_all toplevel_counter_increment_ghost >> simp[]
QED

Theorem toplevel_copy_seq_split:
  !pre s t G tn Gf tnf.
    EVERY (\i. ~is_terminator i.inst_opcode) pre /\
    run_inst_seq pre s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (pre ++ post) s Gf tnf ==>
    ?Gm tnm. inst_seq_ptr D 0 ctx fn PG G tn pre s Gm tnm /\
      inst_seq_ptr D 0 ctx fn PG Gm tnm post
        (t with vs_inst_idx := s.vs_inst_idx + LENGTH pre) Gf tnf
Proof
  Induct_on `pre`
  >- (simp[exprLoweringPropsTheory.run_inst_seq_def, inst_seq_ptr_def] >>
      rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[exprLoweringPropsTheory.run_inst_seq_def, inst_seq_ptr_def] >>
  rename1 `step_inst_base h s = OK u` >>
  `run_inst_seq pre (u with vs_inst_idx := SUC s.vs_inst_idx) =
    OK (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[fragExecTheory.run_inst_seq_inst_idx, instIdxIndepTheory.exec_result_map_def] >>
  first_x_assum (qspecl_then
    [`u with vs_inst_idx := SUC s.vs_inst_idx`,
     `t with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  simp[] >> disch_then drule >>
  strip_tac >> qexistsl [`Gm`, `tnm`] >>
  `LENGTH pre + SUC s.vs_inst_idx = SUC (LENGTH pre + s.vs_inst_idx)` by decide_tac >>
  simp[inst_seq_ptr_def, arithmeticTheory.ADD_CLAUSES] >> metis_tac[]
QED

Theorem toplevel_copy_run_split:
  run_inst_seq (pre ++ post) s = OK r ==>
  ?t. run_inst_seq pre s = OK t /\ run_inst_seq post t = OK r
Proof
  strip_tac >>
  Cases_on `?t. run_inst_seq pre s = OK t`
  >- (gvs[] >> drule exprLoweringPropsTheory.run_inst_seq_append >>
      disch_then (qspec_then `post` assume_tac) >> metis_tac[]) >>
  `!t. run_inst_seq pre s <> OK t` by metis_tac[] >>
  drule exprLoweringPropsTheory.run_inst_seq_append_err >>
  disch_then (qspec_then `post` assume_tac) >> metis_tac[]
QED

Theorem toplevel_copy_body_counter_ghost:
  ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
  FLOOKUP G cv = NONE /\ op_taint tn (Var cv) = {} /\
  code = [mk_inst id ADD [src;Var cv] [sv];
    mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
    mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
    mk_inst (id+3) ADD [Var dst;Var mv] [dv];
    mk_inst (id+4) MSTORE [Var dv;Var vv] [];
    mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
    mk_inst (id+6) ASSIGN [Var nv] [cv]] /\
  run_inst_seq code s = OK r /\
  inst_seq_ptr D 0 ctx fn PG G tn code s Gf tnf ==>
  FLOOKUP Gf cv = NONE /\ op_taint tnf (Var cv) = {}
Proof
  strip_tac >>
  qabbrev_tac `pre = TAKE 5 code` >>
  qabbrev_tac `post = DROP 5 code` >>
  `code = pre ++ post` by simp[Abbr `pre`, Abbr `post`] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) pre /\
   EVERY (\i. ~MEM cv i.inst_outputs) pre` by
    (Cases_on `loc = LocStorage` >>
     gvs[Abbr `pre`, mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  `?t. run_inst_seq pre s = OK t /\ run_inst_seq post t = OK r` by
    (irule toplevel_copy_run_split >> metis_tac[]) >>
  `?Gm tnm. inst_seq_ptr D 0 ctx fn PG G tn pre s Gm tnm /\
    inst_seq_ptr D 0 ctx fn PG Gm tnm post
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH pre) Gf tnf` by
    (irule toplevel_copy_seq_split >> metis_tac[]) >>
  `FLOOKUP Gm cv = NONE /\ op_taint tnm (Var cv) = {}` by
    (drule_all toplevel_copy_seq_register_frame >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) post` by
    gvs[Abbr `post`, mk_inst_def, is_terminator_def] >>
  `run_inst_seq post (t with vs_inst_idx := s.vs_inst_idx + LENGTH pre) =
    OK (r with vs_inst_idx := s.vs_inst_idx + LENGTH pre)` by
    simp[fragExecTheory.run_inst_seq_inst_idx, instIdxIndepTheory.exec_result_map_def] >>
  `post = [mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
    mk_inst ((id+5)+1) ASSIGN [Var nv] [cv]]` by
    gvs[Abbr `post`] >>
  `cv <> nv` by gvs[] >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ post _ _ _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  qpat_x_assum `run_inst_seq post (_ with vs_inst_idx := _) = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all toplevel_copy_counter_suffix_ghost >> simp[]
QED
