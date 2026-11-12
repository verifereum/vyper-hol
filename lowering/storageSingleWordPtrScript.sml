(* Actual one-slot normalization: arbitrary-taint load followed by MSTORE. *)
Theory storageSingleWordPtr
Ancestors
  storageCopyBodyRaisePtr storageNormalizationFramePtr appendStorageGhostPtr
  exprSimStorageCopy fragGasPathPtr bodyPtrDefs compileEnv fragExec
  exprLoweringProps
  ptrDiscipline ptrSafeRun venomState finite_map pred_set words arithmetic
  immutableMemoryFrame

Theorem storage_single_word_path_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ value <> root /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst lid (if tr then TLOAD else SLOAD) [src] [value]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst sid MSTORE [Var root;Var value] []) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  lookup_var root s = SOME (n2w b) /\ ptr_covers G tn root s 32 /\
  b+32 < dimword(:256) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    G' = DRESTRICT G (COMPL {value}) /\
    t = (mstore b (if tr then tload a s else sload a s)
      (update_var value (if tr then tload a s else sload a s) s
        with vs_inst_idx := SUC s.vs_inst_idx)
      with vs_inst_idx := SUC (SUC s.vs_inst_idx)) /\
    tn' = ((tn with t_var := tn.t_var |+
      (value,key_taint (if tr then tn.t_trans else tn.t_stor) a)) with
      t_mem := (tn.t_mem DIFF {x | b <= x /\ x < b+32}) UNION
        {b+r | r < 32 /\ (a,r) IN (if tr then tn.t_trans else tn.t_stor)})
Proof
  strip_tac >>
  drule_all storage_copy_load_path_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] assume_tac) >>
  qabbrev_tac `u = update_var value (if tr then tload a s else sload a s) s
    with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {value})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+
    (value,key_taint (if tr then tn.t_trans else tn.t_stor) a)` >>
  `ptr_covers G1 tn1 root u 32` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `u`, ptr_covers_def,
      update_var_def, lookup_var_def, op_taint_def, FLOOKUP_UPDATE,
      DOMSUB_FLOOKUP_THM, FLOOKUP_DRESTRICT] >>
     gvs[ptr_covers_def, op_taint_def, lookup_var_def]) >>
  `lookup_var root u = SOME (n2w b) /\
   eval_operand (Var value) u = SOME (if tr then tload a s else sload a s) /\
   ~u.vs_halted /\
   lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb u.vs_inst_idx = SOME (mk_inst sid MSTORE [Var root;Var value] [])` by
    (simp[Abbr `u`, update_var_def, lookup_var_def, eval_operand_def,
         FLOOKUP_UPDATE] >> fs[lookup_var_def]) >>
  drule_all storage_copy_mstore_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  `w2n (n2w b : 256 word) = b` by simp[] >>
  `op_taint tn1 (Var value) = key_taint
      (if tr then tn.t_trans else tn.t_stor) a` by
    simp[Abbr `tn1`, op_taint_def, FLOOKUP_UPDATE] >>
  `step_taint (mk_inst sid MSTORE [Var root;Var value] []) u
      (mstore b (if tr then tload a s else sload a s) u) tn1 =
    tn1 with t_mem := (tn.t_mem DIFF {x | b <= x /\ x < b+32}) UNION
      {b+r | r < 32 /\ (a,r) IN (if tr then tn.t_trans else tn.t_stor)}` by
    (`eval_operand (Var root) u = SOME (n2w b)` by simp[eval_operand_def] >>
     drule_all (Q.INST [`dst` |-> `root`] storage_copy_mstore_ghost) >>
     disch_then (qspec_then `sid` mp_tac) >> simp[Abbr `tn1`]) >>
  qexistsl_tac [`G1`,
    `step_taint (mk_inst sid MSTORE [Var root;Var value] []) u
      (mstore b (if tr then tload a s else sload a s) u) tn1`,
    `mstore b (if tr then tload a s else sload a s) u
      with vs_inst_idx := SUC u.vs_inst_idx`] >>
  simp[Abbr `tn1`] >> reverse conj_tac
  >- simp[Abbr `u`, update_var_def] >>
  irule (SRULE[] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
  qexistsl_tac [`G1`, `u`,
    `tn with t_var := tn.t_var |+ (value,key_taint
      (if tr then tn.t_trans else tn.t_stor) a)`] >> fs[]
QED

Theorem storage_single_word_copy_prefix:
  copy_prefix (if tr then LocTransient else LocStorage) a b 1 s 1
    (mstore b (if tr then tload a s else sload a s)
      (update_var value (if tr then tload a s else sload a s) s
        with vs_inst_idx := SUC s.vs_inst_idx)
      with vs_inst_idx := SUC (SUC s.vs_inst_idx))
Proof
  mp_tac (Q.INST [`k` |-> `0`, `n` |-> `1`,
    `loc` |-> `if tr then LocTransient else LocStorage`,
    `sbase` |-> `s`,
    `s` |-> `update_var value (if tr then tload a s else sload a s) s
      with vs_inst_idx := SUC s.vs_inst_idx`] copy_prefix_extend) >>
  simp[copy_runtime_word_def, copy_prefix_idx, copy_prefix_update_var,
       copy_prefix_zero, WORD_ADD_0] >> Cases_on `tr` >> simp[WORD_ADD_0]
QED

Theorem storage_single_word_resources_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ value <> root /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst lid (if tr then TLOAD else SLOAD) [src] [value]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst sid MSTORE [Var root;Var value] []) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  lookup_var root s = SOME (n2w b) /\ ptr_covers G tn root s 32 /\
  b+32 < dimword(:256) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    copy_prefix (if tr then LocTransient else LocStorage) a b 1 s 1 t /\
    ptr_covers G' tn' root t 32 /\ copy_static t = copy_static s /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    tn'.t_mem = (tn.t_mem DIFF {x | b <= x /\ x < b+32}) UNION
      {b+r | r < 32 /\ (a,r) IN (if tr then tn.t_trans else tn.t_stor)} /\
    (!x. x <> value ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = SUC (SUC s.vs_inst_idx) /\ ~t.vs_halted
Proof
  strip_tac >> drule_all storage_single_word_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    (simp[immutable_mstore_capacity, update_var_def, arithmeticTheory.MAX_DEF] >>
     IF_CASES_TAC >> decide_tac) >>
  qexistsl_tac [`G'`, `tn'`, `t`] >> asm_rewrite_tac[] >>
  gvs[] >> simp[storage_single_word_copy_prefix] >>
  simp[copy_static_def, mstore_def, write_memory_with_expansion_def,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT, op_taint_def] >>
  fs[ptr_covers_def, op_taint_def, lookup_var_def] >>
  gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem storage_single_word_compiled_fetch:
  do v <- emitHelper$emit_op (if tr then TLOAD else SLOAD) [src];
     emitHelper$emit_void MSTORE [Var root;v] od sa = (result,sb) /\
  fn_has_code sa sb fn ==>
  ?bb value.
    lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [src] [value]) /\
    get_instruction bb (SUC (LENGTH sa.cs_current_insts)) =
      SOME (mk_inst (sa.cs_next_id+1) MSTORE [Var root;Var value] []) /\
    (!x. not_fresh_at sa x ==> x <> value) /\
    sb.cs_current_bb = sa.cs_current_bb /\
    LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + 2
Proof
  strip_tac >> drule storage_copy_word_layout >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  `sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [src]
      [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id+1) MSTORE
      [Var root;Var (STRING #"%" (toString sa.cs_next_var))] []]` by
    (fs[emitted_insts_def] >> metis_tac[prefix_drop_equiv]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qexistsl_tac [`bb`, `STRING #"%" (toString sa.cs_next_var)`] >>
  simp[] >> conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  conj_tac
  >- (first_x_assum (qspec_then `1` mp_tac) >> simp[ADD1]) >>
  metis_tac[]
QED

Theorem compile_storage_single_word_path_ptr:
  do v <- emitHelper$emit_op (if tr then TLOAD else SLOAD) [src];
     emitHelper$emit_void MSTORE [Var root;v] od sa = (result,sb) /\
  fn_has_code sa sb fn /\ not_fresh_at sa root /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  lookup_var root s = SOME (n2w b) /\ ptr_covers G tn root s 32 /\
  b+32 < dimword(:256) /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    copy_prefix (if tr then LocTransient else LocStorage) a b 1 s 1 t /\
    ptr_covers G' tn' root t 32 /\ copy_static t = copy_static s /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    tn'.t_mem = (tn.t_mem DIFF {x | b <= x /\ x < b+32}) UNION
      {b+r | r < 32 /\ (a,r) IN (if tr then tn.t_trans else tn.t_stor)} /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    (!p sz. not_fresh_at sa p /\ ptr_covers G tn p s sz ==>
      ptr_covers G' tn' p t sz) /\
    (!off len. off+len <= b \/ b+32 <= off ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!x. ~(b <= x /\ x < b+32) ==> (x IN tn'.t_mem <=> x IN tn.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all storage_single_word_compiled_fetch >> strip_tac >>
  `value <> root` by metis_tac[] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [src] [value]) /\
   get_instruction bb (SUC s.vs_inst_idx) =
     SOME (mk_inst (sa.cs_next_id+1) MSTORE [Var root;Var value] [])` by simp[] >>
  drule_all storage_single_word_resources_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  qexistsl_tac [`G'`, `tn'`, `t`] >> asm_rewrite_tac[] >>
  simp[ADD1] >> conj_tac
  >- (rpt strip_tac >> irule ptr_covers_old_transport >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule storage_copy_exterior_bytes >>
      goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  rpt strip_tac >>
  qpat_x_assum `tn'.t_mem = _` SUBST1_TAC >>
  simp[] >> eq_tac >> rpt strip_tac >> gvs[] >> decide_tac
QED
