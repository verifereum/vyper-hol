(* Checked compiled storage copy with conditional old-buffer frames. *)
Theory storageNormalizationCopyPtr
Ancestors
  storageNormalizationFramePtr storageCopyCompiledPtr appendStorageGhostPtr
  exprSimStorageCopy fragGasPathPtr bodyPtrDefs compileEnv exprLoweringProps
  ptrDiscipline ptrSafeRun venomState finite_map pred_set

Theorem compile_storage_copy_framed_path_ptr:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop src (Var root) n loc LocMemory F sa = (u,sb) /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ root = x ==> not_fresh_at sa x) /\
  eval_operand src sbase = SOME a /\ lookup_var root sbase = SOME (n2w b) /\
  op_taint tn src = {} /\ ptr_covers G tn root sbase (32*n) /\
  n < dimword(:256) /\ b+32*n < dimword(:256) /\
  ~sbase.vs_halted /\ ~ctx_has_dalloca ctx /\
  sbase.vs_current_bb = sa.cs_current_bb /\
  sbase.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn sbase 0 G' tn' (OK t) /\
    LENGTH sbase.vs_memory <= LENGTH t.vs_memory /\
    copy_prefix loc a b n sbase n t /\ ptr_covers G' tn' root t (32*n) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    tn'.t_mem = (tn.t_mem DIFF {x | b <= x /\ x < b+32*n}) UNION
      {b+32*i+r | i < n /\ r < 32 /\
        (a+n2w i,r) IN (if loc = LocStorage then tn.t_stor else tn.t_trans)} /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x sbase /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    (!p sz. not_fresh_at sa p /\ ptr_covers G tn p sbase sz ==>
      ptr_covers G' tn' p t sz) /\
    (!off len. off+len <= b \/ b+32*n <= off ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len sbase.vs_memory) /\
    (!x. ~(b <= x /\ x < b+32*n) ==>
      (x IN tn'.t_mem <=> x IN tn.t_mem))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_storage_copy_content_capacity_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`, `t`] >> asm_rewrite_tac[] >>
  conj_tac
  >- (rpt strip_tac >> irule ptr_covers_old_transport >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule storage_copy_exterior_bytes >> metis_tac[]) >>
  rpt strip_tac >> irule storage_copy_exterior_taint >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `\i r. (a+n2w i,r) IN
    (if loc = LocStorage then tn.t_stor else tn.t_trans)` >> simp[]
QED
