Theory abiDecodePtrBytesFramed
Ancestors
  abiDecodePtrBytesSuccess abiDecodePtrBytesRuntimeFrame abiDecodePtrBytesMember
  abiDecodePtrBytesHeader abiDecoderBytes
  abiDecodePtrMemberFrame bodyPtrHashBuiltinsGhostFrame exprSimBufferStore
  abiDecodeStaticProps assignTuplePtrLocalBytesCopy exprPtrUnwrapPostFrames
  abiEncoder emitHelperProps exprLoweringProps compileEnv context bodyPtrDefs
  ptrDiscipline contractABI vyperTypeABI
  venomExecSemantics venomState venomInst words arithmetic list finite_map pred_set

(* A successful bytes member preserves live source locals outside its capacity.
   Execution existence remains an explicit premise. *)
Theorem abi_decode_bytes_success_framed:
  compile_abi_decode_to_buf (Var dst) pos MLOAD (Var src) hi
    (DecBytestring n) sa = ((),sb) /\ hi <> Lit 0w /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\ fresh_vars_wrt sa s /\
  abi_decode_ptr_window G tn s src b h /\
  lookup_var dst s = SOME d /\ ptr_covers G tn dst s cap /\
  eval_operand pos s = SOME (n2w p) /\ eval_operand hi s = SOME (n2w h) /\
  op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {} /\
  p < dimword(:256) /\ n+31 < dimword(:256) /\
  32+contractABI$ceil32 n <= cap /\ w2n d+cap < dimword(:256) /\
  w2n b+h < dimword(:256) /\
  (w2n b+h <= w2n d \/ w2n d+cap <= w2n b) /\
  run_inst_seq (emitted_insts sa sb) s = OK u /\
  ghost_inv ret cenv cx es G tn s /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!name a k. local_region cenv es.scopes s name a k ==>
    a+k <= w2n d \/ w2n d+cap <= a) /\
  (cenv.ce_is_ctor ==> !name tv v off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) (w2n d) cap) ==>
  ?H tf. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H tf /\
    ghost_inv ret cenv cx es H tf u /\ stmt_state_rel ctx func cenv cx es u /\
    mload (w2n d) u = mload (w2n b+p) s /\
    fresh_vars_wrt sb u /\
    abi_decode_ptr_window H tf u src b h /\
    abi_decode_ptr_window H tf u dst d
      (32+contractABI$ceil32 (w2n (mload (w2n b+p) s))) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!i. ~(w2n d <= i /\ i < w2n d+cap) ==>
      mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decode_bytes_member_success_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H tf` >>
  drule_all abi_decode_bytes_runtime_frame >> strip_tac >>
  suspend "capacity"
QED

Resume abi_decode_bytes_success_framed[capacity]:
  `eval_operand (Var src) s = SOME b` by
    fs[abi_decode_ptr_window_def, eval_operand_def] >>
  `h < dimword(:256) /\ n < dimword(:256)` by decide_tac >>
  drule_all abi_decode_bytes_member_success_bounds >> strip_tac >>
  `w2n b+p < dimword(:256)` by decide_tac >>
  `w2n (mload (w2n b+p) s) <= n` by
    (qpat_x_assum `w2n (mload (w2n (b+n2w p)) s) <= n` mp_tac >>
     `b+n2w p = n2w (w2n b+p)` by simp[GSYM word_add_n2w] >>
     simp[]) >>
  `32+contractABI$ceil32 (w2n (mload (w2n b+p) s)) <= cap` by
    (drule ceil32_mono >> decide_tac) >>
  `!i. ~(w2n d <= i /\ i < w2n d+cap) ==>
      mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tf.t_mem <=> i IN tn.t_mem)` by
    (gen_tac >> disch_tac >>
     `~(w2n d <= i /\ i < w2n d+32+contractABI$ceil32
       (w2n (mload (w2n b+p) s)))` by decide_tac >>
     qpat_x_assum `!i. ~(w2n d <= i /\ i < w2n d+32+_) ==> _`
       (qspec_then `i` mp_tac) >> disch_then irule >> decide_tac) >>
  `mload (w2n d) u = mload (w2n b+p) s` by
    (irule abi_decode_bytes_success_header >> (conj_tac >- simp[]) >>
     goal_assum (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
     simp[] >> qexists_tac `h` >>
     simp[abi_decode_bytes_copy_size_def, GSYM contractABITheory.ceil32_def,
          eval_operand_def] >> decide_tac) >>
  suspend "ghost"
QED

Resume abi_decode_bytes_success_framed[ghost]:
  `u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
   u.vs_call_ctx = s.vs_call_ctx` by
    (qpat_x_assum `(u with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[venom_state_component_equality]) >>
  `stor_taint_ok cx tf u` by
    (irule copy_stor_taint_frame >> qexistsl [`s`, `tn`] >>
     fs[ghost_inv_def]) >>
  `ghost_inv ret cenv cx es H tf u` by
    (irule hash_ghost_inv_exterior_frame >> (conj_tac >- simp[]) >>
     goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
     qexistsl [`ctx`, `func`, `sa`, `{i | w2n d <= i /\ i < w2n d+cap}`] >>
     simp[] >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `!name a k. local_region _ _ _ name a k ==> _` drule >> decide_tac) >>
  suspend "state"
QED

Resume abi_decode_bytes_success_framed[state]:
  `!a k. a+k <= w2n d \/ w2n d+cap <= a ==>
    mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory` by
    (rpt gen_tac >> disch_tac >> irule mem_bytes_at_bytewise >>
     rpt gen_tac >> strip_tac >>
     `~(w2n d <= i /\ i < w2n d+cap)` by decide_tac >>
     qpat_x_assum `!i. ~(w2n d <= i /\ i < w2n d+cap) ==> _`
       (qspec_then `i` mp_tac) >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es u` by
    (irule buffer_store_state_frame >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ s`)) >>
     qexistsl [`w2n d`, `cap`, `sa`] >> simp[] >> metis_tac[ADD_COMM]) >>
  qexistsl [`H`, `tf`] >> simp[]
QED

Finalise abi_decode_bytes_success_framed
