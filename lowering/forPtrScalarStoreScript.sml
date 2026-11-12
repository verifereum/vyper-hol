(* Scalar stores use MSTORE directly, not the word-copy MLOAD/MSTORE pair. *)
Theory forPtrScalarStore
Ancestors wordLoadStorePtr forPtrBoundary forPtrWriteScope forPtrScope forPtrBytes fragExecPtr
  typedCopyPtr valueEncodingProps
  valueEncoding valueEncodingDefs valueEncodingProofs bodyPtrDefs venomMemProofs ptrDiscipline
  venomState venomInst words list pred_set decoderGhostFramePtr

Theorem scalar_mstore_robust:
  !v off taints s mem tv.
  ((?x. v = BoolV x) \/ (?x. v = IntV x) \/
   (?x. v = FlagV x) \/ (?x. v = DecimalV x)) /\
  (!i. off <= i /\ i < off+32 ==> i NOTIN taints) /\
  mem_agree_outside taints (mstore off (val_to_w256 v) s).vs_memory mem ==>
  val_in_memory tv v off mem
Proof
  rpt gen_tac >> strip_tac >>
  `mem_bytes_at off 32 mem =
   mem_bytes_at off 32 (mstore off (val_to_w256 v) s).vs_memory` by
    (irule LIST_EQ >> simp[] >> rpt strip_tac >> rename1 `j < 32` >>
     `off+j NOTIN taints` by simp[] >>
     `mem_bytes_at (off+j) 1 (mstore off (val_to_w256 v) s).vs_memory =
      mem_bytes_at (off+j) 1 mem` by metis_tac[mem_agree_outside_def] >>
     pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]) >>
  `mem_word_at off mem =
   mem_word_at off (mstore off (val_to_w256 v) s).vs_memory` by
    asm_simp_tac bool_ss [mem_word_at_def, GSYM mem_bytes_at_def] >>
  `mem_word_at off mem = val_to_w256 v` by
    metis_tac[mstore_mem_word_at_same] >>
  gvs[val_in_memory_def]
QED

Theorem scalar_mstore_path_ptr:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst iid MSTORE [Var dst; value] []) /\
  ptr_covers G tn dst s 32 /\ op_taint tn value = {} /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w ==>
  ?tf. gas_path_ptr D 0 ctx fn PG G tn s 0 G tf
      (OK ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx)) /\
    tf.t_var = tn.t_var /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    tf.t_imm = tn.t_imm /\
    tf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32}
Proof
  strip_tac >> drule_all mstore_zero_path_ptr >>
  drule_all mstore_ghost_frame >> strip_tac >> gvs[] >>
  `(step_taint (mk_inst iid MSTORE [Var dst; value] []) s
       (mstore (w2n a) w s) tn).t_imm = tn.t_imm` by
    simp[step_taint_def, mk_inst_def, imm_taint_def] >> metis_tac[]
QED

Theorem scalar_mstore_outer_ghost:
  ghost_inv d cenv cx es G tn s /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} /\
  (!name entry p sz.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    val_wf entry.type entry.value /\
    !b i. lookup_var p s = SOME b /\
      w2n b <= i /\ i < w2n b + val_footprint entry.type entry.value ==>
      i < w2n a \/ w2n a+32 <= i) ==>
  ghost_inv d cenv cx es G
    (step_taint (mk_inst iid MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn) (mstore (w2n a) w s)
Proof
  strip_tac >> drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`ARB`, `G`, `iid`] strip_assume_tac) >>
  irule ghost_inv_after_separated_write >>
  goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`UNIV`, `{i | w2n a <= i /\ i < w2n a+32}`] >>
  simp[mstore_memory_frame, op_taint_def, mstore_def,
       write_memory_with_expansion_def, step_taint_nonmemory_frame, mk_inst_def] >>
  simp_tac std_ss [arithmeticTheory.NOT_LESS_EQUAL, arithmeticTheory.NOT_LESS] >>
  first_assum ACCEPT_TAC
QED


Theorem scalar_mstore_binding_endpoint:
  lookup_var dst s = SOME a /\
  eval_operand value s = SOME (val_to_w256 v) /\
  op_taint tn value = {} /\ ptr_covers G tn dst s sz /\
  ((?x. v = BoolV x) \/ (?x. v = IntV x) \/
   (?x. v = FlagV x) \/ (?x. v = DecimalV x)) ==>
  ptr_covers G
    (step_taint (mk_inst iid MSTORE [Var dst; value] []) s
      (mstore (w2n a) (val_to_w256 v) s) tn) dst
    (mstore (w2n a) (val_to_w256 v) s) sz /\
  !mem. mem_agree_outside
    (step_taint (mk_inst iid MSTORE [Var dst; value] []) s
      (mstore (w2n a) (val_to_w256 v) s) tn).t_mem
    (mstore (w2n a) (val_to_w256 v) s).vs_memory mem ==>
    val_in_memory tv v (w2n a) mem
Proof
  strip_tac >>
  (conj_tac
   >- (gvs[ptr_covers_def, op_taint_def] >>
       simp[mstore_def, step_taint_def, set_var_taint_def, mk_inst_def,
            finite_mapTheory.DRESTRICT_UNIV]) >>
   rpt strip_tac >> irule scalar_mstore_robust >>
   conj_tac >- simp[] >>
   goal_assum (drule_at (Pat `mem_agree_outside _ _ _`)) >>
   gen_tac >> strip_tac >> irule mstore_word_clean >>
   goal_assum (drule_at (Pat `op_taint _ _ = {}`)) >>
   simp[eval_operand_def] >> metis_tac[])
QED

Theorem scalar_mstore_install_ghost:
  ghost_inv d cenv cx es G tn s /\
  lookup_var dst s = SOME a /\
  eval_operand value s = SOME (val_to_w256 entry.value) /\
  op_taint tn value = {} /\ ptr_covers G tn dst s sz /\
  ((?x. entry.value = BoolV x) \/ (?x. entry.value = IntV x) \/
   (?x. entry.value = FlagV x) \/ (?x. entry.value = DecimalV x)) /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var dst) sz) /\
  (!name e p sz.
    lookup_scopes name es.scopes = SOME e /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    val_wf e.type e.value /\
    !b i. lookup_var p s = SOME b /\
      w2n b <= i /\ i < w2n b + val_footprint e.type e.value ==>
      i < w2n a \/ w2n a+32 <= i) ==>
  ghost_inv d bc cx
    (es with scopes := (FEMPTY |+ (id,entry)) :: es.scopes) G
    (step_taint (mk_inst iid MSTORE [Var dst; value] []) s
      (mstore (w2n a) (val_to_w256 entry.value) s) tn)
    (mstore (w2n a) (val_to_w256 entry.value) s)
Proof
  strip_tac >>
  (`ghost_inv d cenv cx es G
      (step_taint (mk_inst iid MSTORE [Var dst; value] []) s
        (mstore (w2n a) (val_to_w256 entry.value) s) tn)
      (mstore (w2n a) (val_to_w256 entry.value) s)` by
      (irule scalar_mstore_outer_ghost >> metis_tac[]) >>
   drule_all ghost_inv_push_top_ext >>
   disch_then (mp_then Any mp_tac ghost_inv_set_top_entry) >>
   disch_then (qspecl_then [`FEMPTY`, `es.scopes`, `id`, `entry`] mp_tac) >>
   impl_tac
   >- (simp[] >> irule scalar_mstore_binding_endpoint >> simp[]) >>
   simp[])
QED
