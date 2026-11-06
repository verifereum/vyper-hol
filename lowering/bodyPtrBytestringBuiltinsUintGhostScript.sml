Theory bodyPtrBytestringBuiltinsUintGhost
Ancestors
  bodyPtrBytestringBuiltinsUintArithmetic bodyPtrBytestringBuiltinsCalldataCopy
  typedCopyPtr immutableMemoryFrame bodyPtrDefs ptrDiscipline
  venomState venomInst finite_map byte words

(* The concrete store endpoint is retained so the existing fresh-allocation
   write-memory boundary can be used without an arbitrary-state frame axiom. *)
Theorem clean_mstore_taint_state:
  !tn s id dst value a w.
    lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} ==>
    step_taint (mk_inst id MSTORE [Var dst;value] []) s
      (mstore (w2n a) w s) tn =
    (tn with t_mem := tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32})
Proof
  rpt strip_tac >>
  drule_all mstore_ghost_frame >> strip_tac >>
  simp[taint_component_equality] >>
  simp[step_taint_def, imm_taint_def, adopt_reset_def, mk_inst_def,
       set_var_taint_def]
QED

Theorem clean_mstore_ghost_inv:
  !d cenv cx es G tn s id dst value a w func inst q b asz.
    ghost_inv d cenv cx es G tn s /\
    local_ptrs_rel func cenv es.scopes s /\
    alloca_inv s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
    not_local_ptr cenv es.scopes q /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,asz) /\
    b <= w2n a /\ w2n a+32 <= b+asz /\
    lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} ==>
    ghost_inv d cenv cx es
      (step_prov PG G (mk_inst id MSTORE [Var dst;value] []) (mstore (w2n a) w s))
      (step_taint (mk_inst id MSTORE [Var dst;value] []) s (mstore (w2n a) w s) tn)
      (mstore (w2n a) w s)
Proof
  rpt strip_tac >>
  drule_all mstore_ghost_frame >> strip_tac >>
  simp[clean_mstore_taint_state, mstore_ghost_frame] >>
  `LENGTH (word_to_bytes w T) = 32` by
    simp[LENGTH_word_to_bytes, dimword_def,
         fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  simp[immutable_mstore_as_write] >>
  qpat_assum `LENGTH _ = 32` (fn th => pure_rewrite_tac[GSYM th]) >>
  irule write_memory_ghost_inv_alloca >> simp[] >>
  qexistsl_tac [`asz`, `b`, `func`, `inst`, `q`] >> simp[]
QED

Theorem clean_mstore_ghost_kept:
  !cenv es sa G0 tn0 s0 PG G tn s id dst value a w.
    lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} /\ ghost_kept cenv es sa G0 tn0 s0 G tn ==>
    ghost_kept cenv es sa G0 tn0 s0
      (step_prov PG G (mk_inst id MSTORE [Var dst;value] []) (mstore (w2n a) w s))
      (step_taint (mk_inst id MSTORE [Var dst;value] []) s (mstore (w2n a) w s) tn)
Proof
  rpt strip_tac >> drule_all mstore_ghost_frame >> strip_tac >>
  simp[clean_mstore_taint_state] >>
  irule ghost_kept_mem_taint_decrease >> simp[pred_setTheory.DIFF_SUBSET]
QED

Theorem digit_store_suffix_clean:
  !tn b n i.
    i <= n /\
    (!j. b+n+32-i <= j /\ j < b+n+32 ==> j NOTIN tn.t_mem) ==>
    !j. b+n+31-i <= j /\ j < b+n+32 ==>
      j NOTIN (tn.t_mem DIFF {j | b+n-i <= j /\ j < b+n-i+32})
Proof
  rpt strip_tac >> gvs[]
QED
