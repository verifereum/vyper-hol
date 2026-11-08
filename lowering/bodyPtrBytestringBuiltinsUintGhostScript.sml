Theory bodyPtrBytestringBuiltinsUintGhost
Ancestors
  bodyPtrBytestringBuiltinsUintArithmetic bodyPtrBytestringBuiltinsCalldataCopy
  typedCopyPtr immutableMemoryFrame bodyPtrDefs ptrDiscipline wordLoadStorePtr
  venomState venomInst finite_map byte words codegenRel
  exprSimPtrLiteralBuffer exprSimUint2Str loweringPosts valueEncoding

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

(* Arithmetic that cannot propagate pointer provenance. ASSIGN is handled
   separately because it also propagates operand taint. *)
Theorem uint_scalar_ghost:
  MEM opc [Mod; Div; EQ; ADD] /\
  (!op. MEM op ops ==> op_prov G op = NONE) /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  step_prov PG G (mk_inst id opc ops [out]) s' =
    DRESTRICT G (COMPL {out}) /\
  step_taint (mk_inst id opc ops [out]) s s' tn =
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  `first_prov G ops = NONE` by
    (qpat_x_assum `!op. _` mp_tac >>
     Induct_on `ops` >> simp[first_prov_def]) >>
  `new_site_bytes s s' = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  gvs[] >>
  (simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       set_var_taint_def, mk_inst_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, range_bytes_def, taint_component_equality] >>
   Cases_on `ops` >> simp[out_taint_def] >>
   Cases_on `t` >- (simp[out_taint_def] >> Cases_on `eval_operand h s` >> simp[]) >>
   Cases_on `t'` >> simp[out_taint_def] >>
   Cases_on `eval_operand h s` >> simp[] >>
   Cases_on `t` >> simp[])
QED

Theorem uint_assign_ghost:
  op_prov G op = NONE /\ op_taint tn op = {} /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  step_prov PG G (mk_inst id ASSIGN [op] [out]) s' =
    DRESTRICT G (COMPL {out}) /\
  step_taint (mk_inst id ASSIGN [op] [out]) s s' tn =
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  `new_site_bytes s s' = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       step_taint_def, set_var_taint_def, mk_inst_def, mem_taint_def,
       step_writes_def, source_memory_write_ranges_def, written_taint_def,
       store_taint_def, adopt_reset_def, imm_taint_def, range_bytes_def,
       taint_component_equality, out_taint_def] >>
  Cases_on `eval_operand op s` >> simp[]
QED

Theorem uint_digits_header_representation:
  u2s_digits a b n X 0 str s ==>
  val_in_memory ty (StringV (num_to_dec_string X)) (b+n-LENGTH str)
    (mstore (b+n-LENGTH str) (n2w (LENGTH str)) s).vs_memory
Proof
  strip_tac >> gvs[u2s_digits_def] >>
  irule mstore_string_header >> simp[]
QED

Theorem uint_string_clean_robust:
  val_in_memory (BaseTV (StringT cap)) (StringV str) p mem /\
  LENGTH str + 32 <= type_memory_size (BaseTV (StringT cap)) /\
  (!i. p <= i /\ i < p+32+LENGTH str ==> i NOTIN dirty) ==>
  !mem'. mem_agree_outside dirty mem mem' ==>
    val_in_memory (BaseTV (StringT cap)) (StringV str) p mem'
Proof
  rpt strip_tac >> irule literal_clean_representation_robust >>
  simp[val_wf_def, val_footprint_def] >>
  qexistsl_tac [`dirty`, `mem`] >> simp[]
QED

(* The header write cleans exactly 32 bytes; only the logical payload, not
   the unused allocation padding, needs to have been clean already. *)
Theorem uint_digits_header_robust:
  u2s_digits a b n X 0 str s /\
  LENGTH str + 32 <= type_memory_size (BaseTV (StringT cap)) /\
  (!j. b+n-LENGTH str+32 <= j /\ j < b+n+32 ==> j NOTIN tn.t_mem) ==>
  !mem'.
    mem_agree_outside
      (tn.t_mem DIFF {j | b+n-LENGTH str <= j /\ j < b+n-LENGTH str+32})
      (mstore (b+n-LENGTH str) (n2w (LENGTH str)) s).vs_memory mem' ==>
    val_in_memory (BaseTV (StringT cap)) (StringV (num_to_dec_string X))
      (b+n-LENGTH str) mem'
Proof
  rpt strip_tac >>
  `num_to_dec_string X = str /\ LENGTH str <= n` by
    gvs[u2s_digits_def] >>
  asm_rewrite_tac[] >> irule uint_string_clean_robust >> simp[] >>
  qexistsl_tac
    [`tn.t_mem DIFF {j | b+n-LENGTH str <= j /\ j < b+n-LENGTH str+32}`,
     `(mstore (b+n-LENGTH str) (n2w (LENGTH str)) s).vs_memory`] >>
  simp[] >> reverse conj_tac
  >- (drule uint_digits_header_representation >> simp[]) >>
  rpt strip_tac >> gvs[] >>
  Cases_on `i < b+n+32-LENGTH (num_to_dec_string X)` >> simp[] >>
  disj1_tac >> first_x_assum irule >> decide_tac
QED
