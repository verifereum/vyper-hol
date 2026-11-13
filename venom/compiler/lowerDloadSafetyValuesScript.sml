(* Selected-value consumer boundaries. *)
Theory lowerDloadSafetyValues
Ancestors
  lowerDloadSafetyRelation lowerDloadSafetyKernel ptrDiscipline
  venomState venomInst irSupply unitLabelMapIdentity finite_map pred_set list arithmetic words
  memLocDefs pointerConfinedDefs

Theorem ld_vars_operand_defined:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  (!v. op = Var v ==> MEM v (fn_ir_vars f.lf_fn)) ==>
  (IS_SOME (eval_operand op f.lf_src) <=>
   IS_SOME (eval_operand op f.lf_tgt))
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def] >>
  simp[ld_vars_def, SUBSET_DEF, FLOOKUP_DEF] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `s IN FDOM f.lf_tgt.vs_vars` >> simp[]
QED

Theorem ld_vars_value:
  ld_vars P A f /\ ~retpc_var f.lf_fn v /\
  FLOOKUP f.lf_src.vs_vars v = SOME x /\
  FLOOKUP f.lf_tgt.vs_vars v = SOME y ==>
  case FLOOKUP f.lf_H v of
    SOME a => ld_wordrel A (SOME a) x y
  | NONE => word_agree_except
      (case FLOOKUP f.lf_tv v of NONE => {} | SOME m => m) x y
Proof
  simp[ld_vars_def] >> metis_tac[]
QED

Theorem ld_vars_selected:
  ld_vars P A f /\ ~retpc_var f.lf_fn v /\
  FLOOKUP f.lf_src.vs_vars v = SOME x /\
  FLOOKUP f.lf_tgt.vs_vars v = SOME y /\ FLOOKUP f.lf_H v = SOME a ==>
  ld_wordrel A (SOME a) x y
Proof
  strip_tac >> drule_all ld_vars_value >> simp[]
QED

Theorem ld_word_agree_empty:
  word_agree_except {} x y <=> x = y
Proof
  simp[word_agree_except_bits, fcpTheory.CART_EQ] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]
QED

Theorem ld_vars_scalar:
  ld_vars P A f /\ ~retpc_var f.lf_fn v /\
  FLOOKUP f.lf_src.vs_vars v = SOME x /\
  FLOOKUP f.lf_tgt.vs_vars v = SOME y /\ FLOOKUP f.lf_H v = NONE /\
  (FLOOKUP f.lf_tv v = NONE \/ FLOOKUP f.lf_tv v = SOME {}) ==>
  x = y
Proof
  strip_tac >> drule_all ld_vars_value >> simp[ld_word_agree_empty]
QED

Theorem ld_vars_operand_scalar:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  eval_operand op f.lf_src = SOME x /\
  eval_operand op f.lf_tgt = SOME y /\ op_prov f.lf_H op = NONE /\
  (!v. op = Var v ==> ~retpc_var f.lf_fn v /\
    (case FLOOKUP f.lf_tv v of NONE => {} | SOME m => m) = {}) ==>
  x = y
Proof
  Cases_on `op` >>
  simp[eval_operand_def, lookup_var_def, op_prov_def] >> strip_tac >> gvs[] >>
  drule_all ld_vars_value >> simp[ld_word_agree_empty]
QED

Theorem ld_vars_operand_selected:
  ld_vars P A f /\ eval_operand op f.lf_src = SOME x /\
  eval_operand op f.lf_tgt = SOME y /\ op_prov f.lf_H op = SOME a /\
  (!v. op = Var v ==> ~retpc_var f.lf_fn v) ==>
  ld_wordrel A (SOME a) x y
Proof
  Cases_on `op` >>
  simp[eval_operand_def, lookup_var_def, op_prov_def] >>
  metis_tac[ld_vars_selected]
QED

Theorem ld_wordrel_affine:
  ld_wordrel A q x y ==>
  ld_wordrel A q (x + z) (y + z) /\
  ld_wordrel A q (x - z) (y - z)
Proof
  Cases_on `q` >> simp[ld_wordrel_def] >>
  rpt strip_tac >> qexistsl_tac [`b`, `c`, `n`] >>
  simp[] >> wordsLib.WORD_DECIDE_TAC
QED

Theorem ld_numeric_operand_untainted:
  taint_ok fn tn inst s /\ MEM op inst.inst_operands /\
  ~MEM inst.inst_opcode [ASSIGN; MUL; SHL; SHR; SAR; MSTORE; SSTORE; TSTORE; ISTORE] ==>
  op_taint tn op = {}
Proof
  simp[taint_ok_def] >> metis_tac[]
QED

Theorem ld_numeric_operand_nonopaque:
  fn_shape_ok fn /\ MEM inst (fn_insts fn) /\ MEM (Var v) inst.inst_operands /\
  ~MEM inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET] ==>
  ~retpc_var fn v
Proof
  strip_tac >> strip_tac >> drule_all lowerDloadSafetyBoundaryTheory.shape_retpc_operand_boundary >>
  gvs[]
QED

Theorem ld_slot_source_site:
  FDOM A = ld_slots A frames /\ FLOOKUP A k = SOME (b,c,n) ==>
  ?j aid. j < LENGTH frames /\
    k = ((EL j frames).lf_serial,aid) /\
    (j,aid,b,n) IN ld_sites frames T
Proof
  strip_tac >>
  `k IN FDOM A` by (gvs[FLOOKUP_DEF] >> metis_tac[]) >>
  `k IN ld_slots A frames` by metis_tac[] >>
  pop_assum mp_tac >> simp[ld_slots_def] >> strip_tac >> gvs[] >>
  gvs[MEM_EL] >> qexists_tac `n'` >>
  simp[ld_sites_def] >> metis_tac[]
QED

(* Positive-sized sites can share numerical source coordinates only when
   they have the same live identity.  No such claim holds at size zero. *)
Theorem ld_positive_source_identity:
  ld_global lo A frames /\ FDOM A = ld_slots A frames /\
  FLOOKUP A a = SOME (b,c,n) /\ FLOOKUP A a' = SOME (b,c',n) /\ 0 < n ==>
  a = a'
Proof
  strip_tac >>
  drule_all ld_slot_source_site >> strip_tac >>
  qpat_x_assum `FLOOKUP A a' = _` kall_tac >>
  drule_all ld_slot_source_site >> strip_tac >>
  spose_not_then assume_tac >>
  `(j,aid) <> (j',aid')` by (strip_tac >> gvs[]) >>
  drule_all ld_global_separate >> decide_tac
QED


Theorem ld_translate_cancel[local]:
  ((u:bytes32) + v) + w - u = w + v
Proof
  wordsLib.WORD_DECIDE_TAC
QED

Theorem ld_wordrel_site_value:
  ld_wordrel A (SOME a) x y /\ FLOOKUP A a = SOME (b,c,n) /\
  b <= w2n x /\ w2n x <= b+n /\ c+n < dimword (:256) ==>
  w2n y = c + (w2n x - b)
Proof
  pure_rewrite_tac[ld_wordrel_SOME] >> strip_tac >>
  `y = x + n2w c - n2w b` by
    metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
  `x = n2w b + n2w (w2n x - b)` by
    (simp[word_add_n2w, GSYM n2w_w2n] >> AP_TERM_TAC >> decide_tac) >>
  `x + n2w c - n2w b = n2w (c + (w2n x - b))` by
    (qpat_x_assum `x = n2w b + _` (fn th =>
       CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
     pure_rewrite_tac[ld_translate_cancel, word_add_n2w] >> REFL_TAC) >>
  `c + (w2n x - b) < dimword (:256)` by decide_tac >>
  qpat_x_assum `y = x + n2w c - n2w b`
    (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `x + n2w c - n2w b = _`
    (fn th => pure_rewrite_tac[th]) >>
  simp[LESS_MOD]
QED

Theorem ld_wordrel_site_comparisons:
  ld_wordrel A (SOME a) x1 y1 /\ ld_wordrel A (SOME a) x2 y2 /\
  FLOOKUP A a = SOME (b,c,n) /\
  b <= w2n x1 /\ w2n x1 <= b+n /\
  b <= w2n x2 /\ w2n x2 <= b+n /\ c+n < dimword (:256) ==>
  ((y1 = y2) <=> (x1 = x2)) /\
  ((w2n y1 < w2n y2) <=> (w2n x1 < w2n x2)) /\
  ((w2n y2 < w2n y1) <=> (w2n x2 < w2n x1))
Proof
  strip_tac >>
  `w2n y1 = c + (w2n x1 - b)` by metis_tac[ld_wordrel_site_value] >>
  `w2n y2 = c + (w2n x2 - b)` by metis_tac[ld_wordrel_site_value] >>
  once_rewrite_tac[GSYM w2n_11] >>
  asm_rewrite_tac[] >> decide_tac
QED

Theorem ld_vars_operand_equal:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  op_prov f.lf_H op = NONE /\
  (!v. op = Var v ==> MEM v (fn_ir_vars f.lf_fn) /\
    ~retpc_var f.lf_fn v /\
    (case FLOOKUP f.lf_tv v of NONE => {} | SOME m => m) = {}) ==>
  eval_operand op f.lf_src = eval_operand op f.lf_tgt
Proof
  strip_tac >>
  `IS_SOME (eval_operand op f.lf_src) <=> IS_SOME (eval_operand op f.lf_tgt)` by
    (irule ld_vars_operand_defined >> metis_tac[]) >>
  Cases_on `eval_operand op f.lf_src` >> Cases_on `eval_operand op f.lf_tgt` >>
  gvs[] >> metis_tac[ld_vars_operand_scalar]
QED

Theorem ld_vars_operands_equal:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  (!op. MEM op ops ==> op_prov f.lf_H op = NONE /\
    (!v. op = Var v ==> MEM v (fn_ir_vars f.lf_fn) /\
      ~retpc_var f.lf_fn v /\
      (case FLOOKUP f.lf_tv v of NONE => {} | SOME m => m) = {})) ==>
  eval_operands ops f.lf_src = eval_operands ops f.lf_tgt
Proof
  Induct_on `ops` >- simp[eval_operands_def] >>
  rpt strip_tac >>
  qpat_x_assum `!op. MEM op (h::ops) ==> _` mp_tac >>
  simp[] >> strip_tac >>
  `eval_operand h f.lf_src = eval_operand h f.lf_tgt` by
    (irule ld_vars_operand_equal >> metis_tac[]) >>
  `eval_operands ops f.lf_src = eval_operands ops f.lf_tgt` by metis_tac[] >>
  simp[eval_operands_def]
QED

Theorem ld_vars_nonpointer_provenance:
  ld_vars P A f /\ (!v. op = Var v ==> v NOTIN fn_pv P f.lf_fn) ==>
  op_prov f.lf_H op = NONE
Proof
  Cases_on `op` >> simp[op_prov_def] >>
  simp[ld_vars_def, SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem ld_ptr_use_scalar:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode <> INVOKE /\
  ~is_pointer_preserving_op inst.inst_opcode /\
  ~MEM inst.inst_opcode [LT; GT; EQ] /\
  mem_write_ops inst = NONE /\ mem_read_ops inst = NONE /\
  MEM (Var v) inst.inst_operands ==>
  v NOTIN fn_pv P fn
Proof
  simp[fn_ptr_ok_def, ptr_use_ok_def] >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem ld_vars_numeric_operands_equal:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ MEM inst (fn_insts f.lf_fn) /\
  taint_ok f.lf_fn tn inst f.lf_src /\ tn.t_var = f.lf_tv /\
  ~MEM inst.inst_opcode
    [ASSIGN; PHI; RET; RETFMP; DRET; MUL; SHL; SHR; SAR; MSTORE; SSTORE; TSTORE; ISTORE] /\
  (!v. MEM (Var v) inst.inst_operands ==>
    MEM v (fn_ir_vars f.lf_fn) /\ v NOTIN fn_pv P f.lf_fn) ==>
  eval_operands inst.inst_operands f.lf_src =
  eval_operands inst.inst_operands f.lf_tgt
Proof
  strip_tac >> irule ld_vars_operands_equal >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  qx_gen_tac `op` >> strip_tac >> conj_tac
  >- (irule ld_vars_nonpointer_provenance >> metis_tac[]) >>
  qx_gen_tac `v` >> strip_tac >> gvs[] >>
  `op_taint tn (Var v) = {}` by
    (irule ld_numeric_operand_untainted >> simp[] >> metis_tac[]) >>
  gvs[op_taint_def] >>
  irule ld_numeric_operand_nonopaque >> simp[] >> metis_tac[]
QED

Theorem ld_inst_input_ir:
  MEM inst (fn_insts fn) /\ MEM (Var v) inst.inst_operands ==>
  MEM v (fn_ir_vars fn)
Proof
  simp[fn_insts_MEM] >> strip_tac >>
  simp[fn_ir_vars_def, block_ir_vars_def, MEM_FLAT, MEM_MAP] >>
  irule_at Any EQ_REFL >> qexists_tac `bb` >> simp[] >>
  simp[MEM_FLAT, MEM_MAP] >> irule_at Any EQ_REFL >>
  qexists_tac `inst` >> simp[inst_ir_vars_def] >> disj2_tac >>
  simp[inst_uses_def] >>
  qpat_x_assum `MEM (Var v) inst.inst_operands` mp_tac >>
  Q.SPEC_TAC (`inst.inst_operands`, `ops`) >> Induct >>
  simp[operand_vars_def] >> Cases_on `h` >>
  simp[operand_var_def] >> metis_tac[]
QED

Theorem ld_read_access_cases:
  access_ok lo (ld_erase A o_f H) fn inst s /\
  ~in_revert_forward fn s /\ mem_read_ops inst = SOME ops /\
  MEM (w2n x,n) (source_memory_read_ranges inst s) /\ 0 < n /\
  (op_prov H ops.iao_ofst = NONE ==> x = y) /\
  (!a. op_prov H ops.iao_ofst = SOME a ==> ld_wordrel A (SOME a) x y) /\
  (!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword (:256)) ==>
  (w2n x+n <= lo /\ y=x) \/
  (?a b c sz delta. op_prov H ops.iao_ofst = SOME a /\
    FLOOKUP A a = SOME (b,c,sz) /\ w2n x=b+delta /\
    w2n y=c+delta /\ delta+n <= sz)
Proof
  strip_tac >>
  qpat_x_assum `access_ok _ _ _ _ _` mp_tac >>
  simp[access_ok_def] >> strip_tac >>
  qpat_x_assum `!off len. MEM (off,len) (source_memory_read_ranges inst s) /\ _ ==> _`
    (qspecl_then [`w2n x`, `n`] mp_tac) >> simp[] >>
  Cases_on `op_prov H ops.iao_ofst` >> gvs[]
  >- (Cases_on `w2n y+n <= lo` >> simp[] >>
      strip_tac >> Cases_on `ops.iao_ofst` >>
      gvs[op_prov_def, FLOOKUP_o_f]) >>
  `?b c sz. FLOOKUP A x' = SOME (b,c,sz)` by
    metis_tac[ld_wordrel_SOME] >>
  `op_prov (ld_erase A o_f H) ops.iao_ofst = SOME (b,sz)` by
    (Cases_on `ops.iao_ofst` >> gvs[op_prov_def, FLOOKUP_o_f, ld_erase_def]) >>
  simp[] >> strip_tac >>
  `b <= w2n x /\ w2n x+n <= b+sz` by
    (gvs[op_prov_def, FLOOKUP_o_f, ld_erase_def]) >>
  `w2n y = c+(w2n x-b)` by
    (irule ld_wordrel_site_value >> simp[] >>
     qexistsl_tac [`A`, `x'`, `sz`] >> simp[] >>
     metis_tac[]) >>
  disj2_tac >> qexists_tac `w2n x-b` >>
  simp[] >> decide_tac
QED

(* BUMP's explicit base is a scalar under the source discipline. *)
Theorem ld_vars_bump_operands_equal:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_ptr_ok P f.lf_fn /\ fn_shape_ok f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ inst.inst_opcode = BUMP /\
  taint_ok f.lf_fn tn inst f.lf_src /\ tn.t_var = f.lf_tv ==>
  eval_operands inst.inst_operands f.lf_src =
  eval_operands inst.inst_operands f.lf_tgt
Proof
  strip_tac >> irule ld_vars_numeric_operands_equal >>
  simp[] >> conj_tac
  >- (qexistsl_tac [`A`, `P`] >> simp[] >>
      qx_gen_tac `v` >> strip_tac >> conj_tac
      >- metis_tac[ld_inst_input_ir] >>
      irule ld_ptr_use_scalar >> simp[] >> qexists_tac `inst` >>
      simp[mem_write_ops_def, mem_read_ops_def, is_pointer_preserving_op_def] >>
      metis_tac[]) >>
  qexists_tac `tn` >> simp[]
QED

Theorem ld_nonghost_initial_fmp:
  ld_nonghost tn s t ==> s.vs_initial_fmp = t.vs_initial_fmp
Proof
  simp[ld_nonghost_def]
QED

(* No distinctness of the two output names is needed. *)
Theorem ld_bump_output_ghosts:
  inst.inst_opcode = BUMP /\ inst.inst_outputs = [x;y] ==>
  step_prov PG G inst s' = DRESTRICT G (COMPL {x;y}) /\
  (step_taint inst s s' tn).t_var =
    DRESTRICT tn.t_var (COMPL {x;y})
Proof
  simp[step_prov_def, out_prov_def, set_prov_def,
       step_taint_def, set_var_taint_def]
QED

val _ = if null (hyp ld_vars_bump_operands_equal) andalso
           null (hyp ld_nonghost_initial_fmp) andalso
           null (hyp ld_bump_output_ghosts) then ()
        else raise Fail "residual scalar boundary has hypotheses";
