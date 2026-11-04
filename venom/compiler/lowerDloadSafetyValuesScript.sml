(* Selected-value consumer boundaries. *)
Theory lowerDloadSafetyValues
Ancestors
  lowerDloadSafetyRelation lowerDloadSafetyKernel ptrDiscipline
  venomState finite_map pred_set list arithmetic words

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
  ~MEM inst.inst_opcode [ASSIGN; SHL; SHR; SAR; MSTORE; SSTORE; TSTORE; ISTORE] ==>
  op_taint tn op = {}
Proof
  simp[taint_ok_def] >> metis_tac[]
QED

Theorem ld_numeric_operand_nonopaque:
  fn_shape_ok fn /\ MEM inst (fn_insts fn) /\ MEM (Var v) inst.inst_operands /\
  ~MEM inst.inst_opcode [ASSIGN; PHI; RET] ==>
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
