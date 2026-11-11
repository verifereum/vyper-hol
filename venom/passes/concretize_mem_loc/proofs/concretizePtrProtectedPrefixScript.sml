Theory concretizePtrProtectedPrefix
Ancestors
  concretizePtrKillBoundary concretizePtrPrefixCoverage concretizePtrReadCoverage
  concretizeMemLocDefs finite_map
  memLocDefs ptrDiscipline codegenRel venomExecSemantics venomState venomInst

(* The proposed offset-only footprint interface fails on an absent value. *)
Theorem ptr_offset_only_footprint_counterexample:
  inst_write_size (mk_inst 0 MSTORE [Lit 0w; Var "missing"] []) = SOME 32 /\
  mem_write_ops (mk_inst 0 MSTORE [Lit 0w; Var "missing"] []) =
    SOME <| iao_ofst := Lit 0w; iao_size := SOME (Lit 32w);
            iao_max_size := SOME (Lit 32w) |> /\
  eval_operand (Lit 0w) (init_venom_state "entry") = SOME 0w /\
  source_memory_write_ranges (mk_inst 0 MSTORE [Lit 0w; Var "missing"] [])
    (init_venom_state "entry") = []
Proof
  EVAL_TAC >> CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> EVAL_TAC
QED

Theorem ptr_ready_literal_write_range:
  !inst s n ops dst vals.
  inst_write_size inst = SOME n /\ mem_write_ops inst = SOME ops /\
  eval_operand ops.iao_ofst s = SOME dst /\
  eval_operands inst.inst_operands s = SOME vals ==>
  MEM (w2n dst,n) (source_memory_write_ranges inst s)
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode` >>
  simp[inst_write_size_def, mem_write_ops_def,
       source_memory_write_ranges_def] >> rpt strip_tac >>
  gvs[AllCaseEqs(), fixed_source_write_range_def,
      sized_source_write_range_def, eval_operands_def] >>
  gvs[AllCaseEqs(), eval_operand_def, wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> simp[]
QED

Theorem ptr_protected_byte_no_kill:
  !a bp sizes inst lo G fn s ops v b sz dst vals byte.
    sizes a = SOME sz /\ mem_write_ops inst = SOME ops /\
    ops.iao_ofst = Var v /\ FLOOKUP G v = SOME (b,sz) /\
    eval_operand ops.iao_ofst s = SOME dst /\
    eval_operands inst.inst_operands s = SOME vals /\
    access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
    b <= byte /\ byte < b + sz /\
    (!off len. MEM (off,len) (source_memory_write_ranges inst s) ==>
      ~(off <= byte /\ byte < off + len)) ==>
    ~ptr_ml_can_kill a bp sizes inst
Proof
  rpt strip_tac >>
  `inst_write_size inst = SOME sz` by gvs[ptr_ml_can_kill_def] >>
  `MEM (w2n dst,sz) (source_memory_write_ranges inst s)` by
    metis_tac[ptr_ready_literal_write_range] >>
  `sz <> 0` by decide_tac >>
  `(w2n dst,sz) = (b,sz)` by metis_tac[ptr_guarded_kill_exact] >>
  metis_tac[]
QED

(* Runtime witnesses belong to their associated prefix instruction.  No
   assertion that such witnesses follow from mere syntactic membership is made. *)
Theorem ptr_protected_prefix_records:
  MEM a live /\ ALL_DISTINCT (MAP FST xs) /\ MEM (idx,inst) xs /\
  (!j i. MEM (j,i) xs /\ (?n. inst_write_size i = SOME n) ==>
    ?lo G fn s ops v b sz dst byte.
      sizes a = SOME sz /\ mem_write_ops i = SOME ops /\
      ops.iao_ofst = Var v /\ FLOOKUP G v = SOME (b,sz) /\
      eval_operand ops.iao_ofst s = SOME dst /\
      (?vals. eval_operands i.inst_operands s = SOME vals) /\
      access_ok lo G fn i s /\ ~in_revert_forward fn s /\
      b <= byte /\ byte < b + sz /\
      (!off len. MEM (off,len) (source_memory_write_ranges i s) ==>
        ~(off <= byte /\ byte < off + len))) ==>
  MEM a (ml_lookup
    (SND (ml_liveat_insts_rev bp mems sizes label live la xs)) (label,idx))
Proof
  strip_tac >> irule ptr_liveat_prefix_records >>
  simp[] >> reverse conj_tac >- metis_tac[] >>
  simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
  PairCases_on `p` >> gvs[] >>
  `?n. inst_write_size p1 = SOME n` by metis_tac[ptr_ml_can_kill_def] >>
  qpat_x_assum `!j i. _` (qspecl_then [`p0`,`p1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  metis_tac[ptr_protected_byte_no_kill, arithmeticTheory.ADD_COMM]
QED
