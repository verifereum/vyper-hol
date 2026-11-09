(* Symbolic kind and memory boundaries used by exact-output planner proofs. *)
Theory symPlannerBase
Ancestors
  codegenSymRel asmSymBridge asmSymSem planExec stackModel dfgDefs
  finite_map list rich_list arithmetic planWf reorderSim

Theorem op_kind_ok_operand_equiv:
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  operand_equiv dfg op at ==>
  (op_kind_ok fn ret op sv <=> op_kind_ok fn ret at sv)
Proof
  simp[operand_equiv_def] >>
  metis_tac[op_kind_ok_normalize_operand]
QED

Theorem op_kind_ok_val_payload:
  op_kind_ok fn ret op (Val w) <=> op_kind_ok fn ret op (Val v)
Proof
  Cases_on `op` >> simp[op_kind_ok_def] >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem mem_label_at_cong:
  (!i. in_mem_range off 32 i ==> FLOOKUP a i = FLOOKUP b i) ==>
  mem_label_at a off = mem_label_at b off
Proof
  strip_tac >> simp[mem_label_at_def] >>
  `FLOOKUP a off = FLOOKUP b off` by
    (first_x_assum irule >> simp[in_mem_range_def]) >>
  simp[] >> AP_TERM_TAC >>
  simp[FUN_EQ_THM, pairTheory.FORALL_PROD] >>
  rpt gen_tac >>
  `!i. i < 32 ==> FLOOKUP a (i+off) = FLOOKUP b (i+off)` by
    (rpt strip_tac >> first_x_assum irule >> simp[in_mem_range_def]) >>
  simp[EVERY_MEM, MEM_COUNT_LIST]
QED

Theorem mem_sval_at_cong:
  (!i. in_mem_range off 32 i ==> FLOOKUP a i = FLOOKUP b i) ==>
  (mem_sval_at a off sv <=> mem_sval_at b off sv)
Proof
  Cases_on `sv` >> simp[mem_sval_at_def]
  >- metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
  metis_tac[mem_label_at_cong]
QED

Theorem mem_sval_at_store_label:
  mem_sval_at (labs |++ GENLIST (\i. (off+i,(l,d,i))) 32) off (Lab l d)
Proof
  simp[mem_sval_at_def, mem_label_at_def, mstore_labels_lookup,
       EVERY_MEM, MEM_COUNT_LIST]
QED

Theorem mem_sval_at_clear:
  mem_sval_at (mem_labels_clear labs (in_mem_range off 32)) off (Val w)
Proof
  simp[mem_sval_at_def, mem_labels_clear_def, finite_mapTheory.FDOM_DRESTRICT]
QED

Theorem sym_steps_compose_ok:
  sym_steps p env m ss = SymOK mid /\
  sym_steps p env n mid = SymOK last ==>
  sym_steps p env (m+n) ss = SymOK last
Proof
  simp[sym_steps_add]
QED

Theorem store_label_lookup_outside:
  ~in_mem_range off 32 i ==>
  FLOOKUP (labs |++ GENLIST (\j. (off+j,(l,d,j))) 32) i = FLOOKUP labs i
Proof
  simp[mstore_labels_lookup, in_mem_range_def]
QED

Theorem clear_lookup_outside:
  ~in_mem_range off 32 i ==>
  FLOOKUP (mem_labels_clear labs (in_mem_range off 32)) i = FLOOKUP labs i
Proof
  simp[mem_labels_clear_def, finite_mapTheory.FLOOKUP_DRESTRICT]
QED

Theorem mem_sval_at_store_label_disjoint:
  (off+32 <= at \/ at+32 <= off) ==>
  (mem_sval_at (labs |++ GENLIST (\j. (off+j,(l,d,j))) 32) at sv <=>
   mem_sval_at labs at sv)
Proof
  strip_tac >> irule mem_sval_at_cong >>
  simp[mstore_labels_lookup, in_mem_range_def] >> rpt strip_tac >>
  `~(off <= i /\ i < off+32)` by decide_tac >> simp[]
QED

Theorem mem_sval_at_clear_disjoint:
  (off+32 <= at \/ at+32 <= off) ==>
  (mem_sval_at (mem_labels_clear labs (in_mem_range off 32)) at sv <=>
   mem_sval_at labs at sv)
Proof
  strip_tac >> irule mem_sval_at_cong >>
  simp[mem_labels_clear_def, finite_mapTheory.FLOOKUP_DRESTRICT,
       in_mem_range_def] >> rpt strip_tac >>
  `~(off <= i /\ i < off+32)` by decide_tac >> simp[]
QED

Theorem sym_mload_label_kind:
  ss.sym_stack = Val (n2w off) :: stk /\ off < dimword(:256) /\
  mem_sval_at ss.sym_mem_labels off (Lab l d) ==>
  ?last. sym_mload ss = SymOK last /\
    last.sym_stack = Lab l d :: stk /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  simp[mem_sval_at_def, sym_mload_def, asmSemTheory.asm_next_def]
QED

Theorem mem_sval_at_val_no_label:
  mem_sval_at labs off (Val w) ==> mem_label_at labs off = NONE
Proof
  simp[mem_sval_at_def, mem_label_at_def, finite_mapTheory.FLOOKUP_DEF,
       in_mem_range_def]
QED

Theorem sym_mload_val_kind:
  ss.sym_stack = Val (n2w off) :: stk /\ off < dimword(:256) /\
  mem_sval_at ss.sym_mem_labels off (Val w) ==>
  ?last v. sym_mload ss = SymOK last /\
    last.sym_stack = Val v :: stk /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  rpt strip_tac >>
  drule mem_sval_at_val_no_label >> strip_tac >>
  `~mem_labels_hit ss.sym_mem_labels (in_mem_range off 32)` by
    (gvs[mem_sval_at_def, mem_labels_hit_def] >> metis_tac[]) >>
  `((\i:num. T) = UNIV)` by simp[FUN_EQ_THM] >>
  simp[sym_mload_def, sym_step_concrete_def, asm_op_arity_def,
       asm_op_arity_table_def, sval_val_def,
       asm_op_mem_reads_def, asm_op_mem_writes_def, sym_lift_def,
       asmSemTheory.asm_step_op_def, asmSemTheory.asm_step_memory_def,
       asmSemTheory.asm_mload_def, asmSemTheory.asm_next_def,
       asmSemTheory.asm_step_arith_def, asmSemTheory.asm_step_compare_def,
       asmSemTheory.asm_step_bitwise_def, finite_mapTheory.DRESTRICT_UNIV,
       mem_labels_clear_def]
QED

Theorem sym_mload_kind:
  ss.sym_stack = Val (n2w off) :: stk /\ off < dimword(:256) /\
  mem_sval_at ss.sym_mem_labels off sv /\ op_kind_ok fn ret op sv ==>
  ?last v. sym_mload ss = SymOK last /\
    last.sym_stack = v :: stk /\ op_kind_ok fn ret op v /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  Cases_on `sv` >> rpt strip_tac
  >- (drule_all sym_mload_val_kind >>
      metis_tac[op_kind_ok_val_payload]) >>
  drule_all sym_mload_label_kind >> metis_tac[]
QED

Theorem sym_mstore_label:
  ss.sym_stack = Val (n2w off) :: Lab l d :: stk /\ off < dimword(:256) ==>
  ?last. sym_mstore ss = SymOK last /\ last.sym_stack = stk /\
    last.sym_mem_labels =
      ss.sym_mem_labels |++ GENLIST (\i. (off+i,(l,d,i))) 32 /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  simp[sym_mstore_def, sym_lift_def, asmSemTheory.asm_mstore_def,
       asmSemTheory.asm_next_def]
QED

Theorem sym_mstore_val:
  ss.sym_stack = Val (n2w off) :: Val w :: stk /\ off < dimword(:256) ==>
  ?last. sym_mstore ss = SymOK last /\ last.sym_stack = stk /\
    last.sym_mem_labels = mem_labels_clear ss.sym_mem_labels (in_mem_range off 32) /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  simp[sym_mstore_def, sym_step_concrete_def, asm_op_arity_def,
       asm_op_arity_table_def, sval_val_def, asm_op_mem_reads_def,
       mem_labels_hit_def, asm_op_mem_writes_def, sym_lift_def,
       asmSemTheory.asm_step_op_def, asmSemTheory.asm_step_memory_def,
       asmSemTheory.asm_step_arith_def, asmSemTheory.asm_step_compare_def,
       asmSemTheory.asm_step_bitwise_def, asmSemTheory.asm_mstore_def,
       asmSemTheory.asm_next_def, asmSemTheory.log_table_def]
QED

Theorem sym_mstore_kind:
  ss.sym_stack = Val (n2w off) :: sv :: stk /\ off < dimword(:256) ==>
  ?last. sym_mstore ss = SymOK last /\ last.sym_stack = stk /\
    mem_sval_at last.sym_mem_labels off sv /\
    (!i. ~in_mem_range off 32 i ==>
       FLOOKUP last.sym_mem_labels i = FLOOKUP ss.sym_mem_labels i) /\
    (!at v. (off+32 <= at \/ at+32 <= off) ==>
       (mem_sval_at last.sym_mem_labels at v <=> mem_sval_at ss.sym_mem_labels at v)) /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  Cases_on `sv` >> rpt strip_tac
  >- (drule_all sym_mstore_val >>
      metis_tac[mem_sval_at_clear, clear_lookup_outside, mem_sval_at_clear_disjoint]) >>
  drule_all sym_mstore_label >>
  metis_tac[mem_sval_at_store_label, store_label_lookup_outside,
            mem_sval_at_store_label_disjoint]
QED

Theorem sym_kinds_ok_stack_change:
  sym_kinds_ok cplan fn ret srest ps ss /\
  LIST_REL (op_kind_ok fn ret) (REVERSE stk) top /\
  last.sym_stack = top ++ srest /\ last.sym_mem_labels = ss.sym_mem_labels ==>
  sym_kinds_ok cplan fn ret srest (ps with ps_stack := stk) last
Proof
  simp[sym_kinds_ok_def] >> metis_tac[]
QED

Theorem sym_kinds_ok_push:
  sym_kinds_ok cplan fn ret srest ps ss /\ op_kind_ok fn ret op sv ==>
  sym_kinds_ok cplan fn ret srest
    (ps with ps_stack := stack_push op ps.ps_stack)
    (ss with sym_stack := sv :: ss.sym_stack)
Proof
  simp[sym_kinds_ok_def, stack_push_def] >> rpt strip_tac >>
  qexists `sv :: top` >> simp[]
QED

Theorem LIST_REL_stack_dup:
  LIST_REL R (REVERSE stk) top /\ d < LENGTH stk ==>
  LIST_REL R (REVERSE (stack_dup d stk)) (EL d top :: top)
Proof
  simp[stack_dup_def, stack_peek_eq_EL_REVERSE] >>
  simp[LIST_REL_EL_EQN]
QED

Theorem sym_kinds_ok_dup:
  sym_kinds_ok cplan fn ret srest ps ss /\ d < LENGTH ps.ps_stack ==>
  sym_kinds_ok cplan fn ret srest
    (ps with ps_stack := stack_dup d ps.ps_stack)
    (ss with sym_stack := EL d ss.sym_stack :: ss.sym_stack)
Proof
  simp[sym_kinds_ok_def] >> rpt strip_tac >>
  qexists `EL d top :: top` >>
  imp_res_tac LIST_REL_LENGTH >>
  simp[LIST_REL_stack_dup] >> gvs[rich_listTheory.EL_APPEND1]
QED

Theorem sym_kinds_ok_poke_equiv:
  sym_kinds_ok cplan fn ret srest ps ss /\ d < LENGTH ps.ps_stack /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  operand_equiv dfg op (stack_peek d ps.ps_stack) ==>
  sym_kinds_ok cplan fn ret srest
    (ps with ps_stack := stack_poke d op ps.ps_stack) ss
Proof
  simp[sym_kinds_ok_def] >> rpt strip_tac >>
  qexists `top` >> simp[reverse_stack_poke] >>
  gvs[LIST_REL_EL_EQN, EL_LUPDATE, stack_peek_eq_EL_REVERSE] >>
  rpt strip_tac >> Cases_on `n = d` >>
  gvs[] >> metis_tac[op_kind_ok_operand_equiv]
QED
