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

Theorem mem_range_lookup_bytes:
  (!i. in_mem_range off 32 i ==> FLOOKUP a i = FLOOKUP b i) ==>
  (!i. i < 32 ==> FLOOKUP a (i+off) = FLOOKUP b (i+off))
Proof
  rw[in_mem_range_def] >> first_x_assum irule >> decide_tac
QED

Theorem mem_range_lookup_start:
  (!i. in_mem_range off 32 i ==> FLOOKUP a i = FLOOKUP b i) ==>
  FLOOKUP a off = FLOOKUP b off
Proof
  strip_tac >> first_x_assum irule >> simp[in_mem_range_def]
QED

Theorem mem_label_at_cong:
  (!i. in_mem_range off 32 i ==> FLOOKUP a i = FLOOKUP b i) ==>
  mem_label_at a off = mem_label_at b off
Proof
  strip_tac >> map_every imp_res_tac [mem_range_lookup_bytes, mem_range_lookup_start] >>
  simp[mem_label_at_def, mem_range_lookup_start, EVERY_MEM, MEM_COUNT_LIST]
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

Theorem in_mem_range_slots_disjoint:
  (off+32 <= at \/ at+32 <= off) /\ in_mem_range at 32 i ==>
  ~in_mem_range off 32 i
Proof
  simp[in_mem_range_def] >> decide_tac
QED

Theorem mem_sval_at_store_label_disjoint:
  (off+32 <= at \/ at+32 <= off) ==>
  (mem_sval_at (labs |++ GENLIST (\j. (off+j,(l,d,j))) 32) at sv <=>
   mem_sval_at labs at sv)
Proof
  strip_tac >> irule mem_sval_at_cong >>
  metis_tac[store_label_lookup_outside, in_mem_range_slots_disjoint]
QED

Theorem mem_sval_at_clear_disjoint:
  (off+32 <= at \/ at+32 <= off) ==>
  (mem_sval_at (mem_labels_clear labs (in_mem_range off 32)) at sv <=>
   mem_sval_at labs at sv)
Proof
  strip_tac >> irule mem_sval_at_cong >>
  metis_tac[clear_lookup_outside, in_mem_range_slots_disjoint]
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

Theorem mem_sval_at_val_no_hit:
  mem_sval_at labs off (Val w) ==>
  ~mem_labels_hit labs (in_mem_range off 32)
Proof
  simp[mem_sval_at_def, mem_labels_hit_def] >> metis_tac[]
QED

Theorem sym_mload_unlabelled:
  ss.sym_stack = Val (n2w off) :: stk /\ off < dimword(:256) /\
  mem_label_at ss.sym_mem_labels off = NONE /\
  ~mem_labels_hit ss.sym_mem_labels (in_mem_range off 32) ==>
  ?last v. sym_mload ss = SymOK last /\
    last.sym_stack = Val v :: stk /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  rpt strip_tac >>
  `((\i:num. T) = UNIV)` by simp[FUN_EQ_THM] >>
  simp[mem_sval_at_val_no_label, mem_sval_at_val_no_hit,
       sym_mload_def, sym_step_concrete_def, asm_op_arity_def,
       asm_op_arity_table_def, sval_val_def,
       asm_op_mem_reads_def, asm_op_mem_writes_def, sym_lift_def,
       asmSemTheory.asm_step_op_def, asmSemTheory.asm_step_memory_def,
       asmSemTheory.asm_mload_def, asmSemTheory.asm_next_def,
       asmSemTheory.asm_step_arith_def, asmSemTheory.asm_step_compare_def,
       asmSemTheory.asm_step_bitwise_def, finite_mapTheory.DRESTRICT_UNIV,
       mem_labels_clear_def]
QED

Theorem sym_mload_val_kind:
  ss.sym_stack = Val (n2w off) :: stk /\ off < dimword(:256) /\
  mem_sval_at ss.sym_mem_labels off (Val w) ==>
  ?last v. sym_mload ss = SymOK last /\
    last.sym_stack = Val v :: stk /\
    last.sym_mem_labels = ss.sym_mem_labels /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  metis_tac[sym_mload_unlabelled, mem_sval_at_val_no_label, mem_sval_at_val_no_hit]
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
  rw[sym_kinds_ok_def, stack_push_def] >>
  qexists `sv :: top` >> simp[]
QED

Theorem LIST_REL_stack_dup:
  LIST_REL R (REVERSE stk) top /\ d < LENGTH stk ==>
  LIST_REL R (REVERSE (stack_dup d stk)) (EL d top :: top)
Proof
  simp[stack_dup_def, stack_peek_eq_EL_REVERSE] >>
  simp[LIST_REL_EL_EQN]
QED

Theorem LIST_REL_dup_suffix:
  LIST_REL R (REVERSE stk) top /\ d < LENGTH stk ==>
  EL d (top ++ srest) :: (top ++ srest) = (EL d top :: top) ++ srest
Proof
  simp[LIST_REL_EL_EQN] >> rpt strip_tac >> gvs[rich_listTheory.EL_APPEND1]
QED

Theorem sym_kinds_ok_dup:
  sym_kinds_ok cplan fn ret srest ps ss /\ d < LENGTH ps.ps_stack ==>
  sym_kinds_ok cplan fn ret srest
    (ps with ps_stack := stack_dup d ps.ps_stack)
    (ss with sym_stack := EL d ss.sym_stack :: ss.sym_stack)
Proof
  rw[sym_kinds_ok_def] >> qexists `EL d top :: top` >>
  metis_tac[LIST_REL_stack_dup, LIST_REL_dup_suffix]
QED

Theorem LIST_REL_replace_equiv:
  LIST_REL R xs ys /\ d < LENGTH xs /\
  (!sv. R op sv <=> R (EL d xs) sv) ==>
  LIST_REL R (LUPDATE op d xs) ys
Proof
  rw[LIST_REL_EL_EQN, EL_LUPDATE] >> Cases_on `n = d` >> gvs[]
QED

Theorem LIST_REL_stack_poke_equiv:
  LIST_REL R (REVERSE stk) top /\ d < LENGTH stk /\
  (!sv. R op sv <=> R (stack_peek d stk) sv) ==>
  LIST_REL R (REVERSE (stack_poke d op stk)) top
Proof
  rpt strip_tac >> simp[reverse_stack_poke] >>
  metis_tac[LIST_REL_replace_equiv, stack_peek_eq_EL_REVERSE, LENGTH_REVERSE]
QED

Theorem sym_kinds_ok_poke_equiv:
  sym_kinds_ok cplan fn ret srest ps ss /\ d < LENGTH ps.ps_stack /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  operand_equiv dfg op (stack_peek d ps.ps_stack) ==>
  sym_kinds_ok cplan fn ret srest
    (ps with ps_stack := stack_poke d op ps.ps_stack) ss
Proof
  rw[sym_kinds_ok_def] >> qexists `top` >>
  simp[LIST_REL_stack_poke_equiv, op_kind_ok_operand_equiv]
QED

Theorem LIST_REL_stack_swap:
  LIST_REL R (REVERSE stk) top /\ d < LENGTH stk /\ 0 < d ==>
  LIST_REL R (REVERSE (stack_swap d stk))
    (LUPDATE (HD top) d (LUPDATE (EL d top) 0 top))
Proof
  rpt strip_tac >> simp[reverse_stack_swap, lupdate_commutes, EL] >>
  metis_tac[LIST_REL_swap, LENGTH_REVERSE]
QED

Theorem LIST_REL_swap_suffix:
  LIST_REL R (REVERSE stk) top /\ d < LENGTH stk /\ 0 < d ==>
  LUPDATE (HD (top ++ srest)) d (LUPDATE (EL d (top ++ srest)) 0 (top ++ srest)) =
    LUPDATE (HD top) d (LUPDATE (EL d top) 0 top) ++ srest
Proof
  rw[LIST_REL_EL_EQN] >>
  `top <> []` by (Cases_on `top` >> gvs[]) >>
  simp[rich_listTheory.EL_APPEND1, rich_listTheory.LUPDATE_APPEND1,
       rich_listTheory.HD_APPEND_NOT_NIL]
QED

Theorem sym_kinds_ok_swap:
  sym_kinds_ok cplan fn ret srest ps ss /\
  d < LENGTH ps.ps_stack /\ 0 < d ==>
  sym_kinds_ok cplan fn ret srest
    (ps with ps_stack := stack_swap d ps.ps_stack)
    (ss with sym_stack :=
      LUPDATE (HD ss.sym_stack) d (LUPDATE (EL d ss.sym_stack) 0 ss.sym_stack))
Proof
  rw[sym_kinds_ok_def] >>
  qexists `LUPDATE (HD top) d (LUPDATE (EL d top) 0 top)` >>
  metis_tac[LIST_REL_stack_swap, LIST_REL_swap_suffix]
QED

Theorem sym_steps_frame_compose:
  sym_steps p env m ss = SymOK mid /\
  sym_steps p env n mid = SymOK last /\
  sym_kinds_ok cplan fn ret srest out last /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + m /\
  last.sym_base.as_pc = mid.sym_base.as_pc + n /\
  (!b. ~P b ==> FLOOKUP mid.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
  (!b. ~P b ==> FLOOKUP last.sym_mem_labels b = FLOOKUP mid.sym_mem_labels b) ==>
  sym_steps p env (m+n) ss = SymOK last /\
  sym_kinds_ok cplan fn ret srest out last /\
  last.sym_base.as_pc = ss.sym_base.as_pc + (m+n) /\
  (!b. ~P b ==> FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt strip_tac >> gvs[sym_steps_add] >> metis_tac[]
QED

Theorem sym_steps_frame_empty:
  sym_kinds_ok cplan fn ret srest ps ss ==>
  sym_steps p env 0 ss = SymOK ss /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  ss.sym_base.as_pc = ss.sym_base.as_pc + 0 /\
  (!b. ~P b ==> FLOOKUP ss.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  simp[sym_steps_def]
QED
