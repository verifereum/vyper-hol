Theory cseCanonProps
Ancestors cseDefs

(* These are syntactic matching facts, not runtime value equalities. *)
Theorem operand_ids_match_length:
 !c d i s. operand_ids_match c d i s ==>
 LENGTH i.inst_operands = LENGTH s.inst_operands
Proof
 rpt gen_tac >>
 simp[operand_ids_match_def, canonical_operand_ids_def] >>
 disch_then (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]
QED

Theorem canonical_id_update:
 !c k r a. canonical_id (c |+ (k,r)) a =
 if a = k then r else canonical_id c a
Proof
 simp[canonical_id_def, finite_mapTheory.FLOOKUP_UPDATE] >>
 rpt gen_tac >> Cases_on `a = k` >> simp[]
QED

Theorem canonical_operand_ids_update_away:
 !c d i k r.
 (!op. MEM op i.inst_operands ==> operand_producer d {} op <> SOME k) ==>
 canonical_operand_ids (c |+ (k,r)) d i = canonical_operand_ids c d i
Proof
 rpt strip_tac >> simp[canonical_operand_ids_def] >>
 irule listTheory.MAP_CONG >> simp[] >> rpt strip_tac >>
 rename1 `MEM op i.inst_operands` >>
 Cases_on `operand_producer d {} op` >> simp[canonical_id_update] >>
 metis_tac[]
QED

Theorem operand_ids_match_update_away:
 !c d i s k r.
 (!op. MEM op i.inst_operands ==> operand_producer d {} op <> SOME k) /\
 (!op. MEM op s.inst_operands ==> operand_producer d {} op <> SOME k) ==>
 (operand_ids_match (c |+ (k,r)) d i s <=> operand_ids_match c d i s)
Proof
 rpt strip_tac >>
 simp[operand_ids_match_def, canonical_operand_ids_update_away]
QED

Theorem operand_ids_match_nth:
 !c d i s n.
 operand_ids_match c d i s /\ n < LENGTH i.inst_operands ==>
 (operand_producer d {} (EL n i.inst_operands) = NONE /\
  operand_producer d {} (EL n s.inst_operands) = NONE) \/
 (?a b. operand_producer d {} (EL n i.inst_operands) = SOME a /\
        operand_producer d {} (EL n s.inst_operands) = SOME b /\
        canonical_id c a = canonical_id c b)
Proof
 rpt strip_tac >>
 `LENGTH i.inst_operands = LENGTH s.inst_operands` by
   metis_tac[operand_ids_match_length] >>
 qpat_x_assum `operand_ids_match _ _ _ _` mp_tac >>
 simp[operand_ids_match_def, canonical_operand_ids_def] >>
 disch_then (mp_tac o Q.AP_TERM `EL n`) >>
 simp[listTheory.EL_MAP] >>
 Cases_on `operand_producer d {} (EL n i.inst_operands)` >>
 Cases_on `operand_producer d {} (EL n s.inst_operands)` >> simp[]
QED

Theorem operand_producer_terminal:
 !d seen op k. operand_producer d seen op = SOME k ==>
 ?v inst. FLOOKUP d.dfg_defs v = SOME inst /\ inst.inst_id = k /\
 (inst.inst_opcode <> ASSIGN \/ ~(?arg. inst.inst_operands = [arg]))
Proof
 recInduct operand_producer_ind >> rpt strip_tac >>
 gvs[Once operand_producer_def, AllCaseEqs()] >>
 metis_tac[listTheory.NOT_CONS_NIL, listTheory.CONS_11]
QED

Theorem operand_producer_none_leaf_aux[local]:
 !d visited op. !seen.
 set seen = visited /\ operand_producer d visited op = NONE ==>
 (?w. mk_operand_expr d seen op = ExprLit w) \/
 (?v. mk_operand_expr d seen op = ExprVar v)
Proof
 recInduct operand_producer_ind >> rpt strip_tac >>
 gvs[Once operand_producer_def, AllCaseEqs()] >>
 simp[availExprDefsTheory.mk_operand_expr_def,
      dfgDefsTheory.dfg_get_def_def] >>
 Cases_on `is_pseudo ASSIGN` >> simp[] >>
 first_x_assum (qspec_then `v::seen` mp_tac) >> simp[]
QED

Theorem operand_producer_none_leaf:
 !d seen op. operand_producer d (set seen) op = NONE ==>
 (?w. mk_operand_expr d seen op = ExprLit w) \/
 (?v. mk_operand_expr d seen op = ExprVar v)
Proof
 metis_tac[operand_producer_none_leaf_aux]
QED

Theorem operand_producer_none_leaf_empty:
 !d op. operand_producer d {} op = NONE ==>
 (?w. mk_operand_expr d [] op = ExprLit w) \/
 (?v. mk_operand_expr d [] op = ExprVar v)
Proof
 rpt strip_tac >>
 qspecl_then [`d`, `[]`, `op`] mp_tac operand_producer_none_leaf >> simp[]
QED

(* Static fold history: these events are not execution occurrences. *)
Definition cse_canon_inputs_def:
 cse_canon_inputs result fn =
 FLAT (MAP (\bb. MAPi (\idx inst.
   (avail_unwrap (df_at NONE result bb.bb_label idx), inst))
   bb.bb_instructions) fn.fn_blocks)
End

Definition cse_canon_record_def:
 (cse_canon_record dfg c [] = (c,[])) /\
 (cse_canon_record dfg c ((ae,inst)::xs) =
   let (last,events) =
     cse_canon_record dfg (compute_canon_inst dfg c ae inst) xs
   in (last,(c,ae,inst)::events))
End

Theorem cse_canon_record_projection:
 !xs dfg c. FST (cse_canon_record dfg c xs) =
 FOLDL (\m (ae,inst). compute_canon_inst dfg m ae inst) c xs
Proof
 Induct >> simp[cse_canon_record_def] >>
 Cases_on `h` >> simp[cse_canon_record_def] >>
 rpt gen_tac >> pairarg_tac >> gvs[] >>
 first_x_assum (qspecl_then [`dfg`, `compute_canon_inst dfg c q r`] mp_tac) >>
 simp[]
QED

Theorem cse_canon_record_prefix:
 !xs dfg initial c ae inst.
 MEM (c,ae,inst) (SND (cse_canon_record dfg initial xs)) ==>
 ?pre post. xs = pre ++ (ae,inst)::post /\
 c = FOLDL (\m (a,i). compute_canon_inst dfg m a i) initial pre
Proof
 Induct >- simp[cse_canon_record_def] >>
 Cases_on `h` >> rpt gen_tac >>
 simp[cse_canon_record_def] >> pairarg_tac >> gvs[] >>
 strip_tac
 >- (qexistsl [`[]`, `xs`] >> simp[]) >>
 first_x_assum (qspecl_then
   [`dfg`, `compute_canon_inst dfg initial q r`, `c`, `ae`, `inst`] mp_tac) >>
 simp[] >> strip_tac >>
 qexistsl [`(q,r)::pre`, `post`] >> simp[]
QED

Theorem compute_canon_inst_changed:
 !dfg c ae inst. compute_canon_inst dfg c ae inst <> c ==>
 ?src. avail_get_source ae (mk_expr dfg inst) = SOME src /\
 src.inst_id <> inst.inst_id /\ operand_ids_match c dfg inst src /\
 ~is_pseudo inst.inst_opcode /\ inst.inst_opcode <> ASSIGN /\
 ~is_terminator inst.inst_opcode /\ LENGTH inst.inst_outputs <= 1 /\
 compute_canon_inst dfg c ae inst =
 c |+ (inst.inst_id, canonical_id c src.inst_id)
Proof
 rpt gen_tac >> simp[compute_canon_inst_def] >>
 IF_CASES_TAC >- simp[] >>
 IF_CASES_TAC >- simp[] >>
 Cases_on `avail_get_source ae (mk_expr dfg inst)` >> simp[] >>
 IF_CASES_TAC >- simp[] >>
 IF_CASES_TAC >> gvs[]
QED

Theorem cse_canon_indexed_fold[local]:
 !xs c n dfg result lbl.
 FOLDL (\m (ae,inst). compute_canon_inst dfg m ae inst) c
   (MAPi (\idx inst.
     (avail_unwrap (df_at NONE result lbl (n + idx)), inst)) xs) =
 FST (FOLDL (\(m,idx) inst.
   (compute_canon_inst dfg m
     (avail_unwrap (df_at NONE result lbl idx)) inst, idx + 1)) (c,n) xs)
Proof
 Induct >> simp[indexedListsTheory.MAPi_def] >>
 rpt gen_tac >>
 simp[combinTheory.o_DEF, arithmeticTheory.ADD_ASSOC] >>
 first_x_assum (qspecl_then
   [`compute_canon_inst dfg c (avail_unwrap (df_at NONE result lbl n)) h`,
    `n+1`, `dfg`, `result`, `lbl`] mp_tac) >>
 pure_rewrite_tac[GSYM arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES] >>
 disch_then ACCEPT_TAC
QED

Theorem cse_canon_block_inputs:
 !dfg result c bb.
 FOLDL (\m (ae,inst). compute_canon_inst dfg m ae inst) c
   (MAPi (\idx inst.
     (avail_unwrap (df_at NONE result bb.bb_label idx), inst))
     bb.bb_instructions) = compute_canon_block dfg result c bb
Proof
 rpt gen_tac >>
 qspecl_then [`bb.bb_instructions`, `c`, `0`, `dfg`, `result`, `bb.bb_label`]
   mp_tac cse_canon_indexed_fold >>
 simp[compute_canon_block_def]
QED

Theorem cse_canon_blocks_inputs[local]:
 !bbs c dfg result.
 FOLDL (\m (ae,inst). compute_canon_inst dfg m ae inst) c
 (FLAT (MAP (\bb. MAPi (\idx inst.
   (avail_unwrap (df_at NONE result bb.bb_label idx), inst))
   bb.bb_instructions) bbs)) =
 FOLDL (compute_canon_block dfg result) c bbs
Proof
 Induct >> simp[rich_listTheory.FOLDL_APPEND, cse_canon_block_inputs]
QED

Theorem cse_canon_record_compute_canon:
 !dfg result fn.
 FST (cse_canon_record dfg FEMPTY (cse_canon_inputs result fn)) =
 compute_canon dfg result fn
Proof
 simp[cse_canon_record_projection, cse_canon_inputs_def,
      cse_canon_blocks_inputs, compute_canon_def]
QED
