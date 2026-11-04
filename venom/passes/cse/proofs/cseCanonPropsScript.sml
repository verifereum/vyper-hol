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
