Theory lowerDloadPtrForward
Ancestors
  contextCodegenRel venomExecSemantics list rich_list pred_set

(* Interval membership is deliberately distinct from revert_forward_at:
   the latter marks only the two endpoints. *)
Theorem revert_forward_pair_interval_opcode:
  !bb i j k inst.
    revert_forward_pair bb i j /\ i <= k /\ k <= j /\
    get_instruction bb k = SOME inst ==>
    (k = i /\ inst.inst_opcode = RETURNDATACOPY) \/
    (i < k /\ k < j /\ inst.inst_opcode = ASSIGN) \/
    (k = j /\ inst.inst_opcode = REVERT)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[revert_forward_pair_def] >>
  Cases_on `k = i` >- gvs[] >>
  Cases_on `k = j` >- gvs[] >>
  `i < k /\ k < j` by decide_tac >>
  metis_tac[]
QED

Theorem resolve_block_assigns_nonvar:
  !xs op. (!v. op <> Var v) ==> resolve_block_assigns xs op = op
Proof
  Induct >> Cases_on `op` >> simp[resolve_block_assigns_def]
QED

Theorem resolve_nonassign_chunk_tail:
  !xs tail op.
    EVERY (\r. r.inst_opcode <> ASSIGN) xs ==>
    resolve_block_assigns (xs ++ tail) op =
      if ?v. op = Var v /\
             v IN BIGUNION (set (MAP (\r. set r.inst_outputs) xs))
      then op else resolve_block_assigns tail op
Proof
  Induct >> simp[resolve_block_assigns_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `op` >>
  simp[resolve_block_assigns_def, resolve_block_assigns_nonvar,
       IN_BIGUNION, MEM_MAP, PULL_EXISTS] >>
  Cases_on `MEM s h.inst_outputs` >> simp[] >>
  first_x_assum (qspec_then `tail` (qspec_then `Var s` mp_tac)) >>
  simp[IN_BIGUNION, MEM_MAP] >>
  rpt strip_tac >> rpt IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Theorem resolve_nonassign_chunk_replace:
  EVERY (\r. r.inst_opcode <> ASSIGN) ys /\ q.inst_opcode <> ASSIGN /\
  BIGUNION (set (MAP (\r. set r.inst_outputs) ys)) INTER V =
    set q.inst_outputs INTER V /\
  (!v. op = Var v ==> v IN V) ==>
  resolve_block_assigns (REVERSE ys ++ tail) op =
  resolve_block_assigns (q::tail) op
Proof
  strip_tac >>
  simp[resolve_nonassign_chunk_tail, EVERY_REVERSE] >>
  Cases_on `op` >>
  simp[resolve_block_assigns_def, resolve_block_assigns_nonvar] >>
  `s IN V` by metis_tac[] >>
  `s IN BIGUNION (set (MAP (\r. set r.inst_outputs) ys)) <=>
   MEM s q.inst_outputs` by
    (qpat_x_assum `_ INTER V = _` (mp_tac o Q.AP_TERM `\z. s IN z`) >> simp[]) >>
  gvs[MAP_REVERSE]
QED

Theorem resolve_block_assigns_chunks:
  !xs E V op.
    (!q v. MEM q xs /\ q.inst_opcode = ASSIGN /\
           MEM (Var v) q.inst_operands ==> v IN V) /\
    (!q. MEM q xs ==>
      if q.inst_opcode = ASSIGN then E q = [q]
      else EVERY (\r. r.inst_opcode <> ASSIGN) (E q) /\
           BIGUNION (set (MAP (\r. set r.inst_outputs) (E q))) INTER V =
             set q.inst_outputs INTER V) /\
    (!v. op = Var v ==> v IN V) ==>
    resolve_block_assigns (REVERSE (FLAT (MAP E xs))) op =
    resolve_block_assigns (REVERSE xs) op
Proof
  Induct using SNOC_INDUCT >- simp[resolve_block_assigns_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[MAP_SNOC, FLAT_SNOC, REVERSE_SNOC] >>
  `!z. (!v. z = Var v ==> v IN V) ==>
    resolve_block_assigns (REVERSE (FLAT (MAP E xs))) z =
    resolve_block_assigns (REVERSE xs) z` by
    (rpt strip_tac >> first_x_assum irule >>
     qexists_tac `V` >> metis_tac[]) >>
  Cases_on `x.inst_opcode = ASSIGN`
  >- (`E x = [x]` by metis_tac[] >>
      simp[REVERSE_APPEND, resolve_block_assigns_def] >>
      Cases_on `op` >> simp[resolve_block_assigns_def,
        resolve_block_assigns_nonvar] >>
      Cases_on `MEM s x.inst_outputs` >> simp[] >>
      Cases_on `x.inst_outputs = [s] /\ LENGTH x.inst_operands = 1` >>
      simp[] >>
      qpat_x_assum `!z. _` irule >> rpt strip_tac >>
      `MEM (HD x.inst_operands) x.inst_operands` by
        (Cases_on `x.inst_operands` >> gvs[]) >> metis_tac[]) >>
  `resolve_block_assigns
     (REVERSE (E x) ++ REVERSE (FLAT (MAP E xs))) op =
   resolve_block_assigns (x::REVERSE (FLAT (MAP E xs))) op` by
    (irule resolve_nonassign_chunk_replace >> simp[] >>
     conj_tac >- (qexists_tac `V` >> metis_tac[]) >> metis_tac[]) >>
  simp[REVERSE_APPEND] >>
  asm_rewrite_tac[] >> Cases_on `op` >>
  simp[resolve_block_assigns_def, resolve_block_assigns_nonvar] >>
  Cases_on `MEM s x.inst_outputs` >> simp[]
QED
