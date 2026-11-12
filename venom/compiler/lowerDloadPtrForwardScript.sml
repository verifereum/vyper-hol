Theory lowerDloadPtrForward
Ancestors
  contextCodegenRel venomExecSemantics ptrDiscipline venomState
  list rich_list pred_set finite_map lowerDloadDefs irSupply
  o1PassContract lowerDloadSupplyProofs venomWf o1ContractLowerDload
  venomInst arithmetic

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

Theorem same_after_nonassign_chunk:
  !xs tail a b.
    EVERY (\r. r.inst_opcode <> ASSIGN) xs ==>
    same_after_assigns (xs ++ tail) a b =
      (a = b \/
       ((~?v. a = Var v /\
          v IN BIGUNION (set (MAP (\r. set r.inst_outputs) xs))) /\
        (~?v. b = Var v /\
          v IN BIGUNION (set (MAP (\r. set r.inst_outputs) xs))) /\
        same_after_assigns tail a b))
Proof
  Induct
  >- (rpt gen_tac >> Cases_on `a = b` >> simp[] >>
      Cases_on `tail` >> simp[same_after_assigns_def]) >>
  simp[same_after_assigns_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `a = b` >- gvs[] >>
  Cases_on `a` >> Cases_on `b` >>
  simp[same_after_assigns_def, step_back_assign_def,
       IN_BIGUNION, MEM_MAP, PULL_EXISTS] >>
  rpt IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Theorem same_after_nonassign_chunk_replace:
  EVERY (\r. r.inst_opcode <> ASSIGN) ys /\ q.inst_opcode <> ASSIGN /\
  BIGUNION (set (MAP (\r. set r.inst_outputs) ys)) INTER V =
    set q.inst_outputs INTER V /\
  (!v. a = Var v ==> v IN V) /\ (!v. b = Var v ==> v IN V) ==>
  same_after_assigns (REVERSE ys ++ tail) a b =
  same_after_assigns (q::tail) a b
Proof
  strip_tac >>
  simp[same_after_nonassign_chunk, EVERY_REVERSE, MAP_REVERSE,
       same_after_assigns_def] >>
  Cases_on `a = b` >- simp[] >>
  `!v. v IN V ==>
     (v IN BIGUNION (set (MAP (\r. set r.inst_outputs) ys)) <=>
      MEM v q.inst_outputs)` by
    (rpt strip_tac >>
     qpat_x_assum `_ INTER V = _` (mp_tac o Q.AP_TERM `\z. v IN z`) >> simp[]) >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[step_back_assign_def] >> rpt IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Theorem same_after_assigns_chunks:
  !xs E V a b.
    (!q v. MEM q xs /\ q.inst_opcode = ASSIGN /\
           MEM (Var v) q.inst_operands ==> v IN V) /\
    (!q. MEM q xs ==>
      if q.inst_opcode = ASSIGN then E q = [q]
      else EVERY (\r. r.inst_opcode <> ASSIGN) (E q) /\
           BIGUNION (set (MAP (\r. set r.inst_outputs) (E q))) INTER V =
             set q.inst_outputs INTER V) /\
    (!v. a = Var v ==> v IN V) /\ (!v. b = Var v ==> v IN V) ==>
    same_after_assigns (REVERSE (FLAT (MAP E xs))) a b =
    same_after_assigns (REVERSE xs) a b
Proof
  Induct using SNOC_INDUCT >- simp[same_after_assigns_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[MAP_SNOC, FLAT_SNOC, REVERSE_SNOC] >>
  `!z w. (!v. z = Var v ==> v IN V) /\ (!v. w = Var v ==> v IN V) ==>
    same_after_assigns (REVERSE (FLAT (MAP E xs))) z w =
    same_after_assigns (REVERSE xs) z w` by
    (rpt strip_tac >> first_x_assum irule >> qexists `V` >> metis_tac[]) >>
  qpat_x_assum `!E V a b. _` kall_tac >>
  Cases_on `a = b`
  >- (gvs[] >> Cases_on `REVERSE (E x) ++ REVERSE (FLAT (MAP E xs))` >>
      simp[same_after_assigns_def]) >>
  Cases_on `x.inst_opcode = ASSIGN`
  >- (`E x = [x]` by metis_tac[] >>
      simp[REVERSE_APPEND, same_after_assigns_def] >>
      Cases_on `a` >> Cases_on `b` >>
      gvs[step_back_assign_def] >> rpt IF_CASES_TAC >> gvs[] >>
      first_x_assum irule >> rpt strip_tac >>
      `MEM (HD x.inst_operands) x.inst_operands` by
        (Cases_on `x.inst_operands` >> gvs[]) >>
      qpat_x_assum `!q v. _` (qspec_then `x` mp_tac) >>
      gvs[] >> metis_tac[]) >>
  `same_after_assigns (REVERSE (E x) ++ REVERSE (FLAT (MAP E xs))) a b =
   same_after_assigns (x::REVERSE (FLAT (MAP E xs))) a b` by
    (irule same_after_nonassign_chunk_replace >> simp[] >>
     conj_tac >- (qexists `V` >> metis_tac[]) >> metis_tac[]) >>
  simp[REVERSE_APPEND] >> asm_rewrite_tac[] >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[same_after_assigns_def, step_back_assign_def] >>
  rpt IF_CASES_TAC >> gvs[]
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

(* A definition-interface probe: ASSIGN out_taint tests definedness before
   copying operand taint. Equal variable taints alone do not suffice. *)
Theorem forwarding_taint_definedness_probe:
  !i s.
  let inst = i with <| inst_opcode := ASSIGN;
                       inst_operands := [Var "x"]; inst_outputs := ["y"] |>;
      tn = entry_taint with t_var := FEMPTY |+ ("x", {0});
      a = s with vs_vars := FEMPTY |+ ("x", 0w);
      b = s with vs_vars := FEMPTY
  in
    (!v. op_taint tn (Var v) = op_taint tn (Var v)) /\
    op_taint (step_taint inst a a tn) (Var "y") = {0} /\
    op_taint (step_taint inst b b tn) (Var "y") = {} /\
    op_taint (step_taint inst a a tn) (Var "y") <>
      op_taint (step_taint inst b b tn) (Var "y")
Proof
  simp[step_taint_def, out_taint_def, op_taint_def,
       set_var_taint_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem forwarding_step_var_taint:
  (inst.inst_opcode = ASSIGN \/ inst.inst_opcode = RETURNDATACOPY) /\
  (!v. v IN V ==> op_taint tn (Var v) = op_taint un (Var v)) /\
  (!v. MEM (Var v) inst.inst_operands ==> v IN V) /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) ==>
  !v. v IN V ==>
    op_taint (step_taint inst s s' tn) (Var v) =
    op_taint (step_taint inst t t' un) (Var v)
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> op_taint tn op = op_taint un op` by
    (Cases >> simp[op_taint_def] >> metis_tac[op_taint_def]) >>
  `out_taint tn inst s = out_taint un inst t` by
    (Cases_on `inst.inst_operands` >- simp[out_taint_def] >>
     rename1 `inst.inst_operands = a::rest` >>
     Cases_on `rest`
     >- (simp[out_taint_def] >>
         Cases_on `eval_operand a s` >>
         Cases_on `eval_operand a t` >> gvs[] >> metis_tac[]) >>
     rename1 `inst.inst_operands = a::b::rest` >>
     Cases_on `rest` >> simp[out_taint_def] >>
     Cases_on `eval_operand a s` >>
     Cases_on `eval_operand a t` >> gvs[]) >>
  (rpt strip_tac >>
  `op_taint tn (Var v) = op_taint un (Var v)` by metis_tac[] >>
  fs[op_taint_def] >>
  simp[step_taint_def, op_taint_def, set_var_taint_def] >>
  Cases_on `inst.inst_outputs`
  >- simp[FLOOKUP_DRESTRICT] >>
  rename1 `inst.inst_outputs = dst::outs` >>
  Cases_on `outs` >> simp[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt IF_CASES_TAC >> simp[])
QED

(* DLOADBYTES accepts arbitrary outputs syntactically, but drops them.
   A source-shape premise is necessary for configured resolver transport. *)
Theorem dloadbytes_resolver_shape_probe:
  let supply = <| irs_next_inst := 0; irs_next_var := 0;
                  irs_next_label := 0; irs_used_inst_ids := [];
                  irs_used_vars := ["x"]; irs_used_labels := [] |>;
      a = <| inst_id := 10; inst_opcode := ASSIGN;
             inst_operands := [Lit 7w]; inst_outputs := ["x"] |>;
      b = <| inst_id := 11; inst_opcode := DLOADBYTES;
             inst_operands := [Lit 0w; Lit 0w; Lit 0w];
             inst_outputs := ["x"] |>
  in
    {"x"} SUBSET set supply.irs_used_vars /\
    (!q v. MEM q [a;b] /\ MEM (Var v) q.inst_operands ==> v IN {"x"}) /\
    resolve_block_assigns (REVERSE [a;b]) (Var "x") = Var "x" /\
    resolve_block_assigns
      (REVERSE (FST (lower_dload_insts_supply supply [a;b]))) (Var "x") = Lit 7w
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem o1_ctx_shape_dloadbytes_outputs:
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\
  MEM bb fn.fn_blocks /\ MEM q bb.bb_instructions /\
  q.inst_opcode = DLOADBYTES ==> q.inst_outputs = []
Proof
  strip_tac >>
  `o1_fn_shape C fn` by
    (gvs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `inst_wf q` by
    (gvs[o1_fn_shape_def, fn_inst_wf_def] >> metis_tac[]) >>
  gvs[inst_wf_def]
QED

Theorem lower_dload_inst_supply_resolver_footprint:
  lower_dload_inst_supply s q = (ys,t) /\
  V SUBSET set s.irs_used_vars /\
  (q.inst_opcode = DLOADBYTES ==> q.inst_outputs = []) ==>
  (q.inst_opcode = ASSIGN ==> ys = [q]) /\
  (q.inst_opcode <> ASSIGN ==>
    EVERY (\r. r.inst_opcode <> ASSIGN) ys /\
    BIGUNION (set (MAP (\r. set r.inst_outputs) ys)) INTER V =
      set q.inst_outputs INTER V)
Proof
  Cases_on `q.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac (cj 1 fresh_ir_var_contract) >>
      imp_res_tac (cj 2 fresh_ir_var_contract) >>
      gvs[SUBSET_DEF] >>
      `~(alloca_v IN V) /\ ~(add_v IN V)` by metis_tac[] >>
      simp[EXTENSION] >> metis_tac[]) >>
  Cases_on `q.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac (cj 1 fresh_ir_var_contract) >>
      gvs[SUBSET_DEF] >>
      `~(add_v IN V)` by metis_tac[] >> simp[EXTENSION]) >>
  simp[lower_dload_inst_supply_def] >> rpt strip_tac >> gvs[]
QED

Theorem lower_dload_inst_supply_used_vars:
  lower_dload_inst_supply s q = (ys,t) ==>
  set s.irs_used_vars SUBSET set t.irs_used_vars
Proof
  Cases_on `q.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac (cj 2 fresh_ir_var_contract) >> gvs[SUBSET_DEF]) >>
  Cases_on `q.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac (cj 2 fresh_ir_var_contract) >> gvs[SUBSET_DEF]) >>
  simp[lower_dload_inst_supply_def]
QED

Theorem lower_dload_insts_supply_used_vars:
  !xs s ys t. lower_dload_insts_supply s xs = (ys,t) ==>
    set s.irs_used_vars SUBSET set t.irs_used_vars
Proof
  Induct >> simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  drule lower_dload_inst_supply_used_vars >>
  first_x_assum drule >> metis_tac[SUBSET_TRANS]
QED

Theorem lower_dload_insts_supply_resolve:
  !ins s outs t V op.
  lower_dload_insts_supply s ins = (outs,t) /\
  V SUBSET set s.irs_used_vars /\
  (!q v. MEM q ins /\ MEM (Var v) q.inst_operands ==> v IN V) /\
  (!q. MEM q ins /\ q.inst_opcode = DLOADBYTES ==> q.inst_outputs = []) /\
  (!v. op = Var v ==> v IN V) ==>
  resolve_block_assigns (REVERSE outs) op =
    resolve_block_assigns (REVERSE ins) op
Proof
  Induct using SNOC_INDUCT >- simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lower_dload_insts_supply _ _ = _` mp_tac >>
  rewrite_tac[SNOC_APPEND] >>
  strip_tac >> drule_then strip_assume_tac lower_dload_insts_supply_append >>
  gvs[lower_dload_insts_supply_def, AllCaseEqs()] >>
  `V SUBSET set u.irs_used_vars` by
    (drule lower_dload_insts_supply_used_vars >> metis_tac[SUBSET_TRANS]) >>
  drule lower_dload_inst_supply_resolver_footprint >>
  disch_then (qspec_then `V` mp_tac) >> simp[] >>
  strip_tac >>
  `!z. (!v. z = Var v ==> v IN V) ==>
     resolve_block_assigns (REVERSE ys) z =
     resolve_block_assigns (REVERSE ins) z` by
    (rpt strip_tac >> first_x_assum irule >>
     qexistsl_tac [`V`, `s`, `u`] >> metis_tac[]) >>
  Cases_on `x.inst_opcode = ASSIGN`
  >- (`zs = [x]` by metis_tac[] >>
      simp[REVERSE_APPEND, resolve_block_assigns_def] >>
      Cases_on `op` >> simp[resolve_block_assigns_def,
        resolve_block_assigns_nonvar] >>
      Cases_on `MEM s' x.inst_outputs` >> simp[] >>
      Cases_on `x.inst_outputs = [s'] /\ LENGTH x.inst_operands = 1` >>
      simp[] >>
      qpat_x_assum `!z. _` irule >> rpt strip_tac >>
      `MEM (HD x.inst_operands) x.inst_operands` by
        (Cases_on `x.inst_operands` >> gvs[]) >> metis_tac[]) >>
  `resolve_block_assigns (REVERSE zs ++ REVERSE ys) op =
   resolve_block_assigns (x::REVERSE ys) op` by
    (irule resolve_nonassign_chunk_replace >> simp[] >>
     qexists_tac `V` >> metis_tac[]) >>
  simp[REVERSE_APPEND] >> asm_rewrite_tac[] >>
  Cases_on `op` >> simp[resolve_block_assigns_def,
    resolve_block_assigns_nonvar] >>
  Cases_on `MEM s' x.inst_outputs` >> simp[]
QED

Theorem lower_dload_insts_supply_unchanged:
  !xs s. EVERY (\q. ~MEM q.inst_opcode [DLOAD; DLOADBYTES]) xs ==>
    lower_dload_insts_supply s xs = (xs,s)
Proof
  Induct >> simp[lower_dload_insts_supply_def] >> rpt strip_tac >>
  simp[lower_dload_inst_supply_def]
QED

Theorem lower_dload_insts_supply_prefix:
  lower_dload_insts_supply s xs = (ys,t) /\ n <= LENGTH xs ==>
  ?ps u qs. lower_dload_insts_supply s (TAKE n xs) = (ps,u) /\
    lower_dload_insts_supply u (DROP n xs) = (qs,t) /\ ys = ps ++ qs
Proof
  strip_tac >>
  `xs = TAKE n xs ++ DROP n xs` by simp[] >>
  metis_tac[lower_dload_insts_supply_append]
QED

Theorem lower_dload_insts_supply_at_unchanged:
  !n xs s ys t q.
  lower_dload_insts_supply s xs = (ys,t) /\ n < LENGTH xs /\
  EL n xs = q /\ ~MEM q.inst_opcode [DLOAD; DLOADBYTES] ==>
  ?ps u qs. lower_dload_insts_supply s (TAKE n xs) = (ps,u) /\
    lower_dload_insts_supply u (DROP (SUC n) xs) = (qs,t) /\
    ys = ps ++ q::qs
Proof
  Induct
  >- (Cases >> simp[lower_dload_insts_supply_def] >>
      rpt gen_tac >> strip_tac >>
      `lower_dload_inst_supply s h = ([h],s)` by
        (irule lower_dload_inst_supply_special >> simp[]) >>
      gvs[AllCaseEqs()] >> metis_tac[]) >>
  Cases >> simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  qexistsl_tac [`out ++ ps`, `u`, `qs`] >>
  simp[lower_dload_insts_supply_def] >> metis_tac[APPEND_ASSOC]
QED

Theorem revert_forward_pair_middle_assigns:
  revert_forward_pair bb i j ==>
  EVERY (\q. q.inst_opcode = ASSIGN)
    (TAKE (j - SUC i) (DROP (SUC i) bb.bb_instructions))
Proof
  strip_tac >> gvs[revert_forward_pair_def] >>
  `j < LENGTH bb.bb_instructions` by
    (gvs[get_instruction_def, AllCaseEqs()]) >>
  `j - SUC i <= LENGTH (DROP (SUC i) bb.bb_instructions)` by
    (simp[LENGTH_DROP] >> decide_tac) >>
  simp[EVERY_EL] >> rpt strip_tac >>
  `i < SUC i + n /\ SUC i + n < j /\
   SUC i + n < LENGTH bb.bb_instructions` by
    (gvs[LENGTH_TAKE, LENGTH_DROP] >> decide_tac) >>
  `get_instruction bb (SUC i + n) =
    SOME (EL (SUC i + n) bb.bb_instructions)` by
    simp[get_instruction_def] >>
  `(EL (SUC i + n) bb.bb_instructions).inst_opcode = ASSIGN` by metis_tac[] >>
  gvs[EL_TAKE, EL_DROP, ADD_COMM]
QED

Theorem take_between_endpoints[local]:
  !i j xs. i < j /\ j < LENGTH xs ==>
    TAKE j xs = TAKE i xs ++ EL i xs ::
      TAKE (j - SUC i) (DROP (SUC i) xs)
Proof
  Induct >> Cases_on `xs` >> Cases_on `j` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem lower_dload_insts_supply_prefix_resolve:
  lower_dload_insts_supply s (TAKE n xs) = (ps,u) /\
  V SUBSET set s.irs_used_vars /\
  (!q v. MEM q xs /\ MEM (Var v) q.inst_operands ==> v IN V) /\
  (!q. MEM q xs /\ q.inst_opcode = DLOADBYTES ==> q.inst_outputs = []) /\
  (!v. op = Var v ==> v IN V) ==>
  resolve_block_assigns (REVERSE ps) op =
    resolve_block_assigns (REVERSE (TAKE n xs)) op
Proof
  strip_tac >> irule lower_dload_insts_supply_resolve >>
  conj_tac >- metis_tac[MEM_TAKE] >>
  qexistsl_tac [`V`, `s`, `u`] >> simp[] >>
  metis_tac[MEM_TAKE]
QED

Theorem lower_dload_insts_supply_same_after:
  !ins s outs t V a b.
  lower_dload_insts_supply s ins = (outs,t) /\
  V SUBSET set s.irs_used_vars /\
  (!q v. MEM q ins /\ MEM (Var v) q.inst_operands ==> v IN V) /\
  (!q. MEM q ins /\ q.inst_opcode = DLOADBYTES ==> q.inst_outputs = []) /\
  (!v. a = Var v ==> v IN V) /\ (!v. b = Var v ==> v IN V) ==>
  same_after_assigns (REVERSE outs) a b = same_after_assigns (REVERSE ins) a b
Proof
  Induct using SNOC_INDUCT >- simp[lower_dload_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lower_dload_insts_supply _ _ = _` mp_tac >>
  rewrite_tac[SNOC_APPEND] >> strip_tac >>
  drule_then strip_assume_tac lower_dload_insts_supply_append >> gvs[] >>
  qpat_assum `lower_dload_insts_supply s ins = _`
    (mp_then Any mp_tac lower_dload_insts_supply_used_vars) >> strip_tac >>
  `V SUBSET set u.irs_used_vars` by
    (irule SUBSET_TRANS >> qexists `set s.irs_used_vars` >> simp[]) >>
  gvs[lower_dload_insts_supply_def, AllCaseEqs()] >>
  `x.inst_opcode = DLOADBYTES ==> x.inst_outputs = []` by metis_tac[] >>
  drule_all lower_dload_inst_supply_resolver_footprint >> strip_tac >>
  `!z w. (!v. z = Var v ==> v IN V) /\ (!v. w = Var v ==> v IN V) ==>
    same_after_assigns (REVERSE ys) z w = same_after_assigns (REVERSE ins) z w` by
    (rpt strip_tac >> first_x_assum irule >>
     qexistsl [`V`,`s`,`u`] >> metis_tac[]) >>
  qpat_x_assum `!s outs t V a b. _` kall_tac >>
  Cases_on `a = b`
  >- (gvs[] >> Cases_on `REVERSE zs ++ REVERSE ys` >> simp[same_after_assigns_def]) >>
  Cases_on `x.inst_opcode = ASSIGN`
  >- (`zs = [x]` by metis_tac[] >>
      simp[REVERSE_APPEND, same_after_assigns_def] >>
      Cases_on `a` >> Cases_on `b` >> gvs[step_back_assign_def] >>
      rpt IF_CASES_TAC >> gvs[] >> first_x_assum irule >> rpt strip_tac >>
      `MEM (HD x.inst_operands) x.inst_operands` by
        (Cases_on `x.inst_operands` >> gvs[]) >>
      qpat_x_assum `!q v. _` (qspec_then `x` mp_tac) >> gvs[] >> metis_tac[]) >>
  `same_after_assigns (REVERSE zs ++ REVERSE ys) a b =
   same_after_assigns (x::REVERSE ys) a b` by
    (irule same_after_nonassign_chunk_replace >> simp[] >> qexists `V` >> metis_tac[]) >>
  simp[REVERSE_APPEND] >> asm_rewrite_tac[] >>
  Cases_on `a` >> Cases_on `b` >> gvs[same_after_assigns_def, step_back_assign_def] >>
  rpt IF_CASES_TAC >> gvs[]
QED

Theorem resolve_block_assigns_tracked:
  !xs op V.
    (!q v. MEM q xs /\ q.inst_opcode = ASSIGN /\ MEM (Var v) q.inst_operands ==> v IN V) /\
    (!v. op = Var v ==> v IN V) ==>
    !v. resolve_block_assigns xs op = Var v ==> v IN V
Proof
  Induct >> simp[resolve_block_assigns_def] >> rpt gen_tac >> strip_tac >>
  `!z. (!v. z = Var v ==> v IN V) ==>
    !v. resolve_block_assigns xs z = Var v ==> v IN V` by
    (rpt strip_tac >> first_x_assum (drule_at (Pat `resolve_block_assigns`)) >>
     simp[] >> disch_then irule >> metis_tac[]) >>
  qpat_x_assum `!op V. (!q v. _) /\ _ ==> _` kall_tac >>
  `LENGTH h.inst_operands = 1 ==>
    !v. HD h.inst_operands = Var v /\ h.inst_opcode = ASSIGN ==> v IN V` by
    (strip_tac >> rpt strip_tac >>
     `MEM (HD h.inst_operands) h.inst_operands` by
       (Cases_on `h.inst_operands` >> gvs[]) >>
     qpat_x_assum `!q v. _` (qspec_then `h` mp_tac) >> gvs[] >> metis_tac[]) >>
  Cases_on `op` >> simp[resolve_block_assigns_def] >>
  rpt IF_CASES_TAC >> gvs[] >> rpt strip_tac >>
  qpat_x_assum `!z. _` (drule_at (Pat `resolve_block_assigns`)) >> simp[]
QED

Theorem lower_dload_insts_supply_prefix_same_after:
  lower_dload_insts_supply s (TAKE n xs) = (ps,u) /\
  V SUBSET set s.irs_used_vars /\
  (!q v. MEM q xs /\ MEM (Var v) q.inst_operands ==> v IN V) /\
  (!q. MEM q xs /\ q.inst_opcode = DLOADBYTES ==> q.inst_outputs = []) /\
  (!v. a = Var v ==> v IN V) /\ (!v. b = Var v ==> v IN V) ==>
  same_after_assigns (REVERSE ps) a b = same_after_assigns (REVERSE (TAKE n xs)) a b
Proof
  strip_tac >> irule lower_dload_insts_supply_same_after >>
  conj_tac >- metis_tac[MEM_TAKE] >>
  qexistsl [`V`,`s`,`u`] >> simp[] >> metis_tac[MEM_TAKE]
QED

Theorem lower_dload_insts_supply_forward_pair:
  lower_dload_insts_supply s bb.bb_instructions = (ys,t) /\
  V SUBSET set s.irs_used_vars /\
  (!q v. MEM q bb.bb_instructions /\ MEM (Var v) q.inst_operands ==> v IN V) /\
  (!q. MEM q bb.bb_instructions /\ q.inst_opcode = DLOADBYTES ==>
       q.inst_outputs = []) /\
  revert_forward_pair bb i j ==>
  ?prei si pj sj.
    lower_dload_insts_supply s (TAKE i bb.bb_instructions) = (prei,si) /\
    lower_dload_insts_supply s (TAKE j bb.bb_instructions) = (pj,sj) /\
    revert_forward_pair (bb with bb_instructions := ys) (LENGTH prei) (LENGTH pj)
Proof
  strip_tac >>
  `EVERY (\q. q.inst_opcode = ASSIGN)
    (TAKE (j - SUC i) (DROP (SUC i) bb.bb_instructions))` by
    metis_tac[revert_forward_pair_middle_assigns] >>
  qpat_x_assum `revert_forward_pair _ _ _` mp_tac >>
  rewrite_tac[revert_forward_pair_def] >> strip_tac >>
  `i < LENGTH bb.bb_instructions /\ j < LENGTH bb.bb_instructions /\
   EL i bb.bb_instructions = inst1 /\ EL j bb.bb_instructions = inst2` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `?prei si qi. lower_dload_insts_supply s (TAKE i bb.bb_instructions) = (prei,si) /\
    lower_dload_insts_supply si (DROP (SUC i) bb.bb_instructions) = (qi,t) /\
    ys = prei ++ inst1::qi` by
    (irule lower_dload_insts_supply_at_unchanged >> simp[]) >>
  `?pj sj qj. lower_dload_insts_supply s (TAKE j bb.bb_instructions) = (pj,sj) /\
    lower_dload_insts_supply sj (DROP (SUC j) bb.bb_instructions) = (qj,t) /\
    ys = pj ++ inst2::qj` by
    (irule lower_dload_insts_supply_at_unchanged >> simp[]) >>
  qmatch_asmsub_abbrev_tac `EVERY _ mid` >>
  `TAKE j bb.bb_instructions = TAKE i bb.bb_instructions ++ inst1::mid` by
    (drule_all take_between_endpoints >> simp[Abbr `mid`]) >>
  `lower_dload_insts_supply si mid = (mid,si)` by
    (irule lower_dload_insts_supply_unchanged >>
     gvs[EVERY_MEM] >> metis_tac[]) >>
  `pj = prei ++ inst1::mid` by
    (qpat_x_assum `lower_dload_insts_supply s (TAKE j _) = _` mp_tac >>
     asm_rewrite_tac[] >> strip_tac >>
     drule_then strip_assume_tac lower_dload_insts_supply_append >>
     gvs[lower_dload_insts_supply_def, lower_dload_inst_supply_def]) >>
  `!a b. (!v. a = Var v ==> v IN V) /\ (!v. b = Var v ==> v IN V) ==>
    same_after_assigns (REVERSE prei) a b =
    same_after_assigns (REVERSE (TAKE i bb.bb_instructions)) a b` by
    (rpt strip_tac >> irule lower_dload_insts_supply_prefix_same_after >>
     simp[] >> qexistsl [`V`,`s`,`si`] >> metis_tac[]) >>
  `MEM inst1 bb.bb_instructions /\ MEM inst2 bb.bb_instructions` by
    metis_tac[MEM_EL] >>
  `!v. p = Var v \/ src = Var v \/ rds = Var v \/ p' = Var v \/ rds' = Var v ==> v IN V` by
    (qpat_assum `!q v. MEM q bb.bb_instructions /\ _ ==> _`
       (qspec_then `inst1` mp_tac) >>
     qpat_assum `!q v. MEM q bb.bb_instructions /\ _ ==> _`
       (qspec_then `inst2` mp_tac) >> simp[] >> metis_tac[]) >>
  `!op v. (!v. op = Var v ==> v IN V) /\
     resolve_block_assigns (REVERSE mid) op = Var v ==> v IN V` by
    (rpt strip_tac >> irule resolve_block_assigns_tracked >>
     qexistsl [`op`,`REVERSE mid`] >> simp[] >>
     rpt strip_tac >> qpat_x_assum `!q v. MEM q bb.bb_instructions /\ _ ==> _`
       (qspec_then `q` mp_tac) >> simp[] >>
     `MEM q bb.bb_instructions` by
       (qpat_x_assum `MEM q mid` mp_tac >> simp[Abbr `mid`] >>
        rpt (pop_assum kall_tac) >> strip_tac >>
        drule MEM_TAKE >> strip_tac >>
        `TAKE (SUC i) bb.bb_instructions ++ DROP (SUC i) bb.bb_instructions =
          bb.bb_instructions` by simp[] >>
        metis_tac[MEM_APPEND]) >> metis_tac[]) >>
  `same_after_assigns (REVERSE prei) src (Lit 0w) /\
   same_after_assigns (REVERSE prei) p (resolve_block_assigns (REVERSE mid) p') /\
   same_after_assigns (REVERSE prei) rds (resolve_block_assigns (REVERSE mid) rds')` by
    (rpt conj_tac >>
     qpat_x_assum `!a b. _ ==> (same_after_assigns _ _ _ = _)`
       (fn th => dep_rewrite.DEP_REWRITE_TAC [th]) >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`prei`, `si`, `pj`, `sj`] >> simp[] >>
  conj_tac >- suspend "middle" >>
  suspend "endpoints"
QED

Resume lower_dload_insts_supply_forward_pair[middle]:
  qpat_x_assum `EVERY _ mid` mp_tac >>
  rpt (pop_assum kall_tac) >> strip_tac >> rpt strip_tac >>
  `~(k < LENGTH prei) /\ k - LENGTH prei <> 0 /\
   k - LENGTH prei - 1 < LENGTH mid` by decide_tac >>
  gvs[get_instruction_def, EL_APPEND, EL_CONS, AllCaseEqs()] >>
  gvs[EVERY_EL]
QED

Resume lower_dload_insts_supply_forward_pair[endpoints]:
  qexistsl_tac [`inst1`, `inst2`, `p`, `src`, `rds`, `p'`, `rds'`] >>
  `LENGTH prei - (LENGTH prei + SUC (LENGTH mid)) = 0` by decide_tac >>
  simp[get_instruction_def, EL_APPEND, EL_CONS, TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >>
  `LENGTH prei + SUC (LENGTH mid) - SUC (LENGTH prei) = LENGTH mid /\
   LENGTH prei - SUC (LENGTH prei) = 0 /\
   DROP (SUC (LENGTH prei)) prei = []` by
    (simp[DROP_EQ_NIL] >> decide_tac) >>
  simp[DROP_APPEND, DROP_def, TAKE_APPEND]
QED

Finalise lower_dload_insts_supply_forward_pair


(* The configured consumer obtains the resolver's shape premise from the
   source context, not from an additional pass-stage assumption. *)
Theorem lower_dload_block_supply_forward_pair:
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\ MEM bb fn.fn_blocks /\
  lower_dload_block_supply s bb = (bb',t) /\
  V SUBSET set s.irs_used_vars /\
  (!q v. MEM q bb.bb_instructions /\ MEM (Var v) q.inst_operands ==> v IN V) /\
  revert_forward_pair bb i j ==>
  ?prei si prej sj.
    lower_dload_insts_supply s (TAKE i bb.bb_instructions) = (prei,si) /\
    lower_dload_insts_supply s (TAKE j bb.bb_instructions) = (prej,sj) /\
    revert_forward_pair bb' (LENGTH prei) (LENGTH prej)
Proof
  strip_tac >>
  `!q. MEM q bb.bb_instructions /\ q.inst_opcode = DLOADBYTES ==>
       q.inst_outputs = []` by metis_tac[o1_ctx_shape_dloadbytes_outputs] >>
  gvs[lower_dload_block_supply_def, AllCaseEqs()] >>
  irule lower_dload_insts_supply_forward_pair >> metis_tac[]
QED
