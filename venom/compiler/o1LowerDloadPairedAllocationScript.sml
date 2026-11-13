(* Operational allocation boundaries shared by the LowerDload simulation. *)
Theory o1LowerDloadPairedAllocation
Ancestors
  venomExecSemantics venomState finite_map words venomMemProps lowerDloadDefs list rich_list

(* Allocation boundary equations: no memory is initialized by ALLOCA. *)
Theorem lower_dload_alloca_fresh:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE ==>
  exec_alloca inst s amount =
    OK (update_var out (n2w s.vs_alloca_next)
      (s with <|vs_allocas := s.vs_allocas |+
                    (inst.inst_id, (s.vs_alloca_next, w2n amount));
                vs_alloca_next := s.vs_alloca_next + w2n amount|>))
Proof
  simp[venomExecSemanticsTheory.exec_alloca_def]
QED

Theorem lower_dload_alloca_repeated:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (addr,sz) ==>
  exec_alloca inst s amount = OK (update_var out (n2w addr) s)
Proof
  simp[venomExecSemanticsTheory.exec_alloca_def]
QED

Theorem lower_dload_merge_allocation_memory:
  (merge_callee_state caller callee).vs_allocas = caller.vs_allocas /\
  (merge_callee_state caller callee).vs_alloca_next = caller.vs_alloca_next /\
  (merge_callee_state caller callee).vs_memory = callee.vs_memory
Proof
  simp[venomExecSemanticsTheory.merge_callee_state_def]
QED

Theorem lower_dload_frontier_credit_bound:
  !n m k q. m = n + 32*k /\ k <= q /\
    n + 32*q < dimword (:256) ==> m < dimword (:256)
Proof
  rpt strip_tac >> decide_tac
QED

Theorem lower_dload_frontier_credit_step:
  !n m k a:num. m = n + 32*k ==>
    m+a = (n+a) + 32*k /\ m+32 = n + 32*(k+1)
Proof
  rpt strip_tac >> decide_tac
QED

(* One effect equation covers fresh, repeated and target-only scratch sites. *)
Theorem lower_dload_alloca_frontier:
  exec_alloca inst s amount = OK t ==>
  t.vs_alloca_next = s.vs_alloca_next +
    (if FLOOKUP s.vs_allocas inst.inst_id = NONE then w2n amount else 0)
Proof
  Cases_on `inst.inst_outputs` >>
  simp[venomExecSemanticsTheory.exec_alloca_def] >>
  rename1 `inst.inst_outputs = out::outs` >>
  Cases_on `outs` >> simp[] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (simp[venomStateTheory.update_var_def] >> strip_tac >> gvs[]) >>
  PairCases_on `x` >> simp[venomStateTheory.update_var_def] >>
  strip_tac >> gvs[]
QED

Theorem lower_dload_alloca_credit:
  exec_alloca i s (amount:bytes32) = OK t /\
  exec_alloca j s' amount = OK t' /\
  (FLOOKUP s.vs_allocas i.inst_id = NONE <=>
   FLOOKUP s'.vs_allocas j.inst_id = NONE) /\
  s'.vs_alloca_next = s.vs_alloca_next + 32*k ==>
  t'.vs_alloca_next = t.vs_alloca_next + 32*k
Proof
  strip_tac >>
  qpat_x_assum `exec_alloca i _ _ = _`
    (mp_then Any assume_tac lower_dload_alloca_frontier) >>
  qpat_x_assum `exec_alloca j _ _ = _`
    (mp_then Any assume_tac lower_dload_alloca_frontier) >>
  Cases_on `FLOOKUP s.vs_allocas i.inst_id = NONE` >> gvs[] >> decide_tac
QED

Theorem lower_dload_scratch_credit:
  exec_alloca i s' (32w:bytes32) = OK t' /\
  FLOOKUP s'.vs_allocas i.inst_id = NONE /\
  s'.vs_alloca_next = s.vs_alloca_next + 32*k ==>
  t'.vs_alloca_next = s.vs_alloca_next + 32*(k+1)
Proof
  strip_tac >> drule lower_dload_alloca_frontier >>
  CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >>
  simp[] >> strip_tac >> decide_tac
QED

Theorem lower_dload_merge_credit:
  caller'.vs_alloca_next = caller.vs_alloca_next + 32*k /\
  R caller.vs_allocas caller'.vs_allocas ==>
  (merge_callee_state caller' callee').vs_alloca_next =
    (merge_callee_state caller callee).vs_alloca_next + 32*k /\
  R (merge_callee_state caller callee).vs_allocas
    (merge_callee_state caller' callee').vs_allocas
Proof
  simp[lower_dload_merge_allocation_memory]
QED

(* Metadata and returned pointers, with independent source/target bases. *)
Theorem lower_dload_paired_alloca_fresh:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  FLOOKUP t.vs_allocas inst.inst_id = NONE /\
  t.vs_alloca_next = s.vs_alloca_next + 32*k ==>
  ?s1 t1.
    exec_alloca inst s z = OK s1 /\ exec_alloca inst t z = OK t1 /\
    s1.vs_allocas = s.vs_allocas |+ (inst.inst_id,(s.vs_alloca_next,w2n z)) /\
    t1.vs_allocas = t.vs_allocas |+ (inst.inst_id,(t.vs_alloca_next,w2n z)) /\
    s1.vs_alloca_next = s.vs_alloca_next + w2n z /\
    t1.vs_alloca_next = t.vs_alloca_next + w2n z /\
    t1.vs_alloca_next = s1.vs_alloca_next + 32*k /\
    FLOOKUP s1.vs_vars out = SOME (n2w s.vs_alloca_next) /\
    FLOOKUP t1.vs_vars out = SOME (n2w t.vs_alloca_next)
Proof
  strip_tac >> imp_res_tac lower_dload_alloca_fresh >>
  simp[update_var_def, FLOOKUP_UPDATE] >> decide_tac
QED

Theorem lower_dload_paired_alloca_repeated:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (c,sz) /\
  t.vs_alloca_next = s.vs_alloca_next + 32*k ==>
  ?s1 t1.
    exec_alloca inst s z = OK s1 /\ exec_alloca inst t z = OK t1 /\
    s1.vs_allocas = s.vs_allocas /\ t1.vs_allocas = t.vs_allocas /\
    s1.vs_alloca_next = s.vs_alloca_next /\
    t1.vs_alloca_next = t.vs_alloca_next /\
    t1.vs_alloca_next = s1.vs_alloca_next + 32*k /\
    FLOOKUP s1.vs_vars out = SOME (n2w b) /\
    FLOOKUP t1.vs_vars out = SOME (n2w c)
Proof
  strip_tac >> imp_res_tac lower_dload_alloca_repeated >> simp[update_var_def, FLOOKUP_UPDATE]
QED

(* ALLOCA accepts a literal, rather than an arbitrary evaluated operand. *)
Theorem lower_dload_step_alloca:
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit z] ==>
  step_inst fuel C inst s = exec_alloca inst s z
Proof
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs]
QED

(* The three nonallocating microsteps use arbitrary supplied names and IDs.
   step_inst itself does not increment the instruction index. *)
Theorem lower_dload_copy_load_microsteps:
  eval_operand off s = SOME x /\
  FLOOKUP s.vs_vars av = SOME p /\ av <> bv /\
  FLOOKUP s.vs_labels "code_end" = SOME e ==>
  ?s2 s3 s4.
    step_inst fuel C
      <|inst_id := add_id; inst_opcode := ADD;
        inst_operands := [off; Label "code_end"]; inst_outputs := [bv]|> s = OK s2 /\
    step_inst fuel C
      <|inst_id := copy_id; inst_opcode := CODECOPY;
        inst_operands := [Var av; Var bv; Lit 32w]; inst_outputs := []|> s2 = OK s3 /\
    step_inst fuel C
      <|inst_id := load_id; inst_opcode := MLOAD;
        inst_operands := [Var av]; inst_outputs := [out]|> s3 = OK s4 /\
    s4.vs_allocas = s.vs_allocas /\ s4.vs_alloca_next = s.vs_alloca_next /\
    FLOOKUP s4.vs_vars out = SOME
      (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n (x+e)) s.vs_code ++ REPLICATE 32 0w)))
Proof
  strip_tac >>
  qabbrev_tac `bs = TAKE 32 (DROP (w2n (x+e)) s.vs_code ++ REPLICATE 32 0w)` >>
  qabbrev_tac `s2 = update_var bv (x+e) s` >>
  qabbrev_tac `s3 = write_memory_with_expansion (w2n p) bs s2` >>
  qexistsl_tac [`s2`, `s3`, `update_var out (mload (w2n p) s3) s3`] >>
  CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >>
  rpt conj_tac
  >- (simp[Abbr `s2`, step_inst_non_invoke, step_inst_base_opcode_eqs,
           exec_pure2_def, eval_operands_def, eval_operand_def, bind_outputs_def])
  >- (simp[Abbr `s2`, Abbr `s3`, Abbr `bs`, step_inst_non_invoke,
           step_inst_base_opcode_eqs, eval_operand_def, update_var_def,
           FLOOKUP_UPDATE, lookup_var_def])
  >- (simp[Abbr `s3`, Abbr `s2`, step_inst_non_invoke, step_inst_base_opcode_eqs,
           exec_read1_def, eval_operand_def, bind_outputs_def,
           write_memory_with_expansion_def, update_var_def, FLOOKUP_UPDATE, lookup_var_def])
  >- simp[Abbr `s3`, Abbr `s2`, write_memory_with_expansion_def, update_var_def]
  >- simp[Abbr `s3`, Abbr `s2`, write_memory_with_expansion_def, update_var_def] >>
  `LENGTH bs = 32` by simp[Abbr `bs`, LENGTH_TAKE] >>
  `TAKE 32 (DROP (w2n p) s3.vs_memory) = bs` by
    metis_tac[write_memory_with_expansion_read_self] >>
  `32 <= LENGTH (DROP (w2n p) s3.vs_memory)` by
    (qpat_x_assum `TAKE 32 _ = bs` (mp_tac o AP_TERM ``LENGTH:word8 list -> num``) >>
     simp[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >> rw[] >> decide_tac) >>
  fs[LENGTH_DROP] >>
  `w2n p + 32 - LENGTH s3.vs_memory = 0` by decide_tac >>
  simp[update_var_def, FLOOKUP_UPDATE, mload_def, TAKE_APPEND] >>
  simp[Abbr `bs`]
QED

Theorem lower_dload_supply_microsteps:
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\ inst.inst_outputs = [out] /\
  fresh_ir_var u = (av,u1) /\ fresh_ir_var u1 = (bv,u2) /\
  lower_dload_inst_supply u inst = (es,u') /\
  eval_operand off t = SOME x /\ off <> Var av /\
  code_layout_valid t /\
  w2n x + (LENGTH t.vs_code - LENGTH t.vs_data_section) < dimword(:256) /\
  ((FLOOKUP t.vs_allocas (EL 0 es).inst_id = NONE /\ b = t.vs_alloca_next) \/
   FLOOKUP t.vs_allocas (EL 0 es).inst_id = SOME (b,32)) /\
  b+32 < dimword(:256) ==>
  ?t1 t2 t3 t4.
    LENGTH es = 4 /\
    step_inst fuel C (EL 0 es) t = OK t1 /\
    step_inst fuel C (EL 1 es) t1 = OK t2 /\
    step_inst fuel C (EL 2 es) t2 = OK t3 /\
    step_inst fuel C (EL 3 es) t3 = OK t4 /\
    t4.vs_allocas = t.vs_allocas |+ ((EL 0 es).inst_id,(b,32)) /\
    t4.vs_alloca_next = t.vs_alloca_next +
      (if FLOOKUP t.vs_allocas (EL 0 es).inst_id = NONE then 32 else 0) /\
    FLOOKUP t4.vs_vars out = SOME
      (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n x) t.vs_data_section ++ REPLICATE 32 0w)))
Proof
  rpt gen_tac >> strip_tac >>
  `av <> bv` by metis_tac[irSupplyTheory.fresh_ir_var_two_calls_distinct] >>
  `FLOOKUP t.vs_labels "code_end" =
     SOME (n2w (LENGTH t.vs_code - LENGTH t.vs_data_section))` by
    fs[code_layout_valid_def] >>
  `DROP (w2n (x + n2w (LENGTH t.vs_code - LENGTH t.vs_data_section))) t.vs_code =
   DROP (w2n x) t.vs_data_section` by
    (gvs[code_layout_valid_def] >>
     `LENGTH prefix < dimword(:256)` by
       (CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> decide_tac) >>
     simp[word_add_def, w2n_n2w, DROP_APPEND, DROP_DROP]) >>
  gvs[lower_dload_inst_supply_def, AllCaseEqs()]
  >- (qabbrev_tac `t1 = update_var av (n2w t.vs_alloca_next)
        (t with <|vs_allocas := t.vs_allocas |+ (alloca_id,(t.vs_alloca_next,32));
                  vs_alloca_next := t.vs_alloca_next+32|>)` >>
      `step_inst fuel C
        <|inst_id := alloca_id; inst_opcode := ALLOCA;
          inst_operands := [Lit 32w]; inst_outputs := [av]|> t = OK t1` by
        simp[Abbr `t1`, step_inst_non_invoke, step_inst_base_opcode_eqs, exec_alloca_def] >>
      `t1.vs_allocas = t.vs_allocas |+ (alloca_id,(t.vs_alloca_next,32)) /\
       t1.vs_alloca_next = t.vs_alloca_next+32` by
        simp[Abbr `t1`, update_var_def] >>
      qexists_tac `t1` >> asm_rewrite_tac[] >>
      qpat_x_assum `t1.vs_allocas = _` (fn th => rewrite_tac[GSYM th]) >>
      qpat_x_assum `t1.vs_alloca_next = _` (fn th => rewrite_tac[GSYM th]) >>
      suspend "tail") >>
  qabbrev_tac `t1 = update_var av (n2w b) t` >>
  `step_inst fuel C
    <|inst_id := alloca_id; inst_opcode := ALLOCA;
      inst_operands := [Lit 32w]; inst_outputs := [av]|> t = OK t1` by
    simp[Abbr `t1`, step_inst_non_invoke, step_inst_base_opcode_eqs, exec_alloca_def] >>
  `t1.vs_allocas = t.vs_allocas |+ (alloca_id,(b,32)) /\
   t1.vs_alloca_next = t.vs_alloca_next` by
    (simp[Abbr `t1`, update_var_def, fmap_eq_flookup, FLOOKUP_UPDATE] >>
     gen_tac >> IF_CASES_TAC >> gvs[]) >>
  qexists_tac `t1` >> asm_rewrite_tac[] >>
  qpat_x_assum `t1.vs_allocas = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `t1.vs_alloca_next = _` (fn th => rewrite_tac[GSYM th]) >>
  suspend "tail"
QED

Resume lower_dload_supply_microsteps[tail]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `DROP (w2n x) t.vs_data_section =
   DROP (w2n (x + n2w (LENGTH t.vs_code - LENGTH t.vs_data_section))) t1.vs_code` by
    simp[Abbr `t1`, update_var_def] >>
  qpat_x_assum `DROP (w2n x) _ = _` (fn th => rewrite_tac[th]) >>
  irule lower_dload_copy_load_microsteps >>
  Cases_on `off` >>
  gvs[Abbr `t1`, update_var_def, FLOOKUP_UPDATE, eval_operand_def, lookup_var_def]
QED
Finalise lower_dload_supply_microsteps
