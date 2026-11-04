Theory o1LowerDloadSuppliedSegmentExec
Ancestors
  o1LowerDloadPairedAllocation lowerDloadDefs irSupply
  venomExecSemantics venomState finite_map words list rich_list

(* The allocation helper theory predates the current task edit boundary.
   Recover exact witnesses from its existing execution packet, without editing it. *)
Theorem ld_copy_load_exact:
  eval_operand off s = SOME x /\
  FLOOKUP s.vs_vars av = SOME p /\ av <> bv /\
  FLOOKUP s.vs_labels "code_end" = SOME e ==>
  let bs = TAKE 32 (DROP (w2n (x+e)) s.vs_code ++ REPLICATE 32 0w);
      s2 = update_var bv (x+e) s;
      s3 = write_memory_with_expansion (w2n p) bs s2;
      s4 = update_var out (word_of_bytes T (0w:bytes32) bs) s3
  in
    step_inst fuel C
      <|inst_id := add_id; inst_opcode := ADD;
        inst_operands := [off; Label "code_end"]; inst_outputs := [bv]|> s = OK s2 /\
    step_inst fuel C
      <|inst_id := copy_id; inst_opcode := CODECOPY;
        inst_operands := [Var av; Var bv; Lit 32w]; inst_outputs := []|> s2 = OK s3 /\
    step_inst fuel C
      <|inst_id := load_id; inst_opcode := MLOAD;
        inst_operands := [Var av]; inst_outputs := [out]|> s3 = OK s4
Proof
  strip_tac >> drule_all lower_dload_copy_load_microsteps >>
  disch_then (qspec_then `out` mp_tac) >>
  CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
       exec_pure2_def, eval_operands_def, eval_operand_def, bind_outputs_def,
       update_var_def, FLOOKUP_UPDATE, lookup_var_def] >>
  simp[write_memory_with_expansion_def, exec_read1_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  strip_tac >> gvs[]
QED


Theorem ld_layout_data_drop:
  code_layout_valid t /\
  w2n (x:bytes32) + (LENGTH t.vs_code - LENGTH t.vs_data_section) < dimword(:256) ==>
  DROP (w2n (x + n2w (LENGTH t.vs_code - LENGTH t.vs_data_section))) t.vs_code =
  DROP (w2n x) t.vs_data_section
Proof
  strip_tac >> gvs[code_layout_valid_def] >>
  `LENGTH prefix < dimword(:256)` by
    (CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> decide_tac) >>
  simp[word_add_def, w2n_n2w, DROP_APPEND, DROP_DROP]
QED

Theorem ld_supply_dloadbytes_exact:
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dst;src;sz] /\
  fresh_ir_var u = (bv,u1) /\ lower_dload_inst_supply u inst = (es,u') /\
  eval_operand dst t = SOME p /\ eval_operand src t = SOME x /\
  eval_operand sz t = SOME z /\ dst <> Var bv /\ sz <> Var bv /\
  code_layout_valid t /\
  w2n x + (LENGTH t.vs_code - LENGTH t.vs_data_section) < dimword(:256) ==>
  let t2 = update_var bv (x + n2w (LENGTH t.vs_code - LENGTH t.vs_data_section)) t;
      t3 = write_memory_with_expansion (w2n p)
        (TAKE (w2n z) (DROP (w2n x) t.vs_data_section ++ REPLICATE (w2n z) 0w)) t2
  in LENGTH es = 2 /\ step_inst fuel C (EL 0 es) t = OK t2 /\
     step_inst fuel C (EL 1 es) t2 = OK t3
Proof
  strip_tac >>
  drule_all ld_layout_data_drop >> strip_tac >>
  `FLOOKUP t.vs_labels "code_end" =
   SOME (n2w (LENGTH t.vs_code - LENGTH t.vs_data_section))` by
    fs[code_layout_valid_def] >>
  `!v. eval_operand dst (update_var bv v t) = SOME p` by
    (Cases_on `dst` >> gvs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `!v. eval_operand sz (update_var bv v t) = SOME z` by
    (Cases_on `sz` >> gvs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
       exec_pure2_def, eval_operands_def, eval_operand_def, bind_outputs_def] >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED


Theorem ld_supply_dload_exact:
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\ inst.inst_outputs = [out] /\
  fresh_ir_var u = (av,u1) /\ fresh_ir_var u1 = (bv,u2) /\
  lower_dload_inst_supply u inst = (es,u') /\
  eval_operand off t = SOME x /\ off <> Var av /\
  code_layout_valid t /\
  w2n x + (LENGTH t.vs_code - LENGTH t.vs_data_section) < dimword(:256) /\
  ((FLOOKUP t.vs_allocas (EL 0 es).inst_id = NONE /\ b = t.vs_alloca_next) \/
   FLOOKUP t.vs_allocas (EL 0 es).inst_id = SOME (b,32)) /\
  b+32 < dimword(:256) ==>
  let t1 = update_var av (n2w b)
        (if FLOOKUP t.vs_allocas (EL 0 es).inst_id = NONE then
           t with <|vs_allocas := t.vs_allocas |+ ((EL 0 es).inst_id,(b,32));
                    vs_alloca_next := t.vs_alloca_next+32|>
         else t);
      t2 = update_var bv (x + n2w (LENGTH t.vs_code - LENGTH t.vs_data_section)) t1;
      bs = TAKE 32 (DROP (w2n x) t.vs_data_section ++ REPLICATE 32 0w);
      t3 = write_memory_with_expansion b bs t2;
      t4 = update_var out (word_of_bytes T (0w:bytes32) bs) t3
  in LENGTH es = 4 /\
     step_inst fuel C (EL 0 es) t = OK t1 /\
     step_inst fuel C (EL 1 es) t1 = OK t2 /\
     step_inst fuel C (EL 2 es) t2 = OK t3 /\
     step_inst fuel C (EL 3 es) t3 = OK t4
Proof
  strip_tac >>
  `av <> bv` by metis_tac[fresh_ir_var_two_calls_distinct] >>
  drule_all ld_layout_data_drop >> strip_tac >>
  `FLOOKUP t.vs_labels "code_end" =
   SOME (n2w (LENGTH t.vs_code - LENGTH t.vs_data_section))` by
    fs[code_layout_valid_def] >>
  gvs[lower_dload_inst_supply_def, AllCaseEqs()]
  >- (conj_tac
      >- simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_alloca_def] >>
      suspend "tail") >>
  conj_tac
  >- simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_alloca_def] >>
  suspend "tail"
QED

Resume ld_supply_dload_exact[tail]:
  markerLib.RESUME_TAC >>
  qmatch_goalsub_abbrev_tac `update_var bv _ ast` >>
  `eval_operand off ast = SOME x` by
    (Cases_on `off` >>
     gvs[Abbr `ast`, eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion addr bs` >>
  `addr < dimword(:256)` by
    (simp[Abbr `addr`] >> CONV_TAC (DEPTH_CONV wordsLib.SIZES_CONV) >> decide_tac) >>
  `FLOOKUP ast.vs_vars av = SOME (n2w addr)` by
    simp[Abbr `ast`, Abbr `addr`, update_var_def, FLOOKUP_UPDATE] >>
  `FLOOKUP ast.vs_labels "code_end" =
   SOME (n2w (LENGTH t.vs_code - LENGTH t.vs_data_section))` by
    simp[Abbr `ast`, update_var_def] >>
  `bs = TAKE 32
     (DROP (w2n (x + n2w (LENGTH t.vs_code - LENGTH t.vs_data_section)))
       ast.vs_code ++ REPLICATE 32 0w)` by
    simp[Abbr `bs`, Abbr `ast`, update_var_def] >>
  `w2n (n2w addr:bytes32) = addr` by simp[] >>
  qpat_x_assum `bs = _` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `w2n _ = addr` (fn th => once_rewrite_tac[GSYM th]) >>
  drule_all (BETA_RULE (PURE_REWRITE_RULE [LET_THM] ld_copy_load_exact)) >>
  disch_then irule
QED
Finalise ld_supply_dload_exact
