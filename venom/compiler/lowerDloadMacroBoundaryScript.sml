Theory lowerDloadMacroBoundary
Ancestors
  lowerDloadPhaseBoundary lowerDloadPairedBoundary lowerDloadDefs
  venomExecSemantics venomState venomInst finite_map words list

Theorem ld_configured_bytes_code:
  inst.inst_opcode = DLOADBYTES /\
  inst.inst_operands = [dst;off;sz] /\
  fresh_ir_var q = (av,q1) /\ fresh_inst_id q1 = (ai,q2) /\
  fresh_inst_id q2 = (ci,q3) ==>
  lower_dload_inst_supply q inst =
    ([<|inst_id := ai; inst_opcode := ADD;
        inst_operands := [off; Label "code_end"]; inst_outputs := [av]|>;
      <|inst_id := ci; inst_opcode := CODECOPY;
        inst_operands := [dst; Var av; sz]; inst_outputs := []|>],q3)
Proof
  simp[lower_dload_inst_supply_def]
QED

Theorem ld_macro_add_step:
  i.inst_opcode = ADD /\ i.inst_operands = [a;b] /\
  i.inst_outputs = [v] ==>
  step_inst fuel C i s =
    case (eval_operand a s, eval_operand b s) of
      (SOME x,SOME y) => OK (update_var v (x + y) s)
    | _ => Error "undefined operand"
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def,
    exec_pure2_def]
QED

Theorem ld_macro_copy_step:
  i.inst_opcode = CODECOPY /\ i.inst_operands = [dst;off;sz] ==>
  step_inst fuel C i s =
    case (eval_operand dst s, eval_operand off s, eval_operand sz s) of
      (SOME d,SOME a,SOME n) =>
        OK (write_memory_with_expansion (w2n d)
          (TAKE (w2n n) (DROP (w2n a) s.vs_code ++ REPLICATE (w2n n) 0w)) s)
    | _ => Error "undefined operand"
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def]
QED

Theorem ld_bytes_first_prefix:
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\
  a.inst_outputs = [av] ==>
  (ld_target_prefix C [a;c] t0 u0 (SUC 0) t u <=>
   ?x y. eval_operand off t0 = SOME x /\
     eval_operand (Label "code_end") t0 = SOME y /\
     t = (update_var av (x + y) t0) with vs_inst_idx := SUC t0.vs_inst_idx /\
     u = step_taint a t0 (update_var av (x + y) t0) u0)
Proof
  strip_tac >> rewrite_tac[ld_target_prefix_step_iff] >>
  simp[ld_target_prefix_empty] >>
  drule_all ld_macro_add_step >> disch_then (fn th => rewrite_tac[th]) >>
  Cases_on `eval_operand off t0` >>
  Cases_on `eval_operand (Label "code_end") t0` >> simp[]
QED

Theorem ld_macro_operand_pc:
  eval_operand op (s with vs_inst_idx := n) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem ld_bytes_copy_after_add:
  c.inst_opcode = CODECOPY /\ c.inst_operands = [dst;Var av;sz] /\
  (!v. dst = Var v ==> v <> av) /\
  (!v. sz = Var v ==> v <> av) ==>
  step_inst fuel C c
    ((update_var av sum t0) with vs_inst_idx := n) =
    case (eval_operand dst t0, eval_operand sz t0) of
      (SOME d,SOME k) =>
        OK (write_memory_with_expansion (w2n d)
          (TAKE (w2n k) (DROP (w2n sum) t0.vs_code ++ REPLICATE (w2n k) 0w))
          ((update_var av sum t0) with vs_inst_idx := n))
    | _ => Error "undefined operand"
Proof
  strip_tac >>
  `eval_operand dst (update_var av sum t0) = eval_operand dst t0` by
    (Cases_on `dst` >> simp[eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE] >> metis_tac[]) >>
  `eval_operand sz (update_var av sum t0) = eval_operand sz t0` by
    (Cases_on `sz` >> simp[eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE] >> metis_tac[]) >>
  drule_all ld_macro_copy_step >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[ld_macro_operand_pc] >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  Cases_on `eval_operand dst t0` >> Cases_on `eval_operand sz t0` >> simp[]
QED

Theorem ld_bytes_completed_prefix:
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\
  a.inst_outputs = [av] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [dst;Var av;sz] /\
  (!v. dst = Var v ==> v <> av) /\
  (!v. sz = Var v ==> v <> av) ==>
  (ld_target_prefix C [a;c] t0 u0 (SUC (SUC 0)) t u <=>
   ?x y d k r w z.
     eval_operand off t0 = SOME x /\
     eval_operand (Label "code_end") t0 = SOME y /\
     eval_operand dst t0 = SOME d /\ eval_operand sz t0 = SOME k /\
     r = (update_var av (x + y) t0) with vs_inst_idx := SUC t0.vs_inst_idx /\
     w = step_taint a t0 (update_var av (x + y) t0) u0 /\
     z = write_memory_with_expansion (w2n d)
       (TAKE (w2n k) (DROP (w2n (x + y)) t0.vs_code ++ REPLICATE (w2n k) 0w)) r /\
     t = z with vs_inst_idx := SUC r.vs_inst_idx /\
     u = step_taint c r z w)
Proof
  strip_tac >> once_rewrite_tac[ld_target_prefix_step_iff] >>
  drule_all ld_bytes_first_prefix >> disch_then (fn th => rewrite_tac[th]) >>
  simp[PULL_EXISTS] >>
  drule_all ld_bytes_copy_after_add >>
  disch_then (fn th => rewrite_tac[th]) >>
  Cases_on `eval_operand off t0` >>
  Cases_on `eval_operand (Label "code_end") t0` >>
  Cases_on `eval_operand dst t0` >> Cases_on `eval_operand sz t0` >> simp[]
QED

Theorem ld_bytes_completed_defined:
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\
  a.inst_outputs = [av] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [dst;Var av;sz] /\
  (!v. dst = Var v ==> v <> av) /\
  (!v. sz = Var v ==> v <> av) /\
  ld_target_prefix C [a;c] t0 u0 (SUC (SUC 0)) t u ==>
  ?d x k. eval_operand dst t0 = SOME d /\
    eval_operand off t0 = SOME x /\ eval_operand sz t0 = SOME k
Proof
  strip_tac >> drule_all ld_bytes_completed_prefix >>
  disch_then (fn th => gvs[th]) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem ld_bytes_source_success:
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dst;off;sz] /\
  ld_owned_vars V E AG AH tn un s t0 /\
  (!v. MEM (Var v) [dst;off;sz] ==> v IN V) /\
  (?d x k. eval_operand dst t0 = SOME d /\
     eval_operand off t0 = SOME x /\ eval_operand sz t0 = SOME k) ==>
  ?z. step_inst fuel C inst s = OK z
Proof
  strip_tac >>
  `eval_operand dst s <> NONE` by
    (drule ld_owned_operand_defined >>
     disch_then (qspec_then `dst` mp_tac) >> simp[] >> metis_tac[]) >>
  `eval_operand off s <> NONE` by
    (drule ld_owned_operand_defined >>
     disch_then (qspec_then `off` mp_tac) >> simp[] >> metis_tac[]) >>
  `eval_operand sz s <> NONE` by
    (drule ld_owned_operand_defined >>
     disch_then (qspec_then `sz` mp_tac) >> simp[] >> metis_tac[]) >>
  simp[step_inst_non_invoke, step_inst_base_def] >>
  Cases_on `eval_operand dst s` >> Cases_on `eval_operand off s` >>
  Cases_on `eval_operand sz s` >> gvs[]
QED

Theorem ld_bytes_first_projections:
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\
  a.inst_outputs = [av] /\
  ld_target_prefix C [a;c] t0 u0 (SUC 0) t u ==>
  t.vs_memory = t0.vs_memory /\ t.vs_allocas = t0.vs_allocas /\
  t.vs_alloca_next = t0.vs_alloca_next /\ t.vs_labels = t0.vs_labels /\
  (!v. v <> av ==> lookup_var v t = lookup_var v t0)
Proof
  strip_tac >> drule_all ld_bytes_first_prefix >>
  disch_then (fn th => gvs[th]) >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem ld_bytes_prefix_exists:
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\
  a.inst_outputs = [av] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [dst;Var av;sz] /\
  (!v. dst = Var v ==> v <> av) /\
  (!v. sz = Var v ==> v <> av) ==>
  ((?t u. ld_target_prefix C [a;c] t0 u0 (SUC 0) t u) <=>
     (?x y. eval_operand off t0 = SOME x /\
            eval_operand (Label "code_end") t0 = SOME y)) /\
  ((?t u. ld_target_prefix C [a;c] t0 u0 (SUC (SUC 0)) t u) <=>
     (?x y d k. eval_operand off t0 = SOME x /\
       eval_operand (Label "code_end") t0 = SOME y /\
       eval_operand dst t0 = SOME d /\ eval_operand sz t0 = SOME k))
Proof
  strip_tac >>
  drule_all ld_bytes_first_prefix >> disch_then (fn th => rewrite_tac[th]) >>
  drule_all ld_bytes_completed_prefix >> disch_then (fn th => rewrite_tac[th]) >>
  simp[PULL_EXISTS]
QED

Theorem ld_macro_add_error:
  i.inst_opcode = ADD /\ i.inst_operands = [a;b] /\
  i.inst_outputs = [v] ==>
  ((?e. step_inst fuel C i s = Error e) <=>
    eval_operand a s = NONE \/ eval_operand b s = NONE) /\
  ((?z. step_inst fuel C i s = OK z) <=>
    eval_operand a s <> NONE /\ eval_operand b s <> NONE)
Proof
  strip_tac >> drule_all ld_macro_add_step >>
  disch_then (fn th => rewrite_tac[th]) >>
  Cases_on `eval_operand a s` >> Cases_on `eval_operand b s` >> simp[]
QED

Theorem ld_bytes_copy_error:
  c.inst_opcode = CODECOPY /\ c.inst_operands = [dst;Var av;sz] /\
  (!v. dst = Var v ==> v <> av) /\
  (!v. sz = Var v ==> v <> av) ==>
  ((?e. step_inst fuel C c
      ((update_var av sum t0) with vs_inst_idx := n) = Error e) <=>
    eval_operand dst t0 = NONE \/ eval_operand sz t0 = NONE) /\
  ((?z. step_inst fuel C c
      ((update_var av sum t0) with vs_inst_idx := n) = OK z) <=>
    eval_operand dst t0 <> NONE /\ eval_operand sz t0 <> NONE)
Proof
  strip_tac >> drule_all ld_bytes_copy_after_add >>
  disch_then (fn th => rewrite_tac[th]) >>
  Cases_on `eval_operand dst t0` >> Cases_on `eval_operand sz t0` >> simp[]
QED

Theorem ld_bytes_completed_projections:
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\
  a.inst_outputs = [av] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [dst;Var av;sz] /\
  (!v. dst = Var v ==> v <> av) /\
  (!v. sz = Var v ==> v <> av) /\
  ld_target_prefix C [a;c] t0 u0 (SUC (SUC 0)) t u ==>
  t.vs_vars = (update_var av
    (THE (eval_operand off t0) + THE (eval_operand (Label "code_end") t0)) t0).vs_vars /\
  t.vs_allocas = t0.vs_allocas /\ t.vs_alloca_next = t0.vs_alloca_next /\
  t.vs_labels = t0.vs_labels
Proof
  strip_tac >> drule_all ld_bytes_completed_prefix >>
  disch_then (fn th => gvs[th]) >>
  simp[write_memory_with_expansion_def, expand_memory_def, write_memory_def,
    update_var_def]
QED

Theorem ld_bytes_completed_source_success:
  a.inst_opcode = ADD /\ a.inst_operands = [off;Label "code_end"] /\
  a.inst_outputs = [av] /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [dst;Var av;sz] /\
  (!v. dst = Var v ==> v <> av) /\
  (!v. sz = Var v ==> v <> av) /\
  ld_target_prefix C' [a;c] t0 u0 (SUC (SUC 0)) t u /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dst;off;sz] /\
  ld_owned_vars V E AG AH tn un s t0 /\
  (!v. MEM (Var v) [dst;off;sz] ==> v IN V) ==>
  ?z. step_inst fuel C inst s = OK z
Proof
  strip_tac >> drule_all ld_bytes_completed_defined >> strip_tac >>
  irule ld_bytes_source_success >>
  qpat_assum `ld_owned_vars _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem ld_macro_alloca_step:
  i.inst_opcode = ALLOCA /\ i.inst_operands = [Lit 32w] /\
  i.inst_outputs = [av] ==>
  step_inst fuel C i s = OK
    (case FLOOKUP s.vs_allocas i.inst_id of
       SOME (b,sz) => update_var av (n2w b) s
     | NONE => update_var av (n2w s.vs_alloca_next)
         (s with <|vs_allocas := s.vs_allocas |+ (i.inst_id,(s.vs_alloca_next,32));
                   vs_alloca_next := s.vs_alloca_next + 32|>))
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas i.inst_id`
  >- simp[dimword_def] >>
  rename1 `SOME p` >> PairCases_on `p` >> simp[]
QED

Theorem ld_load_first_prefix:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
  a.inst_outputs = [av] ==>
  (ld_target_prefix C [a;b;c;d] t0 u0 (SUC 0) t u <=>
   ?r. r = (case FLOOKUP t0.vs_allocas a.inst_id of
       SOME (bp,sz) => update_var av (n2w bp) t0
     | NONE => update_var av (n2w t0.vs_alloca_next)
         (t0 with <|vs_allocas := t0.vs_allocas |+ (a.inst_id,(t0.vs_alloca_next,32));
                   vs_alloca_next := t0.vs_alloca_next + 32|>)) /\
     t = r with vs_inst_idx := SUC t0.vs_inst_idx /\
     u = step_taint a t0 r u0)
Proof
  strip_tac >> rewrite_tac[ld_target_prefix_step_iff] >>
  simp[ld_target_prefix_empty] >>
  drule_all ld_macro_alloca_step >> disch_then (fn th => rewrite_tac[th]) >> simp[]
QED

Theorem ld_configured_load_code:
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\
  inst.inst_outputs = [out] /\
  fresh_ir_var q = (av,q1) /\ fresh_ir_var q1 = (bv,q2) /\
  fresh_inst_id q2 = (ai,q3) /\ fresh_inst_id q3 = (bi,q4) /\
  fresh_inst_id q4 = (ci,q5) /\ fresh_inst_id q5 = (di,q6) ==>
  lower_dload_inst_supply q inst =
    ([<|inst_id := ai; inst_opcode := ALLOCA;
        inst_operands := [Lit 32w]; inst_outputs := [av]|>;
      <|inst_id := bi; inst_opcode := ADD;
        inst_operands := [off; Label "code_end"]; inst_outputs := [bv]|>;
      <|inst_id := ci; inst_opcode := CODECOPY;
        inst_operands := [Var av; Var bv; Lit 32w]; inst_outputs := []|>;
      <|inst_id := di; inst_opcode := MLOAD;
        inst_operands := [Var av]; inst_outputs := [out]|>],q6)
Proof
  simp[lower_dload_inst_supply_def]
QED

Theorem ld_load_first_operands:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
  a.inst_outputs = [av] /\
  ld_target_prefix C [a;b;c;d] t0 u0 (SUC 0) t u /\
  (!v. op = Var v ==> v <> av) ==>
  eval_operand op t = eval_operand op t0
Proof
  strip_tac >> drule_all ld_load_first_prefix >>
  disch_then (fn th => gvs[th]) >>
  Cases_on `FLOOKUP t0.vs_allocas a.inst_id`
  >- (simp[ld_macro_operand_pc] >>
      Cases_on `op` >> simp[eval_operand_def, update_var_def, lookup_var_def,
        FLOOKUP_UPDATE] >> metis_tac[]) >>
  rename1 `SOME p` >> PairCases_on `p` >>
  simp[ld_macro_operand_pc] >>
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def, update_var_def,
    FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem ld_load_second_prefix:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
  a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ (!v. off = Var v ==> v <> av) ==>
  (ld_target_prefix C [a;b;c;d] t0 u0 (SUC (SUC 0)) t u <=>
   ?r w x y. ld_target_prefix C [a;b;c;d] t0 u0 (SUC 0) r w /\
     eval_operand off t0 = SOME x /\ eval_operand (Label "code_end") t0 = SOME y /\
     t = (update_var bv (x + y) r) with vs_inst_idx := SUC r.vs_inst_idx /\
     u = step_taint b r (update_var bv (x + y) r) w)
Proof
  strip_tac >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [ld_target_prefix_step_iff])) >> simp[] >>
  drule_all ld_macro_add_step >> disch_then (fn th => rewrite_tac[th]) >>
  eq_tac
  >- (strip_tac >>
      `eval_operand off v = eval_operand off t0` by
        (irule ld_load_first_operands >> simp[] >>
         qpat_assum `ld_target_prefix _ _ _ _ _ _ _` (irule_at Any) >> simp[] >> metis_tac[]) >>
      `eval_operand (Label "code_end") v = eval_operand (Label "code_end") t0` by
        (irule ld_load_first_operands >> simp[] >>
         qpat_assum `ld_target_prefix _ _ _ _ _ _ _` (irule_at Any) >> simp[] >> metis_tac[]) >>
      gvs[] >> gvs[AllCaseEqs()] >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  strip_tac >>
  `eval_operand off r = eval_operand off t0` by
    (irule ld_load_first_operands >> simp[] >>
         qpat_assum `ld_target_prefix _ _ _ _ _ _ _` (irule_at Any) >> simp[] >> metis_tac[]) >>
  `eval_operand (Label "code_end") r = eval_operand (Label "code_end") t0` by
    (irule ld_load_first_operands >> simp[] >>
         qpat_assum `ld_target_prefix _ _ _ _ _ _ _` (irule_at Any) >> simp[] >> metis_tac[]) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem ld_load_first_pointer:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
  a.inst_outputs = [av] /\
  ld_target_prefix C [a;b;c;d] t0 u0 (SUC 0) t u ==>
  (?p. eval_operand (Var av) t = SOME p) /\
  t.vs_code = t0.vs_code /\ t.vs_memory = t0.vs_memory /\
  t.vs_labels = t0.vs_labels /\
  (!v. v <> av ==> lookup_var v t = lookup_var v t0)
Proof
  strip_tac >> drule_all ld_load_first_prefix >>
  disch_then (fn th => gvs[th]) >>
  Cases_on `FLOOKUP t0.vs_allocas a.inst_id`
  >- simp[ld_macro_operand_pc, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE] >>
  rename1 `SOME p` >> PairCases_on `p` >>
  simp[ld_macro_operand_pc, eval_operand_def, lookup_var_def,
    update_var_def, FLOOKUP_UPDATE]
QED

Theorem ld_load_second_values:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
  a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ av <> bv /\
  (!v. off = Var v ==> v <> av) /\
  ld_target_prefix C [a;b;c;d] t0 u0 (SUC (SUC 0)) t u ==>
  ?p x y. eval_operand (Var av) t = SOME p /\
    eval_operand (Var bv) t = SOME (x + y) /\
    eval_operand off t0 = SOME x /\
    eval_operand (Label "code_end") t0 = SOME y /\
    t.vs_code = t0.vs_code /\ t.vs_memory = t0.vs_memory
Proof
  strip_tac >> drule_all ld_load_second_prefix >>
  disch_then (fn th => gvs[th]) >>
  drule_all (SRULE [] ld_load_first_pointer) >> strip_tac >>
  `eval_operand (Var av) (update_var bv (x + y) r) =
    eval_operand (Var av) r` by
    (gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  simp[ld_macro_operand_pc] >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem ld_macro_load_step:
  i.inst_opcode = MLOAD /\ i.inst_operands = [ptr] /\ i.inst_outputs = [out] ==>
  step_inst fuel C i s =
    case eval_operand ptr s of
      SOME p => OK (update_var out (mload (w2n p) s) s)
    | NONE => Error "undefined operand"
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def, exec_read1_def]
QED

Theorem ld_load_third_prefix:
  c.inst_opcode = CODECOPY /\
  c.inst_operands = [Var av;Var bv;Lit 32w] ==>
  (ld_target_prefix C [a;b;c;d] t0 u0 (SUC (SUC (SUC 0))) t u <=>
   ?r w p sum z.
     ld_target_prefix C [a;b;c;d] t0 u0 (SUC (SUC 0)) r w /\
     eval_operand (Var av) r = SOME p /\
     eval_operand (Var bv) r = SOME sum /\
     z = write_memory_with_expansion (w2n p)
       (TAKE 32 (DROP (w2n sum) r.vs_code ++ REPLICATE 32 0w)) r /\
     t = z with vs_inst_idx := SUC r.vs_inst_idx /\
     u = step_taint c r z w)
Proof
  strip_tac >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [ld_target_prefix_step_iff])) >>
  simp[] >> drule_all ld_macro_copy_step >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[eval_operand_def, dimword_def, PULL_EXISTS, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem ld_load_fourth_prefix:
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\
  d.inst_outputs = [out] ==>
  (ld_target_prefix C [a;b;c;d] t0 u0 (SUC (SUC (SUC (SUC 0)))) t u <=>
   ?r w p z.
     ld_target_prefix C [a;b;c;d] t0 u0 (SUC (SUC (SUC 0))) r w /\
     eval_operand (Var av) r = SOME p /\
     z = update_var out (mload (w2n p) r) r /\
     t = z with vs_inst_idx := SUC r.vs_inst_idx /\
     u = step_taint d r z w)
Proof
  strip_tac >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [ld_target_prefix_step_iff])) >>
  simp[] >> drule_all ld_macro_load_step >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[PULL_EXISTS, AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_load_third_pointer:
  c.inst_opcode = CODECOPY /\
  c.inst_operands = [Var av;Var bv;Lit 32w] /\
  ld_target_prefix C [a;b;c;d] t0 u0 (SUC (SUC (SUC 0))) t u ==>
  ?p. eval_operand (Var av) t = SOME p
Proof
  strip_tac >> drule_all ld_load_third_prefix >>
  disch_then (fn th => gvs[th]) >>
  simp[ld_macro_operand_pc, eval_operand_def, lookup_var_def,
    write_memory_with_expansion_def] >>
  gvs[eval_operand_def, lookup_var_def]
QED

Theorem ld_load_copy_exists:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
  a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ av <> bv /\
  (!v. off = Var v ==> v <> av) /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] ==>
  ((?t u. ld_target_prefix C [a;b;c;d] t0 u0 (SUC (SUC (SUC 0))) t u) <=>
   (?t u. ld_target_prefix C [a;b;c;d] t0 u0 (SUC (SUC 0)) t u))
Proof
  strip_tac >> drule_all ld_load_third_prefix >>
  disch_then (fn th => rewrite_tac[th]) >> simp[PULL_EXISTS] >>
  eq_tac >- metis_tac[] >>
  strip_tac >> gvs[] >> drule_all (SRULE [] ld_load_second_values) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem ld_load_mload_exists:
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] ==>
  ((?t u. ld_target_prefix C [a;b;c;d] t0 u0 (SUC (SUC (SUC (SUC 0)))) t u) <=>
   (?t u. ld_target_prefix C [a;b;c;d] t0 u0 (SUC (SUC (SUC 0))) t u))
Proof
  strip_tac >> drule_all ld_load_fourth_prefix >>
  disch_then (fn th => rewrite_tac[th]) >> simp[PULL_EXISTS] >>
  eq_tac >- metis_tac[] >>
  strip_tac >> drule_all (SRULE [] ld_load_third_pointer) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem ld_load_prefix_exists:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
  a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ av <> bv /\
  (!v. off = Var v ==> v <> av) /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] ==>
  ((?t u. ld_target_prefix C [a;b;c;d] t0 u0 (SUC (SUC (SUC (SUC 0)))) t u) <=>
   (?x y. eval_operand off t0 = SOME x /\
      eval_operand (Label "code_end") t0 = SOME y))
Proof
  strip_tac >> drule_all ld_load_mload_exists >>
  disch_then (fn th => rewrite_tac[th]) >>
  drule_all ld_load_copy_exists >> disch_then (fn th => rewrite_tac[th]) >>
  drule_all ld_load_second_prefix >> disch_then (fn th => rewrite_tac[th]) >>
  drule_all ld_load_first_prefix >> disch_then (fn th => rewrite_tac[th]) >>
  simp[PULL_EXISTS]
QED

Theorem ld_load_source_success:
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\
  inst.inst_outputs = [out] /\
  ld_owned_vars V E AG AH tn un s t0 /\
  (!v. off = Var v ==> v IN V) /\
  eval_operand off t0 <> NONE ==>
  ?z. step_inst fuel C inst s = OK z
Proof
  strip_tac >>
  `eval_operand off s <> NONE` by
    (drule ld_owned_operand_defined >>
     disch_then (qspec_then `off` mp_tac) >> simp[] >> metis_tac[]) >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_read1_def] >>
  Cases_on `eval_operand off s` >> gvs[]
QED

Theorem ld_load_completed_source_success:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
  a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ av <> bv /\
  (!v. off = Var v ==> v <> av) /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  ld_target_prefix C' [a;b;c;d] t0 u0 (SUC (SUC (SUC (SUC 0)))) t u /\
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\
  inst.inst_outputs = [out] /\
  ld_owned_vars V E AG AH tn un s t0 /\
  (!v. off = Var v ==> v IN V) ==>
  ?z. step_inst fuel C inst s = OK z
Proof
  strip_tac >>
  `?x y. eval_operand off t0 = SOME x /\
    eval_operand (Label "code_end") t0 = SOME y` by
    (drule_all ld_load_prefix_exists >>
     disch_then (qspecl_then [`u0`,`t0`,`C'`]
       (fn th => rewrite_tac[GSYM th])) >>
     goal_assum (drule_at Any)) >>
  irule ld_load_source_success >>
  qpat_assum `ld_owned_vars _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem ld_load_add_error:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
  a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ (!v. off = Var v ==> v <> av) /\
  ld_target_prefix C [a;b;c;d] t0 u0 (SUC 0) t u ==>
  ((?e. step_inst fuel C b t = Error e) <=>
   eval_operand off t0 = NONE \/ eval_operand (Label "code_end") t0 = NONE)
Proof
  strip_tac >>
  `eval_operand off t = eval_operand off t0` by
    (irule ld_load_first_operands >>
     qpat_assum `ld_target_prefix _ _ _ _ _ _ _` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  `eval_operand (Label "code_end") t = eval_operand (Label "code_end") t0` by
    (irule ld_load_first_operands >>
     qpat_assum `ld_target_prefix _ _ _ _ _ _ _` (irule_at Any) >> simp[]) >>
  drule_all ld_macro_add_error >> simp[]
QED

Theorem ld_load_copy_no_error:
  a.inst_opcode = ALLOCA /\ a.inst_operands = [Lit 32w] /\
  a.inst_outputs = [av] /\
  b.inst_opcode = ADD /\ b.inst_operands = [off;Label "code_end"] /\
  b.inst_outputs = [bv] /\ av <> bv /\
  (!v. off = Var v ==> v <> av) /\
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  ld_target_prefix C [a;b;c;d] t0 u0 (SUC (SUC 0)) t u ==>
  ~(?e. step_inst fuel C c t = Error e)
Proof
  strip_tac >> drule_all ld_load_second_values >> strip_tac >>
  drule_all ld_macro_copy_step >> disch_then (fn th => rewrite_tac[th]) >>
  simp[eval_operand_def]
QED

Theorem ld_load_mload_no_error:
  c.inst_opcode = CODECOPY /\ c.inst_operands = [Var av;Var bv;Lit 32w] /\
  d.inst_opcode = MLOAD /\ d.inst_operands = [Var av] /\ d.inst_outputs = [out] /\
  ld_target_prefix C [a;b;c;d] t0 u0 (SUC (SUC (SUC 0))) t u ==>
  ~(?e. step_inst fuel C d t = Error e)
Proof
  strip_tac >> drule_all ld_load_third_pointer >> strip_tac >>
  drule_all ld_macro_load_step >> disch_then (fn th => rewrite_tac[th]) >> simp[]
QED

