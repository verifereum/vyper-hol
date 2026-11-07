(* Read-only word forcing preserves resources at its actual counted endpoint. *)
Theory bodyIntCallWordLanding
Ancestors
  bodyIntCallLiteralLanding exprSimBopRestWordLoadPath
  exprSimBopRestWordLayout exprLowering venomState compileEnv list

Theorem protected_ptr_load_landing:
  !ctx func ce scopes loc addr sa sb op s a b value reserved.
  compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc addr sa = (op,sb) /\
  loc <> LocCalldata /\ eval_operand addr s = SOME a /\
  (loc = LocCode /\ ce.ce_is_ctor /\ ce.ce_imm_alloca <> NONE ==>
    eval_operand (THE ce.ce_imm_alloca) s = SOME b) /\
  value = (case loc of
      LocStorage => sload a s
    | LocTransient => tload a s
    | LocCode => if ce.ce_is_ctor then
        mload (w2n (if ce.ce_imm_alloca = NONE then a else a+b)) s
      else word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))
    | _ => mload (w2n a) s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved ce sa /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) ==>
  ?u. gas_path ctx func s 0 (OK u) /\
    eval_operand op u = SOME value /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    u = s with <|vs_vars := u.vs_vars;
                 vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!name base sz. local_region ce scopes u name base sz <=>
      local_region ce scopes s name base sz)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all rest_word_ptr_load_run >> strip_tac >>
  drule_all rest_word_ptr_load_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule rest_word_ptr_load_fresh >> strip_tac >>
  `!x. not_fresh_at sa x ==>
    FLOOKUP u.vs_vars x = FLOOKUP s.vs_vars x` by
    (rpt strip_tac >> first_x_assum irule >>
     gvs[EVERY_MEM] >> metis_tac[]) >>
  `!q. (!x. q = Var x ==> not_fresh_at sa x) ==>
    eval_operand q u = eval_operand q s` by
    (Cases >> simp[eval_operand_def, lookup_var_def] >>
     qpat_x_assum `u = _` (fn th => simp[Once th])) >>
  `!name base sz. local_region ce scopes u name base sz <=>
    local_region ce scopes s name base sz` by
    (irule local_region_reserved_operands >>
     qexists_tac `\q. !x. q = Var x ==> not_fresh_at sa x` >>
     gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  qexists_tac `u` >> simp[] >>
  conj_tac
  >- (qpat_x_assum `u = _` (fn th => simp[Once th])) >>
  metis_tac[]
QED

Theorem protected_word_unwrap_landing:
  !ctx func ce scopes ty p sa sb op s a b value reserved.
  unwrap_value ce (LocatedValue ty p) sa = (op,sb) /\
  is_word_type ty /\ p.ptr_location <> LocCalldata /\
  eval_operand p.ptr_operand s = SOME a /\
  (p.ptr_location = LocCode /\ ce.ce_is_ctor /\ ce.ce_imm_alloca <> NONE ==>
    eval_operand (THE ce.ce_imm_alloca) s = SOME b) /\
  value = (case p.ptr_location of
      LocStorage => sload a s
    | LocTransient => tload a s
    | LocCode => if ce.ce_is_ctor then
        mload (w2n (if ce.ce_imm_alloca = NONE then a else a+b)) s
      else word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))
    | _ => mload (w2n a) s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved ce sa /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) ==>
  ?u. gas_path ctx func s 0 (OK u) /\
    eval_operand op u = SOME value /\ ~u.vs_halted /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    u = s with <|vs_vars := u.vs_vars;
                 vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!name base sz. local_region ce scopes u name base sz <=>
      local_region ce scopes s name base sz)
Proof
  rpt gen_tac >> strip_tac >> gvs[unwrap_value_def] >>
  drule protected_ptr_load_landing >> simp[] >>
  disch_then drule_all >> simp[]
QED
