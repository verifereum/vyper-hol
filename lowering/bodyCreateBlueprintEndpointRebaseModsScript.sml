(* Transport the materialized append post back across the blueprint check. *)
Theory bodyCreateBlueprintEndpointRebaseMods
Ancestors
  builtinCreate compileEnv fragExec fragGasOriginPtr fragGasOriginPtrLoop
  venomState venomInst venomLayout ptrDiscipline bodyPtrDefs stmtFragPtr
  vyperCreate vfmTypes words finite_map arithmetic list

Theorem blueprint_append_endpoint_rebase:
  cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)) /\
  (u = s with <|vs_vars := u.vs_vars; vs_inst_idx := LENGTH sm.cs_current_insts|>) /\
  tu.t_mem = tn.t_mem /\ tu.t_stor = tn.t_stor /\ tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
     FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)) /\
  allocas_below_fmp s /\
  LENGTH (take_pad_0 (blueprint_copy_size (w2n ow) code_bytes) (DROP (w2n ow) code_bytes)) +
    LENGTH args < dimword (:256) /\
  compile_create_dispatch (Var p) sz amount sop rof sc = (result,sb) /\
  fn_has_code sc sb func /\ cs_extends sm sc /\ sm.cs_next_var <= sc.cs_next_var /\
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK t,H,z)) /\
  ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\
  (t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx;
            vs_memory := u.vs_memory; vs_fmp := u.vs_fmp|>) = u /\
  lookup_var p t = SOME u.vs_fmp /\
  ptr_covers H z p t (LENGTH (take_pad_0 (blueprint_copy_size (w2n ow) code_bytes)
                            (DROP (w2n ow) code_bytes)) + LENGTH args) /\
  eval_operand sz t = SOME (n2w (LENGTH (take_pad_0 (blueprint_copy_size (w2n ow) code_bytes)
                                         (DROP (w2n ow) code_bytes)) + LENGTH args)) /\
  op_taint z sz = {} /\
  (!x. Var x = sz \/ x = p ==> not_fresh_at sc x) /\
  w2n u.vs_initial_fmp <= w2n u.vs_fmp /\
  w2n t.vs_fmp = w2n u.vs_fmp + venomLayout$ceil32
    (LENGTH (take_pad_0 (blueprint_copy_size (w2n ow) code_bytes)
                       (DROP (w2n ow) code_bytes)) + LENGTH args) /\
  w2n u.vs_fmp + LENGTH (take_pad_0 (blueprint_copy_size (w2n ow) code_bytes)
                                   (DROP (w2n ow) code_bytes)) + LENGTH args <= LENGTH t.vs_memory /\
  LENGTH u.vs_memory <= LENGTH t.vs_memory /\
  read_memory (w2n u.vs_fmp)
    (LENGTH (take_pad_0 (blueprint_copy_size (w2n ow) code_bytes)
                       (DROP (w2n ow) code_bytes)) + LENGTH args) t =
    take_pad_0 (blueprint_copy_size (w2n ow) code_bytes) (DROP (w2n ow) code_bytes) ++ args /\
  (!j k. j+k <= w2n u.vs_fmp ==> read_memory j k t = read_memory j k u) /\
  (!i. w2n u.vs_fmp <= i /\
       i < w2n u.vs_fmp + LENGTH (take_pad_0 (blueprint_copy_size (w2n ow) code_bytes)
                                            (DROP (w2n ow) code_bytes)) + LENGTH args ==>
       i NOTIN z.t_mem) /\
  (!i. i < w2n u.vs_fmp /\ i IN z.t_mem ==> i IN tu.t_mem) /\
  z.t_stor = tu.t_stor /\ z.t_trans = tu.t_trans /\ z.t_imm = tu.t_imm /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x u /\
     FLOOKUP H x = FLOOKUP Gu x /\ op_taint z (Var x) = op_taint tu (Var x)) ==>
  compile_create_dispatch (Var p) sz amount sop rof sc = (result,sb) /\
  fn_has_code sc sb func /\ cs_extends sa sc /\ sa.cs_next_var <= sc.cs_next_var /\
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,H,z)) /\
  ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\
  (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
            vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|>) = s /\
  eval_operand (Var p) t = SOME s.vs_fmp /\
  ptr_covers H z p t (blueprint_copy_size (w2n ow) code_bytes + LENGTH args) /\
  eval_operand sz t = SOME (n2w (blueprint_copy_size (w2n ow) code_bytes + LENGTH args)) /\
  op_taint z (Var p) = {} /\ op_taint z sz = {} /\
  (!x. Var x = sz \/ x = p ==> not_fresh_at sc x) /\
  blueprint_copy_size (w2n ow) code_bytes + LENGTH args < dimword (:256) /\
  w2n t.vs_initial_fmp <= w2n s.vs_fmp /\
  w2n t.vs_fmp = w2n s.vs_fmp + venomLayout$ceil32 (blueprint_copy_size (w2n ow) code_bytes + LENGTH args) /\
  w2n s.vs_fmp + (blueprint_copy_size (w2n ow) code_bytes + LENGTH args) <= w2n t.vs_fmp /\
  w2n s.vs_fmp + (blueprint_copy_size (w2n ow) code_bytes + LENGTH args) <= LENGTH t.vs_memory /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\ allocas_below_fmp t /\
  read_memory (w2n s.vs_fmp) (blueprint_copy_size (w2n ow) code_bytes + LENGTH args) t =
    blueprint_initcode (blueprint_copy_size (w2n ow) code_bytes) (w2n ow) code_bytes args /\
  (!j k. j+k <= w2n s.vs_fmp ==> read_memory j k t = read_memory j k s) /\
  (!i. w2n s.vs_fmp <= i /\ i < w2n s.vs_fmp + (blueprint_copy_size (w2n ow) code_bytes + LENGTH args) ==>
       i NOTIN z.t_mem) /\
  (!i. i < w2n s.vs_fmp /\ i IN z.t_mem ==> i IN tn.t_mem) /\
  z.t_stor = tn.t_stor /\ z.t_trans = tn.t_trans /\ z.t_imm = tn.t_imm /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
     FLOOKUP H x = FLOOKUP G x /\ op_taint z (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends sa sc` by (irule cs_extends_trans >> metis_tac[]) >>
  `sa.cs_next_var <= sc.cs_next_var` by decide_tac >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,H,z)` by
    (rpt gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gu`,`u`,`tu`] >> conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `(t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
             vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|>) = s` by
    (qpat_assum `t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx;
                          vs_memory := u.vs_memory; vs_fmp := u.vs_fmp|> = u`
       (mp_tac o AP_TERM ``\v:venom_state. v with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
                   vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|>``) >>
     simp[NoAsms] >>
     qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (PURE_ONCE_REWRITE_TAC o single) >> simp[NoAsms]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_initial_fmp = s.vs_initial_fmp` by
    (qpat_assum `t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
                          vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|> = s`
       (fn th => mp_tac (AP_TERM ``\v:venom_state. v.vs_allocas`` th) >>
                 mp_tac (AP_TERM ``\v:venom_state. v.vs_initial_fmp`` th)) >> simp[NoAsms]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_fmp = s.vs_fmp /\
   u.vs_initial_fmp = s.vs_initial_fmp` by
    (qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (PURE_ONCE_REWRITE_TAC o single) >> simp[NoAsms]) >>
  qpat_x_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>` kall_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP H x = FLOOKUP G x /\ op_taint z (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >>
     `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
     qpat_assum `!x. not_fresh_at sm x ==> lookup_var x t = _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _` (drule_then strip_assume_tac) >>
     simp[]) >>
  `op_taint z (Var p) = {}` by
    qpat_assum `ptr_covers H z p t _`
      (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[ptr_covers_def]) >>
  map_every (fn pat => qpat_assum pat (rule_assum_tac o PURE_ONCE_REWRITE_RULE o single))
    [`u.vs_fmp = s.vs_fmp`, `u.vs_initial_fmp = s.vs_initial_fmp`,
     `tu.t_mem = tn.t_mem`, `tu.t_stor = tn.t_stor`, `tu.t_trans = tn.t_trans`,
     `tu.t_imm = tn.t_imm`] >>
  qpat_assum `u.vs_memory = s.vs_memory` (fn th =>
    qpat_x_assum `!j k. _ ==> read_memory j k t = read_memory j k u`
      (assume_tac o PURE_REWRITE_RULE[read_memory_def,th]) >>
    rule_assum_tac (PURE_ONCE_REWRITE_RULE[th])) >>
  qpat_assum `t.vs_initial_fmp = s.vs_initial_fmp` (PURE_ONCE_REWRITE_TAC o single) >>
  PURE_REWRITE_TAC[eval_operand_def,blueprint_initcode_def,ADD_ASSOC,read_memory_def] >>
  rule_assum_tac (PURE_REWRITE_RULE[LENGTH_take_pad_0,read_memory_def,ADD_ASSOC]) >>
  (rpt conj_tac >> TRY (first_assum ACCEPT_TAC))
  >- (PURE_ONCE_REWRITE_TAC[GSYM ADD_ASSOC] >>
      qpat_assum `w2n t.vs_fmp = _` (PURE_ONCE_REWRITE_TAC o single) >>
      simp[NoAsms,ceil32_ge]) >>
  qpat_assum `allocas_below_fmp s`
    (strip_assume_tac o PURE_REWRITE_RULE[allocas_below_fmp_def]) >>
  PURE_REWRITE_TAC[allocas_below_fmp_def] >>
  conj_tac
  >- (qpat_assum `t.vs_initial_fmp = _` (PURE_ONCE_REWRITE_TAC o single) >>
      qpat_assum `w2n t.vs_fmp = _` (PURE_ONCE_REWRITE_TAC o single) >>
      qpat_assum `w2n s.vs_initial_fmp <= w2n s.vs_fmp` mp_tac >> decide_tac) >>
  qpat_assum `t.vs_allocas = _` (PURE_ONCE_REWRITE_TAC o single) >>
  qpat_assum `t.vs_initial_fmp = _` (PURE_ONCE_REWRITE_TAC o single) >>
  first_assum ACCEPT_TAC
QED
