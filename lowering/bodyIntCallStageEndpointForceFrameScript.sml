(* Adapt the raw protected forcing frames to expression continuations. *)
Theory bodyIntCallStageEndpointForceFrame
Ancestors
  bodyIntCallJointAggCore bodyIntCallJointContract freshWrites

Theorem intcall_stage_forcing_cont:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
  sa.cs_next_var <= sb.cs_next_var /\
  s.vs_alloca_next <= u.vs_alloca_next /\ allocas_above fp.jc_lo u /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
    lookup_var x u = SOME w) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!a k. fp.jc_prot a k ==>
    mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!op. fp.jc_reserved op ==> eval_operand op u = eval_operand op s) /\
  (!name b sz. local_region ce es.scopes u name b sz <=>
    local_region ce es.scopes s name b sz) /\
  (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
    aid < sa.cs_next_id /\
    (!name b k. local_region ce es.scopes s name b k ==>
       off + sz <= b \/ b + k <= off) ==>
    mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz s.vs_memory) /\
  locals_kept ce es es s u /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  intcall_expr_cont fp ce env es sa s es sb u
Proof
  strip_tac >>
  `intcall_expr_res fp ce env es sb u` by
    (irule intcall_joint_res_frame >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  simp[intcall_expr_cont_def] >> metis_tac[]
QED

Theorem intcall_stage_forcing_destination:
  intcall_expr_cont fp ce env es sa s es sb u /\
  aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME (n2w b) /\ (?x. dst = Var x) /\
  (!name a n. local_region ce es.scopes s name a n ==>
    regions_disjoint b sz a n) /\
  (!name a n. local_region ce es.scopes u name a n <=>
    local_region ce es.scopes s name a n) /\
  sa.cs_next_var <= sb.cs_next_var ==>
  FLOOKUP u.vs_allocas aid = SOME (b,sz) /\
  eval_operand dst u = SOME (n2w b) /\
  mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory /\
  (!x. dst = Var x ==> not_fresh_at sb x) /\
  (!name a n. local_region ce es.scopes u name a n ==>
    regions_disjoint b sz a n)
Proof
  strip_tac >>
  `eval_operand dst u = SOME (n2w b)` by
    (Cases_on `dst` >> fs[venomStateTheory.eval_operand_def, intcall_expr_cont_def] >>
     metis_tac[]) >>
  fs[intcall_expr_cont_def, loweringStateRelDefsTheory.regions_disjoint_def] >>
  metis_tac[not_fresh_at_mono]
QED
