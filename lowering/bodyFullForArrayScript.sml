(* Allocation framing for non-slot For element preparation. *)
Theory bodyFullForArray
Ancestors
  whitelistForIterImmCopy stmtSimDeclCompose exprSimCopy exprLoweringProps
  stmtLowering loweringPosts loweringStateRelDefs venomMemDefs venomState
  compileEnv vyperState valueEncoding finite_map words

(* This boundary preserves the original entry frame through the actual
   immutable element copy and source binding. It makes no joint-path claim. *)
Theorem for_immutable_element_copy_alloca_frame:
  compile_iter_elem_copy c src (Var p) bytes LocCode F ty ty sa = ((),sb) /\
  bytes = type_memory_size tv /\ 0 < bytes /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  stmt_state_rel H ctx func c cx es1 s /\
  immutable_holds c cx ty (Value v) a es1 s /\
  copy_old_operand sa src /\ not_fresh_at sa p /\
  eval_operand src s = SOME a /\ lookup_var p s = SOME w /\
  w2n w + bytes < dimword (:256) /\
  (c.ce_is_ctor ==> regions_disjoint (w2n a) bytes (w2n w) bytes) /\
  (!region. c.ce_is_ctor /\ c.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) /\
  alloca_frame c es0 sa0 s0 c es1 s /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP s.vs_allocas aid = SOME b) /\
  venomMemDefs$allocas_non_overlapping s /\
  FLOOKUP s.vs_allocas aid0 = SOME (w2n w,capacity) /\
  sa0.cs_next_id <= aid0 /\ bytes <= capacity /\
  FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) capacity) /\
  es1.scopes = sc :: rest /\ ee.scopes = (sc |+ (id,entry)) :: rest /\
  local_ptrs_reserved c sa ==>
  ?z. copy_runtime_frame sa s sb z /\
      val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
      val_footprint tv v <= bytes /\
      LENGTH s.vs_memory <= LENGTH z.vs_memory /\
      (!off len. off + len <= w2n w \/ w2n w + bytes <= off ==>
        mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
      (z with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      alloca_frame c es0 sa0 s0 c ee z
Proof
  strip_tac >>
  `copy_old_operand sa (Var p)` by simp[copy_old_operand_def] >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  drule_all immutable_iter_copy_typed_run_full >> strip_tac >>
  qexists_tac `z` >> asm_rewrite_tac[] >>
  irule alloca_frame_declare_store >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`aid0`, `s`, `sa0`, `w`] >>
  asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL] >>
  conj_tac >- gvs[copy_runtime_frame_def] >>
  rpt gen_tac >> strip_tac >>
  `aid <> aid0` by decide_tac >>
  `off + z' <= w2n w \/ w2n w + capacity <= off` by
    (qpat_x_assum `allocas_non_overlapping s`
       (mp_tac o REWRITE_RULE [venomMemDefsTheory.allocas_non_overlapping_def]) >>
     strip_tac >> first_x_assum drule_all >> simp[]) >>
  first_x_assum irule >> decide_tac
QED
