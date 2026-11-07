(* Identity unwrap branches require a certified string buffer explicitly;
   a stack word's pointer-value predicate alone does not provide one. *)
Theory revertReasonIdentityPtr
Ancestors
  revertReasonTailCodePtr reasonMemoryUnwrapPtr exprLowering context compileEnv
  bodyPtrDefs venomInst venomState venomMemDefs words arithmetic finite_map


Theorem revert_reason_identity_unwrap_path_ptr:
  (vv = StackValue ty (Var src) \/
   (vv = LocatedValue ty r /\ ~is_word_type ty /\
    r.ptr_location = LocMemory /\ r.ptr_operand = Var src)) /\
  unwrap_value cenv vv sm = (out,sn) /\
  fn_has_code sn sb fn /\ sb.cs_current_bb = sn.cs_current_bb /\
  sb.cs_current_insts = sn.cs_current_insts ++
    (revert_reason_copy sn.cs_next_id sn.cs_next_var (Var q) out ++
     revert_reason_suffix sn.cs_next_id sn.cs_next_var (Var b) (Var p) (Var q)) /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~s.vs_halted /\
  not_fresh_at sm b /\ not_fresh_at sm p /\
  not_fresh_at sm q /\ not_fresh_at sm src /\
  lookup_var b s = SOME B /\ lookup_var p s = SOME P /\
  lookup_var q s = SOME Q /\ lookup_var src s = SOME A /\
  ptr_covers G tn b s (64+ms) /\ ptr_covers G tn p s (32+ms) /\
  ptr_covers G tn q s ms /\
  ptr_covers G tn src s (32+contractABI$ceil32 L) /\
  mload (w2n A) s = n2w L /\
  (!j. w2n A <= j /\ j < w2n A+32 ==> j NOTIN tn.t_mem) /\
  32+contractABI$ceil32 L <= ms /\ L+63 < dimword(:256) /\
  64+ms < dimword(:256) /\ w2n B+64+ms < dimword(:256) /\
  w2n P+32+ms < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ alloca_inv s /\ alloca_room ctx fn s /\
  (!a sz. FLOOKUP s.vs_allocas (sm.cs_next_id+5) = SOME (a,sz) ==> sz = 32) /\
  FLOOKUP s.vs_allocas parent = SOME (w2n Q,ms) /\ parent <> sm.cs_next_id+5 ==>
  ?z Gf tnf. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (Abort Revert_abort z)
Proof
  strip_tac >>
  `out = Var src /\ sn = sm` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     asm_rewrite_tac[unwrap_value_def, comp_return_def] >> simp[NoAsms, comp_return_def]) >>
  qpat_x_assum `out = Var src` SUBST_ALL_TAC >>
  qpat_x_assum `sn = sm` SUBST_ALL_TAC >>
  drule_at (Pat `_ = _ ++ _`) revert_reason_tail_at_compile_endpoint_ptr >>
  disch_then drule_all >> simp[]
QED
