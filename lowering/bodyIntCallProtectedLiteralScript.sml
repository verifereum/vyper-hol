(* Byte-chunk stores carry protected regions and reserved operands on one run. *)
Theory bodyIntCallProtectedLiteral
Ancestors
  exprSimLiteralBuffer exprLoweringProps exprLowering compileEnv loweringStateRelDefs
  venomState venomInst valueEncoding list words

Theorem protected_literal_chunks_run:
  !ptr bs off sa sb s b P reserved.
    compile_store_byte_chunks ptr bs off sa = ((),sb) /\
    (!x. ptr = Var x ==> not_fresh_at sa x) /\
    eval_operand ptr s = SOME (n2w b) /\ b < dimword (:256) /\
    b + off + 32 * word_size (LENGTH bs) < dimword (:256) /\
    (!a len. P a len ==>
      regions_disjoint a len (b+off) (32 * word_size (LENGTH bs))) /\
    (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      mem_bytes_at (b+off) (LENGTH bs) t.vs_memory = bs /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. P a len ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      (!op. reserved op ==> eval_operand op t = eval_operand op s) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  rpt strip_tac >>
  drule_all literal_chunks_run >> strip_tac >> simp[] >>
  conj_tac >- gvs[venom_state_component_equality] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      metis_tac[regions_disjoint_def]) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `op` >>
      gvs[eval_operand_def, venom_state_component_equality]) >>
  gvs[venom_state_component_equality]
QED
