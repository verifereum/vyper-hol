(* Relative member navigation reads only its checked offset word. *)
Theory abiDecodeSelectionMem
Ancestors
  abiDecodePtrHead abiDecodePtrRead abiEncoderWindowSequence
  bodyPtrBopScalarSeq bodyPtrBopScalarCompile fragExecMem
  abiDecoderGuard abiEncoder emitHelperProps exprLoweringProps
  compileEnv venomState venomExecSemantics words list rich_list arithmetic

Theorem abi_decode_selection_prefix_mem_ok[local]:
  emit_op ADD [pos; Lit (n2w off)] sa = (head,c1) /\
  compile_abi_dec_addr (Var src) head c1 = (addr,c2) /\
  emit_op MLOAD [addr] c2 = (offset,c3) /\
  not_fresh_at sa src /\ lookup_var src s = SOME b /\
  eval_operand pos s = SOME z /\ p = w2n (z + n2w off) /\
  w2n b+p < dimword(:256) /\ w2n b+p+32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa c3) s
Proof
  strip_tac >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off)` by simp[eval_operand_def] >>
  drule_all window_emit_add_pure >> strip_tac >>
  `lookup_var src t = SOME b /\ eval_operand head t = SOME (n2w p) /\
   t.vs_alloca_next = s.vs_alloca_next` by
    fs[window_pure_seq_def, window_seq_def] >>
  `run_inst_seq_mem_ok (emitted_insts c1 c3) t` by
    (irule abi_decode_relative_load_mem_ok >>
     goal_assum (drule_at (Pat `compile_abi_dec_addr _ _ _ = _`)) >>
     qexistsl_tac [`b`, `p`, `offset`] >> simp[]) >>
  `bop_scalar_seq {} UNIV (emitted_insts sa c1) (head INSERT UNIV)` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl_tac [`ADD`, `[pos; Lit (n2w off)]`] >> simp[]) >>
  `inst_extends c1 c3` by
    (fs[compile_abi_dec_addr_def] >>
     metis_tac[inst_extends_emit_op, inst_extends_trans]) >>
  `emitted_insts sa c3 = emitted_insts sa c1 ++ emitted_insts c1 c3` by
    (irule emitted_insts_append >> fs[window_pure_seq_def, window_seq_def,
       inst_extends_def]) >>
  pop_assum SUBST1_TAC >> match_mp_tac run_inst_seq_mem_ok_append >> conj_tac
  >- metis_tac[bop_scalar_seq_mem_ok] >>
  fs[window_pure_seq_def, window_seq_def] >> metis_tac[]
QED

Theorem abi_decode_getelemptr_mem_ok:
  compile_getelemptr_abi pos dyn off MLOAD (Var src) hi sa = (v,sb) /\
  not_fresh_at sa src /\ lookup_var src s = SOME b /\
  eval_operand pos s = SOME z /\ p = w2n (z + n2w off) /\
  (dyn ==> w2n b+p < dimword(:256) /\ w2n b+p+32 <= s.vs_alloca_next) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> Cases_on `dyn` >> fs[]
  >- (drule abi_decode_getelemptr_dynamic_split >> strip_tac >>
      mp_tac (abi_decode_selection_prefix_mem_ok |> Q.INST
        [`sa` |-> `sa`, `c1` |-> `c1`, `c2` |-> `c2`, `c3` |-> `c3`,
         `pos` |-> `pos`, `off` |-> `off`, `head` |-> `head`, `addr` |-> `addr`,
         `offset` |-> `offset`, `src` |-> `src`, `s` |-> `s`, `b` |-> `b`,
         `p` |-> `p`, `z` |-> `z`]) >>
      (impl_tac >- simp[]) >> strip_tac >>
      `?A. bop_scalar_seq {} UNIV (emitted_insts c3 sb) A /\ v IN A` by
        (irule abi_decode_position_suffix_scalar >> simp[] >> metis_tac[]) >>
      `inst_extends sa c3 /\ inst_extends c3 mid` by
        (fs[compile_abi_dec_addr_def] >>
         metis_tac[inst_extends_emit_op, inst_extends_trans]) >>
      `inst_extends mid sb` by
        (Cases_on `hi = Lit 0w` >> gvs[] >- simp[inst_extends_refl] >>
         drule abi_decode_ge_guard_shape >> simp[]) >>
      `emitted_insts sa sb = emitted_insts sa c3 ++ emitted_insts c3 sb` by
        (irule emitted_insts_append >> conj_tac
         >- fs[inst_extends_def] >>
         `inst_extends c3 sb` by metis_tac[inst_extends_trans] >>
         fs[inst_extends_def]) >>
      pop_assum SUBST1_TAC >> match_mp_tac run_inst_seq_mem_ok_append >>
      simp[] >> metis_tac[bop_scalar_seq_mem_ok]) >>
  `emit_op ADD [pos; Lit (n2w off)] sa = (v,sb)` by
    (Cases_on `emit_op ADD [pos; Lit (n2w off)] sa` >>
     fs[compile_getelemptr_abi_def, comp_bind_def, comp_return_def]) >>
  `bop_scalar_seq {} UNIV (emitted_insts sa sb) (v INSERT UNIV)` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl_tac [`ADD`, `[pos; Lit (n2w off)]`] >> simp[]) >>
  metis_tac[bop_scalar_seq_mem_ok]
QED
