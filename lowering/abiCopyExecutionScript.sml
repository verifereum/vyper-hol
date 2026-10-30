(* TOP-LEVEL: compile_abi_copy_frag.
   Exact CFG execution of the production ABI bulk-copy case, including padded
   source reads and a disjoint frame for previously saved memory slices. *)
Theory abiCopyExecution
Ancestors
  copyExecution createSourceCallback abiEncoder emitHelper
  compileEnv context venomState list words

Theorem compile_abi_copy_shape:
  compile_abi_encode_to_buf dst src (AbiCopy n) cs = (result,cs') ⇔
  result = Lit (n2w n) ∧
  compile_copy_memory_dynamic dst src (Lit (n2w n)) cs = ((),cs')
Proof
  simp[Once compile_abi_encode_child_def, compile_copy_memory_dynamic_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `emit_void MCOPY [dst;src;Lit (n2w n)] cs` >> simp[] >> metis_tac[]
QED

Theorem compile_abi_copy_frag:
  n < 2 ** 256 ∧
  compile_abi_encode_to_buf dst src (AbiCopy n) cs = (result,cs') ⇒
  result = Lit (n2w n) ∧ cs_extends cs cs' ∧
  frag_exec ctx cs cs'
    (λs. fresh_vars_wrt cs s ∧
         eval_operand dst s = SOME d ∧ eval_operand src s = SOME p ∧
         create_live live s ∧ create_memory_snapshot regions s ∧
         EVERY (λ(off,bs). off + LENGTH bs ≤ LENGTH s.vs_memory ∧
           (off + LENGTH bs ≤ w2n d ∨ w2n d + n ≤ off)) regions ∧
         read_memory (w2n p) n s = bytes)
    (λs. fresh_vars_wrt cs' s ∧ create_live live s ∧
         create_memory_snapshot ((w2n d,bytes)::regions) s)
    (K F)
Proof
  strip_tac >> gvs[compile_abi_copy_shape] >>
  drule compile_copy_memory_dynamic_frag >>
  disch_then (qspecl_then [`regions`, `p`, `n2w n : bytes32`, `live`, `d`,
                          `ctx`, `bytes`] mp_tac) >>
  simp[eval_operand_def, w2n_n2w, dimword_def]
QED
