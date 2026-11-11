(* Boundary probes for the callee's protected-memory invariant. *)
Theory bodyIntCallFrameProbe
Ancestors
  intCallFrame valueEncoding valueEncodingProps compileEnv venomState
  vyperValue vyperAST

(* Constructor zero values may be represented entirely by implicit memory
   padding.  Preserving a region does not require it to be materialized. *)
Theorem implicit_zero_memory_frame_probe[local]:
  !s. val_in_memory (BaseTV BoolT) (BoolV F) 0 [] /\
      mem_bytes_at 0 32
        (mstore 64 1w (s with vs_memory := [])).vs_memory =
      mem_bytes_at 0 32 []
Proof
  gen_tac >> conj_tac
  >- (EVAL_TAC >> simp[]) >>
  simp[mstore_mem_bytes_at_disjoint]
QED
