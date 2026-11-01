Theory unwrapCopyBoundaryProbe
Ancestors
  valueEncoding venomExecSemantics venomInst venomState finite_map
Libs
  wordsLib

(* The semantic allocator has no Python-sized allocation rejection. *)
Theorem alloca_large_success:
  !s. exec_alloca (mk_inst 0 ALLOCA [Lit (n2w (2 ** 64))] ["out"])
          (s with vs_allocas := FEMPTY) (n2w (2 ** 64) : bytes32) =
      OK (update_var "out" (n2w s.vs_alloca_next)
        (s with <| vs_allocas := FEMPTY |+ (0, (s.vs_alloca_next, 2 ** 64));
                   vs_alloca_next := s.vs_alloca_next + 2 ** 64 |>))
Proof
  simp[exec_alloca_def, mk_inst_def, wordsTheory.dimword_def]
QED

Theorem dynamic_bytes_large_size:
  type_memory_size (BaseTV (BytesT (Dynamic (2 ** 64)))) = 32 + 2 ** 64
Proof
  simp[type_memory_size_def, vfmConstantsTheory.word_size_def] >> decide_tac
QED
