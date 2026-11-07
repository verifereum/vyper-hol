(* Actual counted paths for storage/transient word-copy loops. *)
Theory storageCopyGasPath
Ancestors
  exprSimStorageCopy bodyStorageCopyMemory gasSummary fragGasMode
  fragGasPath fragGasPathMem fragGasSeq fragGasSeqMem
  fragExec fragExecMem gasCount context compileEnv emitHelper emitHelperProps
  exprLoweringProps loweringSlice instMemFrontier
  memSafeRun venomExecSemantics venomState venomInst
  words arithmetic list rich_list finite_map
Libs
  monadsyntax

Theorem storage_copy_seq_path:
  !code s t memory ctx func bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
    EVERY (\i. i.inst_opcode <> GAS) code /\
    (memory ==> run_inst_seq_mem_ok code s) /\
    run_inst_seq code s = OK t ==>
    gas_marked_path memory ctx func s 0
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code))
Proof
  cheat
QED

Theorem storage_copy_jump_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ) /\
  step_inst_base inst s = OK (jump_to lbl s) ==>
  gas_marked_path memory ctx func s 0 (OK (jump_to lbl s))
Proof
  cheat
QED

Theorem storage_copy_inv_control[local]:
  storage_copy_inv cv ds loc a b n sbase k s ==>
  storage_copy_inv cv ds loc a b n sbase k (jump_to lbl s) /\
  storage_copy_inv cv ds loc a b n sbase k (s with vs_inst_idx := idx)
Proof
  cheat
QED

Theorem storage_copy_init_path[local]:
  ~s.vs_halted /\ MEM cv ds /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ASSIGN [Lit 0w] [cv]]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_marked_path memory ctx func s 0 (OK t) /\
      storage_copy_inv cv ds loc a b n s 0 t /\
      ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx + 1
Proof
  cheat
QED

Theorem storage_copy_test_path[local]:
  ~s.vs_halted /\ cv <> tv /\ MEM tv ds /\ k <= n /\ n < 2**256 /\
  storage_copy_inv cv ds loc a b n sbase k s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id EQ [Var cv; Lit (n2w n)] [tv]]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_marked_path memory ctx func s 0 (OK t) /\
      storage_copy_test cv tv ds loc a b n sbase k t /\
      ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx + 1
Proof
  cheat
QED

Theorem storage_copy_body_run_inv[local]:
  run_inst_seq
    [mk_inst id ADD [src; Var cv] [sv];
     mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
     mk_inst (id+2) MUL [Var cv; Lit 32w] [mv];
     mk_inst (id+3) ADD [dst; Var mv] [dv];
     mk_inst (id+4) MSTORE [Var dv; Var vv] [];
     mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv]] s = OK t ==>
  storage_copy_inv cv ds loc a b n sbase k s /\
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [cv;sv;vv;mv;dv;nv]) /\
  (!x. MEM x [cv;sv;vv;mv;dv;nv] ==> MEM x ds) /\
  k < n /\ b+32*n < 2**256 /\
  eval_operand (Var cv) t = SOME (n2w k + 1w) /\
  (!x. ~MEM x [cv;sv;vv;mv;dv;nv] ==> lookup_var x t = lookup_var x s) ==>
  storage_copy_inv cv ds loc a b n sbase (k+1) t
Proof
  cheat
QED

Theorem storage_copy_body_path[local]:
  code =
    [mk_inst id ADD [src; Var cv] [sv];
     mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
     mk_inst (id+2) MUL [Var cv; Lit 32w] [mv];
     mk_inst (id+3) ADD [dst; Var mv] [dv];
     mk_inst (id+4) MSTORE [Var dv; Var vv] [];
     mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv]] /\
  ~s.vs_halted /\ storage_copy_inv cv ds loc a b n sbase k s /\
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [cv;sv;vv;mv;dv;nv]) /\
  (!x. MEM x [cv;sv;vv;mv;dv;nv] ==> MEM x ds) /\
  k < n /\ b+32*n < 2**256 /\
  (memory ==> b+32*n <= s.vs_alloca_next) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_marked_path memory ctx func s 0 (OK t) /\
      storage_copy_inv cv ds loc a b n sbase (k+1) t /\
      ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx + 7
Proof
  cheat
QED

Theorem storage_copy_path_jmp[local]:
  gas_marked_path memory ctx func s 0 (OK r) /\
  storage_copy_inv cv ds loc a b n sbase k r /\ ~r.vs_halted /\
  lookup_block r.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb r.vs_inst_idx = SOME (mk_inst id JMP [Label hdr] []) ==>
  gas_marked_path memory ctx func s 0 (OK (jump_to hdr r)) /\
  storage_copy_inv cv ds loc a b n sbase k (jump_to hdr r) /\
  ~(jump_to hdr r).vs_halted /\
  (jump_to hdr r).vs_current_bb = hdr /\ (jump_to hdr r).vs_inst_idx = 0
Proof
  cheat
QED

Theorem storage_copy_path_jnz[local]:
  gas_marked_path memory ctx func s 0 (OK r) /\
  storage_copy_test cv tv ds loc a b n sbase k r /\ ~r.vs_halted /\
  lookup_block r.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb r.vs_inst_idx =
    SOME (mk_inst id JNZ [Var tv; Label exit; Label loop_body] []) ==>
  gas_marked_path memory ctx func s 0
    (OK (jump_to (if k = n then exit else loop_body) r)) /\
  storage_copy_inv cv ds loc a b n sbase k
    (jump_to (if k = n then exit else loop_body) r) /\
  ~(jump_to (if k = n then exit else loop_body) r).vs_halted /\
  (jump_to (if k = n then exit else loop_body) r).vs_current_bb =
    (if k = n then exit else loop_body) /\
  (jump_to (if k = n then exit else loop_body) r).vs_inst_idx = 0
Proof
  cheat
QED

Theorem storage_copy_iterate_path[local]:
  !(remaining:num) k s.
  (!j q. j <= n /\ Inv j q /\ ~q.vs_halted /\
          q.vs_current_bb = hdr /\ q.vs_inst_idx = 0 ==>
     ?r. gas_marked_path memory ctx func q 0 (OK r) /\ Inv j r /\
         ~r.vs_halted /\ r.vs_inst_idx = 0 /\
         r.vs_current_bb = (if j = n then exit else loop_body)) /\
  (!j q. j < n /\ Inv j q /\ ~q.vs_halted /\
          q.vs_current_bb = loop_body /\ q.vs_inst_idx = 0 ==>
     ?r. gas_marked_path memory ctx func q 0 (OK r) /\ Inv (j+1) r /\
         ~r.vs_halted /\ r.vs_current_bb = hdr /\ r.vs_inst_idx = 0) /\
  k + remaining = n /\ Inv k s /\ ~s.vs_halted /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?t. gas_marked_path memory ctx func s 0 (OK t) /\ Inv n t /\
      ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0
Proof
  cheat
QED

Theorem storage_copy_code_prefix:
  !sa sb func. fn_has_code sa sb func /\ same_blocks sa sb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts ==>
  ?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts sa sb)
         (DROP (LENGTH sa.cs_current_insts) bb.bb_instructions)
Proof
  cheat
QED

(* The exit block may have PHIs: its compiled instruction prefix is empty.
   The actual final jump can therefore land at index zero. *)
Theorem compile_storage_copy_content_capacity_path:
  !memory (ctx,func) loc src dst n sa u sb sbase a b.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_word_copy_loop src dst n loc LocMemory F sa = (u,sb) /\
    fn_has_code sa sb func /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src sbase = SOME a /\
    eval_operand dst sbase = SOME (n2w b) /\
    n < 2**256 /\ b+32*n < 2**256 /\
    (memory ==> b+32*n <= sbase.vs_alloca_next) /\
    ~sbase.vs_halted /\
    sbase.vs_current_bb = sa.cs_current_bb /\
    sbase.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path memory ctx func sbase 0 (OK t) /\
        copy_prefix loc a b n sbase n t /\
        LENGTH sbase.vs_memory <= LENGTH t.vs_memory /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x sbase) /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED
