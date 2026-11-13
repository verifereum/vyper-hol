(* A program that never reads self.code runs the same whatever code its
   transaction carries.

   The source semantics reads the transaction's code (cx.txn.code) only in
   evaluate_code_source, for slice(self.code, ...), which
   ~program_reads_self_code excludes.  The optimizer case of the top
   theorems uses this to run the lowering proof (whose entry relation pins
   the Venom state's code to tx.code) on the unoptimized code layout while
   the frame runs the optimized one.  The deployment also evaluates
   constant initialisers, which program_reads_self_code doesn't scan;
   supported_program excludes Constant declarations.

   TOP-LEVEL: call_external_self_code_free, load_contract_self_code_free.
 *)
Theory e2eSelfCodeFree
Ancestors
  e2eProducers supportedProgram vyperInterpreter

Theorem call_external_self_code_free:
  !orc gobs am tx c tops.
    ALOOKUP am.sources tx.target = SOME [(NONE, tops)] /\
    ~program_reads_self_code tops ==>
    call_external orc gobs am (tx with code := c) =
    call_external orc gobs am tx
Proof
  cheat
QED

Theorem load_contract_self_code_free:
  !orc gobs am tx c tops.
    supported_program tops /\ ~program_reads_self_code tops ==>
    load_contract orc gobs am (tx with code := c) [(NONE, tops)] [] =
    load_contract orc gobs am tx [(NONE, tops)] []
Proof
  cheat
QED
