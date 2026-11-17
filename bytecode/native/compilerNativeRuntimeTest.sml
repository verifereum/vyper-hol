(*
 * Checks of compilerNativeRuntime's primitives against their HOL definitions.
 * Run from this directory:  poly --script compilerNativeRuntimeTest.sml
 * Exits non-zero if any check fails.
 *)
use "compilerNativeRuntime.sml";
open compilerNativeRuntime;

val failures = ref 0;
fun check name expected actual =
  if actual = SOME expected then ()
  else (failures := !failures + 1;
        print ("FAIL " ^ name ^ ": expected " ^ IntInf.toString expected ^
               ", got " ^ (case actual of SOME v => IntInf.toString v
                                        | NONE => "an exception") ^ "\n"));
fun run f = SOME (f ()) handle _ => NONE;

(* 2^256 - 1, the largest uint256 and so the largest exponent a program has. *)
val huge = IntInf.<< (1, 0w256) - 1;

(* EXP: 0 EXP 0 = 1, 0 EXP SUC n = 0, 1 EXP n = 1, and ordinary powers. *)
val () = check "0 EXP 0" 1 (run (fn () => hn_EXP 0 0));
val () = check "0 EXP 5" 0 (run (fn () => hn_EXP 0 5));
val () = check "0 EXP huge" 0 (run (fn () => hn_EXP 0 huge));
val () = check "1 EXP 0" 1 (run (fn () => hn_EXP 1 0));
val () = check "1 EXP huge" 1 (run (fn () => hn_EXP 1 huge));
val () = check "7 EXP 0" 1 (run (fn () => hn_EXP 7 0));
val () = check "2 EXP 255" (IntInf.<< (1, 0w255)) (run (fn () => hn_EXP 2 255));
val () = check "3 EXP 5" 243 (run (fn () => hn_EXP 3 5));
val () = check "10 EXP 18" 1000000000000000000 (run (fn () => hn_EXP 10 18));
(* 2 EXP 2^64 can't be built: it must raise Overflow, not wrap the exponent. *)
val () = if (ignore (hn_EXP 2 (IntInf.<< (1, 0w64))); false) handle Overflow => true
         then ()
         else (failures := !failures + 1;
               print "FAIL 2 EXP 2^64: expected Overflow\n");

(* int ** num, as the generator exports it:
   i ** n = if i < 0 /\ ODD n then ~&(Num i EXP n) else &(Num i EXP n). *)
fun int_exp i n =
  if hn_int_lt i (hn_int_of_num 0) andalso hn_ODD n
  then hn_int_neg (hn_int_of_num (hn_EXP (hn_Num i) n))
  else hn_int_of_num (hn_EXP (hn_Num i) n);
val () = check "~1 ** huge" (~1) (run (fn () => int_exp (~1) huge));
val () = check "~1 ** (huge - 1)" 1 (run (fn () => int_exp (~1) (huge - 1)));
val () = check "~1 ** 0" 1 (run (fn () => int_exp (~1) 0));
val () = check "0 ** huge" 0 (run (fn () => int_exp 0 huge));
val () = check "~2 ** 3" (~8) (run (fn () => int_exp (~2) 3));

val () = if !failures = 0 then print "compilerNativeRuntimeTest: all checks passed\n"
         else (print ("compilerNativeRuntimeTest: " ^ Int.toString (!failures) ^
                      " checks failed\n");
               OS.Process.exit OS.Process.failure);
