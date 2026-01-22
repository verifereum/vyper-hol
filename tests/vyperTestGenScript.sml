Theory vyperTestGen[no_sig_docs]
Libs
  vyperTestLib

val () =
  (vyperTestLib.generate_defn_scripts();
   vyperTestLib.generate_test_scripts())
