open preamble basis ml_progTheory astPP fromSexpTheory astToSexprLib
open listrevTheory

val _ = new_theory "listrevProg";

val _ = translation_extends "basisProg"

Definition help_string_def:
  help_string = concat $ MAP (λx. strlit $ x ++ "\n") [
    "rev - reverse lines characterwise";
    "";
    "usage: rev [option] [file...]";
    "";
    "The rev utility copies the specified files to standard output, reversing";
    "the order of characters in every line. If no files are specified, standard";
    "input is read.";
    "";
    "OPTIONS";
    "  -h, --help   Display help text and exit.";
    "  -0, --zero   Zero termination. Use the byte '\\0' as line separator.";
    "";
    "(Text from util-linux <https://www.kernel.org/pub/linux/utils/util-linux/>)";
    ""
  ]
End

Theorem help_string_thm = EVAL ``help_string``

val _ = translate qrev_acc_def
val _ = translate qrev_def
val _ = translate help_string_thm

val res = append_prog o process_topdecs $ `
fun main () =
let
  val args = CommandLine.arguments()
  val zero_flags = ["-0","--zero"]
  val help_flags = ["-h","--help"]
  val help = List.exists (fn f => List.member f help_flags) args
  val zero = List.exists (fn f => List.member f zero_flags) args
  val args_filter = List.filter
    (fn f => not(List.member f (zero_flags @ help_flags))) args
  val split_char = Char.chr (if zero then 0 else 10)
  val content = case args_filter of
     [] => TextIO.inputAll TextIO.stdIn
    | args => String.concat (List.map (TextIO.inputAll o TextIO.openIn) args)
  val content_lines = String.tokens (fn c => c = split_char) content
in
  if help then
    TextIO.print help_string
  else
    TextIO.print
      (String.concatWith
        (String.str split_char)
        (List.map (String.implode o qrev o String.explode) content_lines))
end;
`;

val prog =
  ``SNOC
    (Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short "main"); Con NONE []]))
    ^(get_ml_prog_state() |> get_prog)
  `` |> EVAL |> concl |> rhs

val _ = astToSexprLib.write_ast_to_file "revProg.sexp" prog;

val _ = export_theory ();
