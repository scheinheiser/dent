open! Language
open! Parser

let border () =
  Seq.init 30 (fun _ -> '-') |> String.of_seq |> print_endline;
  print_newline ()


let () =
  let input = In_channel.(open_text "examples/test.dent" |> input_all) in
  (* let input = "{a : Type} -> {b : Type} -> (a -> b) -> List a -> List b" in *)
  let l = Lexer.of_string input in
  let res = Parser.parse_program l in
  match res with
  | Ok res -> (
      Ast.pp_program Format.std_formatter res;
      border ();
      let res = Elab.check_program res in
      match res with
      | Error e -> print_endline (Base.Error.to_string_hum e)
      | Ok res -> Elab.pp_program Format.std_formatter res)
  | Error e -> print_endline (Base.Error.to_string_hum e)
