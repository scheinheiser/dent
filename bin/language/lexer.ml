open Util
open Token

(* utility *)
let report_err err =
  Error.pp_err Format.err_formatter err;
  exit 1


let with_pos (l : Sedlexing.lexbuf) (t : token) = (Location.of_lexbuf l, t)
let lexeme = Sedlexing.Utf8.lexeme
let lexeme_char l = Sedlexing.Utf8.sub_lexeme l 0 1 |> Fun.flip String.get 0
let is_upper (s : string) = match s.[0] with 'A' .. 'Z' -> true | _ -> false
let is_dot_separated (s : string) = String.exists (( = ) '.') s

let keywords =
  [
    ("if", IF);
    ("then", THEN);
    ("else", ELSE);
    ("let", LET);
    ("in", IN);
    ("end", END);
    ("rassoc", RASSOC);
    ("lassoc", LASSOC);
    ("module", MODULE);
    ("import", IMPORT);
    ("Int", TY_INT);
    ("Float", TY_FLOAT);
    ("Char", TY_CHAR);
    ("String", TY_STRING);
    ("Bool", TY_BOOL);
    ("Unit", TY_UNIT);
    ("Atom", TY_ATOM);
    ("with", WITH);
    ("without", WITHOUT);
    ("true", BOOL true);
    ("false", BOOL false);
    ("when", WHEN);
    ("where", WHERE);
    ("match", MATCH);
    ("to", TO);
    ("dec", DEC);
    ("def", DEF);
    ("type", TYPE);
    ("alias", ALIAS);
    ("union", UNION);
    ("record", RECORD);
    ("constructor", CONSTRUCTOR);
    ("universe", UNIVERSE);
    ("Type", TTYPE);
    ("fun", FUN);
    ("λ", FUN);
  ]


let builtin_symbol =
  [
    (":=", ASSIGNMENT);
    ("=", EQ);
    ("=>", F_ARROW);
    ("⇒", F_ARROW);
    ("->", ARROW);
    ("→", ARROW);
    ("→", ARROW);
    ("@", ATSIGN);
    ("|", PIPE);
  ]


let digit = [%sedlex.regexp? '0' .. '9']
let letter = [%sedlex.regexp? 'a' .. 'z' | 'A' .. 'Z']
let int = [%sedlex.regexp? Opt '-', digit, Star (digit | '_')]
let float = [%sedlex.regexp? Opt '-', Plus digit, '.', Plus digit]

(* https://www.unicode.org/charts *)
let utf_letter =
  [%sedlex.regexp?
    0x0370 .. 0x03FF | 0x1D539 | 0x2102 | 0x210D | 0x2115 | 0x2119 | 0x211A | 0x211D | 0x2124]


let utf_op = [%sedlex.regexp? 0x2200 .. 0x22FF | 0x2190 .. 0x21FF | 0x00D7 | 0x00AC]

let symbol =
  [%sedlex.regexp?
    ( '_' | '-' | '+' | '*' | '\\' | '&' | '(' | ')' | '{' | '}' | '=' | '|' | '@' | '>' | '<' | '%'
    | '$' | '^' | '#' | '!' | ';' | ':' | '?' | '.' | ',' )]


let op =
  [%sedlex.regexp?
    ( '+' | '-' | '!' | '%' | '^' | '&' | '*' | '>' | '<' | '=' | '/' | '~' | '#' | '$' | '.' | '|'
    | '@' | ':' | ',' | utf_op )]


let newline = [%sedlex.regexp? '\n' | '\r' | "\r\n"]
let whitespace = [%sedlex.regexp? Plus (' ' | '\t')]
let str = [%sedlex.regexp? ' ' | '\'' | letter | digit | symbol | newline]
let ident = [%sedlex.regexp? letter, Star ('_' | '.' | letter | digit) | utf_letter]

let rec token lexbuf =
  match%sedlex lexbuf with
  | Plus whitespace | Plus newline -> token lexbuf
  | int -> with_pos lexbuf (INT (lexeme lexbuf |> int_of_string))
  | float -> with_pos lexbuf (FLOAT (lexeme lexbuf |> float_of_string))
  | '{' -> with_pos lexbuf LBRACE
  | '}' -> with_pos lexbuf RBRACE
  | "()" -> with_pos lexbuf UNIT
  | '(' -> with_pos lexbuf LPAREN
  | ')' -> with_pos lexbuf RPAREN
  | '[' -> with_pos lexbuf LBRACE
  | ']' -> with_pos lexbuf RBRACE
  | '|' -> with_pos lexbuf PIPE
  | "(*" -> comment 0 lexbuf
  | ':' -> with_pos lexbuf COLON
  | ';' -> with_pos lexbuf SEMI
  | ',' -> with_pos lexbuf COMMA
  | '_' -> with_pos lexbuf WILDCARD
  | Plus op ->
      let op' = lexeme lexbuf in
      let tok = match List.assoc_opt op' builtin_symbol with Some op' -> op' | None -> OP op' in
      with_pos lexbuf tok
  | '\'' -> char lexbuf
  | '"' -> string (Buffer.create 20) lexbuf
  | ident ->
      let i = lexeme lexbuf in
      let tok =
        match List.assoc_opt i keywords with
        | Some t -> t
        | None when is_upper i -> UPPER_IDENT i
        | None when is_dot_separated i -> DOT_SEP_IDENT (String.split_on_char '.' i)
        | None -> IDENT i
      in
      with_pos lexbuf tok
  | eof -> with_pos lexbuf EOF
  | _ ->
      let c = lexeme_char lexbuf in
      report_err (Some (Location.of_lexbuf lexbuf), Printf.sprintf "Unrecognised character: %C." c)


and comment n lexbuf =
  match%sedlex lexbuf with
  | "(*" -> comment (n + 1) lexbuf
  | "*)" -> if n = 0 then token lexbuf else comment (n - 1) lexbuf
  | eof -> report_err (Some (Location.of_lexbuf lexbuf), "Unterminated comment.")
  | _ ->
      ignore (Sedlexing.next lexbuf);
      comment n lexbuf


and char lexbuf =
  match%sedlex lexbuf with
  | '\\' -> control lexbuf
  | eof -> report_err (Some (Location.of_lexbuf lexbuf), "Unterminated char.")
  | (letter | digit | symbol), '\'' -> with_pos lexbuf (CHAR (lexeme_char lexbuf))
  | _ ->
      let c = lexeme_char lexbuf in
      report_err (Some (Location.of_lexbuf lexbuf), Printf.sprintf "Invalid char: %C" c)


and control lexbuf =
  match%sedlex lexbuf with
  | 'n', '\'' -> with_pos lexbuf (CHAR '\n')
  | 't', '\'' -> with_pos lexbuf (CHAR '\t')
  | 'b', '\'' -> with_pos lexbuf (CHAR '\b')
  | '\\', '\'' -> with_pos lexbuf (CHAR '\\')
  | _ ->
      let c = lexeme_char lexbuf in
      report_err (Some (Location.of_lexbuf lexbuf), Printf.sprintf "Invalid escape sequence: %C" c)


and string b lexbuf =
  match%sedlex lexbuf with
  | '"' -> with_pos lexbuf (STRING (Buffer.contents b))
  | str ->
      Buffer.add_string b (lexeme lexbuf);
      string b lexbuf
  | eof -> report_err @@ (Some (Location.of_lexbuf lexbuf), "Unterminated string.")
  | _ ->
      let c = lexeme_char lexbuf in
      report_err (Some (Location.of_lexbuf lexbuf), Printf.sprintf "Invalid string character: %C" c)
