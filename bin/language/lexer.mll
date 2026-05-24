{
  open Lexing
  open Util
  open Token

  let report_err err =
    Error.pp_err Format.err_formatter err;
    exit 1

  let next_line lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_bol = lexbuf.lex_curr_pos;
                 pos_lnum = pos.pos_lnum + 1
      }

  let with_pos (l: lexbuf) (t: token) = Location.of_lexbuf l, t

  let is_upper (s: string) =
    match s.[0] with
    | 'A' .. 'Z' -> true
    | _ -> false

  let is_dot_separated (s: string) = String.exists (( = ) '.') s

  let keywords = [
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
  ]

  let builtin_symbol = [
    (":=", ASSIGNMENT);
    ("=", EQ);
    ("=>", F_ARROW);
    ("->", ARROW);
    ("@", ATSIGN);
    ("|", PIPE);
  ]
}

let int = '-'? ['0'-'9'] ['0'-'9' '_']*
let float = '-'? ['0'-'9']+ '.' ['0'-'9']+

let symbol = ['-' '+' '*' '\\' '&' '(' ')' '{' '}' '=' '|' '@' '>' '<' '%' '$' '^' '#' '!' ';' ':' '?' '.' ',']
let op = ['+' '-' '!' '%' '^' '&' '*' '>' '<' '=' '/' '~' '#' '$' '.' '|' '@' ':']

let newline = '\n' | '\r' | "\r\n"
let whitespace = [' ' '\t']+
let str = ['a'-'z' 'A'-'Z' '0'-'9' '_' ' ' '\''] | symbol | newline
let ident = ['a'-'z' 'A'-'Z'] ['a'- 'z' 'A'-'Z' '0'-'9' '_' '.']*

rule token = parse
  | whitespace  {token lexbuf}
  | newline     {next_line lexbuf; token lexbuf}
  | int as i    {with_pos lexbuf (INT (int_of_string i))}
  | float as f  {with_pos lexbuf (FLOAT (float_of_string f))}
  | '{'         {with_pos lexbuf LBRACE}
  | '}'         {with_pos lexbuf RBRACE}
  | "()"        {with_pos lexbuf UNIT}
  | '('         {with_pos lexbuf LPAREN}
  | ')'         {with_pos lexbuf RPAREN}
  | '['         {with_pos lexbuf LBRACK}
  | ']'         {with_pos lexbuf RBRACK}
  | '|'         {with_pos lexbuf PIPE}
  | "(*"        {skip_multiline_comment 0 lexbuf}
  | '`'         {with_pos lexbuf BTICK}
  | ':'         {with_pos lexbuf COLON}
  | ';'         {with_pos lexbuf SEMI}
  | ";;"        {with_pos lexbuf SEMISEMI}
  | ','         {with_pos lexbuf COMMA}
  | '_'         {with_pos lexbuf WILDCARD}
  | op+ as op'
    {let tok = match (List.assoc_opt op' builtin_symbol) with
              | (Some op') -> op'
              | None        -> OP op'
     in with_pos lexbuf tok}
  | '\''        {tokenize_char lexbuf}
  | '\"'        {tokenize_string (Buffer.create 20) lexbuf}
  | ident as i
    {let tok = match (List.assoc_opt i keywords) with
                | (Some t)                     -> t
                | None when is_upper i         -> UPPER_IDENT i
                | None when is_dot_separated i -> DOT_SEP_IDENT (String.split_on_char '.' i)
                | None                         -> IDENT i
      in with_pos lexbuf tok}
  | eof         {with_pos lexbuf EOF}
  | _ as c      {
    let err = (Some (Location.of_lexbuf lexbuf), Printf.sprintf "Unrecognised character: '%c'." c) in
    report_err err
  }
and tokenize_char = parse
  | '\\' {tokenize_control lexbuf}
  | ((['a'-'z' 'A'-'Z' '0'-'9' '_'] | symbol) as c) '\'' {with_pos lexbuf (CHAR c)}
  | _ as c {
    let err = (Some (Location.of_lexbuf lexbuf), Printf.sprintf "Invalid char: %c" c) in
    report_err err
  }
and tokenize_control = parse
  | 'n' '\'' {with_pos lexbuf (CHAR '\n')}
  | 't' '\'' {with_pos lexbuf (CHAR '\t')}
  | 'b' '\'' {with_pos lexbuf (CHAR '\b')}
  | 'r' '\'' {with_pos lexbuf (CHAR '\r')}
  | '\\' '\'' {with_pos lexbuf (CHAR '\\')}
  | _ as c {
    let err = (Some (Location.of_lexbuf lexbuf), Printf.sprintf "Invalid escape sequence: %c" c) in
    report_err err
  }
and tokenize_string buf = parse
  | '\"'     {with_pos lexbuf (STRING (Buffer.contents buf))}
  | str as s {Buffer.add_string buf s; tokenize_string buf lexbuf}
  | eof      {
    let err = (Some (Location.of_lexbuf lexbuf), "Unterminated string.") in
    report_err err
  }
  | _ as c {
    let err = (Some (Location.of_lexbuf lexbuf), Printf.sprintf "Invalid string char: %c" c) in
    report_err err
  }
and skip_multiline_comment nesting = parse
  | "(*"    {skip_multiline_comment (nesting + 1) lexbuf}
  | "*)"    {if nesting = 0 then (token lexbuf) else (skip_multiline_comment (nesting - 1) lexbuf)}
  | newline {next_line lexbuf; skip_multiline_comment nesting lexbuf}
  | _       {skip_multiline_comment nesting lexbuf}
  | eof     {
    let err = (Some (Location.of_lexbuf lexbuf), "Unterminated comment.") in
    report_err err
  }
